# ruff: noqa: I001
from __future__ import annotations
__all__ = [
    'CLI_PRINCIPLES',
    'CLI_SEVEN_PRINCIPLES',
    'SCRIPT_SIX_PRINCIPLES',
    'CLIBestPracticesEngine',
    'CLIComplianceReport',
    'ComplianceReport',
    'ErrorResult',
    'ScriptComplianceReport',
    'ScriptInvocationResult',
    'ScriptOptimizationResult',
    'ScriptOptimizerAnalyzer',
    'check_cli_flag_compliance',
    'check_module_standards',
    'describe_script_layout',
    'generate_script_report',
    'generate_scripts_segment',
    'optimize_script_invocation',
    'validate_black_box',
    'wrap_with_error_isolation',
]
import ast
import copy
import inspect
import io
import keyword
import math
import os
import re
import shlex
import subprocess
import tokenize
from collections.abc import Callable
from dataclasses import dataclass, field
from functools import lru_cache, wraps
from pathlib import Path
from typing import Any, ClassVar
from jwsgj.build_script_generation import (
    declares_cli_flag,
    detect_cli_json_flag,
    enhance_script_agent_friendly,
    generate_scripts_for_skill,
    has_main_entry_guard,
    _main_rebound_after,
    parse_tree_for_enhance,
    read_script_text,
    strip_bom_prefix,
)
from jwsgj.build_text_scoring import (
    GRADE_BANDS_RATIO,
    band_to_grade,
    normalize_keywords,
)
from jwsgj.diag_guard_io import atomic_replace_bytes, fs_path_text
from jwsgj.diag_shared_ast_bindings import (
    binding_names_of,
    build_scope_index,
)
from jwsgj.diag_shared_ast_nodes import (
    build_parent_map,
    iter_arg_nodes,
    iter_module_scope_funcdefs,
    iter_module_scope_nodes,
    own_scope_line_span,
    resolve_import_binding,
)
from jwsgj.diag_shared_ast_views import (
    parent_map as import_parent_map,
    scope_import_tables,
)
from jwsgj.diag_types_normalize import signal_bool
from jwsgj.diag_types_vocab import (
    FIELD_RECOMMENDATIONS,
    PARSE_DEGRADE_EXC,
)
from jwsgj.log_config import get_module_logger
from jwsgj.skill_profile import (
    LAYOUT_DOC,
    LAYOUT_EMPTY,
    LAYOUT_FLAT,
    LAYOUT_OTHER,
    LAYOUT_SCRIPTS,
    LAYOUT_SRC,
    detect_layout,
)
from jwsgj.diag_taint_dataflow import lookup_name_assignment
from jwsgj.prevention_scope_facts import walk_nodes
logger = get_module_logger(__name__, __file__)
CLI_SEVEN_PRINCIPLES = {
    "non_interactive": {
        "name": "非交互式",
        "description": "脚本必须能完全以命令行参数运行，不需要任何用户输入",
        "check": "检查源码是否出现 input( 交互调用",
        "weight": 0.20,
    },
    "structured_output": {
        "name": "结构化输出",
        "description": "输出应为 JSON/YAML 等可解析格式，或带明确分隔符的文本",
        "check": "检查源码是否使用 json.dumps 结构化输出",
        "weight": 0.18,
    },
    "error_guidance": {
        "name": "错误指导",
        "description": "错误信息须包含：什么错了 + 为什么 + 怎么修复",
        "check": "检查源码是否含 error 字样与 fix/suggestion/修复 关键词",
        "weight": 0.15,
    },
    "safe_retry": {
        "name": "安全重试",
        "description": "幂等操作确保重复执行不会产生副作用",
        "check": "检查写盘调用是否配套 .tmp/mkstemp+replace 原子写入痕迹（只读 open 不计写盘）",
        "weight": 0.12,
    },
    "progressive_help": {
        "name": "渐进帮助",
        "description": "支持 --help 和 --version，帮助信息按场景分组",
        "check": "检查显式 --help 声明或 ArgumentParser 实际解析命令行",
        "weight": 0.12,
    },
    "command_consistency": {
        "name": "命令一致性",
        "description": "同一技能下所有脚本的参数命名、行为模式保持一致",
        "check": "检查是否避免裸 -o 短选项（已含 --output 时不判）",
        "weight": 0.10,
    },
    "output_boundary": {
        "name": "输出边界",
        "description": "输出大小可控，避免向 stdout 倾泻大量数据",
        "check": "检查是否有输出截断/分页机制",
        "weight": 0.13,
    },
}
SCRIPT_SIX_PRINCIPLES = {
    "black_box": {
        "name": "黑盒封装",
        "description": "Agent 不需要理解脚本内部实现，只需知道输入输出",
        "check": "检查脚本前 500 字符是否含三引号说明块",
        "weight": 0.20,
    },
    "stateless": {
        "name": "无状态",
        "description": "每次调用独立，不依赖前次调用的内存状态",
        "check": "检查是否出现 global 声明（模块级可变状态不在判据内）",
        "weight": 0.18,
    },
    "strong_validation": {
        "name": "强校验",
        "description": "输入参数在脚本入口处就完成校验，提前失败",
        "check": "检查是否含 raise/assert 提前失败",
        "weight": 0.17,
    },
    "structured_response": {
        "name": "结构化响应",
        "description": "返回值应包含 ok/error/data 等标准字段",
        "check": "检查返回字面量是否含 ok/status 键",
        "weight": 0.15,
    },
    "exception_isolation": {
        "name": "异常隔离",
        "description": "异常不向上冒泡，而是转为结构化错误信息",
        "check": "检查是否含 except 异常捕获",
        "weight": 0.15,
    },
    "observability": {
        "name": "可观测性",
        "description": "关键步骤有日志/进度输出，方便 Agent 判断执行状态",
        "check": "检查是否含 print(/logging/logger 进度输出",
        "weight": 0.15,
    },
}
_ATOMIC_TEMP_RE = re.compile(r"\.tmp\b|NamedTemporaryFile|mkstemp")
_TEMP_FILE_CREATORS = frozenset({"NamedTemporaryFile", "mkstemp"})
_TEMP_PATH_PROJECTION_METHODS = frozenset({
    "with_name", "with_suffix", "with_stem",
})
_PATH_CONSTRUCTORS = frozenset({
    "Path", "PurePath", "PurePosixPath", "PureWindowsPath",
})
_PATH_OBJECT_FACTORY_METHODS = _TEMP_PATH_PROJECTION_METHODS | frozenset({
    "joinpath", "with_segments",
})
_PATH_OBJECT_METHODS = _PATH_OBJECT_FACTORY_METHODS | frozenset({
    "resolve", "absolute", "expanduser",
})
_DIRECT_WRITE_RE = re.compile(
    r"\bopen\s*\(|\.write_text\s*\(|\.write_bytes\s*\(")
@lru_cache(maxsize=128)
def _parse_source_tree(source: str) -> ast.Module | None:
    try:
        return ast.parse(strip_bom_prefix(source))
    except (SyntaxError, ValueError, MemoryError, RecursionError):
        return None
def _code_only_text(source: str) -> str:
    try:
        tokens = tokenize.generate_tokens(io.StringIO(source).readline)
        kept = [tok.string for tok in tokens
                if tok.type not in (tokenize.COMMENT, tokenize.STRING)]
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError):
        return source
    return " ".join(kept)
def _has_interactive_input(source: str) -> bool:
    tree = _parse_source_tree(source)
    if tree is not None:
        imports = scope_import_tables(tree)
        parents = import_parent_map(tree)
        for node in walk_nodes(tree):
            if not isinstance(node, ast.Call):
                continue
            if (isinstance(node.func, ast.Name)
                    and node.func.id in ("input", "getpass")):
                return True
            module, member = _imported_call_origin(node, imports, parents)
            if (member in ("input", "getpass")
                    and module in {"builtins", "__builtins__", "getpass"}):
                return True
        return False
    return bool(re.search(
        r"(?<![\w.])(?:input|getpass)\s*\(", _code_only_text(source)))
def _has_global_statement(source: str) -> bool:
    tree = _parse_source_tree(source)
    if tree is not None:
        return any(isinstance(node, ast.Global) for node in walk_nodes(tree))
    return bool(re.search(
        r"(?m)^\s*global\s+\w+", _code_only_text(source)))
def _called_name(node: ast.Call) -> str:
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        return node.func.attr
    return ""
@lru_cache(maxsize=128)
def _implementation_text(source: str) -> str:
    tree = _parse_source_tree(source)
    if tree is None:
        return ""
    executable_tree = copy.deepcopy(tree)
    for node in walk_nodes(executable_tree):
        if (isinstance(node, ast.Expr)
                and isinstance(node.value, ast.Constant)
                and isinstance(node.value.value, str)):
            node.value.value = ""
    return ast.unparse(executable_tree)
def _has_structured_output(source: str) -> bool:
    tree = _parse_source_tree(source)
    if tree is None:
        return False
    imports = scope_import_tables(tree)
    parents = import_parent_map(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        module, member = _imported_call_origin(node, imports, parents)
        if (module in {"json", "yaml"}
                and re.fullmatch(r"\w*dump\w*", member) is not None):
            return True
    return False
def _has_error_guidance(source: str) -> bool:
    implementation = _implementation_text(source).lower()
    return ("error" in implementation
            and any(keyword in implementation
                    for keyword in ("fix", "suggestion", "修复")))
def _has_cli_flag_use(source: str, flag: str) -> bool:
    if declares_cli_flag(source, flag):
        return True
    tree = _parse_source_tree(source)
    if tree is None:
        return False
    return any(
        isinstance(node, ast.Compare) and any(
            isinstance(item, ast.Constant) and item.value == flag
            for item in walk_nodes(node))
        for node in walk_nodes(tree))
def _has_consistent_output_flags(source: str) -> bool:
    if _has_cli_flag_use(source, "--output"):
        return True
    return not _has_cli_flag_use(source, "-o")
def _has_output_boundary(source: str) -> bool:
    tree = _parse_source_tree(source)
    if tree is None:
        return False
    if any(isinstance(node, ast.Slice) and node.upper is not None
           for node in walk_nodes(tree)):
        return True
    if declares_cli_flag(source, "--limit"):
        return True
    for node in walk_nodes(tree):
        if (isinstance(node, ast.keyword) and node.arg
                and node.arg.lower() in _OUTPUT_BOUNDARY_NAMES):
            return True
    return False
def _has_strong_validation(source: str) -> bool:
    tree = _parse_source_tree(source)
    return bool(tree is not None and any(
        isinstance(node, (ast.Raise, ast.Assert)) for node in walk_nodes(tree)))
def _has_structured_response(source: str) -> bool:
    tree = _parse_source_tree(source)
    if tree is None:
        return False
    return any(
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Dict)
        and any(
            isinstance(key, ast.Constant) and key.value in {"ok", "status"}
            for key in node.value.keys)
        for node in walk_nodes(tree))
def _has_exception_isolation(source: str) -> bool:
    tree = _parse_source_tree(source)
    return bool(tree is not None and any(
        isinstance(node, _TRY_TYPES) and bool(node.handlers)
        for node in walk_nodes(tree)))
_OBSERVABILITY_METHODS = frozenset({
    "debug", "info", "warning", "warn", "error", "exception",
    "critical", "fatal", "log",
})
def _is_logger_owner(node: ast.AST) -> bool:
    for owner in walk_nodes(node):
        if isinstance(owner, ast.Name):
            name = owner.id.lower()
            if (name in {"logging", "log"}
                    or name.endswith(("logger", "_log"))):
                return True
        elif (isinstance(owner, ast.Attribute)
              and owner.attr.lower().endswith(("logger", "_log"))):
            return True
    return False
def _has_observability(source: str) -> bool:
    tree = _parse_source_tree(source)
    if tree is None:
        return False
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        called = _called_name(node)
        if called == "print":
            return True
        if (isinstance(node.func, ast.Attribute)
                and called in _OBSERVABILITY_METHODS
                and _is_logger_owner(node.func.value)):
            return True
    return False
def _imported_call_origin(
        node: ast.Call, imports: dict, parents: dict) -> tuple[str, str]:
    func = node.func
    if isinstance(func, ast.Name):
        record = resolve_import_binding(imports, parents, node, func.id)
        if record is not None and record[0] == "from":
            return record[1], record[2]
        return "", func.id
    if not (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)):
        return "", ""
    owner = func.value
    record = resolve_import_binding(imports, parents, node, owner.id)
    if record is not None:
        if record[0] == "import":
            return record[1], func.attr
        if record[0] == "from":
            return f"{record[1]}.{record[2]}", func.attr
    return owner.id, func.attr
def _assignment_statement(node: ast.AST, parents: dict[int, ast.AST]):
    owner: ast.AST | None = node
    assignment_types = (ast.Assign, ast.AnnAssign, ast.AugAssign)
    while owner is not None and not isinstance(owner, assignment_types):
        owner = parents.get(id(owner))
    return owner
def _nearest_assignment_if(
        statement: ast.AST, parents: dict[int, ast.AST]) -> ast.If | None:
    owner: ast.AST | None = statement
    while owner is not None:
        owner = parents.get(id(owner))
        if isinstance(owner, ast.If):
            return owner
        if isinstance(owner, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda, ast.ClassDef, ast.Module)):
            break
    return None
def _latest_name_assignment(statements: list[ast.stmt], name: str):
    assignments = []
    stack: list[ast.AST] = list(reversed(statements))
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda, ast.ClassDef)):
            continue
        targets: list[ast.AST] = []
        if isinstance(node, ast.Assign):
            targets = list(node.targets)
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
            if isinstance(node, ast.AnnAssign) and node.value is None:
                continue
            targets = [node.target]
        if any(name in binding_names_of(target) for target in targets):
            assignments.append(node)
        stack.extend(reversed(list(ast.iter_child_nodes(node))))
    return max(assignments, key=lambda node: (
        getattr(node, "lineno", 0), getattr(node, "col_offset", 0)), default=None)
def _name_assignment_value(statement: ast.AST, name: str) -> ast.AST | None:
    if isinstance(statement, ast.Assign) and any(
            isinstance(target, ast.Name) and target.id == name
            for target in statement.targets):
        return statement.value
    if (isinstance(statement, ast.AnnAssign)
            and isinstance(statement.target, ast.Name)
            and statement.target.id == name):
        return statement.value
    return None
def _conditional_assignment_is_temp(
        assigned: ast.AST, name: str, tree: ast.Module, scope: str,
        scope_idx: dict[int, str], parents: dict[int, ast.AST],
        boundary_if: ast.If | None = None,
        seen: frozenset[int] = frozenset()) -> bool:
    statement = _assignment_statement(assigned, parents)
    if statement is None:
        return _is_temp_path_expression_at(
            assigned, tree, scope_idx, parents, seen)
    if_node = _nearest_assignment_if(statement, parents)
    if if_node is None or if_node is boundary_if:
        return _is_temp_path_expression_at(
            assigned, tree, scope_idx, parents, seen)
    for branch in (if_node.body, if_node.orelse):
        branch_assignment = _latest_name_assignment(branch, name)
        if branch_assignment is None:
            value = lookup_name_assignment(
                tree, name, if_node.lineno, scope, scope_idx,
                getattr(if_node, "col_offset", None))
        else:
            value = _name_assignment_value(branch_assignment, name)
        if value is None or not _conditional_assignment_is_temp(
                value, name, tree, scope, scope_idx, parents, if_node, seen):
            return False
    return True
def _is_temp_path_expression_at(
        node: ast.AST, tree: ast.Module, scope_idx: dict[int, str],
        parents: dict[int, ast.AST], seen: frozenset[int] | None = None) -> bool:
    seen = frozenset() if seen is None else seen
    if id(node) in seen:
        return False
    next_seen = seen | {id(node)}
    for item in walk_nodes(node):
        if not (isinstance(item, ast.Call)
                and isinstance(item.func, ast.Attribute)
                and item.func.attr in _TEMP_PATH_PROJECTION_METHODS):
            continue
        replacement = (item.args[0] if item.args else next(
            (kw.value for kw in item.keywords
             if kw.arg in {"name", "suffix", "stem"}), None))
        if (replacement is None or not _is_temp_path_expression_at(
                replacement, tree, scope_idx, parents, next_seen)):
            return False
    for item in walk_nodes(node):
        if isinstance(item, ast.IfExp):
            branches = (item.body, item.orelse)
        elif isinstance(item, ast.BoolOp):
            branches = tuple(item.values)
        else:
            continue
        if not all(_is_temp_path_expression_at(
                branch, tree, scope_idx, parents, next_seen)
                for branch in branches):
            return False
    if any(
        (isinstance(item, ast.Constant) and isinstance(item.value, str)
         and _ATOMIC_TEMP_RE.search(item.value))
        or (isinstance(item, ast.Call)
            and _called_name(item) in _TEMP_FILE_CREATORS)
        for item in walk_nodes(node)
    ):
        return True
    for item in walk_nodes(node):
        if not isinstance(item, ast.Name):
            continue
        owner: ast.AST | None = item
        scope = ""
        while owner is not None:
            indexed_scope = scope_idx.get(id(owner))
            if indexed_scope is not None:
                scope = indexed_scope
                break
            owner = parents.get(id(owner))
        assigned = lookup_name_assignment(
            tree, item.id, getattr(item, "lineno", 0), scope, scope_idx,
            getattr(item, "col_offset", None))
        if assigned is not None and _conditional_assignment_is_temp(
                assigned, item.id, tree, scope, scope_idx, parents,
                seen=next_seen):
            return True
    return False
def _is_path_object_expression_at(
        node: ast.AST, tree: ast.Module, scope_idx: dict[int, str],
        parents: dict[int, ast.AST], imports: dict,
        seen: frozenset[int] = frozenset()) -> bool:
    if id(node) in seen:
        return False
    next_seen = seen | {id(node)}
    if isinstance(node, ast.Call):
        module, member = _imported_call_origin(
            node, imports, import_parent_map(tree))
        if member in _PATH_CONSTRUCTORS and module in {"", "pathlib"}:
            return True
        if (isinstance(node.func, ast.Attribute)
                and node.func.attr in _PATH_OBJECT_METHODS):
            if node.func.attr in _PATH_OBJECT_FACTORY_METHODS:
                return True
            return _is_path_object_expression_at(
                node.func.value, tree, scope_idx, parents, imports, next_seen)
    if isinstance(node, (ast.IfExp, ast.BoolOp)):
        branches = ((node.body, node.orelse) if isinstance(node, ast.IfExp)
                    else tuple(node.values))
        return all(_is_path_object_expression_at(
            branch, tree, scope_idx, parents, imports, next_seen)
            for branch in branches)
    if not isinstance(node, ast.Name):
        return False
    owner: ast.AST | None = node
    scope = ""
    while owner is not None:
        indexed_scope = scope_idx.get(id(owner))
        if indexed_scope is not None:
            scope = indexed_scope
            break
        owner = parents.get(id(owner))
    assigned = lookup_name_assignment(
        tree, node.id, getattr(node, "lineno", 0), scope, scope_idx,
        getattr(node, "col_offset", None))
    return assigned is not None and _is_path_object_expression_at(
        assigned, tree, scope_idx, parents, imports, next_seen)
def _path_expression_fingerprint(
        node: ast.AST, tree: ast.Module, scope_idx: dict[int, str],
        parents: dict[int, ast.AST],
        seen: frozenset[int] = frozenset()) -> tuple[Any, ...]:
    if id(node) in seen:
        return ("cycle",)
    next_seen = seen | {id(node)}
    if isinstance(node, ast.Name):
        owner: ast.AST | None = node
        scope = ""
        while owner is not None:
            indexed_scope = scope_idx.get(id(owner))
            if indexed_scope is not None:
                scope = indexed_scope
                break
            owner = parents.get(id(owner))
        assigned = lookup_name_assignment(
            tree, node.id, getattr(node, "lineno", 0), scope, scope_idx,
            getattr(node, "col_offset", None))
        if isinstance(assigned, (ast.Assign, ast.AnnAssign)):
            assigned = _name_assignment_value(assigned, node.id)
        if assigned is not None and assigned is not node:
            return _path_expression_fingerprint(
                assigned, tree, scope_idx, parents, next_seen)
        return "name", scope, node.id
    if isinstance(node, ast.Call):
        called = _called_name(node)
        if called in _TEMP_FILE_CREATORS:
            return ("temp-file", called, getattr(node, "lineno", 0),
                    getattr(node, "col_offset", 0))
        if (called in _PATH_CONSTRUCTORS | {"str", "fspath"}
                and len(node.args) == 1 and not node.keywords):
            return _path_expression_fingerprint(
                node.args[0], tree, scope_idx, parents, next_seen)
        if (isinstance(node.func, ast.Attribute)
                and node.func.attr in {"resolve", "absolute", "expanduser"}):
            return _path_expression_fingerprint(
                node.func.value, tree, scope_idx, parents, next_seen)
        if (isinstance(node.func, ast.Attribute)
                and node.func.attr == "joinpath"):
            return ("join", _path_expression_fingerprint(
                node.func.value, tree, scope_idx, parents, next_seen),
                *(_path_expression_fingerprint(
                    arg, tree, scope_idx, parents, next_seen)
                  for arg in node.args))
        return ("call", getattr(node, "lineno", 0),
                getattr(node, "col_offset", 0),
                ast.dump(node, include_attributes=False))
    if isinstance(node, ast.Attribute):
        owner_key = _path_expression_fingerprint(
            node.value, tree, scope_idx, parents, next_seen)
        if node.attr == "name" and owner_key[0] == "temp-file":
            return owner_key
        return "attribute", owner_key, node.attr
    if isinstance(node, ast.BinOp):
        return ("binop", type(node.op).__name__,
                _path_expression_fingerprint(
                    node.left, tree, scope_idx, parents, next_seen),
                _path_expression_fingerprint(
                    node.right, tree, scope_idx, parents, next_seen))
    if isinstance(node, ast.JoinedStr):
        return ("joined", *(_path_expression_fingerprint(
            value, tree, scope_idx, parents, next_seen)
            for value in node.values))
    if isinstance(node, ast.FormattedValue):
        return ("formatted", _path_expression_fingerprint(
            node.value, tree, scope_idx, parents, next_seen), node.conversion,
            _path_expression_fingerprint(
                node.format_spec, tree, scope_idx, parents, next_seen)
            if node.format_spec is not None else None)
    if isinstance(node, ast.Subscript):
        owner_key = _path_expression_fingerprint(
            node.value, tree, scope_idx, parents, next_seen)
        # ``tempfile.mkstemp()[1]`` 与 ``NamedTemporaryFile().name`` 同为
        # 「临时文件句柄 → 路径」投影，须归一到 temp-file 指纹，否则
        # ``_has_atomic_write_evidence`` 拿 ``os.replace`` 源指纹去比对写入
        # 目标时会错配，把规范的 mkstemp 下标写法误判为非原子写入。
        if owner_key[0] == "temp-file":
            return owner_key
        return ("subscript", owner_key, _path_expression_fingerprint(
            node.slice, tree, scope_idx, parents, next_seen))
    if isinstance(node, ast.Slice):
        return ("slice", *(_path_expression_fingerprint(
            value, tree, scope_idx, parents, next_seen)
            if value is not None else None
            for value in (node.lower, node.upper, node.step)))
    if isinstance(node, ast.IfExp):
        return ("ifexp", _path_expression_fingerprint(
            node.body, tree, scope_idx, parents, next_seen),
            _path_expression_fingerprint(
                node.orelse, tree, scope_idx, parents, next_seen))
    if isinstance(node, ast.BoolOp):
        return (type(node.op).__name__, *(_path_expression_fingerprint(
            value, tree, scope_idx, parents, next_seen)
            for value in node.values))
    return "syntax", ast.dump(node, include_attributes=False)
def _has_atomic_write_evidence(
        source: str, target: ast.AST | None = None) -> bool:
    tree = _parse_source_tree(source)
    if tree is None:
        return False
    calls = [node for node in walk_nodes(tree) if isinstance(node, ast.Call)]
    has_temp = any(
        _called_name(node) in _TEMP_FILE_CREATORS
        for node in calls
    ) or any(
        isinstance(node, ast.Constant) and isinstance(node.value, str)
        and _ATOMIC_TEMP_RE.search(node.value)
        for node in walk_nodes(tree)
    )
    if not has_temp:
        return False
    scope_idx = build_scope_index(tree)
    parents = build_parent_map(tree)
    imports = scope_import_tables(tree)
    import_parents = import_parent_map(tree)
    target_key = (_path_expression_fingerprint(
        target, tree, scope_idx, parents) if target is not None else None)
    for node in calls:
        module, member = _imported_call_origin(node, imports, import_parents)
        if member == "replace_with_retry" or (member == "replace"
                                              and module == "os"):
            source_node = (node.args[0] if node.args else next(
                (kw.value for kw in node.keywords if kw.arg == "src"), None))
            if (source_node is not None and _is_temp_path_expression_at(
                    source_node, tree, scope_idx, parents)
                    and (target_key is None
                         or _path_expression_fingerprint(
                             source_node, tree, scope_idx, parents
                         ) == target_key)):
                return True
            continue
        func = node.func
        if not isinstance(func, ast.Attribute) or func.attr != "replace":
            continue
        owner = func.value
        if (_is_path_object_expression_at(
                owner, tree, scope_idx, parents, imports)
                and _is_temp_path_expression_at(
                    owner, tree, scope_idx, parents)
                and (target_key is None
                     or _path_expression_fingerprint(
                         owner, tree, scope_idx, parents) == target_key)):
            return True
    return False
_MODULE_OPEN_OWNERS = frozenset({"builtins", "io", "os"})
_OS_OPEN_WRITE_FLAGS = frozenset({
    "O_WRONLY", "O_RDWR", "O_APPEND", "O_CREAT", "O_TRUNC", "O_TMPFILE",
})
_OS_OPEN_READONLY_FLAGS = frozenset({
    "O_RDONLY", "O_BINARY", "O_TEXT", "O_EXCL", "O_CLOEXEC",
    "O_NOINHERIT", "O_NONBLOCK", "O_NDELAY", "O_DIRECTORY",
    "O_NOFOLLOW", "O_NOCTTY", "O_DSYNC", "O_RSYNC", "O_SYNC",
})
def _module_open_owner(
        node: ast.Call, imports: dict | None = None,
        parents: dict | None = None) -> str:
    if imports is not None and parents is not None:
        module, member = _imported_call_origin(node, imports, parents)
        if member == "open" and module in _MODULE_OPEN_OWNERS:
            return module
    func = node.func
    if (isinstance(func, ast.Attribute) and func.attr == "open"
            and isinstance(func.value, ast.Name)
            and func.value.id in _MODULE_OPEN_OWNERS):
        return func.value.id
    return ""
def _os_open_flags_are_readonly(node: ast.AST, write_mask: int) -> bool:
    if (isinstance(node, ast.Constant) and isinstance(node.value, int)
            and not isinstance(node.value, bool)):
        return not bool(node.value & write_mask)
    if (isinstance(node, ast.Attribute)
            and node.attr in _OS_OPEN_READONLY_FLAGS):
        return True
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        return (_os_open_flags_are_readonly(node.left, write_mask)
                and _os_open_flags_are_readonly(node.right, write_mask))
    return False
def _os_open_call_writes(node: ast.Call) -> bool:
    flags_node = (node.args[1] if len(node.args) >= 2 else next(
        (kw.value for kw in node.keywords if kw.arg == "flags"), None))
    if flags_node is None:
        return True
    write_mask = 0
    for name in _OS_OPEN_WRITE_FLAGS:
        write_mask |= getattr(os, name, 0)
    return not _os_open_flags_are_readonly(flags_node, write_mask)
def _open_call_writes(
        node: ast.Call, imports: dict | None = None,
        parents: dict | None = None) -> bool:
    if _module_open_owner(node, imports, parents) == "os":
        return _os_open_call_writes(node)
    mode_node: ast.AST | None = None
    if len(node.args) >= 2:
        mode_node = node.args[1]
    for keyword_arg in node.keywords:
        if keyword_arg.arg == "mode":
            mode_node = keyword_arg.value
    if mode_node is None:
        return (
            any(isinstance(arg, ast.Starred) for arg in node.args)
            or any(kw.arg is None for kw in node.keywords)
        )
    if isinstance(mode_node, ast.Constant) and isinstance(mode_node.value, str):
        return any(ch in mode_node.value for ch in "wax+")
    return True
def _iter_direct_write_calls(tree: ast.AST):
    imports = scope_import_tables(tree)
    parents = import_parent_map(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        module, member = _imported_call_origin(node, imports, parents)
        if member in _TEMP_FILE_CREATORS and module in {"", "tempfile"}:
            yield node
            continue
        func = node.func
        if isinstance(func, ast.Name):
            if (member == "open"
                    and (func.id == "open" or module in _MODULE_OPEN_OWNERS)
                    and _open_call_writes(node, imports, parents)):
                yield node
            continue
        if not isinstance(func, ast.Attribute):
            continue
        if (func.attr in ("write_text", "write_bytes")
                or (func.attr == "open"
                    and _open_call_writes(node, imports, parents))):
            yield node
def _direct_write_target(
        node: ast.Call, imports: dict | None = None,
        parents: dict | None = None) -> ast.AST | None:
    if _called_name(node) in _TEMP_FILE_CREATORS:
        return node
    func = node.func
    if isinstance(func, ast.Attribute):
        if _module_open_owner(node, imports, parents):
            if node.args:
                return node.args[0]
            return next(
                (kw.value for kw in node.keywords
                 if kw.arg in {"file", "path"}), None)
        return func.value
    if node.args:
        return node.args[0]
    return next(
        (kw.value for kw in node.keywords if kw.arg in {"file", "path"}), None)
def _has_direct_write_evidence(source: str) -> bool:
    tree = _parse_source_tree(source)
    if tree is None:
        return bool(_DIRECT_WRITE_RE.search(source))
    return any(True for _node in _iter_direct_write_calls(tree))
def _file_writes_are_retry_safe(source: str) -> bool:
    tree = _parse_source_tree(source)
    if tree is None:
        return not _has_direct_write_evidence(source)
    writes = list(_iter_direct_write_calls(tree))
    if not writes:
        return True
    scope_idx = build_scope_index(tree)
    parents = build_parent_map(tree)
    imports = scope_import_tables(tree)
    import_parents = import_parent_map(tree)
    for write in writes:
        target = _direct_write_target(write, imports, import_parents)
        if (target is None or not _is_temp_path_expression_at(
                target, tree, scope_idx, parents)):
            return False
        if not _has_atomic_write_evidence(source, target):
            return False
    return True
_OUTPUT_BOUNDARY_NAMES = frozenset({
    "maxlen", "max_len", "page_size", "page_limit", "limit",
})
@dataclass
class ComplianceReport:
    script_path: str
    total_score: float = 0.0
    grade: str = "F"
    principles: dict[str, dict[str, Any]] = field(default_factory=dict)
    passed: int = 0
    failed: int = 0
    recommendations: list[str] = field(default_factory=list)
    read_error: str = ""
@dataclass
class CLIComplianceReport(ComplianceReport):
    pass
@dataclass
class ScriptComplianceReport(ComplianceReport):
    pass
class CLIBestPracticesEngine:
    CLI_CHECKS: ClassVar[dict[str, Any]] = {
        "non_interactive": lambda s: (
            not _has_interactive_input(s), "检测 input()/交互调用"),
        "structured_output": lambda s: (
            _has_structured_output(s),
            "主输出建议 print(json.dumps(...)) 或 yaml.safe_dump(...)"),
        "error_guidance": lambda s: (
            _has_error_guidance(s),
            "异常信息建议含 什么错了+怎么修复"),
        "safe_retry": lambda s: (
            _file_writes_are_retry_safe(s),
            "文件写入建议临时文件+原子重命名"),
        "progressive_help": lambda s: (
            _has_executable_argparse_help(s)
            or declares_cli_flag(s, "--help"),
            "建议支持 --help/--version"),
        "command_consistency": lambda s: (
            _has_consistent_output_flags(s),
            "参数命名保持一致（--output 而非混用 -o）"),
        "output_boundary": lambda s: (
            _has_output_boundary(s),
            "输出边界：建议提供截断/分页机制（如 [:500] / 分页参数）",
        ),
    }
    SCRIPT_CHECKS: ClassVar[dict[str, Any]] = {
        "black_box": lambda s: (
            '"""' in s[:500] or "'''" in s[:500],
            "顶部建议清晰用途说明与 I/O 规格"),
        "stateless": lambda s: (
            not _has_global_statement(s), "避免全局可变状态"),
        "strong_validation": lambda s: (
            _has_strong_validation(s),
            "入口处完成参数校验并提前失败"),
        "structured_response": lambda s: (
            _has_structured_response(s),
            "返回 {'ok': bool, 'data': ..., 'error': ...} 结构"),
        "exception_isolation": lambda s: (
            _has_exception_isolation(s), "顶层 try/except 包装，异常转结构化错误"),
        "observability": lambda s: (
            _has_observability(s),
            "关键步骤有日志/进度输出"),
    }
    @staticmethod
    def _read_script(script_path: str, content: str | None) -> tuple[str, str]:
        if content is not None:
            if isinstance(content, str):
                return content, ""
            error = f"content 参数非 str（{type(content).__name__}）"
            logger.warning("%s: %s", error, script_path)
            return "", error
        try:
            return read_script_text(script_path, lenient=True), ""
        except (OSError, ValueError) as e:
            error = f"脚本读取失败: {e}"
            logger.warning("%s: %s", error, script_path)
            return "", error
    @classmethod
    def _evaluate_principles(cls, source: str,
                             principles: dict[str, dict[str, Any]],
                             checks: dict[str, Any]) -> dict[str, dict[str, Any]]:
        report: dict[str, dict[str, Any]] = {}
        for key, meta in principles.items():
            entry = {"name": meta["name"], "passed": False,
                     "weight": meta["weight"], "detail": ""}
            check_fn = checks.get(key)
            if check_fn is None:
                entry["detail"] = "检查函数缺失（principles 与 checks 的 key 不同步）"
            else:
                try:
                    entry["passed"], entry["detail"] = check_fn(source)
                except Exception as e:  # noqa: BLE001
                    logger.warning(
                        "[CLIBestPracticesEngine] 检查函数执行异常（按未通过评估）"
                        "key=%s: %s", key, e)
                    entry["detail"] = f"检查函数执行异常: {e}"
            report[key] = entry
        return report
    @classmethod
    def _summarize(cls, report: dict[str, dict[str, Any]],
                   principles: dict[str, dict[str, Any]]) -> tuple[float, int, int]:
        total_w = sum(m["weight"] for m in principles.values())
        passed_entries = [m for m in report.values() if m["passed"]]
        passed_w = sum(m["weight"] for m in passed_entries)
        passed = len(passed_entries)
        failed = len(report) - passed
        score = (passed_w / total_w * 100.0) if total_w > 0 else 0.0
        return round(score, 1), passed, failed
    @classmethod
    def _build_report(cls, script_path: str, source: str,
                      principles: dict[str, dict[str, Any]],
                      checks: dict[str, Any],
                      report_cls: type,
                      read_error: str = "") -> CLIComplianceReport | ScriptComplianceReport:
        if read_error:
            return report_cls(
                script_path=str(script_path),
                total_score=0.0,
                grade="F",
                principles={},
                passed=0,
                failed=len(principles),
                recommendations=[read_error],
                read_error=read_error,
            )
        principles_report = cls._evaluate_principles(source, principles, checks)
        score, passed, failed = cls._summarize(principles_report, principles)
        recs = [f"{m['name']}: {m['detail']}" for m in principles_report.values()
                if not m["passed"]]
        return report_cls(
            script_path=str(script_path),
            total_score=score,
            grade=band_to_grade(score / 100.0, GRADE_BANDS_RATIO),
            principles=principles_report,
            passed=passed,
            failed=failed,
            recommendations=recs,
        )
    @classmethod
    def check_cli_compliance(cls, script_path: str,
                             content: str | None = None) -> CLIComplianceReport:
        source, read_error = cls._read_script(script_path, content)
        return cls._build_report(script_path, source, CLI_SEVEN_PRINCIPLES,
                                 cls.CLI_CHECKS, CLIComplianceReport,
                                 read_error=read_error)
    @classmethod
    def check_script_compliance(cls, script_path: str,
                                content: str | None = None) -> ScriptComplianceReport:
        source, read_error = cls._read_script(script_path, content)
        return cls._build_report(script_path, source, SCRIPT_SIX_PRINCIPLES,
                                 cls.SCRIPT_CHECKS, ScriptComplianceReport,
                                 read_error=read_error)
_CLI_FLAG_SPEC: tuple[tuple[str, str, tuple[str, ...], float], ...] = (
    ("has_json", "支持 --json/--output-json 结构化输出",
     ("--output-json", "--json"), 20.0),
    ("has_dry_run", "支持 --dry-run 预览", ("--dry-run", "--dry_run"), 20.0),
    ("has_quiet", "支持 --quiet 静默模式", ("--quiet",), 10.0),
    ("has_help", "支持 --help 帮助", ("--help",), 0.0),
    ("has_force", "支持 --force 强制模式", ("--force",), 10.0),
)
CLI_PRINCIPLES = {name: desc for name, desc, _, _ in _CLI_FLAG_SPEC}
_CLI_FLAG_NEEDLES = {name: needles for name, _, needles, _ in _CLI_FLAG_SPEC}
_CLI_FLAG_WEIGHTS = {name: weight for name, _, _, weight in _CLI_FLAG_SPEC}
_MODULE_STANDARD_WEIGHTS: dict[str, float] = {
    "module_doc": 0.2,
    "all_export": 0.2,
    "func_docs": 0.2,
    "type_hints": 0.2,
    "dependency_isolation": 0.1,
    "agent_example": 0.1,
}
_WEIGHT_DOCSTRING = 0.15
_WEIGHT_TYPE_HINTS = 0.15
_WEIGHT_ALL_EXPORT = 0.10
_WEIGHT_CLI_ENTRY = 0.15
_WEIGHT_MODULE_DOC = 0.15
_WEIGHT_AGENT_EXAMPLE = 0.10
_WEIGHT_TOKEN_FRIENDLY = 0.10
_WEIGHT_DEPENDENCY_ISOLATION = 0.10
@dataclass
class ScriptOptimizationResult:
    file_path: str = ""
    script_name: str = ""
    issues: list[str] = field(default_factory=list)
    priority: str = "normal"
    docstring_score: float = 0.0
    type_hint_score: float = 0.0
    all_export_score: float = 0.0
    cli_entry_score: float = 0.0
    module_doc_score: float = 0.0
    agent_example_score: float = 0.0
    token_friendly_score: float = 0.0
    dependency_isolation_score: float = 0.0
    overall_score: float = 0.0
    suggestions: list[str] = field(default_factory=list)
    optimized_content: str | None = None
    def to_dict(self) -> dict[str, Any]:
        return {
            "file_path": self.file_path,
            "script_name": self.script_name,
            "issues": self.issues,
            "priority": self.priority,
            "docstring_score": self.docstring_score,
            "type_hint_score": self.type_hint_score,
            "all_export_score": self.all_export_score,
            "cli_entry_score": self.cli_entry_score,
            "module_doc_score": self.module_doc_score,
            "agent_example_score": self.agent_example_score,
            "token_friendly_score": self.token_friendly_score,
            "dependency_isolation_score": self.dependency_isolation_score,
            "overall_score": self.overall_score,
            "suggestions": self.suggestions,
        }
@dataclass
class ErrorResult:
    error_code: str = ""
    message: str = ""
    suggestion: str = ""
@dataclass
class ScriptInvocationResult:
    script_name: str = ""
    original_score: float = 0.0
    cli_score: float = 0.0
    script_score: float = 0.0
    issues: list[str] = field(default_factory=list)
    suggestions: list[str] = field(default_factory=list)
    generated_cli_template: str = ""
    generated_module_template: str = ""
_ENABLING_CLI_FLAG_CHECKS = frozenset({
    "has_json", "has_dry_run", "has_quiet", "has_force",
})
def _cli_flag_present(content: str, needle: str, *, enabling: bool) -> bool:
    if needle.startswith("-"):
        return declares_cli_flag(content, needle, enabling=enabling)
    return needle in content
def _has_executable_argparse_help(content: str) -> bool:
    tree = _parse_source_tree(content)
    if tree is None:
        return False
    calls = [node for node in walk_nodes(tree) if isinstance(node, ast.Call)]
    has_parser = any(_called_name(node) == "ArgumentParser" for node in calls)
    has_parse = any(
        _called_name(node) in {"parse_args", "parse_known_args"}
        for node in calls
    )
    return has_parser and has_parse
def _cli_flag_check(content: str, name: str, needles: tuple[str, ...]) -> bool:
    if name == "has_help" and _has_executable_argparse_help(content):
        return True
    enabling = name in _ENABLING_CLI_FLAG_CHECKS
    return any(
        _cli_flag_present(content, needle, enabling=enabling)
        for needle in needles
    )
def check_cli_flag_compliance(content: str) -> dict[str, Any]:
    if not isinstance(content, str):
        logger.warning("check_cli_flag_compliance 内容非 str（%s），按空内容评估",
                       type(content).__name__)
        content = ""
    checks = {
        name: _cli_flag_check(content, name, needles)
        for name, needles in _CLI_FLAG_NEEDLES.items()
    }
    missing = [name for name, passed in checks.items() if not passed]
    issues = [f"缺少 {name} 支持" for name in missing]
    suggestions = [f"补齐 {name}（{CLI_PRINCIPLES[name]}）" for name in missing]
    total_weight = sum(_CLI_FLAG_WEIGHTS.values())
    passed_weight = sum(
        weight for name, weight in _CLI_FLAG_WEIGHTS.items()
        if checks.get(name))
    score = (100.0 * passed_weight / total_weight) if total_weight else 0.0
    return {
        "score": score,
        "max_score": 100.0,
        "issues": issues,
        "suggestions": suggestions,
        "checks": checks,
    }
def _module_has_all(tree: ast.AST) -> bool:
    for n in iter_module_scope_nodes(tree, descend_classes=False):
        if isinstance(n, ast.AnnAssign) and n.value is None:
            continue
        if isinstance(n, (ast.Assign, ast.AnnAssign)):
            targets = n.targets if isinstance(n, ast.Assign) else [n.target]
            if any(isinstance(t, ast.Name) and t.id == "__all__"
                   for t in targets):
                return True
    return False
def _public_funcs(tree: ast.AST) -> list[ast.FunctionDef | ast.AsyncFunctionDef]:
    return [n for n in iter_module_scope_funcdefs(tree)
            if not n.name.startswith("_")]
def _weighted_ratio_check(percent: float, *, threshold: float,
                          weight: float,
                          issue: str) -> tuple[float, str | None]:
    return percent * weight, (issue if percent < threshold else None)
def _docstring_ratio(funcs: list) -> float:
    if not funcs:
        return 1.0
    return sum(1 for f in funcs if ast.get_docstring(f)) / len(funcs)
def _type_hint_ratio(funcs: list) -> float:
    if not funcs:
        return 100.0
    scored = 0.0
    for f in funcs:
        all_args = iter_arg_nodes(f.args)
        if not all_args:
            scored += 70.0 + (30.0 if f.returns else 0.0)
            continue
        scored += 70.0 * sum(1 for a in all_args if a.annotation) / len(all_args)
        scored += 30.0 if f.returns else 0.0
    return scored / len(funcs)
def _agent_example_ratio(funcs: list) -> float:
    if not funcs:
        return 100.0
    with_example = 0
    for f in funcs:
        doc = (ast.get_docstring(f) or "").lower()
        if "agent" in doc or "示例" in doc or "example" in doc:
            with_example += 1
    return with_example / len(funcs) * 100.0
def check_module_standards(content: str) -> dict[str, Any]:
    if not isinstance(content, str):
        logger.warning("check_module_standards 内容非 str（%s），按不可评估处理",
                       type(content).__name__)
        return {"score": 0.0, "max_score": 100.0, "issues": ["内容非字符串"],
                "suggestions": ["传入 str 形态的源码后重新检查"],
                "details": {}}
    content = strip_bom_prefix(content)
    try:
        tree = ast.parse(content)
    except PARSE_DEGRADE_EXC as _e:
        logger.debug("suppressed %s: %s", type(_e).__name__, _e)
        return {"score": 0.0, "max_score": 100.0, "issues": ["语法错误"],
                "suggestions": ["修复语法错误后重新检查"], "details": {}}
    funcs = _public_funcs(tree)
    checks: list[tuple[float, str | None]] = [
        _weighted_ratio_check(
            100.0 if ast.get_docstring(tree) else 0.0,
            threshold=100.0, weight=_MODULE_STANDARD_WEIGHTS["module_doc"],
            issue="缺少模块级 docstring"),
        _weighted_ratio_check(
            100.0 if _module_has_all(tree) else 0.0,
            threshold=100.0, weight=_MODULE_STANDARD_WEIGHTS["all_export"],
            issue="缺少 __all__"),
    ]
    applicable_weight = (
        _MODULE_STANDARD_WEIGHTS["module_doc"]
        + _MODULE_STANDARD_WEIGHTS["all_export"])
    if funcs:
        checks.extend([
            _weighted_ratio_check(
                _docstring_ratio(funcs) * 100.0, threshold=80.0,
                weight=_MODULE_STANDARD_WEIGHTS["func_docs"],
                issue="部分公开函数缺少 docstring"),
            _weighted_ratio_check(
                _type_hint_ratio(funcs), threshold=50.0,
                weight=_MODULE_STANDARD_WEIGHTS["type_hints"],
                issue="类型注解覆盖率低"),
            _weighted_ratio_check(
                _agent_example_ratio(funcs), threshold=50.0,
                weight=_MODULE_STANDARD_WEIGHTS["agent_example"],
                issue="缺少 Agent 使用示例"),
        ])
        applicable_weight += (
            _MODULE_STANDARD_WEIGHTS["func_docs"]
            + _MODULE_STANDARD_WEIGHTS["type_hints"]
            + _MODULE_STANDARD_WEIGHTS["agent_example"])
    checks.append(_weighted_ratio_check(
        _dependency_isolation_score(tree), threshold=100.0,
        weight=_MODULE_STANDARD_WEIGHTS["dependency_isolation"],
        issue="缺少 try/except 依赖隔离"))
    applicable_weight += _MODULE_STANDARD_WEIGHTS["dependency_isolation"]
    score = sum(s for s, _ in checks)
    normalized = score / applicable_weight if applicable_weight > 0 else 0.0
    issues = [i for _, i in checks if i]
    return {
        "score": round(min(normalized, 100.0), 1),
        "max_score": 100.0,
        "issues": issues,
        "suggestions": [f"修复: {i}" for i in issues] if issues else [],
        "details": {
            "module_doc": bool(ast.get_docstring(tree)),
            "has_all": _module_has_all(tree),
            "applicable_weight": applicable_weight,
        },
    }
def _finite_numeric(value: Any) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    try:
        numeric = float(value)
    except (OverflowError, TypeError, ValueError):
        return None
    return numeric if math.isfinite(numeric) else None
def _compliance_score(check: dict[str, Any] | None) -> float:
    if not isinstance(check, dict):
        return 0.0
    numeric = _finite_numeric(check.get("score", 0.0))
    return numeric if numeric is not None else 0.0
def _compliance_items(check: dict[str, Any] | None, key: str) -> list:
    if not isinstance(check, dict):
        return []
    value = check.get(key)
    return list(value) if isinstance(value, (list, tuple)) else []
@dataclass(frozen=True)
class _CompliancePair:
    cli_report: dict[str, Any]
    script_report: dict[str, Any]
    cli_score: float
    script_score: float
    cli_issues: list[str]
    script_issues: list[str]
    cli_suggestions: list[str]
    script_suggestions: list[str]
def _run_dual_compliance(content: str) -> _CompliancePair:
    cli_report = check_cli_flag_compliance(content)
    script_report = check_module_standards(content)
    return _CompliancePair(
        cli_report=cli_report,
        script_report=script_report,
        cli_score=_compliance_score(cli_report),
        script_score=_compliance_score(script_report),
        cli_issues=_compliance_items(cli_report, "issues"),
        script_issues=_compliance_items(script_report, "issues"),
        cli_suggestions=_compliance_items(cli_report, "suggestions"),
        script_suggestions=_compliance_items(script_report, "suggestions"),
    )
_TRY_TYPES = (ast.Try,) + ((ast.TryStar,) if hasattr(ast, "TryStar") else ())
_CONTROL_FLOW_NODES = (
    ast.If, ast.For, ast.AsyncFor, ast.While, ast.With, ast.AsyncWith,
    *_TRY_TYPES, *((ast.Match,) if hasattr(ast, "Match") else ()),
)
def _iter_try_executed_nodes(statement: ast.stmt):
    stack = [statement]
    while stack:
        node = stack.pop()
        yield node
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            continue
        stack.extend(ast.iter_child_nodes(node))
def _module_imports(tree: ast.AST) -> list[ast.Import | ast.ImportFrom]:
    return [
        node
        for node in iter_module_scope_nodes(tree, descend_classes=False)
        if isinstance(node, (ast.Import, ast.ImportFrom))
        and getattr(node, "module", None) != "__future__"
    ]
def _has_guarded_import(tree: ast.AST) -> bool:
    imports = _module_imports(tree)
    guarded = {
        id(node)
        for tb in walk_nodes(tree)
        if isinstance(tb, _TRY_TYPES)
        for stmt in tb.body
        for node in _iter_try_executed_nodes(stmt)
        if isinstance(node, (ast.Import, ast.ImportFrom))
    }
    return bool(imports) and all(id(node) in guarded for node in imports)
def _dependency_isolation_score(tree: ast.AST) -> float:
    if not _module_imports(tree):
        return 100.0
    return 100.0 if _has_guarded_import(tree) else 0.0
def _priority_for_score(overall_score: float) -> str:
    if overall_score < 40:
        return "critical"
    if overall_score < 60:
        return "high"
    if overall_score < 80:
        return "normal"
    return "low"
def _max_control_flow_depth(node: ast.AST) -> int:
    depth = 0
    stack: list[tuple[ast.AST, int]] = [(node, 0)]
    while stack:
        current, cur = stack.pop()
        current_orelse = current.orelse if isinstance(current, ast.If) else ()
        for child in ast.iter_child_nodes(current):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.Lambda, ast.ClassDef)):
                continue
            same_layer = (
                isinstance(child, ast.If)
                and any(child is branch for branch in current_orelse)
                and (getattr(child, "col_offset", -1)
                     == getattr(current, "col_offset", -2)))
            nd = cur + 1 if (isinstance(child, _CONTROL_FLOW_NODES)
                             and not same_layer) else cur
            depth = max(depth, nd)
            stack.append((child, nd))
    return depth
def _cli_entry_suggestion(score: float, content: str,
                          tree: ast.Module | None = None) -> str | None:
    if tree is None:
        tree = parse_tree_for_enhance(content)
    if not has_main_entry_guard(content, tree):
        return "[CLI入口] 缺少if __name__ == '__main__'自测入口"
    if score >= 50:
        return None
    return "[CLI入口] 已有__main__入口，建议补充--json/--dry-run等CLI标志"
_CODING_COOKIE_RE = re.compile(r"^[ \t\f]*#.*?coding[:=][ \t]*([-\w.]+)")
def _declared_source_encoding(content: str) -> str:
    for line in content.splitlines()[:2]:
        match = _CODING_COOKIE_RE.match(line)
        if match:
            return match.group(1)
    return "utf-8"
def _strip_coding_cookie(content: str) -> str:
    lines = content.splitlines(keepends=True)
    return "".join(
        line for index, line in enumerate(lines)
        if not (index < 2 and _CODING_COOKIE_RE.match(line)))
def _encode_optimized_source(content: str) -> bytes:
    encoding = _declared_source_encoding(content)
    try:
        return content.encode(encoding)
    except (UnicodeEncodeError, LookupError) as exc:
        logger.warning(
            "优化产物无法按声明编码 %s 保存，改用 UTF-8 并移除编码声明: %s",
            encoding, exc)
        return _strip_coding_cookie(content).encode("utf-8")
class ScriptOptimizerAnalyzer:
    def _score_cli_entry(self, content: str,
                         tree: ast.Module | None = None) -> float:
        if tree is None:
            tree = parse_tree_for_enhance(content)
        score = 40.0 if has_main_entry_guard(content, tree) else 0.0
        checks = check_cli_flag_compliance(content)["checks"]
        return score + sum(
            weight for flag, weight in _CLI_FLAG_WEIGHTS.items()
            if checks.get(flag))
    def _score_module_doc(self, tree: ast.AST) -> float:
        doc = ast.get_docstring(tree)
        if not doc:
            return 0.0
        score = 40.0
        if len(doc) > 50:
            score += 30.0
        if any(kw in doc.lower() for kw in ['usage', '用法', 'example', '示例']):
            score += 30.0
        return min(score, 100.0)
    def _score_token_friendly(self, tree: ast.AST) -> float:
        funcs = [n for n in walk_nodes(tree)
                 if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
        if not funcs:
            return 100.0
        scores = []
        for f in funcs:
            fscore = 100.0
            lines = own_scope_line_span(f)
            if lines > 100:
                fscore -= 30
            elif lines > 50:
                fscore -= 15
            if _max_control_flow_depth(f) > 6:
                fscore -= 20
            scores.append(max(fscore, 0))
        return round(sum(scores) / len(scores), 1)
    def _load_script(self, path: Path,
                     result: ScriptOptimizationResult) -> str | None:
        if not path.exists():
            result.issues.append("文件不存在")
            result.priority = "critical"
            return None
        try:
            return read_script_text(path)
        except (OSError, UnicodeDecodeError) as e:
            logger.debug("suppressed (OSError, UnicodeDecodeError): %s", e)
            result.issues.append(f"读取失败: {e}")
            result.priority = "critical"
            return None
    def _parse_script(self, content: str,
                      result: ScriptOptimizationResult) -> ast.AST | None:
        try:
            return ast.parse(content)
        except PARSE_DEGRADE_EXC as e:
            logger.debug("suppressed %s: %s", type(e).__name__, e)
            result.issues.append(f"语法错误: {e}")
            result.priority = "critical"
            return None
    def _apply_dimension_scores(self, result: ScriptOptimizationResult,
                                tree: ast.AST, content: str) -> None:
        result.docstring_score = round(
            _docstring_ratio(_public_funcs(tree)) * 100, 1)
        result.type_hint_score = round(_type_hint_ratio(_public_funcs(tree)), 1)
        result.all_export_score = 100.0 if _module_has_all(tree) else 0.0
        result.cli_entry_score = self._score_cli_entry(content, tree)
        result.module_doc_score = self._score_module_doc(tree)
        result.agent_example_score = round(
            _agent_example_ratio(_public_funcs(tree)), 1)
        result.token_friendly_score = self._score_token_friendly(tree)
        result.dependency_isolation_score = _dependency_isolation_score(tree)
    def _weighted_overall(self, result: ScriptOptimizationResult, *,
                          has_public_funcs: bool,
                          has_any_funcs: bool) -> float:
        weighted = {
            "docstring": (result.docstring_score, _WEIGHT_DOCSTRING),
            "type_hint": (result.type_hint_score, _WEIGHT_TYPE_HINTS),
            "all_export": (result.all_export_score, _WEIGHT_ALL_EXPORT),
            "cli_entry": (result.cli_entry_score, _WEIGHT_CLI_ENTRY),
            "module_doc": (result.module_doc_score, _WEIGHT_MODULE_DOC),
            "agent_example": (result.agent_example_score,
                              _WEIGHT_AGENT_EXAMPLE),
            "token_friendly": (result.token_friendly_score,
                               _WEIGHT_TOKEN_FRIENDLY),
            "dependency_isolation": (result.dependency_isolation_score,
                                     _WEIGHT_DEPENDENCY_ISOLATION),
        }
        if not has_public_funcs:
            for key in ("docstring", "type_hint", "agent_example"):
                weighted.pop(key)
        if not has_any_funcs:
            weighted.pop("token_friendly")
        total_weight = sum(weight for _, weight in weighted.values())
        if total_weight <= 0:
            return 0.0
        return round(
            sum(score * weight for score, weight in weighted.values())
            / total_weight, 1)
    def analyze(self, file_path: str,
                skill_keywords: list[str] | None = None) -> ScriptOptimizationResult:
        path_text = fs_path_text(file_path)
        if not path_text:
            return ScriptOptimizationResult(
                issues=["文件路径无效"], priority="critical")
        path = Path(path_text)
        result = ScriptOptimizationResult(
            file_path=str(path), script_name=path.name)
        content = self._load_script(path, result)
        if content is None:
            return result
        tree = self._parse_script(content, result)
        if tree is None:
            return result
        self._apply_dimension_scores(result, tree, content)
        result.overall_score = self._weighted_overall(
            result, has_public_funcs=bool(_public_funcs(tree)),
            has_any_funcs=any(
                isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                for node in walk_nodes(tree)))
        result.priority = _priority_for_score(result.overall_score)
        result.suggestions = self._generate_suggestions(
            result, content, skill_keywords or [], tree)
        if result.suggestions:
            try:
                optimized = enhance_script_agent_friendly(content, path.stem)
            except Exception as exc:  # noqa: BLE001
                logger.warning("脚本增强失败，保留原内容: %s: %s", path, exc)
                result.issues.append(f"增强失败: {exc}")
                result.optimized_content = None
            else:
                result.optimized_content = (
                    optimized if optimized != content else None)
        else:
            result.optimized_content = None
        return result
    def analyze_directory(self, skill_dir: str,
                          skill_keywords: list[str] | None = None) -> list[ScriptOptimizationResult]:
        root_text = fs_path_text(skill_dir)
        if not root_text:
            return []
        root = Path(root_text)
        try:
            layout = detect_layout(str(root))
        except (OSError, ValueError) as _layout_exc:
            logger.warning("布局探测失败，降级为空脚本面: %s", _layout_exc)
            return []
        results = []
        for py_file in _analysable_script_paths(root, layout):
            try:
                result = self.analyze(str(py_file), skill_keywords)
                results.append(result)
            except Exception as e:  # noqa: BLE001
                logger.warning("分析脚本 %s 失败: %s", py_file.name, e)
        return results
    def _dimension_suggestions(self, result: ScriptOptimizationResult,
                               content: str,
                               tree: ast.Module | None = None) -> list[str]:
        suggestions: list[str] = []
        if result.module_doc_score < 60:
            suggestions.append("[模块文档] 文件顶部缺少模块级docstring，建议添加文件用途说明")
        if result.all_export_score < 80:
            suggestions.append("[导出声明] 缺少__all__声明")
        if result.docstring_score < 70:
            suggestions.append("[函数文档] 部分函数缺少docstring")
        if result.type_hint_score < 70:
            suggestions.append("[类型注解] 缺少类型注解")
        if result.agent_example_score < 50:
            suggestions.append("[Agent示例] 缺少Agent使用示例")
        cli_suggestion = _cli_entry_suggestion(
            result.cli_entry_score, content, tree)
        if cli_suggestion:
            suggestions.append(cli_suggestion)
        if result.token_friendly_score < 60:
            suggestions.append("[Token友好] 函数过长或嵌套过深")
        if result.dependency_isolation_score < 60:
            suggestions.append("[依赖隔离] 外部导入缺少try/except保护")
        return suggestions
    def _keyword_suggestions(self, content: str,
                             skill_keywords: list[str]) -> list[str]:
        keywords = normalize_keywords(skill_keywords)
        if not keywords:
            return []
        combined = content.lower()
        missing = [kw for kw in keywords if kw.lower() not in combined]
        if not missing:
            return []
        return [f"[语义关联] 脚本未体现技能关键词({missing[:3]})"]
    def _generate_suggestions(self, result: ScriptOptimizationResult,
                              content: str,
                              skill_keywords: list[str],
                              tree: ast.Module | None = None) -> list[str]:
        suggestions = self._dimension_suggestions(result, content, tree)
        suggestions.extend(self._keyword_suggestions(content, skill_keywords))
        return suggestions
    def optimize(self, file_path: str, output_path: str | None = None) -> dict[str, Any]:
        result = self.analyze(file_path)
        return self._optimize_result(result, output_path)
    def _optimize_result(self, result: ScriptOptimizationResult,
                         output_path: str | None) -> dict[str, Any]:
        optimized = result.optimized_content
        target = fs_path_text(output_path) if output_path else ""
        payload = {
            "file_path": result.file_path,
            "analysis": result.to_dict(),
            "optimized_content": optimized,
            "output_path": target if (target and optimized) else None,
        }
        if not payload["output_path"]:
            return payload
        output = Path(target)
        try:
            output.parent.mkdir(parents=True, exist_ok=True)
            atomic_replace_bytes(
                str(output), _encode_optimized_source(optimized),
                prefix=f".{output.name}.", label="脚本优化产物")
        except (OSError, ValueError) as exc:
            logger.warning("脚本优化产物写入失败: %s: %s", output, exc)
            payload["output_path"] = None
            payload["error"] = f"{type(exc).__name__}: {exc}"
        return payload
    def optimize_directory(self, skill_dir: str) -> list[dict[str, Any]]:
        results = []
        for item in self.analyze_directory(skill_dir):
            if not item.file_path:
                continue
            try:
                results.append(self._optimize_result(item, None))
            except Exception as e:  # noqa: BLE001
                logger.warning("优化脚本 %s 失败，跳过: %s", item.file_path, e)
        return results
def generate_script_report(skill_dir: str,
                           skill_keywords: list[str] | None = None) -> dict[str, Any]:
    results = ScriptOptimizerAnalyzer().analyze_directory(
        skill_dir, skill_keywords)
    total = len(results)
    if total == 0:
        return {"total": 0, "average_score": 0.0, "critical_count": 0,
                "high_count": 0, "results": [],
                "message": "未找到可分析的脚本"}
    avg_score = sum(r.overall_score for r in results) / total
    critical = [r for r in results if r.priority == "critical"]
    high = [r for r in results if r.priority == "high"]
    return {
        "total": total,
        "average_score": round(avg_score, 2),
        "critical_count": len(critical),
        "high_count": len(high),
        "results": [r.to_dict() for r in results],
    }
def _evaluate_generated_scripts(skill_dir: str) -> tuple[float, int] | None:
    try:
        report = generate_script_report(skill_dir)
    except (OSError, RuntimeError, ValueError, TypeError, SyntaxError) as exc:
        logger.warning("[build_script_compliance] 脚本评测失败: %s", exc)
        return None
    if not isinstance(report, dict):
        return None
    total = report.get("total")
    numeric = _finite_numeric(report.get("average_score"))
    if (isinstance(total, bool) or not isinstance(total, int) or total <= 0
            or numeric is None):
        return None
    return numeric, total
def generate_scripts_segment(
    skill_dir: str, skill_name: str, optimized_desc: str, auto_generate_scripts: bool
) -> tuple[float, str | None, bool]:
    should_generate = signal_bool(auto_generate_scripts)
    if not skill_dir:
        return 0.0, None, False
    if not os.path.isdir(skill_dir):
        logger.warning(
            "[build_script_compliance] 目标目录不存在，跳过脚本生成与评测: %s",
            skill_dir)
        return 0.0, None, False
    if should_generate:
        purpose = optimized_desc if isinstance(optimized_desc, str) else ""
        try:
            generate_scripts_for_skill(skill_dir, skill_name, purpose[:200])
        except (OSError, RuntimeError, ValueError, TypeError) as exc:
            logger.warning("[build_script_compliance] 脚本生成失败，跳过: %s", exc)
            return 0.0, None, False
    evaluated = _evaluate_generated_scripts(skill_dir)
    if evaluated is None:
        return 0.0, None, False
    score, total = evaluated
    action = "已生成并评测" if should_generate else "已评测"
    return (
        score,
        f"scripts: {action} {total} 个脚本（Agent 友好度 {score:.1f}）",
        True,
    )
_LAYOUT_REASONS: dict[str, str] = {
    LAYOUT_SCRIPTS: "scripts_present",
    LAYOUT_FLAT: "flat_package_entrypoints",
    LAYOUT_SRC: "src_package_entrypoints",
    LAYOUT_OTHER: "non_python_code",
    LAYOUT_DOC: "documentation_only",
    LAYOUT_EMPTY: "empty_directory",
}
def describe_script_layout(skill_dir: str) -> dict[str, Any]:
    try:
        layout = detect_layout(skill_dir)
    except (OSError, ValueError) as _swallowed_exc:
        logger.debug("布局探测失败，降级为不可解释: %s", _swallowed_exc)
        return {
            "kind": "", "applicable": False, "reason": "layout_unavailable",
            "entrypoints": [], "analysable_scripts": [], "languages": [],
        }
    return {
        "kind": layout.kind,
        "applicable": bool(layout.analysable_scripts),
        "reason": _LAYOUT_REASONS.get(layout.kind, "unknown"),
        "entrypoints": list(layout.entrypoints),
        "analysable_scripts": list(layout.analysable_scripts),
        "languages": list(layout.languages),
    }
def optimize_script_invocation(
    skill_dir: str | None = None,
    script_content: str | None = None,
) -> list[dict[str, Any]] | ScriptInvocationResult:
    if script_content is not None:
        return _optimize_script_invocation_single(
            fs_path_text(skill_dir), script_content)
    root_text = fs_path_text(skill_dir)
    if not root_text:
        return []
    return _optimize_script_invocation_dir(root_text)
def _analysable_script_paths(root: Path, layout: Any) -> list[Path]:
    paths: list[Path] = []
    for relative in layout.analysable_scripts:
        candidate = root / relative
        if candidate.is_file() and candidate.suffix.lower() == ".py":
            paths.append(candidate)
    return paths
def _optimize_script_invocation_dir(skill_dir: str) -> list[dict[str, Any]]:
    if not skill_dir:
        return []
    root = Path(skill_dir)
    try:
        layout = detect_layout(skill_dir)
    except (OSError, ValueError) as _layout_exc:
        logger.warning("布局探测失败，降级为空脚本面: %s", _layout_exc)
        return []
    results: list[dict[str, Any]] = []
    for py_file in _analysable_script_paths(root, layout):
        try:
            content = read_script_text(py_file)
        except (OSError, UnicodeDecodeError) as _e:
            logger.debug("suppressed (OSError, UnicodeDecodeError): %s", _e)
            results.append({
                "script_name": py_file.name,
                "original_score": 0.0,
                "error": "无法读取文件",
                FIELD_RECOMMENDATIONS: ["检查文件编码"],
            })
            continue
        pair = _run_dual_compliance(content)
        results.append({
            "script_name": py_file.name,
            "original_score": round(pair.script_score, 1),
            "compliance": pair.script_report,
            "cli_compliance": pair.cli_report,
            FIELD_RECOMMENDATIONS: [
                str(i) for i in pair.script_issues + pair.cli_issues][:5],
        })
    return results
def _source_main_kind(source: str) -> str:
    tree = _parse_source_tree(source)
    if tree is None:
        return ""
    main_defs = [
        node for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        and node.name == "main"
    ]
    if not main_defs:
        return ""
    main_def = main_defs[-1]
    if _main_rebound_after(tree, main_def):
        return ""
    args = main_def.args
    positional = [*args.posonlyargs, *args.args]
    required_positional = positional[:len(positional) - len(args.defaults)]
    if required_positional or any(
            default is None for default in args.kw_defaults):
        return ""
    if any(isinstance(node, (ast.Yield, ast.YieldFrom))
           for statement in main_def.body
           for node in _iter_try_executed_nodes(statement)):
        return ""
    return "async" if isinstance(main_def, ast.AsyncFunctionDef) else "sync"
def _module_import_name(script_name: str) -> str:
    if not script_name:
        return ""
    path = Path(script_name)
    if path.is_absolute() or path.anchor or path.suffix.lower() != ".py":
        return ""
    if any(part in {"", ".", ".."} for part in path.parts):
        return ""
    parts = list(path.parts)
    if parts[-1] == "__init__.py":
        parts.pop()
    else:
        parts[-1] = path.stem
    if parts == ["__main__"]:
        return ""
    if not parts or any(
            not part.isidentifier() or keyword.iskeyword(part)
            for part in parts):
        return ""
    return ".".join(parts)
def _quote_shell_arg(value: str) -> str:
    return (subprocess.list2cmdline([value])
            if os.name == "nt" else shlex.quote(value))
def _invocation_templates(
    script_name: str,
    json_flag: str,
    *,
    dry_run_flag: str,
    supports_help: bool,
    main_kind: str,
) -> tuple[str, str]:
    if not script_name:
        return "", ""
    module_name = _module_import_name(script_name)
    script_arg = _quote_shell_arg(script_name)
    cli_lines = ([f"python {script_arg} {_quote_shell_arg(json_flag)}"]
                 if json_flag else [])
    if dry_run_flag:
        cli_lines.append(
            f"python {script_arg} {_quote_shell_arg(dry_run_flag)}")
    if supports_help:
        cli_lines.append(f"python {script_arg} --help")
    cli_template = "\n".join(cli_lines)
    if main_kind == "async" and module_name:
        module_template = (
            f"import asyncio\nfrom {module_name} import main\n"
            "result = asyncio.run(main())  # 异步模块直调形态（优先于 CLI）"
        )
    elif main_kind == "sync" and module_name:
        module_template = (
            f"from {module_name} import main\n"
            "result = main()  # 模块直调形态（优先于 CLI）"
        )
    else:
        module_template = ""
    return cli_template, module_template
def _optimize_script_invocation_single(
    script_name: str, script_content: str,
) -> ScriptInvocationResult:
    if not isinstance(script_content, str):
        return ScriptInvocationResult(
            script_name=script_name,
            issues=["脚本内容非字符串"],
            suggestions=["传入 str 形态的脚本源码"],
        )
    pair = _run_dual_compliance(script_content)
    cli_checks = (pair.cli_report.get("checks", {})
                  if isinstance(pair.cli_report, dict) else {})
    cli_template, module_template = _invocation_templates(
        script_name,
        detect_cli_json_flag(script_content),
        dry_run_flag=next((
            flag for flag in ("--dry-run", "--dry_run")
            if declares_cli_flag(script_content, flag, enabling=True)
        ), ""),
        supports_help=cli_checks.get("has_help") is True,
        main_kind=_source_main_kind(script_content),
    )
    return ScriptInvocationResult(
        script_name=script_name,
        original_score=round(pair.script_score, 1),
        cli_score=round(pair.cli_score, 1),
        script_score=round(pair.script_score, 1),
        issues=pair.cli_issues + pair.script_issues,
        suggestions=pair.cli_suggestions + pair.script_suggestions,
        generated_cli_template=cli_template,
        generated_module_template=module_template,
    )
def _isolated_error_result(exc: Exception) -> ErrorResult:
    logger.warning("suppressed Exception: %s", exc)
    return ErrorResult(
        error_code="E999", message=str(exc),
        suggestion="检查函数参数和环境",
    )
def wrap_with_error_isolation(func: Callable) -> Callable:
    is_async_generator = (
        inspect.isasyncgenfunction(func)
        or inspect.isasyncgenfunction(func.__call__)
    )
    if is_async_generator:
        @wraps(func)
        async def async_generator_wrapper(*args: Any, **kwargs: Any) -> Any:
            try:
                async for item in func(*args, **kwargs):
                    yield item
            except Exception as exc:  # noqa: BLE001
                yield _isolated_error_result(exc)
        return async_generator_wrapper
    is_generator = (
        inspect.isgeneratorfunction(func)
        or inspect.isgeneratorfunction(func.__call__)
    )
    if is_generator:
        @wraps(func)
        def generator_wrapper(*args: Any, **kwargs: Any) -> Any:
            try:
                yield from func(*args, **kwargs)
            except Exception as exc:  # noqa: BLE001
                yield _isolated_error_result(exc)
        return generator_wrapper
    is_async_callable = (
        inspect.iscoroutinefunction(func)
        or inspect.iscoroutinefunction(func.__call__)
    )
    if is_async_callable:
        @wraps(func)
        async def async_wrapper(*args: Any, **kwargs: Any) -> Any:
            try:
                return await func(*args, **kwargs)
            except Exception as exc:  # noqa: BLE001
                return _isolated_error_result(exc)
        return async_wrapper
    @wraps(func)
    def wrapper(*args: Any, **kwargs: Any) -> Any:
        try:
            return func(*args, **kwargs)
        except Exception as exc:  # noqa: BLE001
            return _isolated_error_result(exc)
    return wrapper
def validate_black_box(input_data: Any, validator: Callable) -> bool:
    try:
        return bool(validator(input_data))
    except Exception as _e:  # noqa: BLE001
        logger.warning("suppressed Exception: %s", _e)
        return False

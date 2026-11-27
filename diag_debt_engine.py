from __future__ import annotations  # noqa: I001
import ast as _ast
import hashlib
import io
import logging
import math
import os
import re
import symtable as _symtable
import time
import tokenize
from collections import OrderedDict
from collections.abc import Iterable, Mapping
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, ClassVar, NamedTuple
from jwsgj.diag_shared_ast_bindings import ScopeNameResolver
from jwsgj.diag_shared_ast_nodes import (
    TRY_STAR,
    calc_nesting,
    class_body_owner,
    collect_annotation_names,
    cyclomatic_complexity,
    has_type_hints,
    is_shell_true_keyword,
    iter_scope_statements,
    own_scope_line_span,
)
from jwsgj.diag_shared_ast_views import parent_map
from jwsgj.diag_shared_source_core import (
    count_lines,
    is_rule_name_constant,
    read_cached,
)
from jwsgj.diag_types_vocab import (
    MSG_SYNTAX_ERROR_SKIP,
    PARSE_DEGRADE_EXC,
    GateDecision,
)
from jwsgj.diag_types_vocab import (
    SENSITIVE_NAME_KEYWORDS as _SENSITIVE_NAME_KEYWORDS,
)
from jwsgj.log_config import write_module_run
from jwsgj.prevention_scope_facts import walk_nodes
_log = logging.getLogger(__name__)
_log.addHandler(logging.NullHandler())
WARN_THRESHOLD = 50
MAX_DUPLICATE_LINES = 6
MAX_NESTING_DEBT = 4
MAX_CLASS_LINES_DEBT = 300
MAX_METHOD_LINES_DEBT = 50
MAX_FUNCTION_LINES_DEBT = 100
_BLOAT_FUNC_LINES = 50
_BLOAT_CLASS_LINES = 200
_TRY_NODE_TYPES = (_ast.Try, TRY_STAR)
_RISKY_CALL_EXACT = frozenset({
    "open", "connect", "urlopen", "request", "socket", "exec", "eval",
    "builtins.open", "builtins.exec", "builtins.eval",
    "os.system", "subprocess.run", "subprocess.Popen",
    "pickle.load", "pickle.loads", "json.load", "json.loads",
})
_RISKY_CALL_METHODS = frozenset({"connect", "urlopen", "request", "socket"})
_HTTP_PREFIX = "http://"
_HARMLESS_MAGIC_NUMBERS = frozenset({
    100, 200, 255, 500, 1000, 1024, 2048, 4096,
})
_WINDOWS_PATH_RE = re.compile(r"[A-Za-z]:[\\/][^\"']+")
_POSIX_PATH_RE = re.compile(
    "/(?:home|Users|var|etc|opt|usr|tmp|root|mnt|srv|data)/[^\"']*")
class DebtLevel(str, Enum):
    PASS = "PASS"
    WARN = "WARN"
    BLOCK = "BLOCK"
@dataclass
class DebtReport:
    total_score: int = 0
    level: DebtLevel = DebtLevel.PASS
    blocked: bool = False
    dimensions: dict[str, dict[str, Any]] = field(default_factory=dict)
    issues: list[str] = field(default_factory=list)
    fix_suggestions: list[str] = field(default_factory=list)
    trend: str = "stable"
    def to_dict(self) -> dict[str, Any]:
        return {**self.__dict__, "level": self.level.value}
def _dim_result(score: int, issues: list[str] | None = None,
                fixes: list[str] | None = None, **metrics: Any) -> dict:
    return {"score": max(0, score), "issues": issues or [],
            "fixes": fixes or [], **metrics}
def _node_span_lines(node: Any) -> int:
    start = min(
        (getattr(deco, "lineno", node.lineno)
         for deco in getattr(node, "decorator_list", ()) or ()),
        default=node.lineno,
    )
    end = getattr(node, "end_lineno", None) or start
    return max(0, end - start + 1)
def _assignment_targets(node: Any) -> list | None:
    if isinstance(node, _ast.Assign):
        return list(node.targets)
    if isinstance(node, (_ast.AnnAssign, _ast.AugAssign)) and isinstance(
            node.target, (_ast.Name, _ast.Attribute)):
        return [node.target]
    return None
def _sensitive_target_name(target: Any) -> str | None:
    if isinstance(target, _ast.Name):
        return target.id
    if isinstance(target, _ast.Attribute):
        return target.attr
    return None
def _collect_all_listed(value: Any, out: set,
                        previous_all: set | None = None) -> None:
    if isinstance(value, _ast.Constant):
        if isinstance(value.value, str):
            out.add(value.value)
    elif (isinstance(value, _ast.Name) and value.id == "__all__"
          and previous_all is not None):
        out.update(previous_all)
    elif isinstance(value, (_ast.List, _ast.Tuple, _ast.Set)):
        for elt in value.elts:
            _collect_all_listed(elt, out, previous_all)
    elif (isinstance(value, _ast.BinOp)
          and isinstance(value.op, (_ast.Add, _ast.BitOr))):
        _collect_all_listed(value.left, out, previous_all)
        _collect_all_listed(value.right, out, previous_all)
    elif isinstance(value, _ast.Starred):
        _collect_all_listed(value.value, out, previous_all)
def _iu_register_import(node: Any, imported: set) -> None:
    if isinstance(node, _ast.ImportFrom) and node.module == "__future__":
        return
    for alias in node.names:
        if alias.name == "*":
            continue
        imported.add(alias.asname or alias.name.split(".")[0])
def _is_all_target(node: Any) -> bool:
    return isinstance(node, _ast.Name) and node.id == "__all__"
def _iu_all_listed(node: Any, all_listed: set) -> None:
    value = getattr(node, "value", None)
    if isinstance(node, _ast.Assign):
        if any(_is_all_target(t) for t in node.targets):
            previous_all = set(all_listed)
            all_listed.clear()
            _collect_all_listed(value, all_listed, previous_all)
        return
    if isinstance(node, _ast.AnnAssign):
        if _is_all_target(node.target):
            if node.value is None:
                return
            previous_all = set(all_listed)
            all_listed.clear()
            _collect_all_listed(value, all_listed, previous_all)
        return
    if isinstance(node, _ast.AugAssign):
        if not _is_all_target(node.target):
            return
        if isinstance(node.op, (_ast.Add, _ast.BitOr)):
            _collect_all_listed(value, all_listed)
        elif isinstance(node.op, _ast.Sub):
            removed: set = set()
            _collect_all_listed(value, removed)
            all_listed.difference_update(removed)
        return
    if not isinstance(node, _ast.Expr):
        return
    call = value
    if not (isinstance(call, _ast.Call)
            and isinstance(call.func, _ast.Attribute)
            and _is_all_target(call.func.value)):
        return
    method = call.func.attr
    if method == "clear" and not call.args and not call.keywords:
        all_listed.clear()
        return
    if method == "remove":
        removed: set = set()
        for arg in call.args:
            _collect_all_listed(arg, removed)
        all_listed.difference_update(removed)
        return
    if method not in ("append", "extend", "insert"):
        return
    for arg in call.args:
        _collect_all_listed(arg, all_listed)
def _unreferenced_import_names(code: str, tree: Any = None) -> set[str]:
    """Return import names having at least one genuinely unreferenced binding.

    以 symtable 为主判定，保留 try/except 可选导入等既有口径；仅对
    Python 3.12+ PEP 709 内联推导式做 AST 复核：这些 Name Load 不会在模块
    符号上标记 referenced，直接读 symtable 会把仅用于推导式的导入误判为
    未使用。复核只对 symtable 已判未使用的名字做“救回”，因此不会把
    try/except 导入回退、局部遮蔽或后续重绑定误当成已使用。
    """
    try:
        root = _symtable.symtable(code, "<debt-engine>", "exec")
    except PARSE_DEGRADE_EXC as exc:
        _log.debug("DebtEngine 符号表构建失败，保留保守导入结果: %s", exc)
        return set()
    tables: list[Any] = []
    parents: dict[int, Any] = {id(root): None}
    stack = [root]
    while stack:
        table = stack.pop()
        tables.append(table)
        for child in table.get_children():
            parents[id(child)] = table
            stack.append(child)
    imported: set[tuple[int, str]] = set()
    referenced: set[tuple[int, str]] = set()
    for table in tables:
        for symbol in table.get_symbols():
            name = symbol.get_name()
            key = (id(table), name)
            if symbol.is_imported():
                imported.add(key)
                if symbol.is_referenced():
                    referenced.add(key)
                continue
            if not symbol.is_referenced():
                continue
            target = root if symbol.is_global() else None
            if symbol.is_free():
                current = parents[id(table)]
                while current is not None:
                    if current.get_type() == "class":
                        current = parents[id(current)]
                        continue
                    try:
                        candidate = current.lookup(name)
                    except KeyError:
                        candidate = None
                    if candidate is not None and candidate.is_global():
                        target = root
                        break
                    if candidate is not None and candidate.is_nonlocal():
                        current = parents[id(current)]
                        continue
                    if candidate is not None and (
                            candidate.is_assigned() or candidate.is_parameter()
                            or candidate.is_imported() or candidate.is_namespace()):
                        target = current
                        break
                    current = parents[id(current)]
            if target is None:
                continue
            try:
                target_symbol = target.lookup(name)
            except KeyError:
                continue
            if target_symbol.is_imported():
                referenced.add((id(target), name))
    unreferenced = {name for _table_id, name in imported - referenced}
    if not unreferenced:
        return unreferenced
    if tree is None:
        try:
            tree = _ast.parse(code)
        except PARSE_DEGRADE_EXC as exc:
            _log.debug("DebtEngine 语法解析失败，保留 symtable 结果: %s", exc)
            return unreferenced
    try:
        resolver = ScopeNameResolver(code, "<debt-engine>", tree, set())
    except PARSE_DEGRADE_EXC as exc:
        _log.debug("DebtEngine 作用域复核失败，保留 symtable 结果: %s", exc)
        return unreferenced
    load_nodes: dict[str, list[Any]] = {}
    for node in walk_nodes(tree):
        if isinstance(node, _ast.Name) and isinstance(node.ctx, _ast.Load):
            load_nodes.setdefault(node.id, []).append(node)
    rescued: set[str] = set()
    for name in unreferenced:
        for node in load_nodes.get(name, ()):
            try:
                if resolver.import_path(node) is not None:
                    rescued.add(name)
                    break
            except PARSE_DEGRADE_EXC as exc:
                _log.debug("DebtEngine 导入复核异常，保留 symtable 结果: %s", exc)
                break
    return unreferenced - rescued


def _collect_import_usage(code: str, tree: Any) -> tuple[set, set, set]:
    imported: set = set()
    used: set = set()
    annotation_used: set = set()
    reexported: set = set()
    all_listed: set = set()
    for node in walk_nodes(tree):
        if isinstance(node, (_ast.Import, _ast.ImportFrom)):
            _iu_register_import(node, imported)
            reexported.update(
                alias.asname for alias in node.names
                if alias.asname and alias.asname == alias.name)
            continue
        if isinstance(node, _ast.Name):
            if isinstance(node.ctx, _ast.Load):
                used.add(node.id)
            continue
        if isinstance(node, (_ast.AnnAssign, _ast.arg)):
            collect_annotation_names(node.annotation, annotation_used)
        elif isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
            collect_annotation_names(node.returns, annotation_used)
    used.update(annotation_used)
    used.update(reexported)
    unreferenced = _unreferenced_import_names(
        code, tree) - annotation_used - reexported
    used.difference_update(unreferenced)
    for node, _in_handler in iter_scope_statements(tree):
        _iu_all_listed(node, all_listed)
    return imported, used, all_listed
def _normalize_findings_list(payload: Any, name: str) -> list:
    if not payload:
        return []
    if isinstance(payload, Mapping):
        return [payload]
    if isinstance(payload, (str, bytes, bytearray)):
        _log.warning("[DebtEngine] %s 载荷非法(%s)，降级为空清单",
                     name, type(payload).__name__)
        return []
    if not isinstance(payload, (list, tuple)):
        if not isinstance(payload, Iterable):
            _log.warning("[DebtEngine] %s 载荷非法(%s)，降级为空清单",
                         name, type(payload).__name__)
            return []
        payload = list(payload)
    return [v for v in payload if isinstance(v, Mapping)]
@dataclass(frozen=True)
class _ReadFailure:
    path: str
    error: OSError | UnicodeDecodeError | SyntaxError
def _decode_py_source(data: bytes, origin: str) -> str | _ReadFailure:
    try:
        encoding = tokenize.detect_encoding(io.BytesIO(data).readline)[0]
        return (data.decode(encoding)
                .replace("\r\n", "\n").replace("\r", "\n"))
    except (SyntaxError, UnicodeDecodeError, LookupError) as _e:
        _log.warning("DebtEngine 源码解码失败，标记为不可读: %s (%s)", origin, _e)
        return _ReadFailure(path=origin, error=_e)
def _read_py_source(path: str) -> Any:
    try:
        with open(path, 'rb') as _f:
            data = _f.read()
    except OSError as _e:
        _log.warning("DebtEngine 读取 .py 失败，标记为不可读: %s (%s)", path, _e)
        return _ReadFailure(path=path, error=_e)
    return _decode_py_source(data, path)
def _make_syntax_error_report() -> DebtReport:
    return DebtReport(
        total_score=0, level=DebtLevel.BLOCK, blocked=True,
        dimensions={}, issues=["语法错误: 无法解析代码"],
        fix_suggestions=["修复语法错误后重新评估"],
    )
def _make_unreadable_report(failure: _ReadFailure) -> DebtReport:
    reason = (getattr(failure.error, "strerror", None)
              or getattr(failure.error, "reason", None)
              or getattr(failure.error, "msg", None)
              or str(failure.error)
              or failure.error.__class__.__name__)
    return DebtReport(
        total_score=0, level=DebtLevel.BLOCK, blocked=True,
        dimensions={},
        issues=[f"文件不可读: {failure.path} ({reason})"],
        fix_suggestions=["检查文件权限/占用状态后重新评估"],
    )
def _pathlike_text(value: Any) -> Any:
    if isinstance(value, os.PathLike):
        return os.fsdecode(os.fspath(value))
    return value
def _looks_like_py_path(code: Any) -> bool:
    return (isinstance(code, str) and bool(code) and "\n" not in code
            and code.lower().endswith(".py"))
def _is_risky_call(name: str) -> bool:
    return (name in _RISKY_CALL_EXACT
            or ("." in name
                and name.rsplit(".", 1)[-1] in _RISKY_CALL_METHODS))
@dataclass(frozen=True)
class _SizeSignals:
    max_depth: int = 0
    deep_funcs: tuple[tuple[str, int], ...] = ()
    long_funcs: tuple[str, ...] = ()
    long_classes: tuple[str, ...] = ()
    long_methods: tuple[str, ...] = ()
    bloat_funcs: tuple[tuple[str, int], ...] = ()
    bloat_classes: tuple[tuple[str, int], ...] = ()
@dataclass
class _SignalAccumulator:
    max_depth: int = 0
    deep_funcs: list = field(default_factory=list)
    long_funcs: list = field(default_factory=list)
    long_classes: list = field(default_factory=list)
    long_methods: list = field(default_factory=list)
    bloat_funcs: list = field(default_factory=list)
    bloat_classes: list = field(default_factory=list)
    def add_function(self, node: Any,
                     *, is_method: bool = False) -> None:
        span = own_scope_line_span(node)
        depth = calc_nesting(node)
        if not is_method:
            if span > _BLOAT_FUNC_LINES:
                self.bloat_funcs.append((node.name, span))
            if span > MAX_FUNCTION_LINES_DEBT:
                self.long_funcs.append(node.name)
        self.max_depth = max(self.max_depth, depth)
        if depth > MAX_NESTING_DEBT:
            self.deep_funcs.append((node.name, depth))
    def add_class(self, node: Any, parents: dict) -> None:
        span = _node_span_lines(node)
        if span > _BLOAT_CLASS_LINES:
            self.bloat_classes.append((node.name, span))
        if span > MAX_CLASS_LINES_DEBT:
            self.long_classes.append(node.name)
        self.long_methods.extend(_long_methods_of(node, parents))
    def freeze(self) -> _SizeSignals:
        return _SizeSignals(
            max_depth=self.max_depth,
            deep_funcs=tuple(self.deep_funcs),
            long_funcs=tuple(self.long_funcs),
            long_classes=tuple(self.long_classes),
            long_methods=tuple(self.long_methods),
            bloat_funcs=tuple(self.bloat_funcs),
            bloat_classes=tuple(self.bloat_classes),
        )
def _collect_size_signals(tree: Any) -> _SizeSignals:
    acc = _SignalAccumulator()
    parents = parent_map(tree)
    method_ids = {
        id(node) for node in walk_nodes(tree)
        if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef))
        and class_body_owner(node, parents) is not None
    }
    for node in walk_nodes(tree):
        if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
            acc.add_function(node, is_method=id(node) in method_ids)
        elif isinstance(node, _ast.ClassDef):
            acc.add_class(node, parents)
    return acc.freeze()
def _long_methods_of(cls_node: Any, parents: dict) -> list[str]:
    found: list[tuple[int, str]] = []
    for child in walk_nodes(cls_node):
        if not isinstance(child, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
            continue
        if class_body_owner(child, parents) is not cls_node:
            continue
        if own_scope_line_span(child) > MAX_METHOD_LINES_DEBT:
            found.append((child.lineno, f"{cls_node.name}.{child.name}"))
    return [name for _lineno, name in sorted(found)]
class _SecurityCallRule(NamedTuple):
    debt_deduction: int
    quality_penalty: int
    label: str
    issue: str
    fix: str
_SECURITY_CALL_RULES: dict[str, _SecurityCallRule] = {
    "os_system": _SecurityCallRule(
        8, 30, "os.system()命令注入",
        "使用 os.system() 存在命令注入风险",
        "替换为 subprocess.run(cmd, shell=False)"),
    "eval_exec": _SecurityCallRule(
        8, 30, "eval/exec使用",
        "使用 {name}() 存在代码注入风险",
        "替换 {name}() 为安全的解析器或 ast.literal_eval()"),
    "subprocess_shell": _SecurityCallRule(
        6, 25, "subprocess shell=True",
        "subprocess 使用 shell=True 存在注入风险",
        "使用 shell=False 并传递参数列表"),
    "pickle": _SecurityCallRule(
        5, 20, "pickle反序列化",
        "pickle 反序列化不可信数据存在安全风险",
        "使用 json 或安全序列化格式替代 pickle"),
}
_HARDCODED_SECRET_LABEL = "硬编码敏感信息"  # jwsgj:suppress E1-HARDCODED-CRED S105
_HARDCODED_SECRET_PENALTY = 20
def _security_call_rule(node: Any, name: str) -> _SecurityCallRule | None:
    if name in ("eval", "exec", "builtins.eval", "builtins.exec"):
        return _SECURITY_CALL_RULES["eval_exec"]
    if name in ("pickle.load", "pickle.loads"):
        return _SECURITY_CALL_RULES["pickle"]
    if name == "os.system":
        return _SECURITY_CALL_RULES["os_system"]
    if name.startswith("subprocess.") and any(
            is_shell_true_keyword(kw) for kw in node.keywords):
        return _SECURITY_CALL_RULES["subprocess_shell"]
    return None
def _scandebt_scan_call(node: Any, name: str,
                        issues: list[str], fixes: list[str]) -> int:
    rule = _security_call_rule(node, name)
    if rule is None:
        return 0
    message = rule.issue.format(name=name)
    if message not in issues:
        issues.append(message)
        fixes.append(rule.fix.format(name=name))
    return rule.debt_deduction
def _iter_literal_target_values(target: Any, value: Any):
    if (isinstance(target, (_ast.Tuple, _ast.List))
            and isinstance(value, (_ast.Tuple, _ast.List))):
        for target_elt, value_elt in zip(target.elts, value.elts,
                                         strict=False):
            yield from _iter_literal_target_values(target_elt, value_elt)
        return
    name = _sensitive_target_name(target)
    if name is None:
        return
    if (isinstance(value, _ast.Constant)
            and isinstance(value.value, str) and value.value):
        yield name, value.value
def _sensitive_assign_hit_names(node: Any) -> list[str]:
    targets = _assignment_targets(node)
    if targets is None:
        return []
    value = getattr(node, "value", None)
    keywords = [kw for kw in _SENSITIVE_NAME_KEYWORDS if kw]
    hits: list[str] = []
    for target in targets:
        for name, literal in _iter_literal_target_values(target, value):
            if not any(kw in name.lower() for kw in keywords):
                continue
            if is_rule_name_constant(literal, (name,)):
                continue
            hits.append(name)
    return list(dict.fromkeys(hits))
def _scandebt_scan_assign(node: Any,
                           issues: list[str], fixes: list[str]) -> int:
    hits = _sensitive_assign_hit_names(node)
    fix_message = "使用环境变量 os.environ.get() 存储敏感信息"
    for name in hits:
        message = f"变量 '{name}' 疑似硬编码敏感信息"
        if message not in issues:
            issues.append(message)
            if fix_message not in fixes:
                fixes.append(fix_message)
    return 5 * len(hits)
def _is_docstring_holder(node: Any) -> bool:
    return (isinstance(node, (_ast.Module, _ast.FunctionDef,
                              _ast.AsyncFunctionDef, _ast.ClassDef))
            and bool(node.body) and isinstance(node.body[0], _ast.Expr)
            and isinstance(node.body[0].value, _ast.Constant)
            and isinstance(node.body[0].value.value, str))
def _http_const_evidence(node: Any) -> bool:
    if not (isinstance(node, _ast.Constant) and isinstance(node.value, str)):
        return False
    return (node.value.casefold().startswith(_HTTP_PREFIX)
            and len(node.value) > len(_HTTP_PREFIX))
def _http_joined_head_is_prefix(node: Any) -> bool:
    if not (isinstance(node, _ast.JoinedStr) and node.values):
        return False
    head = node.values[0]
    return (isinstance(head, _ast.Constant)
            and isinstance(head.value, str)
            and head.value.casefold() == _HTTP_PREFIX)
def _http_joined_has_payload(parts: list) -> bool:
    return any(isinstance(part, _ast.FormattedValue)
               or (isinstance(part, _ast.Constant)
                   and isinstance(part.value, str) and bool(part.value))
               for part in parts)
def _is_http_evidence(node: Any, docstring_ids: set[int]) -> bool:
    if id(node) in docstring_ids:
        return False
    if _http_const_evidence(node):
        return True
    if not _http_joined_head_is_prefix(node):
        return False
    return _http_joined_has_payload(node.values[1:])
def _call_dotted_name(node: _ast.Call,
                      resolver: ScopeNameResolver) -> str:
    func = node.func
    if isinstance(func, _ast.Name):
        imported = resolver.import_path(func)
        if imported is not None:
            return imported
        return "" if resolver.is_bound(func) else func.id
    if not isinstance(func, _ast.Attribute):
        return ""
    parts: list[str] = []
    obj: Any = func
    while isinstance(obj, _ast.Attribute):
        parts.append(obj.attr)
        obj = obj.value
    root = ""
    if isinstance(obj, _ast.Name):
        imported = resolver.import_path(obj)
        if imported is not None:
            root = imported
        elif not resolver.is_bound(obj):
            root = obj.id
    return ".".join((root, *reversed(parts)))
def _resolved_call_names(code: str, tree: Any) -> dict[Any, str]:
    resolver = ScopeNameResolver(code, "<debt-engine>", tree, set())
    return {
        node: _call_dotted_name(node, resolver)
        for node in walk_nodes(tree) if isinstance(node, _ast.Call)
    }
def _is_risky_call_covered(node: Any, parents: dict) -> bool:
    current = node
    while True:
        parent = parents.get(current)
        if parent is None:
            return False
        if (isinstance(parent, _TRY_NODE_TYPES) and parent.handlers
                and any(current is stmt for stmt in parent.body)):
            return True
        if isinstance(parent, _ast.Lambda) and current is parent.body:
            return False
        if isinstance(parent, _ast.comprehension):
            generator = parents.get(parent)
            if isinstance(generator, _ast.GeneratorExp):
                if (current is parent.iter and generator.generators
                        and parent is generator.generators[0]):
                    current = generator
                    continue
                return False
        if (isinstance(parent, _ast.GeneratorExp)
                and (not parent.generators
                     or current is not parent.generators[0].iter)):
            return False
        if (isinstance(parent, (_ast.FunctionDef, _ast.AsyncFunctionDef))
                and any(current is stmt for stmt in parent.body)):
            return False
        current = parent
def _count_risky_and_try(code: str, tree: Any) -> tuple[int, int, int]:
    risky_calls = 0
    covered_risky_calls = 0
    try_blocks = 0
    parents = parent_map(tree)
    call_names = _resolved_call_names(code, tree)
    for node in walk_nodes(tree):
        if isinstance(node, _ast.Call):
            if not _is_risky_call(call_names[node]):
                continue
            risky_calls += 1
            if _is_risky_call_covered(node, parents):
                covered_risky_calls += 1
        elif isinstance(node, _TRY_NODE_TYPES) and node.handlers:
            try_blocks += 1
    return risky_calls, covered_risky_calls, try_blocks
def _is_hardcoded_path(value: str) -> bool:
    return bool(_WINDOWS_PATH_RE.fullmatch(value)
                or _POSIX_PATH_RE.fullmatch(value))
def _docstring_constant_ids(tree: Any) -> set[int]:
    return {
        id(node.body[0].value)
        for node in walk_nodes(tree)
        if _is_docstring_holder(node)
    }
def _find_hardcoded_paths(tree: Any) -> list[str]:
    docstring_ids = _docstring_constant_ids(tree)
    joined_part_ids = {
        id(part)
        for node in walk_nodes(tree) if isinstance(node, _ast.JoinedStr)
        for part in node.values
    }
    paths: list[str] = []
    for node in walk_nodes(tree):
        if id(node) in docstring_ids or id(node) in joined_part_ids:
            continue
        if isinstance(node, _ast.Constant) and isinstance(node.value, str):
            if _is_hardcoded_path(node.value):
                paths.append(node.value)
        elif isinstance(node, _ast.JoinedStr):
            text = "".join(
                part.value for part in node.values
                if isinstance(part, _ast.Constant)
                and isinstance(part.value, str)
            )
            if text and _is_hardcoded_path(text):
                paths.append(text)
    return paths
def _is_constant_style_name(name: str) -> bool:
    core = name.lstrip("_")
    return bool(core) and core == core.upper() and any(
        ch.isalpha() for ch in core)
def _iter_literal_number_nodes(node: Any):
    if isinstance(node, _ast.Constant):
        yield node
    elif (isinstance(node, _ast.UnaryOp)
          and isinstance(node.op, (_ast.UAdd, _ast.USub))):
        yield from _iter_literal_number_nodes(node.operand)
    elif isinstance(node, _ast.BinOp):
        yield from _iter_literal_number_nodes(node.left)
        yield from _iter_literal_number_nodes(node.right)
    elif isinstance(node, (_ast.Tuple, _ast.List, _ast.Set)):
        for elt in node.elts:
            yield from _iter_literal_number_nodes(elt)
    elif isinstance(node, _ast.Dict):
        for item in (*node.keys, *node.values):
            if item is not None:
                yield from _iter_literal_number_nodes(item)
def _mark_named_constant_numbers(target: Any, value: Any,
                                 declared: set[int]) -> None:
    if isinstance(target, _ast.Starred):
        target = target.value
    if (isinstance(target, (_ast.Tuple, _ast.List))
            and isinstance(value, (_ast.Tuple, _ast.List))):
        for target_elt, value_elt in zip(target.elts, value.elts,
                                         strict=False):
            _mark_named_constant_numbers(target_elt, value_elt, declared)
        return
    name = _sensitive_target_name(target)
    if name is None or not _is_constant_style_name(name):
        return
    declared.update(
        id(node) for node in _iter_literal_number_nodes(value))
def _named_constant_number_ids(tree: Any) -> set[int]:
    declared: set[int] = set()
    for node in walk_nodes(tree):
        if isinstance(node, _ast.Assign):
            pairs = ((target, node.value) for target in node.targets)
        elif isinstance(node, _ast.AnnAssign) and node.value is not None:
            pairs = ((node.target, node.value),)
        else:
            continue
        for target, value in pairs:
            _mark_named_constant_numbers(target, value, declared)
    return declared
def _magic_numbers(tree: Any) -> list[int]:
    numbers: list[int] = []
    declared = _named_constant_number_ids(tree)
    for node in walk_nodes(tree):
        if (isinstance(node, _ast.Constant)
                and isinstance(node.value, int)
                and not isinstance(node.value, bool)
                and node.value >= 100
                and id(node) not in declared):
            numbers.append(node.value)
    return numbers
def hash_code(code: str) -> str:
    if not isinstance(code, str):
        code = ""
    return hashlib.sha256(code.encode("utf-8")).hexdigest()
def _history_key_for_input(
        code: Any, loaded: str, history_key: str | None = None) -> str:
    original = history_key or _pathlike_text(code)
    if _looks_like_py_path(original):
        path_key = os.path.normcase(os.path.abspath(original))
        return f"path:{path_key}"
    if history_key:
        return f"caller:{history_key}"
    # Direct snippets have no stable caller identity. Content-addressing keeps
    # unrelated snippets from borrowing each other's trend; callers tracking
    # revisions can still provide history_key explicitly.
    return f"source:{hash_code(loaded)}"
class DebtEngine:
    _HISTORY_LIMIT = 10
    _HISTORY_KEY_LIMIT = 64
    def __init__(self) -> None:
        self._history: list[DebtReport] = []
        self._history_by_key: OrderedDict[str, list[DebtReport]] = (
            OrderedDict())
    def evaluate(self, code: str,
                 violations: list[dict] | None = None,
                 warnings: list[dict] | None = None,
                 *, history_key: str | None = None,
                 ) -> DebtReport:
        _t0 = time.monotonic()
        violations = _normalize_findings_list(violations, "violations")
        warnings = _normalize_findings_list(warnings, "warnings")
        loaded = self._load_code_if_path(code)
        if isinstance(loaded, _ReadFailure):
            report = _make_unreadable_report(loaded)
        else:
            tree = self._safe_parse_code(loaded)
            if tree is None:
                report = _make_syntax_error_report()
            else:
                dimensions, issues, fixes = self._evaluate_dimensions(
                    loaded, violations, warnings, tree)
                report = self._finalize_report(
                    dimensions, issues, fixes,
                    history_key=_history_key_for_input(
                        code, loaded, history_key))
        write_module_run(
            "diag_debt_engine", "DebtEngine.evaluate",
            outcome="ok" if not report.blocked else "blocked",
            duration_ms=(time.monotonic() - _t0) * 1000.0,
            score=report.total_score, level=report.level.value,
            issues=len(report.issues))
        return report
    def _load_code_if_path(self, code: Any) -> Any:
        code = _pathlike_text(code)
        if _looks_like_py_path(code):
            if os.path.exists(code):
                return _read_py_source(code)
            return _ReadFailure(
                path=code,
                error=FileNotFoundError(2, "No such file or directory", code))
        if isinstance(code, (bytes, bytearray)):
            return _decode_py_source(bytes(code), f"<{type(code).__name__}>")
        return code.removeprefix("\ufeff") if isinstance(code, str) else code
    def _safe_parse_code(self, code: Any) -> Any:
        if code is None:
            return None
        try:
            return _ast.parse(code)
        except PARSE_DEGRADE_EXC as e:
            _log.debug("[DebtEngine] 代码解析失败（语法错误报告降级）: %s", e)
            return None
    def _evaluate_dimensions(self, code: str, violations: list, warnings: list, tree: Any) -> tuple:
        dimensions: dict[str, dict[str, Any]] = {}
        issues: list[str] = []
        fixes: list[str] = []
        signals = _collect_size_signals(tree)
        dim_calls = [
            ("ast_violations", self._score_ast_violations, (violations, warnings)),
            ("rule_coverage", self._score_rule_coverage, (violations,)),
            ("duplication", self._score_duplication, (code,)),
            ("hardcoding", self._score_hardcoding, (tree,)),
            ("exception_coverage", self._score_exception_coverage, (code, tree)),
            ("dead_code", self._score_dead_code, (code, tree)),
            ("complexity", self._score_complexity, (tree, signals)),
            ("security", self._score_security_debt, (code, tree)),
            ("size_bloat", self._score_bloat, (code, signals)),
        ]
        for key, caller, args in dim_calls:
            dim = caller(*args)
            dimensions[key] = dim
            if dim.get("issues"):
                issues.extend(dim["issues"])
            if dim.get("fixes"):
                fixes.extend(dim["fixes"])
        return dimensions, issues, fixes
    def _finalize_report(self, dimensions: dict, issues: list, fixes: list,
                         history_key: str | None = None) -> DebtReport:
        total = sum(d["score"] for d in dimensions.values())
        blocking_violations = dimensions.get("ast_violations", {}).get(
            "blocking_violations", 0)
        if blocking_violations:
            level = DebtLevel.BLOCK
            blocked = True
        elif total >= WARN_THRESHOLD:
            level = DebtLevel.PASS
            blocked = False
        elif total >= WARN_THRESHOLD // 2:
            level = DebtLevel.WARN
            blocked = False
        else:
            level = DebtLevel.BLOCK
            blocked = True
        trend = self._analyze_trend(total, history_key=history_key)
        report = DebtReport(
            total_score=total, level=level, blocked=blocked,
            dimensions=dimensions, issues=issues,
            fix_suggestions=fixes, trend=trend,
        )
        self._history.append(report)
        if len(self._history) > self._HISTORY_LIMIT:
            self._history.pop(0)
        if history_key is not None:
            bucket = self._history_by_key.get(history_key)
            if bucket is None:
                bucket = []
                self._history_by_key[history_key] = bucket
                while len(self._history_by_key) > self._HISTORY_KEY_LIMIT:
                    self._history_by_key.popitem(last=False)
            bucket.append(report)
            if len(bucket) > self._HISTORY_LIMIT:
                bucket.pop(0)
        return report
    def _score_ast_violations(self, violations: list[dict], warnings: list[dict]) -> dict:
        score = 15
        issues: list[str] = []
        fixes: list[str] = []
        blocking_violations = 0
        gate = FixGate()
        for v in violations:
            _msg = str(v.get("message") or "")
            decision = gate.check(
                v.get("rule_id", ""), v.get("severity", ""))
            if decision is GateDecision.BLOCK:
                blocking_violations += 1
                score -= 10
                issues.append(f"CRITICAL违规 [{v.get('rule_id')}]: {_msg[:60]}")
            else:
                score -= 4
                issues.append(f"违规 [{v.get('rule_id')}]: {_msg[:60]}")
        for w in warnings:
            _msg = str(w.get("message") or "")
            # 警告项携带的严重度不低于 WARN（含 BLOCK 级）按高等级警告扣分。
            penalty = (
                2 if _gate_decision_of_severity(
                    w.get("severity")) in (GateDecision.WARN,
                                          GateDecision.BLOCK) else 1)
            score -= penalty
            issues.append(f"警告 [{w.get('rule_id')}]: {_msg[:60]}")
        if blocking_violations:
            fixes.append("修复所有 CRITICAL 级别违规项")
        return _dim_result(
            score, issues, fixes, violations=len(violations),
            blocking_violations=blocking_violations)
    def _score_rule_coverage(self, violations: list[dict]) -> dict:
        score = 5
        issues: list[str] = []
        rule_ids = {str(v.get("rule_id")) for v in violations
                    if v.get("rule_id")}
        if len(rule_ids) > 3:
            score -= 3
            issues.append(f"违规涉及 {len(rule_ids)} 种规则,覆盖面过大")
        return _dim_result(score, issues, covered_rules=len(rule_ids))
    def _score_duplication(self, code: str) -> dict:
        score = 10
        issues: list[str] = []
        fixes: list[str] = []
        lines = _code_lines(code)
        if len(lines) < MAX_DUPLICATE_LINES * 2:
            return _dim_result(score, duplicates=0)
        duplicates = _duplicate_window_count(lines, MAX_DUPLICATE_LINES)
        if duplicates:
            issues.append(f"检测到重复代码块 (≥{MAX_DUPLICATE_LINES}行)")
            fixes.append("将重复代码提取为函数")
        score -= min(duplicates * 3, 10)
        return _dim_result(score, issues, fixes, duplicates=duplicates)
    def _score_hardcoding(self, tree: Any) -> dict:
        score = 10
        issues: list[str] = []
        fixes: list[str] = []
        magic_filtered = [
            value for value in _magic_numbers(tree)
            if value not in _HARMLESS_MAGIC_NUMBERS
        ]
        if len(magic_filtered) > 2:
            score -= 5 if len(magic_filtered) > 5 else 2
            issues.append(
                f"检测到 {len(magic_filtered)} 个魔法数字,建议提取为常量")
            fixes.append("将魔法数字提取为命名常量")
        hardcoded_paths = _find_hardcoded_paths(tree)
        if hardcoded_paths:
            score -= 3
            issues.append(f"检测到 {len(hardcoded_paths)} 个硬编码路径")
            fixes.append("将硬编码路径提取为配置或使用相对路径")
        return _dim_result(
            score, issues, fixes, magic_numbers=len(magic_filtered),
            hardcoded_paths=len(hardcoded_paths))
    def _score_exception_coverage(self, code: str, tree: Any) -> dict:
        score = 15
        issues: list[str] = []
        fixes: list[str] = []
        risky_calls, covered_risky_calls, try_blocks = _count_risky_and_try(
            code, tree)
        uncovered_risky_calls = risky_calls - covered_risky_calls
        if uncovered_risky_calls:
            if covered_risky_calls == 0:
                score -= 10
                issues.append(
                    f"检测到 {uncovered_risky_calls} 个风险操作未处于异常处理保护范围")
            else:
                score -= 5
                issues.append(
                    f"风险操作异常处理覆盖不足: {uncovered_risky_calls}/{risky_calls} 个未受保护")
            fixes.append("将风险操作置于匹配的 try/except 保护范围内")
        return _dim_result(
            score, issues, fixes,
            risky_calls=risky_calls,
            covered_risky_calls=covered_risky_calls,
            uncovered_risky_calls=uncovered_risky_calls,
            try_blocks=try_blocks,
        )
    def _score_dead_code(self, code: str, tree: Any) -> dict:
        score = 10
        issues: list[str] = []
        fixes: list[str] = []
        imported, used, all_listed = _collect_import_usage(code, tree)
        unused_imports = imported - used - all_listed
        if unused_imports:
            score -= 3
            issues.append(
                f"未使用的导入: {', '.join(sorted(unused_imports)[:5])}")
            fixes.append("移除未使用的 import 语句")
        return _dim_result(score, issues, fixes, unused_imports=len(unused_imports))
    def _score_complexity(self, tree: Any,
                          signals: _SizeSignals) -> dict:
        score = 10
        issues: list[str] = []
        fixes: list[str] = []
        max_depth = signals.max_depth
        long_funcs = signals.long_funcs
        long_classes = signals.long_classes
        long_methods = signals.long_methods
        for _fname, _fdepth in signals.deep_funcs:
            issues.append(f"函数 '{_fname}' 嵌套深度 {_fdepth} 超过上限 {MAX_NESTING_DEBT}")
            fixes.append(f"重构 '{_fname}' 减少嵌套深度")
        if max_depth > MAX_NESTING_DEBT:
            score -= 5
        for label, items, penalty, fix in (
                ("过长函数", long_funcs, 3,
                 "提取子函数收敛过长函数，保持职责单一"),
                ("过长类", long_classes, 4, "将过长类按上下文内聚拆分"),
                ("过长方法", long_methods, 2, "将过长方法提取为独立函数"),
        ):
            if not items:
                continue
            score -= penalty
            issues.append(f"{label} ({len(items)}个): {', '.join(items[:3])}")
            fixes.append(fix)
        return _dim_result(score, issues, fixes, max_nesting=max_depth)
    def _score_security_debt(self, code: str, tree: Any) -> dict:
        score = 15
        issues: list[str] = []
        fixes: list[str] = []
        score_deduction = 0
        docstring_consts = _docstring_constant_ids(tree)
        call_names = _resolved_call_names(code, tree)
        for node in walk_nodes(tree):
            if isinstance(node, _ast.Call):
                score_deduction += _scandebt_scan_call(
                    node, call_names[node], issues, fixes)
            else:
                score_deduction += _scandebt_scan_assign(node, issues, fixes)
            if _is_http_evidence(node, docstring_consts):
                score_deduction += 2
                if "使用 HTTP 明文传输" not in issues:
                    issues.append("使用 HTTP 明文传输")
                    fixes.append("改用 HTTPS 加密传输")
        score -= score_deduction
        return _dim_result(score, issues, fixes)
    def _score_bloat(self, code: str, signals: _SizeSignals) -> dict:
        score = 10
        issues: list[str] = []
        fixes: list[str] = []
        total_lines = count_lines(code)
        if total_lines > 1000:
            score -= 3
            issues.append(f"严重过大文件: {total_lines}行")
            fixes.append("消除重复、收敛依赖、提取同模块私有实现")
        elif total_lines > 500:
            score -= 1
            issues.append(f"过大文件: {total_lines}行")
            fixes.append("在文件内收敛职责：提取同模块私有实现或迁移到既有职责模块")
        for _name, fn_lines in signals.bloat_funcs:
            score -= min(3, fn_lines // _BLOAT_FUNC_LINES)
            issues.append(f"过长函数: {_name} ({fn_lines}行)")
            fixes.append(f"提取 {_name} 内聚子逻辑为同模块私有函数")
        for _name, cls_lines in signals.bloat_classes:
            score -= min(4, cls_lines // _BLOAT_CLASS_LINES)
            issues.append(f"上帝类: {_name} ({cls_lines}行)")
            fixes.append(f"收敛类 {_name} 的职责边界，提取同模块私有协作者")
        return _dim_result(score, issues, fixes)
    def _analyze_trend(self, current_score: int,
                       history_key: str | None = None) -> str:
        history = (self._history_by_key.get(history_key, [])
                   if history_key is not None else self._history)
        if not history:
            return "stable"
        recent = [r.total_score for r in history[-3:]]
        if not recent:
            return "stable"
        avg_recent = sum(recent) / len(recent)
        if current_score > avg_recent + 5:
            return "improving"
        if current_score < avg_recent - 5:
            return "worsening"
        return "stable"
    def get_history(self) -> list[dict]:
        return [{"score": r.total_score, "level": r.level.value} for r in self._history]
_debt_engine = DebtEngine()
def get_debt_engine() -> DebtEngine:
    return _debt_engine
def _has_hardcoded_secret(tree: _ast.AST) -> bool:
    return any(
        _sensitive_assign_hit_names(node)
        for node in walk_nodes(tree)
        if isinstance(node, (_ast.Assign, _ast.AnnAssign, _ast.AugAssign)))
def _code_lines(code: str) -> list[str]:
    return [
        line.strip() for line in code.splitlines()
        if line.strip() and not line.strip().startswith("#")
    ]
def _halstead_counts(code: str) -> tuple[int, int, int, int]:
    operators: set[str] = set()
    operands: set[str] = set()
    n_operators = 0
    n_operands = 0
    try:
        for token in tokenize.generate_tokens(io.StringIO(code).readline):
            if token.type == tokenize.OP:
                n_operators += 1
                operators.add(token.string)
            elif (token.type in (tokenize.NAME, tokenize.NUMBER,
                                 tokenize.STRING)
                  or token.type == getattr(tokenize, "FSTRING_START", -1)):
                n_operands += 1
                operands.add(token.string)
    except (IndentationError, SyntaxError, tokenize.TokenError):
        operator_hits = re.findall(r"[+\-*/%=<>!&|^~@]", "\n".join(
            _code_lines(code)))
        operand_hits = re.findall(r"\b[a-zA-Z_]\w*\b", "\n".join(
            _code_lines(code)))
        operators, operands = set(operator_hits), set(operand_hits)
        n_operators, n_operands = len(operator_hits), len(operand_hits)
    return n_operators, n_operands, len(operators), len(operands)
def _duplicate_window_count(lines: list[str], window: int) -> int:
    if window <= 0:
        return 0
    seen: set[str] = set()
    duplicates = 0
    i = 0
    while i < len(lines) - window + 1:
        chunk = "\n".join(lines[i:i + window])
        if chunk in seen:
            duplicates += 1
            i += window
        else:
            seen.add(chunk)
            i += 1
    return duplicates
_MAX_FINITE_FLOAT = float.fromhex('0x1.fffffffffffffp+1023')
def _is_weight_entry(key: Any, value: Any, known: dict) -> bool:
    return (key in known and isinstance(value, (int, float))
            and not isinstance(value, bool)
            and 0 <= value <= _MAX_FINITE_FLOAT)
class CodeQualityScorer:
    DEFAULT_WEIGHTS: ClassVar[dict] = {
        "maintainability": 0.30,
        "complexity": 0.20,
        "duplication": 0.15,
        "comment": 0.10,
        "exception": 0.10,
        "type_annotation": 0.05,
        "security": 0.10,
    }
    def __init__(self, weights: dict[str, float] | None = None) -> None:
        self._weights = dict(self.DEFAULT_WEIGHTS)
        for key, value in (weights if isinstance(weights, dict) else {}).items():
            if _is_weight_entry(key, value, self._weights):
                self._weights[key] = float(value)
        self.reset()
    def reset(self) -> None:
        self.issues = []
        self.metrics = {}
    def score(self, code: str) -> dict[str, Any]:
        self.reset()
        if not isinstance(code, str):
            return self._blocked_metrics(
                "非字符串源码输入(" + type(code).__name__ + ")")
        code = code.removeprefix("\ufeff")
        code = code.replace("\r\n", "\n").replace("\r", "\n")
        if not code or not code.strip():
            return self._blocked_metrics("空代码输入")
        try:
            tree = _ast.parse(code)
        except PARSE_DEGRADE_EXC as e:
            _log.warning("%s: %s: %s", MSG_SYNTAX_ERROR_SKIP,
                         type(e).__name__, e)
            return self._blocked_metrics(str(e))
        if not tree.body or (len(tree.body) == 1 and _is_docstring_holder(tree)):
            return self._blocked_metrics("无可执行语句")
        dims = self._compute_dimensions(code, tree)
        total = max(0, min(100, round(self._weighted_total(dims))))
        grade, gate = self._grade_for(total)
        self.metrics = {
            "total_score": total,
            "grade": grade,
            "gate": gate,
            "maintainability_index": round(dims["maintainability"], 1),
            "complexity_score": round(dims["complexity"], 1),
            "duplication_score": round(dims["duplication"], 1),
            "comment_ratio_score": round(dims["comment"], 1),
            "exception_handling_score": round(dims["exception"], 1),
            "type_annotation_score": round(dims["type_annotation"], 1),
            "security_score": round(dims["security"], 1),
            "issues_count": len(self.issues),
        }
        return self.metrics
    def _blocked_metrics(self, error: str) -> dict[str, Any]:
        self.metrics = {"total_score": 0, "grade": "F", "gate": "BLOCK",
                        "error": error}
        return self.metrics
    def _compute_dimensions(self, code: str, tree: Any) -> dict[str, float]:
        return {
            "maintainability": self._calc_maintainability(code, tree),
            "complexity": self._calc_complexity(tree),
            "duplication": self._calc_duplication(code),
            "comment": self._calc_comment_ratio(code),
            "exception": self._calc_exception_handling(tree),
            "type_annotation": self._calc_type_annotations(tree),
            "security": self._calc_security(code, tree),
        }
    def _weighted_total(self, dims: dict[str, float]) -> float:
        weights = {key: self._weights[key] for key in dims}
        scale = max(weights.values(), default=0.0)
        if scale <= 0:
            return 0.0
        scaled = {key: weight / scale for key, weight in weights.items()}
        total_weight = sum(scaled.values())
        return sum(value * scaled[key]
                   for key, value in dims.items()) / total_weight
    @staticmethod
    def _grade_for(total: int) -> tuple[str, str]:
        if total >= 80:
            return "A", "PASS"
        if total >= 60:
            return "B", "WARN"
        if total >= 40:
            return "C", "WARN"
        return "F", "BLOCK"
    def _calc_maintainability(self, code: str, tree: Any) -> float:
        loc = len(_code_lines(code))
        n_operators, n_operands, unique_operators, unique_operands = (
            _halstead_counts(code))
        volume = (n_operators + n_operands) * math.log2(
            max(unique_operators + unique_operands, 2))
        cc = cyclomatic_complexity(tree)
        mi_raw = (171 - 5.2 * math.log(max(volume, 1)) - 0.23 * cc
                  - 16.2 * math.log(max(loc, 1)))
        mi = max(0, mi_raw * 100 / 171)
        if mi < 40:
            self.issues.append({"rule": "MI-001", "message": "可维护性指数过低", "severity": "high"})
        return mi
    _COMPLEXITY_BANDS: ClassVar[tuple[tuple[int, float], ...]] = (
        (10, 100), (20, 80), (50, 60), (100, 40),
    )
    def _calc_complexity(self, tree: Any) -> float:
        cc = cyclomatic_complexity(tree)
        for upper, score in self._COMPLEXITY_BANDS:
            if cc <= upper:
                return score
        return 20
    def _calc_duplication(self, code: str) -> float:
        lines = _code_lines(code)
        if len(lines) < 3:
            return 100
        duplicates = _duplicate_window_count(lines, 3)
        dup_ratio = duplicates / max(len(lines), 1)
        score = max(0, 100 - dup_ratio * 500)
        return min(100, score)
    def _calc_comment_ratio(self, code: str) -> float:
        lines = code.splitlines()
        total_lines = count_lines(code)
        comment_lines = sum(1 for ln in lines if ln.strip().startswith("#"))
        ratio = comment_lines / total_lines
        if ratio < 0.05:
            return 30
        if ratio < 0.10:
            return 60
        if ratio <= 0.30:
            return 100
        if ratio <= 0.50:
            return 80
        return 50
    @staticmethod
    def _is_noop_handler_body(handler: Any) -> bool:
        return bool(handler.body) and all(
            isinstance(stmt, _ast.Pass)
            or (isinstance(stmt, _ast.Expr)
                and isinstance(stmt.value, _ast.Constant)
                and (stmt.value.value is Ellipsis
                     or isinstance(stmt.value.value, str)))
            for stmt in handler.body
        )
    @classmethod
    def _except_defect_counts(cls, node: Any) -> tuple[int, int]:
        return (
            sum(1 for h in node.handlers if h.type is None),
            sum(1 for h in node.handlers if cls._is_noop_handler_body(h)),
        )
    def _calc_exception_handling(self, tree: Any) -> float:
        handler_count = 0
        bare_excepts = 0
        except_pass = 0
        for node in walk_nodes(tree):
            if isinstance(node, (_ast.Try, TRY_STAR)):
                handler_count += len(node.handlers)
                bare_n, noop_n = self._except_defect_counts(node)
                bare_excepts += bare_n
                except_pass += noop_n
        if handler_count == 0:
            return 50
        bare_ratio = bare_excepts / max(handler_count, 1)
        pass_ratio = except_pass / max(handler_count, 1)
        score = 100 - bare_ratio * 60 - pass_ratio * 40
        return max(0, min(100, score))
    def _calc_type_annotations(self, tree: Any) -> float:
        total_funcs = 0
        annotated_funcs = 0
        for node in walk_nodes(tree):
            if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
                total_funcs += 1
                if has_type_hints(node):
                    annotated_funcs += 1
        if total_funcs == 0:
            return 100
        ratio = annotated_funcs / total_funcs
        return min(100, ratio * 100)
    def _scan_security_calls(self, code: str, tree: Any,
                             security_issues: list) -> float:
        delta = 0.0
        call_names = _resolved_call_names(code, tree)
        for node in walk_nodes(tree):
            if not isinstance(node, _ast.Call):
                continue
            rule = _security_call_rule(node, call_names[node])
            if rule is not None:
                if rule.label not in security_issues:
                    security_issues.append(rule.label)
                delta -= rule.quality_penalty
        return delta
    def _calc_security(self, code: str, tree: Any) -> float:
        security_issues: list[str] = []
        score = 100.0 + self._scan_security_calls(
            code, tree, security_issues)
        if _has_hardcoded_secret(tree):
            security_issues.append(_HARDCODED_SECRET_LABEL)
            score -= _HARDCODED_SECRET_PENALTY
        for issue in security_issues:
            self.issues.append({"rule": "SEC", "message": issue, "severity": "critical"})
        return max(0, min(100, score))
def score_code(code: str) -> dict[str, Any]:
    report = CodeQualityScorer().score(code)
    _log.info(
        "score_code 完成: score=%s, grade=%s, gate=%s",
        report.get("total_score", 0),
        report.get("grade"), report.get("gate"),
    )
    return report
def _score_file_unreadable(filepath: str, error: str) -> dict[str, Any]:
    _log.warning("score_file: 无法读取 %s: %s", filepath, error)
    return {
        "ok": False,
        "error": error[:200],
        "file": filepath,
        "total_score": 0,
        "grade": "F",
        "gate": "BLOCK",
    }
def score_file(filepath: str, encoding: str | None = None) -> dict[str, Any]:
    try:
        if encoding is None:
            source = read_cached(filepath)
        else:
            with open(filepath, encoding=encoding, errors="strict") as fh:
                source = fh.read()
    except (OSError, TypeError, UnicodeError, LookupError) as exc:
        return _score_file_unreadable(filepath, str(exc))
    if source is None:
        return _score_file_unreadable(filepath, f"无法读取或解码: {filepath}")
    scored = CodeQualityScorer().score(source)
    report = {"ok": "error" not in scored, "file": filepath, **scored}
    _log.info(
        "score_file 完成: file=%s, score=%s, grade=%s, gate=%s",
        filepath, report.get("total_score", 0),
        report.get("grade"), report.get("gate"),
    )
    return report
_GATE_BLOCK_SEVERITIES = frozenset(
    {"P0", "CRITICAL", "BLOCK", "FATAL", "SECURITY"})
_GATE_WARN_SEVERITIES = frozenset(
    {"P1", "HIGH", "MAJOR", "WARNING", "WARN"})
_GATE_PASS_SEVERITIES = frozenset(
    {"P2", "P3", "P4", "LOW", "MEDIUM", "MINOR", "INFO", "NOTE",
     "PASS", "TRIVIAL"})
_GATE_BLOCK_TOKENS = ("CRITICAL", "BLOCK")
_GATE_WARN_TOKENS = ("HIGH",)
_GATE_BLOCK_PREFIXES = ("P0", "SEC-", "SE-")
_GATE_WARN_PREFIXES = ("P1",)
def _severity_word(value: Any) -> str:
    return value.strip().upper() if isinstance(value, str) else ""
def _severity_words(values: Iterable[Any]) -> tuple[str, ...]:
    words = (_severity_word(value) for value in values)
    return tuple(word for word in words if word)
def _contains_word_token(text: str, token: str) -> bool:
    return re.search(
        r"(?<![A-Za-z])" + re.escape(token) + r"(?![A-Za-z])", text) is not None
def _gate_decision_of_severity(severity: Any) -> GateDecision | None:
    word = _severity_word(severity)
    if not word:
        return None
    if (word in _GATE_BLOCK_SEVERITIES
            or _contains_word_token(word, "P0")
            or any(_contains_word_token(word, token)
                   for token in _GATE_BLOCK_TOKENS)):
        return GateDecision.BLOCK
    if (word in _GATE_WARN_SEVERITIES
            or _contains_word_token(word, "P1")
            or any(_contains_word_token(word, token)
                   for token in _GATE_WARN_TOKENS)):
        return GateDecision.WARN
    if word in _GATE_PASS_SEVERITIES:
        return GateDecision.PASS
    return None
class FixGate:
    def __init__(
        self,
        *,
        block_prefixes: tuple[str, ...] = _GATE_BLOCK_PREFIXES,
        warn_prefixes: tuple[str, ...] = _GATE_WARN_PREFIXES,
        block_tokens: tuple[str, ...] = _GATE_BLOCK_TOKENS,
        warn_tokens: tuple[str, ...] = _GATE_WARN_TOKENS,
    ) -> None:
        self._block_prefixes = _severity_words(block_prefixes)
        self._warn_prefixes = _severity_words(warn_prefixes)
        self._block_tokens = _severity_words(block_tokens)
        self._warn_tokens = _severity_words(warn_tokens)
    def _matches(self, text: str, prefixes: tuple[str, ...],
                 tokens: tuple[str, ...]) -> bool:
        return (text.startswith(prefixes) if prefixes else False) or any(
            _contains_word_token(text, token) for token in tokens)
    def check(self, rule_id: str, severity: Any = "") -> GateDecision:
        severity_decision = _gate_decision_of_severity(severity)
        if not isinstance(rule_id, str) or not rule_id:
            return severity_decision or GateDecision.PASS
        rule_upper = rule_id.upper().strip()
        if (self._matches(rule_upper, self._block_prefixes,
                          self._block_tokens)
                or severity_decision is GateDecision.BLOCK):
            return GateDecision.BLOCK
        if (self._matches(rule_upper, self._warn_prefixes,
                          self._warn_tokens)
                or severity_decision is GateDecision.WARN):
            return GateDecision.WARN
        return severity_decision or GateDecision.PASS
__all__ = [
    'MAX_CLASS_LINES_DEBT',
    'MAX_DUPLICATE_LINES',
    'MAX_FUNCTION_LINES_DEBT',
    'MAX_METHOD_LINES_DEBT',
    'MAX_NESTING_DEBT',
    'WARN_THRESHOLD',
    'CodeQualityScorer',
    'DebtEngine',
    'DebtLevel',
    'DebtReport',
    'FixGate',
    'get_debt_engine',
    'hash_code',
    'score_code',
    'score_file',
]
_log.info("diag_debt_engine 已加载: %d 项导出", len(__all__))

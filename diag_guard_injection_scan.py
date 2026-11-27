from __future__ import annotations

import ast
import logging
import re
import time
from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any, ClassVar

from jwsgj.diag_shared_ast_bindings import ScopeNameResolver
from jwsgj.diag_shared_ast_nodes import (
    TRY_NODE_TYPES,
    build_parent_map,
    collect_import_bindings,
    is_invariant_assert,
    is_shell_true_keyword,
    iter_arg_nodes,
    iter_evaluation_scope_chain,
    module_postpones_annotations,
    multiline_string_spans,
    resolve_call_name,
)
from jwsgj.diag_shared_ast_views import (
    collect_lexical_scope_table,
    scope_import_tables,
    scope_node_bound_names,
)
from jwsgj.diag_shared_source_core import (
    coerce_source_text,
    is_rule_name_constant,
)
from jwsgj.diag_shared_source_scan import (
    filter_suppressed_findings,
    parse_suppressions,
    string_comment_spans,
)
from jwsgj.diag_types_vocab import (
    SENSITIVE_NAME_KEYWORDS,
    SUBPROCESS_CHECK_CALL,
    SUBPROCESS_CHECK_OUTPUT,
    YAML_SAFE_LOADERS,
)
from jwsgj.log_config import log_swallowed, write_module_run
from jwsgj.prevention_scope_facts import walk_nodes

_log = logging.getLogger(__name__)
__all__ = [
    'CIE_WRITE_SAME_ROOT_RULE_IDS',
    'SUBPROCESS_SHELL_CALLS',
    'YAML_UNSAFE_LOADER_CALLS',
    'RefactoringEngineV3',
    'is_always_block_finding',
    'scan_source',
    'scan_write_redlines',
    'yaml_load_has_safe_loader',
]
_log.info("diag_guard_injection_scan 已加载：%d 项导出", len(__all__))
def _safe_str(value: Any) -> str:
    try:
        return str(value)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='_safe_str:Exc')
        return "<unstringifiable>"
def _smell_item_payload(item: Any) -> tuple[str, str]:
    is_mapping = isinstance(item, Mapping)
    raw_smell = item.get("smell", "") if is_mapping else _safe_str(item)
    smell = ("" if raw_smell is None else _safe_str(raw_smell)).lower()
    raw_loc = item.get("location", "") if is_mapping else ""
    return smell, "" if raw_loc is None else _safe_str(raw_loc)
class RefactoringEngineV3:
    _SMELL_ADVICE: ClassVar[dict] = {
        "long method": "提取长方法为多个职责单一的小函数",
        "long parameter list": "使用参数对象封装过长的参数列表",
        "long param list": "使用参数对象封装过长的参数列表",
        "large class": "按单一职责拆分大类",
        "god class": "按职责拆分上帝类",
        "duplicated code": "提取重复代码为公共函数",
        "dead code": "删除未使用的死代码",
        "feature envy": "将方法移动到更相关的类",
        "primitive obsession": "用值对象替换基本类型",
        "switch statements": "用多态替换条件分支",
        "switch": "用多态替换条件分支",
        "speculative generality": "移除过度设计的前瞻性抽象",
        "divergent change": "分离变更原因，遵循单一职责",
        "parallel inheritance": "合并同步变化的两条平行继承层次，用委托消除重复层次",
        "tramp data": "收敛反复传递的参数链，把数据局部化到使用它的对象",
        "incomplete library": "用本地扩展(Introduce Local Extension)补齐不完整的库类接口",
        "shotgun surgery": "收敛散落的关联修改到单一模块",
        "data class": "为数据类补充行为，避免贫血模型",
        "data clumps": "提取数据泥团为独立对象",
        "message chains": "消除消息链，遵循得墨忒耳法则",
        "middle man": "移除多余的中介委托类",
        "refused bequest": "用组合替换不合理的继承",
        "inappropriate intimacy": "降低类间过度耦合",
    }
    def __init__(self, project_root: str = ""):
        self.project_root = project_root
    def recommend_refactorings(self, smell_dicts: list[dict]) -> list[dict]:
        if smell_dicts is None:
            items = []
        elif isinstance(smell_dicts, (str, bytes, Mapping)):
            items = [smell_dicts]
        else:
            try:
                items = list(smell_dicts)
            except TypeError as _e:
                log_swallowed(__name__, _e, context='RefactoringEngineV3.recommend_refactorings:TypeError')
                items = []
        result = []
        for d in items:
            smell, location = _smell_item_payload(d)
            advice = self._SMELL_ADVICE.get(smell, f"针对「{smell}」进行针对性重构")
            result.append({
                "refactoring": advice,
                "smell": smell,
                "location": location,
            })
        return result
YAML_UNSAFE_LOADER_CALLS = frozenset({
    "yaml.load", "yaml.load_all",
    "yaml.full_load", "yaml.full_load_all",
    "yaml.unsafe_load", "yaml.unsafe_load_all",
})
SUBPROCESS_SHELL_CALLS = frozenset({
    "subprocess.run", "subprocess.call", "subprocess.Popen",
    SUBPROCESS_CHECK_CALL, SUBPROCESS_CHECK_OUTPUT,
})
_CIE_RULE_SUPPRESS_CATEGORY: dict[str, str] = {
    "C4": "file_operations",
    "SEC-01": "code_execution",
    "CS-91": "code_execution",
}
_DELETE_RULE_IDS: dict[str, str] = {
    "os.remove": "WRITE-WARN-01",
    "os.rmdir": "WRITE-WARN-02",
    "os.unlink": "WRITE-WARN-01",
    "shutil.rmtree": "WRITE-WARN-02",
}
_DANGEROUS_DELETE_CALLS: frozenset[str] = frozenset(_DELETE_RULE_IDS)
_DELETE_WRITE_RULE_IDS: tuple[str, ...] = tuple(
    dict.fromkeys(_DELETE_RULE_IDS.values()))
_MUTABLE_DEFAULT_CALLS: frozenset[str] = frozenset({
    "list", "dict", "set", "bytearray",
    "collections.defaultdict", "collections.Counter",
    "collections.OrderedDict", "collections.deque",
    "defaultdict", "Counter", "OrderedDict", "deque",
})
_VIOLATION_SUGGESTIONS: dict[str, str] = {
    "C4": "将 " + "/".join(f"{name}()" for name in _DELETE_RULE_IDS)
          + " 改为经路径校验的可恢复删除（优先移入回收站）",
    "C6": "将 bare except: 改为 except Exception as e: 并记录日志",
    "RL-01": "将硬编码敏感信息移入环境变量或密钥管理",
    "CS-91": "subprocess 去掉 shell=True,改用参数列表形式",
    "CS-92": "yaml.load() 改为 yaml.safe_load() 或显式指定 Loader",
    "CS-95": "可变默认参数改为 None 哨兵,函数体内惰性初始化",
    "SEC-01": "去除 eval()/exec(),字面量解析改用 ast.literal_eval(),动态分发改用显式白名单映射",
}
_WARNING_SUGGESTIONS: dict[str, str] = {
    "C13": "在 except 块中添加日志记录,而非仅 pass",
    "DB-02": "sqlite3 连接用 finally 显式 conn.close() 或 contextlib.closing 包装（with 只管事务不关闭连接）",
    "R3": "将 re.compile() 移到循环外部",
}
@dataclass(frozen=True)
class _ScanCollectibles:
    loop_nodes: list
    func_nodes: list
    replace_chains: list
    aliases: Mapping[str, str]
    str_lines: frozenset[int] | None = None
    annotations_evaluated: bool = True
def _write_scan_run(outcome: str, started: float, violations: int,
                    warnings: int) -> None:
    write_module_run("diag_guard_injection_scan",
                     "CodeRuleScanner._ast_scan",
                     outcome=outcome,
                     duration_ms=(time.time() - started) * 1000.0,
                     violations=violations, warnings=warnings)
def _finding(rule_id: str, message: str, line: int,
             severity: str = "CRITICAL", rule_type: str = "") -> dict:
    return {"type": rule_type or rule_id, "rule_id": rule_id,
            "message": message, "line": line, "severity": severity}
def _parse_source(code: str, started: float) -> tuple[Any, list[dict]]:
    try:
        tree = ast.parse(code)
        compile(tree, "<injection-scan>", "exec")
        return tree, []
    except (SyntaxError, ValueError, RecursionError, TypeError, MemoryError) as e:
        _log.warning("[CIE] _ast_scan 语法错误: %s", e, exc_info=True)
        _write_scan_run("degraded_syntax", started, 1, 0)
        return None, [_finding(
            "SYNTAX", "语法错误: " + str(e),
            getattr(e, "lineno", 0) or 0,
            rule_type="syntax_error")]
def _apply_suppressions(code: str, violations: list[dict],
                        warnings: list[dict]) -> tuple[list[dict], list[dict]]:
    suppressions = parse_suppressions(code)
    if not suppressions:
        return violations, warnings
    return (filter_suppressed_findings(
                violations, suppressions, _CIE_RULE_SUPPRESS_CATEGORY),
            filter_suppressed_findings(
                warnings, suppressions, _CIE_RULE_SUPPRESS_CATEGORY))
def _ascii_upper(text: str) -> str:
    return "".join(ch.upper() if "a" <= ch <= "z" else ch for ch in text)
def _sql_word_index(text: str, word: str, start: int = 0) -> int:
    quote = ""
    index = 0
    while index < len(text):
        char = text[index]
        if quote:
            if char == quote:
                if index + 1 < len(text) and text[index + 1] == quote:
                    index += 2
                    continue
                quote = ""
            index += 1
            continue
        if char in "'\"`":
            quote = char
            index += 1
            continue
        if char == "[":
            quote = "]"
            index += 1
            continue
        if text.startswith("--", index):
            newline = text.find("\n", index + 2)
            index = len(text) if newline < 0 else newline + 1
            continue
        if text.startswith("/*", index):
            comment_end = text.find("*/", index + 2)
            index = len(text) if comment_end < 0 else comment_end + 2
            continue
        if index >= start and text.startswith(word, index):
            before = text[index - 1] if index > 0 else ""
            after_at = index + len(word)
            after = text[after_at] if after_at < len(text) else ""
            if not (before.isalnum() or before == "_") and not (
                    after.isalnum() or after == "_"):
                return index
        index += 1
    return -1
def _sql_starts_with_word(text: str, word: str) -> bool:
    if not text.startswith(word):
        return False
    after = text[len(word):len(word) + 1]
    return not (after.isalnum() or after == "_")
_SQL_DEFAULT_NUMERIC_RE = re.compile(
    r"[+-]?(?:0[xX][0-9A-Fa-f]+|"
    r"(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?)")
_SQL_DEFAULT_CONSTANT_WORDS = (
    "NULL", "TRUE", "FALSE",
)
_SQL_DEFAULT_CONSTRAINT_WORDS = (
    "CONSTRAINT", "PRIMARY", "NOT", "NULL", "UNIQUE", "CHECK",
    "COLLATE", "REFERENCES", "GENERATED", "AS",
)
def _sql_skip_trivia(text: str, index: int) -> int:
    while index < len(text):
        if text[index].isspace():
            index += 1
            continue
        if text.startswith("--", index):
            newline = text.find("\n", index + 2)
            if newline < 0:
                return len(text)
            index = newline + 1
            continue
        if text.startswith("/*", index):
            comment_end = text.find("*/", index + 2)
            if comment_end < 0:
                return len(text)
            index = comment_end + 2
            continue
        break
    return index
def _sql_quoted_literal_end(text: str, start: int) -> int:
    quote = text[start]
    index = start + 1
    while index < len(text):
        if text[index] != quote:
            index += 1
            continue
        if index + 1 < len(text) and text[index + 1] == quote:
            index += 2
            continue
        return index + 1
    return -1
def _sql_default_is_constant(rest: str) -> bool:
    start = _sql_skip_trivia(rest, 0)
    if start >= len(rest) or rest[start] == "(":
        return False
    end = -1
    if rest[start] in "\"'":
        end = _sql_quoted_literal_end(rest, start)
    elif rest[start] in "xX" and rest[start + 1:start + 2] == "'":
        end = _sql_quoted_literal_end(rest, start + 1)
    else:
        numeric = _SQL_DEFAULT_NUMERIC_RE.match(rest, start)
        if numeric is not None:
            end = numeric.end()
        else:
            keyword_text = _ascii_upper(rest[start:])
            for keyword in _SQL_DEFAULT_CONSTANT_WORDS:
                if _sql_starts_with_word(keyword_text, keyword):
                    end = start + len(keyword)
                    break
    if end < 0:
        return False
    tail = _sql_skip_trivia(rest, end)
    if tail >= len(rest) or rest[tail] == ";":
        return True
    tail_upper = _ascii_upper(rest[tail:])
    return any(_sql_starts_with_word(tail_upper, keyword)
               for keyword in _SQL_DEFAULT_CONSTRAINT_WORDS)
def _assign_target_label(target: Any) -> str:
    if isinstance(target, ast.Name):
        return target.id
    if isinstance(target, ast.Attribute):
        return resolve_attr_name(target).lstrip(".")
    if isinstance(target, ast.Subscript):
        key = target.slice
        if isinstance(key, ast.Constant) and isinstance(key.value, str):
            return key.value
    return ""
def _str_assign_label(target: Any, value: Any) -> str:
    if not (isinstance(value, ast.Constant)
            and isinstance(value.value, str)
            and len(value.value) > 3):
        return ""
    return _assign_target_label(target)
def _iter_assignment_target_values(target: Any, value: Any):
    if (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))):
        starred = [index for index, element in enumerate(target.elts)
                   if isinstance(element, ast.Starred)]
        if len(starred) == 1:
            star_index = starred[0]
            fixed_count = len(target.elts) - 1
            if len(value.elts) < fixed_count:
                return
            pairs = [*zip(target.elts[:star_index],
                          value.elts[:star_index], strict=False)]
            for target_elt, value_elt in pairs:
                yield from _iter_assignment_target_values(target_elt, value_elt)
            suffix = target.elts[star_index + 1:]
            starred = target.elts[star_index]
            value_stop = len(value.elts) - len(suffix)
            for value_elt in value.elts[star_index:value_stop]:
                yield from _iter_assignment_target_values(
                    starred.value, value_elt)
            for target_elt, value_elt in zip(
                    suffix, value.elts[value_stop:], strict=False):
                yield from _iter_assignment_target_values(target_elt, value_elt)
            return
        for target_elt, value_elt in zip(target.elts, value.elts, strict=False):
            yield from _iter_assignment_target_values(target_elt, value_elt)
        return
    yield target, value
def resolve_attr_name(node: Any) -> str:
    parts: list[str] = []
    cur = node
    while isinstance(cur, ast.Attribute):
        parts.append(cur.attr)
        cur = cur.value
    if isinstance(cur, ast.Name):
        parts.append(cur.id)
        return ".".join(reversed(parts))
    return "." + ".".join(reversed(parts)) if parts else ""
_SAFE_YAML_LOADER_NAMES: frozenset[str] = frozenset(
    YAML_SAFE_LOADERS | {"yaml." + name for name in YAML_SAFE_LOADERS})
def _is_safe_yaml_loader(loader: Any,
                         aliases: Mapping[str, str]) -> bool:
    if not isinstance(loader, (ast.Name, ast.Attribute)):
        return False
    full_name = _resolve_call_alias(resolve_attr_name(loader), aliases, loader)
    return full_name in _SAFE_YAML_LOADER_NAMES
def yaml_load_has_safe_loader(
        node: ast.Call, aliases: Mapping[str, str] | None = None,
) -> bool:
    loader = next((kw.value for kw in node.keywords if kw.arg == "Loader"), None)
    if loader is None and len(node.args) >= 2:
        loader = node.args[1]
    return (loader is not None
            and _is_safe_yaml_loader(loader, aliases or {}))
_UNSAFE_DESERIALIZATION_CALLS = YAML_UNSAFE_LOADER_CALLS | {
    "unsafe_load", "unsafe_load_all",
}
def _is_unsafe_deserialization_call(call_name: str) -> bool:
    return (call_name in _UNSAFE_DESERIALIZATION_CALLS
            or call_name.endswith((".unsafe_load", ".unsafe_load_all")))
_BUILTIN_EXEC_NAMESPACES: frozenset[str] = frozenset({"builtins", "__builtins__"})
_ATTR_EXEC_NAMES: frozenset[str] = frozenset({"eval", "exec"})
_EXEC_RULE_IDS: dict[str, str] = {
    "eval": "WRITE-BLOCK-01", "exec": "WRITE-BLOCK-02",
}
_EXEC_CALL_NAMES = frozenset(_ATTR_EXEC_NAMES | {
    f"{namespace}.{name}"
    for namespace in _BUILTIN_EXEC_NAMESPACES
    for name in _ATTR_EXEC_NAMES
})
_EXEC_MESSAGE = '{call}() 任意代码执行 (行{lineno})'
_CALL_RULE_TABLE: dict[str, tuple[str, str, str]] = {
    **dict.fromkeys(
        _UNSAFE_DESERIALIZATION_CALLS,
        ('WRITE-BLOCK-04', 'BLOCK', '{call}() 不安全反序列化 (行{lineno})'),
    ),
    **{
        name: (_EXEC_RULE_IDS[name], 'BLOCK', _EXEC_MESSAGE)
        for name in _ATTR_EXEC_NAMES
    },
    **{
        f"{namespace}.{name}": (_EXEC_RULE_IDS[name], 'BLOCK', _EXEC_MESSAGE)
        for namespace in _BUILTIN_EXEC_NAMESPACES
        for name in _ATTR_EXEC_NAMES
    },
    'os.system': ('WRITE-BLOCK-03', 'BLOCK', '{call}() 命令注入风险 (行{lineno})'),
    'os.popen': ('WRITE-BLOCK-03', 'BLOCK', '{call}() 命令注入风险 (行{lineno})'),
    'pickle.load': ('WRITE-BLOCK-05', 'BLOCK', '{call}() pickle 反序列化不安全 (行{lineno})'),
    'pickle.loads': ('WRITE-BLOCK-05', 'BLOCK', '{call}() pickle 反序列化不安全 (行{lineno})'),
    **{
        name: (rule_id, 'WARN',
               f'使用 safe_delete() 替代 {name}() (行{{lineno}})')
        for name, rule_id in _DELETE_RULE_IDS.items()
    },
    'print': ('WRITE-WARN-03', 'WARN', '使用 logging 替代 print() (行{lineno})'),
}
def _is_builtin_exec_attr(func: Any) -> bool:
    return (isinstance(func, ast.Attribute)
            and func.attr in _ATTR_EXEC_NAMES
            and isinstance(func.value, ast.Name)
            and func.value.id in _BUILTIN_EXEC_NAMESPACES)
_WRITE_RULE_SUPPRESS_CATEGORY: dict[str, str] = {
    "WRITE-BLOCK-01": "code_execution",
    "WRITE-BLOCK-02": "code_execution",
    "WRITE-BLOCK-03": "code_execution",
    "WRITE-BLOCK-06": "code_execution",
    "WRITE-WARN-01": "file_operations",
    "WRITE-WARN-02": "file_operations",
    "WRITE-WARN-05": "code_execution",
}
_WRITE_FAIL_CLOSED_RULES: frozenset[str] = frozenset({
    "WRITE-BLOCK-04", "WRITE-BLOCK-05", "WRITE-BLOCK-07",
    "WRITE-WARN-03", "WRITE-WARN-04",
})
_WRITE_ALWAYS_BLOCK_RULES: frozenset[str] = frozenset({
    "SYNTAX-ERROR", "NO-PATCH-FIX", "RL-01",
    "WRITE-BLOCK-01", "WRITE-BLOCK-02", "WRITE-BLOCK-03",
    "WRITE-BLOCK-04", "WRITE-BLOCK-05", "WRITE-BLOCK-06",
    "WRITE-BLOCK-07",
})
CIE_WRITE_SAME_ROOT_RULE_IDS: dict[str, tuple[str, ...]] = {
    "SEC-01": ("WRITE-BLOCK-01", "WRITE-BLOCK-02"),
    "CS-91": ("WRITE-BLOCK-06",),
    "CS-92": ("WRITE-BLOCK-04",),
    "C4": _DELETE_WRITE_RULE_IDS,
    "C6": ("WRITE-BLOCK-07",),
}
def is_always_block_finding(finding: Any) -> bool:
    if not isinstance(finding, Mapping):
        return False
    rule_id = str(finding.get("rule_id") or "")
    return (rule_id in _WRITE_ALWAYS_BLOCK_RULES
            or rule_id.startswith(("SEC-", "SE-")))
def is_fail_closed_finding(finding: Any) -> bool:
    return (isinstance(finding, Mapping)
            and str(finding.get("rule_id") or "") in _WRITE_FAIL_CLOSED_RULES)
def _filter_write_suppressed(
    findings: list[dict], suppressions: dict
) -> list[dict]:
    if not suppressions:
        return findings
    kept_ids = {id(v) for v in filter_suppressed_findings(
        [v for v in findings if not is_fail_closed_finding(v)],
        suppressions, _WRITE_RULE_SUPPRESS_CATEGORY)}
    return [v for v in findings
            if is_fail_closed_finding(v) or id(v) in kept_ids]
_STAR_RESOLVABLE_CALLS = frozenset(
    set(_CALL_RULE_TABLE)
    | _DANGEROUS_DELETE_CALLS
    | _EXEC_CALL_NAMES
    | SUBPROCESS_SHELL_CALLS
    | _MUTABLE_DEFAULT_CALLS
    | {"os.close", "re.compile"}
)
class _ScopedCallAliases(Mapping[str, str]):
    def __init__(self, tree: ast.AST, code: str | None = None):
        module_aliases, from_imports, _stars = collect_import_bindings("", tree)
        self._fallback = {**module_aliases, **from_imports}
        self._id_parents = build_parent_map(tree)
        self._imports = scope_import_tables(tree)
        self._lexical = collect_lexical_scope_table(tree)
        self._resolver = (ScopeNameResolver(code, "<injection-scan>", tree, set())
                          if isinstance(code, str) else None)
        self._tree = tree
        self._conditional_bound: dict[ast.AST, set[str]] | None = None
        self._star_modules: dict[ast.AST, list[ast.ImportFrom]] = {}
        for node in walk_nodes(tree):
            if not (isinstance(node, ast.ImportFrom)
                    and node.module and not node.level
                    and any(alias.name == "*" for alias in node.names)):
                continue
            scopes = iter_evaluation_scope_chain(node, self._id_parents)
            if scopes:
                self._star_modules.setdefault(scopes[0], []).append(node)
    def _scope_conditional_bound(self, root: str, scope: ast.AST) -> bool:
        if self._conditional_bound is None:
            self._conditional_bound = self._collect_conditional_bindings(
                self._tree)
        return root in self._conditional_bound.get(scope, ())
    def _collect_conditional_bindings(
            self, tree: ast.AST) -> dict[ast.AST, set[str]]:
        conditional: dict[ast.AST, set[str]] = {}
        conditional_nodes = (
            ast.If, ast.For, ast.AsyncFor, ast.While, ast.IfExp, ast.BoolOp,
            ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
            ast.Match, *TRY_NODE_TYPES,
        )
        for node in walk_nodes(tree):
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                continue
            names = scope_node_bound_names(node)
            if not names:
                continue
            scopes = iter_evaluation_scope_chain(node, self._id_parents)
            if not scopes:
                continue
            scope = scopes[0]
            # 绑定节点自身就是条件容器时（最典型：for 循环目标，循环体
            # 可能零次执行，名字可能仍指向导入对象），祖先链不会包含它，
            # 必须单独登记；否则会把「可能仍是导入」误判为确定阴影。
            if isinstance(node, conditional_nodes):
                conditional.setdefault(scope, set()).update(names)
                continue
            ancestor = self._id_parents.get(id(node))
            while ancestor is not None and ancestor is not scope:
                if isinstance(ancestor, conditional_nodes):
                    conditional.setdefault(scope, set()).update(names)
                    break
                ancestor = self._id_parents.get(id(ancestor))
        return conditional
    def __getitem__(self, key: str) -> str:
        return self._fallback[key]
    def __iter__(self):
        return iter(self._fallback)
    def __len__(self) -> int:
        return len(self._fallback)
    @staticmethod
    def _root_name_node(node: ast.AST) -> ast.Name | None:
        current = node.func if isinstance(node, ast.Call) else node
        while isinstance(current, ast.Attribute):
            current = current.value
        return current if isinstance(current, ast.Name) else None
    def _statement_in_scope(
            self, node: ast.AST, scope: ast.AST) -> ast.stmt | None:
        current = node
        parent = self._id_parents.get(id(current))
        while parent is not None and parent is not scope:
            current = parent
            parent = self._id_parents.get(id(current))
        return current if parent is scope and isinstance(current, ast.stmt) else None
    def _is_deferred_generator_evaluation(
            self, node: ast.AST, scope: ast.AST) -> bool:
        path_ids = {id(node)}
        current = node
        parent = self._id_parents.get(id(current))
        while parent is not None and parent is not scope:
            if isinstance(parent, ast.GeneratorExp):
                first_iter = (parent.generators[0].iter
                              if parent.generators else None)
                if id(first_iter) not in path_ids:
                    return True
            path_ids.add(id(parent))
            current = parent
            parent = self._id_parents.get(id(current))
        return False
    def _is_future_star_import(
            self, star_import: ast.ImportFrom, node: ast.AST,
            scope: ast.AST) -> bool:
        if (not isinstance(scope, ast.Module)
                or self._is_deferred_generator_evaluation(node, scope)):
            return False
        use_statement = self._statement_in_scope(node, scope)
        import_statement = self._statement_in_scope(star_import, scope)
        if (use_statement is None or import_statement is None
                or use_statement is import_statement):
            return False
        return ((import_statement.lineno, import_statement.col_offset)
                > (use_statement.lineno, use_statement.col_offset))
    def binding(self, root: str, node: ast.AST) -> str | None:
        scopes = tuple(iter_evaluation_scope_chain(node, self._id_parents))
        for scope in scopes:
            record = self._imports.get(scope, {}).get(root)
            if record is not None:
                root_node = self._root_name_node(node)
                has_shadow = any(
                    root in self._lexical.shadow_bound.get(scope, ())
                    for scope in scopes)
                if (self._resolver is not None and root_node is not None
                        and has_shadow):
                    active_import = self._resolver.import_path(root_node)
                    if active_import is not None:
                        return active_import
                    if self._resolver.is_bound(root_node):
                        if self._conditional_bound is None:
                            self._conditional_bound = (
                                self._collect_conditional_bindings(self._tree))
                        conditionally_bound = any(
                            root in self._conditional_bound.get(scope, ())
                            for scope in scopes)
                        if not conditionally_bound:
                            return ""
                if record[0] == "import":
                    return record[1]
                if record[0] == "from":
                    module, imported = record[1], record[2]
                    return f"{module}.{imported}" if module else imported
            if root in self._lexical.shadow_bound.get(scope, ()):
                # 局部条件重绑定（if/try/for 分支内赋值）不能让名字变成
                # 「确定不是导入对象」：分支未命中时名字仍是外层导入。
                # 仅当前作用域的条件阴影可穿透，外层确定阴影仍然遮蔽。
                if self._scope_conditional_bound(root, scope):
                    continue
                return ""
        for scope in scopes:
            star_imports = self._star_modules.get(scope)
            if not star_imports:
                continue
            if scope is scopes[0]:
                star_imports = [
                    item for item in star_imports
                    if not self._is_future_star_import(item, node, scope)]
                if not star_imports:
                    continue
            ordered = sorted(
                star_imports,
                key=lambda item: (item.lineno, item.col_offset),
                reverse=True,
            )
            for star_import in ordered:
                candidate = f"{star_import.module}.{root}"
                if candidate in _STAR_RESOLVABLE_CALLS:
                    return candidate
            return None
        return None
def _resolve_call_alias(
        full_name: str, aliases: Mapping[str, str],
        node: ast.AST | None = None,
) -> str:
    root, separator, tail = full_name.partition(".")
    bound = (aliases.binding(root, node)
             if isinstance(aliases, _ScopedCallAliases) and node is not None
             else aliases.get(root))
    if bound is None:
        return full_name
    return bound + (separator + tail if separator else "")
def _scan_call_violations(node: ast.AST,
                          aliases: Mapping[str, str]) -> list[dict]:
    violations: list[dict] = []
    if not isinstance(node, ast.Call):
        return violations
    call_name = _resolve_call_alias(resolve_call_name(node), aliases, node)
    if (call_name in ("yaml.load", "yaml.load_all")
            and yaml_load_has_safe_loader(node, aliases)):
        return violations
    entry = _CALL_RULE_TABLE.get(call_name)
    if entry is not None:
        rule_id, severity, msg_tpl = entry
        violations.append(_finding(
            rule_id, msg_tpl.format(call=call_name, lineno=node.lineno),
            node.lineno, severity))
    elif _is_unsafe_deserialization_call(call_name):
        violations.append(_finding(
            "WRITE-BLOCK-04",
            f"{call_name}() 不安全反序列化 (行{node.lineno})",
            node.lineno, "BLOCK"))
    elif (isinstance(node.func, ast.Attribute)
            and node.func.attr in _ATTR_EXEC_NAMES
            and not _is_builtin_exec_attr(node.func)):
        violations.append(_finding(
            "WRITE-WARN-05",
            f"{call_name}() 属性名为 eval/exec，需确认不是内置同名函数"
            f" (行{node.lineno})", node.lineno, "WARN"))
    elif call_name in SUBPROCESS_SHELL_CALLS:
        violations.extend(_scan_subprocess_shell(node))
    return violations
def _shell_literal_text(node: ast.AST) -> str:
    if isinstance(node, ast.Constant):
        return repr(node.value)
    try:
        return ast.unparse(node)
    except (AttributeError, ValueError, TypeError, RecursionError):
        return "<expr>"
def _iter_true_shell_values(node: ast.Call):
    for kw in node.keywords:
        if is_shell_true_keyword(kw):
            yield kw.value
    if len(node.args) > 8:
        positional = node.args[8]
        if is_shell_true_keyword(ast.keyword(arg="shell", value=positional)):
            yield positional
def _scan_subprocess_shell(node: ast.Call) -> list[dict]:
    return [
        _finding("WRITE-BLOCK-06",
                 f"shell={_shell_literal_text(value)} "
                 f"命令注入风险 (行{node.lineno})",
                 node.lineno, "BLOCK")
        for value in _iter_true_shell_values(node)
    ]
def _scan_except_violations(node: ast.AST) -> list[dict]:
    if isinstance(node, ast.ExceptHandler) and node.type is None:
        return [_finding(
            "WRITE-BLOCK-07",
            f"裸 except 应指定具体异常 (行{node.lineno})",
            node.lineno, "BLOCK")]
    return []
def _scan_assert_violations(node: ast.AST) -> list[dict]:
    if isinstance(node, ast.Assert) and not is_invariant_assert(node):
        return [_finding(
            "WRITE-WARN-04",
            f"assert 应用显式 raise 替代 (行{node.lineno})",
            node.lineno, "WARN")]
    return []
def scan_write_redlines(tree: ast.AST, code: str) -> list[dict]:
    violations: list[dict] = []
    aliases = _ScopedCallAliases(tree, code)
    for node in walk_nodes(tree):
        violations.extend(_scan_call_violations(node, aliases))
        violations.extend(_scan_except_violations(node))
        violations.extend(_scan_assert_violations(node))
    return _filter_write_suppressed(violations, parse_suppressions(code))
def classify_call_redline(
        func: Any, aliases: Mapping[str, str] | None = None,
) -> tuple[str, str] | None:
    full_name = (resolve_attr_name(func) if isinstance(func, ast.Attribute)
                 else func.id if isinstance(func, ast.Name) else "")
    full_name = _resolve_call_alias(
        full_name, aliases if aliases is not None else {}, func)
    if full_name in _DANGEROUS_DELETE_CALLS:
        return "C4", full_name
    if full_name in _EXEC_CALL_NAMES:
        return "SEC-01", full_name
    return None
def classify_except_redline(node: ast.ExceptHandler) -> str | None:
    if node.type is None:
        return "C6"
    if len(node.body) == 1 and isinstance(node.body[0], ast.Pass):
        return "C13"
    return None
_CLOSE_CLEANUP_METHODS: frozenset[str] = frozenset({
    "close", "aclose", "__exit__", "__del__",
    "cleanup", "shutdown", "stop", "release", "disconnect",
})
_CLOSE_GUARD_EXCEPT_NAMES: frozenset[str] = frozenset({
    "OSError", "IOError", "EnvironmentError", "Exception", "BaseException",
})
def _except_guards_close(handler: ast.ExceptHandler) -> bool:
    if handler.type is None:
        return True
    types = (handler.type.elts if isinstance(handler.type, ast.Tuple)
             else [handler.type])
    for item in types:
        name = (resolve_attr_name(item) if isinstance(item, ast.Attribute)
                else item.id if isinstance(item, ast.Name) else "")
        if name.rsplit(".", 1)[-1] in _CLOSE_GUARD_EXCEPT_NAMES:
            return True
    return False
def _close_needs_review(node: ast.Call,
                        guarded_calls: frozenset[int],
                        aliases: Mapping[str, str]) -> bool:
    if _resolve_call_alias(resolve_call_name(node), aliases, node) == "os.close":
        return False
    return id(node) not in guarded_calls
def _with_target_labels(target: ast.AST) -> set[str]:
    if isinstance(target, ast.Name):
        return {target.id}
    if isinstance(target, ast.Attribute):
        return {resolve_attr_name(target)}
    if isinstance(target, ast.Starred):
        return _with_target_labels(target.value)
    if isinstance(target, (ast.Tuple, ast.List)):
        return {label for element in target.elts
                for label in _with_target_labels(element)}
    return set()
def _close_guarded_calls(
        tree: ast.AST, aliases: Mapping[str, str]) -> frozenset[int]:
    guarded: set[int] = set()
    def mark_current_scope_calls(
            blocks: list[ast.stmt],
            receiver_labels: frozenset[str] | None = None,
            guaranteed_only: bool = False) -> None:
        for block in blocks:
            stack = [block]
            while stack:
                current = stack.pop()
                if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                        ast.Lambda)):
                    continue
                if guaranteed_only and isinstance(current, (
                        ast.If, ast.For, ast.AsyncFor, ast.While, ast.With,
                        ast.AsyncWith, ast.IfExp, ast.BoolOp, ast.ListComp,
                        ast.SetComp, ast.DictComp, ast.GeneratorExp, ast.Match,
                        *TRY_NODE_TYPES)):
                    continue
                if (isinstance(current, ast.Call)
                        and isinstance(current.func, ast.Attribute)
                        and current.func.attr == "close"
                        and (receiver_labels is None
                             or resolve_attr_name(current.func.value)
                             in receiver_labels)):
                    guarded.add(id(current))
                stack.extend(ast.iter_child_nodes(current))
    for node in walk_nodes(tree):
        receiver_labels: frozenset[str] | None = None
        if isinstance(node, TRY_NODE_TYPES):
            blocks: list[ast.stmt] = list(node.finalbody)
            guaranteed_only = True
            if (len(node.body) == 1
                    and any(_except_guards_close(handler)
                            for handler in node.handlers)):
                only_statement = node.body[0]
                if (isinstance(only_statement, ast.Expr)
                        and isinstance(only_statement.value, ast.Call)
                        and isinstance(only_statement.value.func, ast.Attribute)
                        and only_statement.value.func.attr == "close"):
                    blocks.extend(node.body)
        elif isinstance(node, (ast.With, ast.AsyncWith)):
            blocks = list(node.body)
            guaranteed_only = False
            receiver_labels = frozenset(
                label for item in node.items
                if item.optional_vars is not None
                and not (
                    isinstance(item.context_expr, ast.Call)
                    and _resolve_call_alias(
                        resolve_call_name(item.context_expr), aliases,
                        item.context_expr) == "sqlite3.connect")
                for label in _with_target_labels(item.optional_vars))
        elif (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
              and node.name in _CLOSE_CLEANUP_METHODS):
            blocks = list(node.body)
            guaranteed_only = False
        else:
            continue
        mark_current_scope_calls(blocks, receiver_labels, guaranteed_only)
    return frozenset(guarded)
class _SecondaryRuleScanner:
    def run(self, code: Any, collectibles: _ScanCollectibles,
            violations: Any, warnings: Any) -> None:
        for loop in collectibles.loop_nodes:
            self._check_loop_recompile(
                loop, warnings, collectibles.aliases,
                collectibles.annotations_evaluated)
        self._check_mutable_default_args(
            collectibles.func_nodes, violations, collectibles.aliases)
        self._check_multiline_concat(code, collectibles.str_lines, warnings)
        self._check_replace_chain_depth(collectibles.replace_chains, warnings)
    @staticmethod
    def _check_loop_recompile(loop: Any, warnings: Any,
                              aliases: Mapping[str, str],
                              annotations_evaluated: bool = True) -> None:
        stack = list(loop.body)
        if isinstance(loop, (ast.For, ast.AsyncFor)):
            stack.append(loop.target)
        if isinstance(loop, ast.While) and loop.test is not None:
            stack.append(loop.test)
        while stack:
            node = stack.pop()
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.Lambda)):
                stack.extend(getattr(node, "decorator_list", ()))
                stack.extend(
                    default for default in (
                        *node.args.defaults, *node.args.kw_defaults)
                    if default is not None)
                if annotations_evaluated:
                    stack.extend(
                        arg.annotation for arg in iter_arg_nodes(node.args)
                        if arg.annotation is not None)
                    returns = getattr(node, "returns", None)
                    if returns is not None:
                        stack.append(returns)
                continue
            if isinstance(node, (ast.For, ast.AsyncFor)):
                stack.append(node.iter)
                continue
            if isinstance(node, ast.While):
                continue
            if (isinstance(node, ast.Call)
                    and _resolve_call_alias(
                        resolve_call_name(node), aliases, node) == "re.compile"):
                warnings.append(_finding(
                    "R3",
                    "循环内编译正则表达式,应将 re.compile 提到循环外",
                    node.lineno, "MEDIUM"))
            stack.extend(ast.iter_child_nodes(node))
    @staticmethod
    def _is_mutable_default_expr(
            expr: Any, aliases: Mapping[str, str]) -> bool:
        if isinstance(expr, (
                ast.List, ast.Dict, ast.Set,
                ast.ListComp, ast.DictComp, ast.SetComp)):
            return True
        if not isinstance(expr, ast.Call):
            return False
        func = expr.func
        name = (func.id if isinstance(func, ast.Name)
                else resolve_attr_name(func) if isinstance(func, ast.Attribute)
                else "")
        return _resolve_call_alias(name, aliases, expr) in _MUTABLE_DEFAULT_CALLS
    def _check_mutable_default_args(self, func_nodes: Any,
                                    violations: Any,
                                    aliases: Mapping[str, str]) -> None:
        for func in func_nodes:
            _fname = getattr(func, "name", "") or "<lambda>"
            for arg in func.args.defaults + func.args.kw_defaults:
                if (arg is not None
                        and self._is_mutable_default_expr(arg, aliases)):
                    violations.append(_finding(
                        "CS-95",
                        "函数 " + _fname + " 使用了可变默认参数,请用 None 哨兵",
                        func.lineno))
    @staticmethod
    def _is_plus_tail(line: str,
                      spans: list[tuple[int, int]] | None = None) -> bool:
        cur = line.rstrip()
        if spans:
            pos = len(cur) - 1
            for start, end in spans:
                if start <= pos < end:
                    cur = cur[:start].rstrip()
                    break
        elif line.lstrip().startswith("#"):
            return False
        if cur.endswith("\\"):
            cur = cur[:-1].rstrip()
        return cur.endswith("+")
    @staticmethod
    def _is_join_exempt(codelines: list, i: int) -> bool:
        return ("join" in codelines[i]
                or "join" in codelines[i + 1]
                or (i > 0 and "join" in codelines[i - 1]))
    @classmethod
    def _is_concat_start(cls, codelines: list, i: int,
                         skip: frozenset, spans: list | None = None) -> bool:
        if (i + 1) in skip or (i + 2) in skip:
            return False
        return (cls._is_plus_tail(codelines[i], spans)
                and codelines[i + 1].lstrip().startswith(('"', "'"))
                and not cls._is_join_exempt(codelines, i))
    @classmethod
    def _check_multiline_concat(cls, code: Any, str_lines: Any,
                                warnings: Any) -> None:
        if not code:
            return
        _skip = str_lines if str_lines is not None else frozenset()
        span_map = string_comment_spans(code)
        codelines = code.split("\n")
        for i in range(len(codelines) - 1):
            spans = span_map.get(i + 1) if span_map else None
            if cls._is_concat_start(codelines, i, _skip, spans):
                warnings.append(_finding(
                    "C11", "多行字符串拼接,建议使用 f-string 或 join()",
                    i + 1, "MEDIUM"))
    @staticmethod
    def _check_replace_chain_depth(replace_chains: Any,
                                   warnings: Any) -> None:
        inner_receivers = {
            id(node.func.value) for node in replace_chains
            if isinstance(node.func.value, ast.Call)
        }
        for node in replace_chains:
            if id(node) in inner_receivers:
                continue
            if isinstance(node.func.value, ast.Call):
                depth = 1
                cur = node.func.value
                while (isinstance(cur, ast.Call)
                       and isinstance(cur.func, ast.Attribute)):
                    if cur.func.attr == "replace":
                        depth += 1
                        cur = cur.func.value
                    else:
                        break
                if depth >= 3:
                    warnings.append(_finding(
                        "R7",
                        "连续 " + str(depth) + " 次 replace() 链式调用需验证正确性",
                        node.lineno, "MEDIUM"))
_SECONDARY_RULES = _SecondaryRuleScanner()
class CodeRuleScanner:
    @staticmethod
    def _iter_sensitive_str_assigns(node: Any):
        for name, value, lineno in CodeRuleScanner._iter_named_str_assigns(node):
            if not any(kw in name.lower() for kw in SENSITIVE_NAME_KEYWORDS):
                continue
            if is_rule_name_constant(value, (name,)):
                continue
            yield name, lineno
    @staticmethod
    def _iter_named_str_assigns(node: Any):
        if isinstance(node, ast.Assign):
            pairs = [(t, node.value) for t in node.targets]
        elif isinstance(node, ast.AnnAssign):
            pairs = [(node.target, node.value)] if node.value is not None else []
        elif isinstance(node, ast.NamedExpr):
            pairs = [(node.target, node.value)]
        else:
            return
        for target, value in pairs:
            target_values = _iter_assignment_target_values(target, value)
            for target_elt, value_elt in target_values:
                label = _str_assign_label(target_elt, value_elt)
                if label:
                    yield label, value_elt.value, node.lineno
    @staticmethod
    def _multiline_string_lines(tree: Any) -> frozenset:
        return frozenset(line for start, end in multiline_string_spans(tree)
                         for line in range(start, end + 1))
    def _check_call_injection(self, node: Any, violations: Any,
                              warnings: Any,
                              aliases: Mapping[str, str]) -> None:
        redline = classify_call_redline(node.func, aliases)
        if redline is not None:
            rule_id, full_name = redline
            message = ("禁止使用 " + full_name + "(),请用 safe_delete()"
                       if rule_id == "C4"
                       else "禁止使用 " + full_name + "(),存在代码注入风险")
            violations.append(_finding(rule_id, message, node.lineno))
            return
        full_name = _resolve_call_alias(resolve_call_name(node), aliases, node)
        if (isinstance(node.func, ast.Attribute)
                and node.func.attr in _ATTR_EXEC_NAMES
                and not _is_builtin_exec_attr(node.func)):
            warnings.append(_finding(
                "SEC-02",
                "属性调用 " + full_name + "() 名称与内置 eval/exec 同名，"
                "需确认不是动态代码执行",
                node.lineno, "LOW", rule_type="exec_attr_review"))
            return
        if full_name in SUBPROCESS_SHELL_CALLS:
            self._append_shell_true_violation(node, violations)
            return
        if _is_unsafe_deserialization_call(full_name):
            self._append_yaml_loader_violation(
                node, full_name, violations, aliases)
    @staticmethod
    def _append_shell_true_violation(node: Any, violations: Any) -> None:
        for _value in _iter_true_shell_values(node):
            violations.append(_finding(
                "CS-91",
                "禁止 subprocess 使用 shell=True,存在命令注入风险",
                node.lineno))
    @staticmethod
    def _append_yaml_loader_violation(node: Any, full_name: str,
                                      violations: Any,
                                      aliases: Mapping[str, str]) -> None:
        _can_take_loader = full_name in ("yaml.load", "yaml.load_all")
        if _can_take_loader and yaml_load_has_safe_loader(node, aliases):
            return
        _safe_alt = ("yaml.safe_load_all()"
                     if full_name.endswith("_all") else "yaml.safe_load()")
        violations.append(_finding(
            "CS-92",
            "禁止 " + full_name + "() 缺失或使用不安全的 Loader,请用 " + _safe_alt,
            node.lineno))
    @staticmethod
    def _is_sql_alter_add_default(arg0: Any) -> bool:
        if not (isinstance(arg0, ast.Constant) and isinstance(arg0.value, str)):
            return False
        sql_upper = _ascii_upper(arg0.value)
        alter = _sql_word_index(sql_upper, "ALTER")
        table = _sql_word_index(sql_upper, "TABLE")
        add = _sql_word_index(sql_upper, "ADD")
        if min(alter, table, add) < 0 or not alter < table < add:
            return False
        index = _sql_word_index(sql_upper, "DEFAULT", add)
        while index >= 0:
            if not _sql_default_is_constant(arg0.value[index + len("DEFAULT"):]):
                return True
            index = _sql_word_index(sql_upper, "DEFAULT", index + len("DEFAULT"))
        return False
    def _check_call_quality(self, node: Any, warnings: Any, replace_chains: Any,
                            guarded_close_calls: Any,
                            aliases: Mapping[str, str]) -> None:
        if not isinstance(node.func, ast.Attribute):
            return
        method = node.func.attr
        if method == "execute":
            if node.args and self._is_sql_alter_add_default(node.args[0]):
                warnings.append(_finding(
                    "DB-01",
                    "SQLite ALTER TABLE 不支持非常量 DEFAULT,请分两步操作",
                    node.lineno, "HIGH"))
            return
        if method == "close":
            if _close_needs_review(node, guarded_close_calls, aliases):
                warnings.append(_finding(
                    "DB-02",
                    "未受保护的 .close() 调用在异常路径上会漏关资源,"
                    "请改用 finally 或 contextlib.closing",
                    node.lineno, "HIGH"))
            return
        if method == "replace":
            replace_chains.append(node)
    def _check_assign_secrets(self, node: Any, violations: Any) -> None:
        for name, lineno in self._iter_sensitive_str_assigns(node):
            violations.append(_finding(
                "RL-01",
                "硬编码敏感信息: " + name + ",请用环境变量或密钥管理",
                lineno))
    def _check_except_handler(self, node: Any, violations: Any, warnings: Any) -> None:
        if not isinstance(node, ast.ExceptHandler):
            return
        rule_id = classify_except_redline(node)
        if rule_id == "C6":
            violations.append(_finding(
                "C6", "禁止 bare except:,必须指定异常类型", node.lineno))
        elif rule_id == "C13":
            warnings.append(_finding(
                "C13", "except 块中只有 pass,应记录日志或重新抛出",
                node.lineno, "HIGH"))
    def _collect_findings(self, code: Any,
                          tree: Any) -> tuple[list[dict], list[dict]]:
        violations: list[dict] = []
        warnings: list[dict] = []
        loop_nodes = []
        func_nodes = []
        replace_chains = []
        aliases = _ScopedCallAliases(tree, code)
        guarded_close_calls = _close_guarded_calls(tree, aliases)
        for node in walk_nodes(tree):
            if isinstance(node, ast.Call):
                self._check_call_injection(node, violations, warnings, aliases)
                self._check_call_quality(
                    node, warnings, replace_chains, guarded_close_calls, aliases)
                continue
            if isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
                self._check_assign_secrets(node, violations)
                continue
            if isinstance(node, ast.ExceptHandler):
                self._check_except_handler(node, violations, warnings)
                continue
            if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
                loop_nodes.append(node)
                continue
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.Lambda)):
                func_nodes.append(node)
        collectibles = _ScanCollectibles(
            loop_nodes=loop_nodes, func_nodes=func_nodes,
            replace_chains=replace_chains, aliases=aliases,
            str_lines=self._multiline_string_lines(tree),
            annotations_evaluated=not module_postpones_annotations(
                tree, require_absolute=True))
        _SECONDARY_RULES.run(code, collectibles, violations, warnings)
        return violations, warnings
    def _ast_scan(self, code: str) -> tuple[list[dict], list[dict]]:
        started = time.time()
        if not isinstance(code, str):
            _write_scan_run("degraded_payload", started, 1, 0)
            return [_finding(
                "SYNTAX",
                "非字符串源码输入(" + type(code).__name__ + ")，物理上不可解析",
                0, rule_type="syntax_error")], []
        tree, violations = _parse_source(code, started)
        if tree is None:
            return violations, []
        violations, warnings = scan_source(code, tree)
        _write_scan_run("ok", started, len(violations), len(warnings))
        return violations, warnings
    def _generate_suggestions(self, violations: list[dict],
                               warnings: list[dict]) -> list[str]:
        suggestions = []
        for v in violations:
            _vtype = v.get("type")
            if _vtype == "syntax_error":
                suggestions.append(
                    self._syntax_suggestion(v.get("message")))
            elif _vtype in _VIOLATION_SUGGESTIONS:
                suggestions.append(_VIOLATION_SUGGESTIONS[_vtype])
        for w in warnings:
            _wtype = w.get("type")
            if _wtype in _WARNING_SUGGESTIONS:
                suggestions.append(_WARNING_SUGGESTIONS[_wtype])
        return list(dict.fromkeys(suggestions))
    @staticmethod
    def _syntax_suggestion(message: Any) -> str:
        text = str(message or "").removeprefix("语法错误: ")
        return f"修复语法错误: {text}" if text else "修复语法错误"
    @staticmethod
    def _calculate_score(violations: list[dict],
                          warnings: list[dict]) -> int:
        violation_penalty = sum(
            20 if item.get("severity") == "CRITICAL" else 10
            for item in violations)
        warning_penalty = sum(
            5 if item.get("severity") == "HIGH" else 2
            for item in warnings)
        return max(0, min(100, 100 - violation_penalty - warning_penalty))
def scan_source(source: str, tree: Any) -> tuple[list[dict], list[dict]]:
    if not isinstance(tree, ast.AST):
        return CodeRuleScanner()._ast_scan(source)
    text = source if isinstance(source, str) else (
        coerce_source_text(source) or "")
    violations, warnings = CodeRuleScanner()._collect_findings(text, tree)
    return _apply_suppressions(text, violations, warnings)

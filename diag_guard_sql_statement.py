from __future__ import annotations  # noqa: I001
import ast
import builtins
import logging
import re
from collections.abc import Iterator
from typing import Any, NamedTuple
from weakref import WeakKeyDictionary
from jwsgj.diag_detectors_registry import register_detector_catalog
from jwsgj.diag_guard_sql_connection import (
    _RD29_FUNCTION_SCOPES,
    _RD29_SELF_BASES,
    _DBConnectResolver,
    _driver_connect_call,
    _make_db_connect_resolver,
    _rd29_assignment_scope,
    _rd29_imported_target,
    _rd29_iter_target_leaves,
    _rd29_unwrap_await,
    _rd31_mapping_items,
    _scope_local_binds,
    _unpack_pairs,
    db_finding,
)
from jwsgj.diag_shared_ast_nodes import dotted_name, iter_pattern_capture_names
from jwsgj.diag_types_defs import (
    FindingRecord,
    finding_scan_exempt,
)
from jwsgj.prevention_scope_facts import walk_nodes
_log = logging.getLogger("jwsgj.diag_guard_sql_statement")
__all__ = [
    "check_RD28",
    "check_RD30",
    "check_RD32",
    "sql_text_channels",
    "static_sql_text",
]
_log.info(
    "diag_guard_sql_statement RD-28/RD-30/RD-32 SQL 语句安全族"
    "（SQL 文本通道 + 拼接注入 + 写事务边界 + ORM 原生 SQL）"
    "已加载: %d 项导出",
    len(__all__),
)
_CONCAT_OPS = (ast.Mod, ast.Add)
def _has_formatted_value(node: ast.JoinedStr) -> bool:
    return any(isinstance(v, ast.FormattedValue) for v in node.values)
def _has_dynamic_item(items) -> bool:
    return any(_sql_has_dynamic_segment(item) for item in items)
def _sql_has_dynamic_segment(node: ast.AST) -> bool:
    if isinstance(node, ast.BinOp) and isinstance(node.op, _CONCAT_OPS):
        return (_sql_has_dynamic_segment(node.left)
                or _sql_has_dynamic_segment(node.right))
    if isinstance(node, ast.JoinedStr):
        return _has_formatted_value(node)
    if isinstance(node, ast.Dict):
        return _has_dynamic_item(node.values)
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return _has_dynamic_item(node.elts)
    return not isinstance(node, ast.Constant)
def _sql_unwrap_text_arg(arg: ast.AST) -> ast.AST:
    while (isinstance(arg, ast.Call)
            and ((isinstance(arg.func, ast.Name) and arg.func.id == "text")
                 or (isinstance(arg.func, ast.Attribute)
                     and arg.func.attr == "text"))):
        channels = sql_text_channels(arg)
        if not channels:
            break
        arg = channels[0]
    return arg
def _format_call_dynamic(expr: ast.Call) -> bool | None:
    if not (isinstance(expr.func, ast.Attribute) and expr.func.attr == "format"):
        return None
    if any(_sql_has_dynamic_segment(arg)
           for arg in (*expr.args, *(kw.value for kw in expr.keywords))):
        return True
    receiver = expr.func.value
    if isinstance(receiver, ast.JoinedStr):
        return _has_formatted_value(receiver)
    if isinstance(receiver, ast.BinOp) and isinstance(receiver.op, _CONCAT_OPS):
        return _sql_has_dynamic_segment(receiver)
    if isinstance(receiver, ast.Call):
        return _format_call_dynamic(receiver) is True
    return False
def static_sql_text(node: ast.AST, call_text=None, name_text=None) -> str:
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    if isinstance(node, ast.JoinedStr):
        return " ".join(v.value for v in node.values
                        if isinstance(v, ast.Constant) and isinstance(v.value, str))
    if isinstance(node, ast.BinOp) and isinstance(node.op, _CONCAT_OPS):
        return (static_sql_text(node.left, call_text, name_text) + " "
                + static_sql_text(node.right, call_text, name_text))
    if name_text is not None and isinstance(node, (ast.Name, ast.Attribute)):
        return name_text(node)
    if call_text is not None and isinstance(node, ast.Call):
        return call_text(node)
    return ""
_RD28_SQL_TEXT_KWARGS = frozenset({"sql", "query", "statement", "stmt", "text"})
def _iter_unpacked_kwargs(kw: ast.keyword) -> Iterator[ast.keyword]:
    if kw.arg is not None:
        return
    for key_node, value_node in _rd31_mapping_items(kw.value):
        if (isinstance(key_node, ast.Constant)
                and isinstance(key_node.value, str)):
            yield ast.keyword(arg=key_node.value, value=value_node)
def _unpacked_kwarg_values(call: ast.Call, names: frozenset[str],
                          *, exclude: bool = False) -> list[ast.AST]:
    values: list[ast.AST] = []
    for kw in call.keywords:
        for unpacked in _iter_unpacked_kwargs(kw):
            hit = (unpacked.arg not in names if exclude
                   else unpacked.arg in names)
            if hit:
                values.append(unpacked.value)
    return values
def sql_text_channels(call: ast.Call) -> list[ast.AST]:
    return [*call.args[:1],
            *(kw.value for kw in call.keywords
              if kw.arg is not None and kw.arg in _RD28_SQL_TEXT_KWARGS),
            *_unpacked_kwarg_values(call, _RD28_SQL_TEXT_KWARGS)]
_RD28_SQL_EXEC_METHODS = frozenset({
    "execute", "executemany", "executescript", "text",
    "read_sql", "read_sql_query",
})
def _joinedstr_risk(expr: ast.JoinedStr, detail: str) -> tuple[bool, str]:
    return (True, detail) if _has_formatted_value(expr) else (False, "")
def _format_call_risk(expr: ast.Call, detail: str) -> tuple[bool, str]:
    return (True, detail) if _format_call_dynamic(expr) is True else (False, "")
def _rd28_binop_risk(expr: ast.BinOp) -> tuple[bool, str]:
    if not _sql_has_dynamic_segment(expr):
        return False, ""
    return True, ("%格式化SQL拼接" if isinstance(expr.op, ast.Mod)
                  else "+字符串拼接SQL")
_RD28_JOINEDSTR_DETAIL = "f-string SQL拼接"
_RD28_FORMAT_DETAIL = ".format() SQL拼接"
def _rd28_classify_arg_risk(expr: ast.AST) -> tuple[bool, str]:
    if isinstance(expr, ast.JoinedStr):
        return _joinedstr_risk(expr, _RD28_JOINEDSTR_DETAIL)
    if isinstance(expr, ast.BinOp) and isinstance(expr.op, (ast.Mod, ast.Add)):
        return _rd28_binop_risk(expr)
    if isinstance(expr, ast.Call):
        return _format_call_risk(expr, _RD28_FORMAT_DETAIL)
    return False, ""
def _rd28_call_method(node: ast.Call) -> str | None:
    if isinstance(node.func, ast.Attribute):
        return node.func.attr if node.func.attr in _RD28_SQL_EXEC_METHODS else None
    if isinstance(node.func, ast.Name) and node.func.id == "text":
        return "text"
    return None
def _rd28_collect_call_methods(tree: ast.AST) -> list[tuple[ast.Call, str]]:
    call_methods: list[tuple[ast.Call, str]] = []
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        method = _rd28_call_method(node)
        if method is not None:
            call_methods.append((node, method))
    return call_methods
def _rd28_collect_text_container_ids(
        call_methods: list[tuple[ast.Call, str]]) -> set[int]:
    container_ids: set[int] = set()
    for call, _method in call_methods:
        for arg in sql_text_channels(call):
            if _sql_unwrap_text_arg(arg) is not arg:
                container_ids.add(id(arg))
    return container_ids
def _rd28_finding(method: str, detail: str, node: ast.Call,
                  filepath: Any) -> FindingRecord:
    return db_finding(
        "RD-28", "P0", node.lineno, filepath,
        title=f"SQL注入风险: {method}()使用{detail}",
        description=(f"数据库执行方法 {method}() 的参数使用了{detail}, "
                     f"可能导致SQL注入攻击 (OWASP A03:2021)"),
        suggestion=(
            "根因: execute()参数使用f-string/format/%拼接SQL语句, 用户输入直接嵌入SQL, "
            "攻击者可通过注入SQL关键字绕过查询逻辑。\n"
            "修复策略(按优先级):\n"
            "1. 参数化查询(首选): cursor.execute('SELECT * FROM users WHERE name = %s', (name,))\n"
            "   - sqlite3使用?占位符: cursor.execute('... WHERE id = ?', (user_id,))\n"
            "   - PostgreSQL使用%s: cursor.execute('... WHERE id = %s', (user_id,))\n"
            "   - SQLAlchemy使用:text: session.execute(text('... WHERE id = :id'), {'id': uid})\n"
            "2. ORM查询集(推荐): User.objects.filter(name=user_input)\n"
            "3. 白名单表名: if table not in ALLOWED_TABLES: raise ValueError\n"
            "4. 输入转义(最后手段): 使用 psycopg2.sql模块进行标识符转义\n"
            "参考: OWASP A03:2021 / CWE-89 / Bandit B608"
        ),
    )
def _rd28_findings(node: ast.Call, method: str, filepath: Any) -> list[FindingRecord]:
    findings = []
    for arg in sql_text_channels(node):
        is_risky, detail = _rd28_classify_arg_risk(_sql_unwrap_text_arg(arg))
        if is_risky:
            findings.append(_rd28_finding(method, detail, node, filepath))
    return findings
def check_RD28(tree: Any, source_lines: Any, filepath: Any) -> list[FindingRecord]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[FindingRecord] = []
    if tree is None:
        return issues
    call_methods = _rd28_collect_call_methods(tree)
    text_container_ids = _rd28_collect_text_container_ids(call_methods)
    for node, method in call_methods:
        if method == "text" and id(node) in text_container_ids:
            continue
        issues.extend(_rd28_findings(node, method, filepath))
    if issues:
        _log.debug("[RD-28] sql_injection 命中 %d 处: %s", len(issues), filepath)
    return issues
_RD32_RAW_METHODS = frozenset({"raw", "extra", "from_statement", "exec_driver_sql"})
_RD32_BINDING_CHANNEL_KWARGS = frozenset({
    "params", "select_params", "parameters",
    "translations", "using", "execution_options",
})
def _rd32_carrier_exprs(arg: ast.AST) -> list[ast.AST]:
    expr = _sql_unwrap_text_arg(arg)
    if isinstance(expr, (ast.List, ast.Tuple, ast.Set)):
        return [e.value if isinstance(e, ast.Starred) else e
                for e in expr.elts]
    if isinstance(expr, ast.Dict):
        return list(expr.values)
    return [expr]
_RD32_SAFE_NAME_IDS = frozenset({"self", "cls"})
_RD32_JOINEDSTR_DETAIL = "f-string"
_RD32_FORMAT_DETAIL = ".format()"
def _rd32_name_risk(expr: ast.Name | ast.Attribute) -> tuple[bool, str]:
    name = dotted_name(expr) or ""
    if not name or name in _RD32_SAFE_NAME_IDS:
        return False, ""
    return True, f"变量 '{name}'"
def _rd32_binop_risk(expr: ast.BinOp) -> tuple[bool, str]:
    if not _sql_has_dynamic_segment(expr):
        return False, ""
    return True, "字符串拼接"
def _rd32_classify_expr_risk(expr: ast.AST) -> tuple[bool, str]:
    if isinstance(expr, ast.JoinedStr):
        return _joinedstr_risk(expr, _RD32_JOINEDSTR_DETAIL)
    if isinstance(expr, (ast.Name, ast.Attribute)):
        return _rd32_name_risk(expr)
    if isinstance(expr, ast.BinOp):
        return _rd32_binop_risk(expr)
    if isinstance(expr, ast.Call) and isinstance(expr.func, ast.Attribute):
        return _format_call_risk(expr, _RD32_FORMAT_DETAIL)
    return False, ""
def _rd32_finding(method: str, detail: str, node: ast.Call,
                  filepath: Any) -> FindingRecord:
    return db_finding(
        "RD-32", "P1", node.lineno, filepath,
        title=f"ORM raw SQL注入风险: {method}()使用{detail}",
        description=(f"ORM方法 {method}() 使用了{detail}, "
                     f"如果输入来自用户则可能导致SQL注入"),
        suggestion=(
            "根因: ORM的raw()/extra()/from_statement()方法接受原始SQL, "
            "参数为f-string/变量时用户输入直接嵌入SQL, 绕过ORM的安全机制。\n"
            "修复策略(按优先级):\n"
            "1. ORM查询集(首选):\n"
            "   User.objects.filter(name=user_input)  # Django\n"
            "   session.query(User).filter(User.name == user_input)  # SQLAlchemy\n"
            "2. 参数化raw(如必须用raw):\n"
            "   User.objects.raw('SELECT * FROM users WHERE name = %s', [user_input])\n"
            "3. SQLAlchemy text()绑定参数:\n"
            "   session.execute(text('SELECT * FROM users WHERE name = :name'), "
            "{'name': user_input})\n"
            "4. 白名单校验: 对表名/列名等动态标识符使用白名单\n"
            "   if table_name not in ALLOWED_TABLES: raise ValueError\n"
            "5. 避免extra(): Django的extra()已弃用, 使用annotate()/aggregate()替代\n"
            "参考: OWASP A03:2021 / CWE-89 / Django Security"
        ),
    )
def _rd32_carrier_kwargs(node: ast.Call) -> list[ast.AST]:
    values = [kw.value for kw in node.keywords
              if kw.arg is not None
              and kw.arg not in _RD32_BINDING_CHANNEL_KWARGS]
    values.extend(_unpacked_kwarg_values(
        node, _RD32_BINDING_CHANNEL_KWARGS, exclude=True))
    return values
def _rd32_findings(node: ast.Call, method: str, filepath: Any) -> list[FindingRecord]:
    findings = []
    for arg in (*node.args[:1], *_rd32_carrier_kwargs(node)):
        for expr in _rd32_carrier_exprs(arg):
            is_risky, detail = _rd32_classify_expr_risk(expr)
            if is_risky:
                findings.append(_rd32_finding(method, detail, node, filepath))
    return findings
def _rd32_iter_raw_calls(tree: ast.AST) -> Iterator[tuple[ast.Call, str]]:
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Attribute):
            continue
        if node.func.attr in _RD32_RAW_METHODS:
            yield node, node.func.attr
def check_RD32(tree: Any, source_lines: Any, filepath: Any) -> list[FindingRecord]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[FindingRecord] = []
    if tree is None:
        return issues
    for node, method in _rd32_iter_raw_calls(tree):
        issues.extend(_rd32_findings(node, method, filepath))
    if issues:
        _log.debug("[RD-32] orm_raw_injection 命中 %d 处: %s", len(issues), filepath)
    return issues
_RD30_WRITE_KW_RES = (
    *(re.compile(r"\b" + kw + r"\b") for kw in
      ("INSERT", "UPDATE", "DELETE", "CREATE", "DROP", "ALTER", "TRUNCATE")),
    re.compile(r"\bREPLACE\s+INTO\b"),
    re.compile(r"\bMERGE\s+INTO\b"),
)
_RD30_QUOTE_CHARS = frozenset({"'", '"', "`"})
_RD30_DOLLAR_TAG_RE = re.compile(r"\$([A-Za-z_][A-Za-z0-9_]*)?\$")
_RD30_EXEC_METHODS = frozenset(
    {"execute", "executemany", "executescript", "exec_driver_sql"})
def _rd30_static_sql_text(node: ast.AST, sql_names: dict[str, str]) -> str:
    return static_sql_text(
        node,
        lambda child: _rd30_static_sql_from_call(child, sql_names),
        lambda child: sql_names.get(dotted_name(child) or "", ""),
    )
def _rd30_static_sql_from_call(
        node: ast.Call, sql_names: dict[str, str],
) -> str:
    unwrapped = _sql_unwrap_text_arg(node)
    if unwrapped is not node:
        return _rd30_static_sql_text(unwrapped, sql_names)
    if (isinstance(node.func, ast.Attribute)
            and node.func.attr == "format"):
        return _rd30_static_sql_text(node.func.value, sql_names)
    return ""
def _rd30_call_is_write(call_node: ast.Call, call_attr: str,
                        sql_names: dict[str, str]) -> bool:
    if call_attr not in _RD30_EXEC_METHODS:
        return False
    return any(_rd30_text_is_write(_rd30_static_sql_text(arg, sql_names))
               for arg in sql_text_channels(call_node))
def _rd30_skip_quoted(sql: str, start: int, quote: str) -> int:
    pos = start + 1
    while pos < len(sql):
        ch = sql[pos]
        if ch == "\\" and quote != "`":
            pos += 2
            continue
        if ch == quote:
            if pos + 1 < len(sql) and sql[pos + 1] == quote:
                pos += 2
                continue
            return pos + 1
        pos += 1
    return pos
def _rd30_dollar_quote_end(sql: str, start: int) -> int | None:
    match = _RD30_DOLLAR_TAG_RE.match(sql, start)
    if match is None:
        return None
    tag = match.group(0)
    end = sql.find(tag, match.end())
    return len(sql) if end < 0 else end + len(tag)
def _rd30_sql_without_noise(sql: str) -> str:
    out: list[str] = []
    pos = 0
    while pos < len(sql):
        ch = sql[pos]
        if ch in _RD30_QUOTE_CHARS:
            pos = _rd30_skip_quoted(sql, pos, ch)
            out.append(" ")
            continue
        if ch == "[":
            pos += 1
            while pos < len(sql):
                if sql[pos] != "]":
                    pos += 1
                    continue
                if pos + 1 < len(sql) and sql[pos + 1] == "]":
                    pos += 2
                    continue
                pos += 1
                break
            out.append(" ")
            continue
        if ch == "$":
            dollar_end = _rd30_dollar_quote_end(sql, pos)
            if dollar_end is not None:
                pos = dollar_end
                out.append(" ")
                continue
        if ch == "#" or (ch == "-" and pos + 1 < len(sql) and sql[pos + 1] == "-"):
            end = sql.find("\n", pos + 1)
            pos = len(sql) if end < 0 else end + 1
            out.append(" ")
            continue
        if ch == "/" and pos + 1 < len(sql) and sql[pos + 1] == "*":
            end = sql.find("*/", pos + 2)
            pos = len(sql) if end < 0 else end + 2
            out.append(" ")
            continue
        out.append(ch)
        pos += 1
    return "".join(out)
_RD30_ROW_LOCK_RE = re.compile(
    r"\bFOR\s+(?:NO\s+KEY\s+)?UPDATE\b"
    r"|\bFOR\s+(?:KEY\s+)?SHARE\b")
def _rd30_text_is_write(sql_text: str) -> bool:
    if not sql_text:
        return False
    structured = _RD30_ROW_LOCK_RE.sub(
        " ", _rd30_sql_without_noise(sql_text).upper())
    return any(pattern.search(structured) for pattern in _RD30_WRITE_KW_RES)
_RD30_AUTO_TX_ATTRS = frozenset({"begin"})
# DB-API 驱动中「``with connection:`` 退出时自动提交/回滚事务」的关系型模块名册。
# RD-30 把这些模块 ``connect()`` 产生的连接视为事务资源：``with`` 托管期间经该
# 连接（含 ``conn.cursor()`` 派生游标与 ``as`` 绑定变量）发出的写操作视为已闭合；
# 不在 ``with``/commit/rollback 之内的写操作仍照报。名册与
# ``diag_guard_sql_connection._RD29_DB_DRIVER_MODULES`` 中的关系型 DB-API 驱动对齐，
# redis/mongo/duckdb 等非事务型或默认自动提交型驱动不纳入。
_RD30_AUTO_TX_CONNECT_MODULES = frozenset({
    "sqlite3", "aiosqlite",
    "psycopg2", "psycopg", "psycopg2cffi",
    "pymysql", "MySQLdb", "aiomysql", "asyncmy",
    "pyodbc", "pymssql", "cx_Oracle", "oracledb",
})
def _rd30_is_cursor_expr(node: ast.AST | None, cursor_names) -> bool:
    if (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "cursor"):
        return True
    return node is not None and (dotted_name(node) or "") in cursor_names
def _rd30_is_auto_tx_expr(node: ast.AST, auto_names: set[str],
                          resolver: _DBConnectResolver,
                          cursor_names=None) -> bool:
    if _rd30_is_cursor_expr(node, cursor_names or ()):
        return False
    if isinstance(node, ast.Name):
        return node.id in auto_names
    if not isinstance(node, ast.Call):
        return False
    if (isinstance(node.func, ast.Attribute)
            and node.func.attr in _RD30_AUTO_TX_ATTRS):
        return True
    return _driver_connect_call(node, resolver)
_RD30_DJANGO_ATOMIC_TARGET = ("django.db.transaction", "atomic")
def _rd30_is_django_atomic(
        node: ast.AST, resolver: _DBConnectResolver,
) -> bool:
    if not isinstance(node, (ast.Call, ast.Name, ast.Attribute)):
        return False
    return _rd29_imported_target(
        node, resolver.import_sources, resolver.index,
    ) == _RD30_DJANGO_ATOMIC_TARGET
def _rd30_sql_receivers(body) -> set[str]:
    receivers: set[str] = set()
    for stmt in body:
        for node in walk_nodes(stmt):
            if not isinstance(node, ast.Call) or not isinstance(
                    node.func, ast.Attribute):
                continue
            if node.func.attr not in _RD30_EXEC_METHODS:
                continue
            name = dotted_name(node.func.value)
            if name:
                receivers.add(name)
    return receivers
def _rd30_is_tx_context_item(
        node: ast.AST, receivers: set[str], optional_vars: ast.AST | None,
        cursor_names=None,
) -> bool:
    if _rd30_is_cursor_expr(node, cursor_names or ()):
        return False
    name = dotted_name(node)
    if not name:
        return False
    if name in receivers:
        return True
    return optional_vars is not None and any(
        alias in receivers for alias in _rd30_target_names(optional_vars))
_RD30_NESTED_SCOPE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda, ast.ClassDef)
def _rd30_target_names(target: ast.AST) -> Iterator[str]:
    for leaf in _rd29_iter_target_leaves(target):
        name = dotted_name(leaf)
        if name:
            yield name
def _rd30_bind_conn_names(target: ast.AST, value: ast.AST | None,
                          names: set[str], autocommit_names: set[str],
                          resolver: _DBConnectResolver) -> None:
    if not _driver_connect_call(value, resolver):
        return
    bound = set(_rd30_target_names(target))
    names.update(bound)
    if _rd30_is_autocommit_call(value):
        autocommit_names.update(bound)
def _rd30_bound_pairs(node: ast.AST) -> list[tuple[ast.AST, ast.AST | None]]:
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return [(item.optional_vars, item.context_expr) for item in node.items
                if item.optional_vars is not None]
    value = _rd29_unwrap_await(node.value)
    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
    pairs: list[tuple[ast.AST, ast.AST | None]] = []
    for target in targets:
        unpacked = _unpack_pairs(target, value)
        if unpacked:
            pairs.extend((sub_target, _rd29_unwrap_await(sub_value))
                         for sub_target, sub_value in unpacked)
        else:
            pairs.append((target, value))
    return pairs
def _rd30_autocommit_kwarg(kw: ast.keyword) -> bool | None:
    if kw.arg is None:
        for unpacked in _iter_unpacked_kwargs(kw):
            if _rd30_autocommit_kwarg(unpacked) is True:
                return True
        return None
    if kw.arg == "autocommit":
        return isinstance(kw.value, ast.Constant) and bool(kw.value.value)
    if kw.arg == "isolation_level":
        return isinstance(kw.value, ast.Constant) and kw.value.value is None
    return None
def _rd30_is_autocommit_call(node: ast.AST) -> bool:
    if not isinstance(node, ast.Call):
        return False
    return any(_rd30_autocommit_kwarg(kw) is True for kw in node.keywords)


def _rd30_autocommit_attr_update(
        target: ast.AST, value: ast.AST | None,
        bindings: dict[str, str],
) -> tuple[str, bool | None] | None:
    base, separator, attr = (dotted_name(target) or "").rpartition(".")
    if not separator or attr not in {"autocommit", "isolation_level"}:
        return None
    channel = _rd30_expression_channel(base, bindings)
    if not isinstance(value, ast.Constant):
        enabled = None
    elif attr == "autocommit":
        enabled = bool(value.value)
    else:
        enabled = value.value is None
    return channel, enabled
class _RD30NameIndex(NamedTuple):
    bound: dict[int, set[str]]
    autocommit: dict[int, set[str]]
    class_cache: dict[int, tuple[set[str], set[str]]]
    sql_assignments: dict[
        int, list[list[tuple[ast.AST, ast.AST | None]]]]
    sql_cache: dict[int, dict[str, str]]
    cursor_cache: dict[int, frozenset[str]]
def _rd30_bound_name_index(
        tree: ast.AST, resolver: _DBConnectResolver,
) -> _RD30NameIndex:
    all_names: dict[int, set[str]] = {}
    auto_names: dict[int, set[str]] = {}
    sql_assignments: dict[
        int, list[list[tuple[ast.AST, ast.AST | None]]]] = {}
    index = resolver.index
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr,
                                 ast.With, ast.AsyncWith)):
            continue
        scope = _rd29_assignment_scope(node, index)
        found: set[str] = set()
        found_auto: set[str] = set()
        pairs = _rd30_bound_pairs(node)
        for target, value in pairs:
            _rd30_bind_conn_names(
                target, value, found, found_auto, resolver)
        if isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
            sql_assignments.setdefault(id(scope), []).append(pairs)
        if found:
            all_names.setdefault(id(scope), set()).update(found)
        if found_auto:
            auto_names.setdefault(id(scope), set()).update(found_auto)
    return _RD30NameIndex(
        all_names, auto_names, {}, sql_assignments, {}, {})
def _rd30_iter_class_scope_nodes(cls_node: ast.ClassDef) -> Iterator[ast.AST]:
    stack: list[ast.AST] = list(cls_node.body)
    while stack:
        node = stack.pop()
        if isinstance(node, ast.ClassDef):
            continue
        yield node
        stack.extend(ast.iter_child_nodes(node))
def _rd30_class_attr_conn_names(
        cls_node: ast.ClassDef, resolver: _DBConnectResolver,
        name_index: _RD30NameIndex,
) -> tuple[set[str], set[str]]:
    if id(cls_node) in name_index.class_cache:
        return name_index.class_cache[id(cls_node)]
    names: set[str] = set()
    auto_names: set[str] = set()
    for node in _rd30_iter_class_scope_nodes(cls_node):
        if not isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
            continue
        value = _rd29_unwrap_await(node.value)
        if not _driver_connect_call(value, resolver):
            continue
        targets = node.targets if isinstance(node, ast.Assign) else [node.target]
        for target in targets:
            bound = {name for name in _rd30_target_names(target)
                     if name.split(".", 1)[0] in _RD29_SELF_BASES}
            names.update(bound)
            if _rd30_is_autocommit_call(value):
                auto_names.update(bound)
    result = (names, auto_names)
    name_index.class_cache[id(cls_node)] = result
    return result
def _rd30_visible_conn_names(
        scope: ast.AST, resolver: _DBConnectResolver,
        name_index: _RD30NameIndex,
) -> tuple[set[str], set[str]]:
    root = resolver.index.tree
    parent = resolver.index.parent
    visible = set(name_index.bound.get(id(scope), ()))
    visible_auto = set(name_index.autocommit.get(id(scope), ()))
    shadowed = _scope_local_binds(scope) if scope is not root else set()
    class_merged = isinstance(scope, ast.ClassDef)
    cur = parent.get(id(scope))
    while cur is not None:
        if isinstance(cur, ast.Module):
            visible |= name_index.bound.get(id(cur), set()) - shadowed
            visible_auto |= name_index.autocommit.get(id(cur), set()) - shadowed
            break
        if isinstance(cur, ast.ClassDef):
            if not class_merged:
                class_names, class_auto = _rd30_class_attr_conn_names(
                    cur, resolver, name_index)
                visible |= class_names - shadowed
                visible_auto |= class_auto - shadowed
                class_merged = True
        elif isinstance(cur, _RD29_FUNCTION_SCOPES):
            visible |= name_index.bound.get(id(cur), set()) - shadowed
            visible_auto |= name_index.autocommit.get(id(cur), set()) - shadowed
            shadowed |= _scope_local_binds(cur)
        cur = parent.get(id(cur))
    return visible, visible_auto
def _rd30_visible_sql_text(
        scope: ast.AST, resolver: _DBConnectResolver,
        name_index: _RD30NameIndex,
) -> dict[str, str]:
    root = resolver.index.tree
    if scope is root:
        return {}
    visible: dict[str, str] = {}
    shadowed = _scope_local_binds(scope)
    class_merged = isinstance(scope, ast.ClassDef)
    cur = resolver.index.parent.get(id(scope))
    while cur is not None:
        if isinstance(cur, ast.Module):
            inherited = _rd30_scope_sql_text(cur, resolver, name_index)
            visible.update((name, text) for name, text in inherited.items()
                           if name not in shadowed)
            break
        if isinstance(cur, _RD29_FUNCTION_SCOPES):
            inherited = _rd30_scope_sql_text(cur, resolver, name_index)
            visible.update((name, text) for name, text in inherited.items()
                           if name not in shadowed)
            shadowed |= _scope_local_binds(cur)
        elif isinstance(cur, ast.ClassDef) and not class_merged:
            inherited = _rd30_scope_sql_text(cur, resolver, name_index)
            for name, text in inherited.items():
                if "." in name:
                    continue
                for base in ("self", "cls"):
                    attr = f"{base}.{name}"
                    if attr not in shadowed:
                        visible[attr] = text
            class_merged = True
        cur = resolver.index.parent.get(id(cur))
    return visible
def _rd30_scope_sql_text(
        scope: ast.AST, resolver: _DBConnectResolver,
        name_index: _RD30NameIndex,
) -> dict[str, str]:
    cached = name_index.sql_cache.get(id(scope))
    if cached is not None:
        return cached
    available = _rd30_visible_sql_text(scope, resolver, name_index)
    if not isinstance(scope, ast.Module):
        for name in _scope_local_binds(scope):
            available.pop(name, None)
    local: dict[str, str] = {}
    assignment_groups = sorted(
        name_index.sql_assignments.get(id(scope), ()),
        key=lambda group: (getattr(group[0][0], "lineno", 0),
                           getattr(group[0][0], "col_offset", 0)))
    for group in assignment_groups:
        before = available.copy()
        prepared = []
        for target, value in group:
            unwrapped = _rd29_unwrap_await(value)
            if unwrapped is None:
                continue
            text = _rd30_static_sql_text(unwrapped, before)
            prepared.append((target, text))
        for target, text in prepared:
            for name in _rd30_target_names(target):
                local.pop(name, None)
                available.pop(name, None)
                if text:
                    local[name] = text
                    available[name] = text
    name_index.sql_cache[id(scope)] = local
    return local
def _rd30_visible_cursor_names(
        scope: ast.AST, resolver: _DBConnectResolver,
        name_index: _RD30NameIndex,
) -> set[str]:
    visible: set[str] = set()
    shadowed = _scope_local_binds(scope)
    class_merged = isinstance(scope, ast.ClassDef)
    cur = resolver.index.parent.get(id(scope))
    while cur is not None:
        if isinstance(cur, (ast.Module, *_RD29_FUNCTION_SCOPES)):
            inherited = _rd30_scope_cursor_names(cur, resolver, name_index)
            visible |= inherited - shadowed
            if isinstance(cur, ast.Module):
                break
            shadowed |= _scope_local_binds(cur)
        elif isinstance(cur, ast.ClassDef) and not class_merged:
            inherited = _rd30_scope_cursor_names(cur, resolver, name_index)
            for name in inherited:
                if "." in name:
                    if name not in shadowed:
                        visible.add(name)
                    continue
                for base in ("self", "cls"):
                    attr = f"{base}.{name}"
                    if attr not in shadowed:
                        visible.add(attr)
            class_merged = True
        cur = resolver.index.parent.get(id(cur))
    return visible
def _rd30_scope_cursor_names(
        scope: ast.AST, resolver: _DBConnectResolver,
        name_index: _RD30NameIndex,
) -> frozenset[str]:
    cached = name_index.cursor_cache.get(id(scope))
    if cached is not None:
        return cached
    available = _rd30_visible_cursor_names(scope, resolver, name_index)
    if not isinstance(scope, ast.Module):
        available.difference_update(_scope_local_binds(scope))
    local: set[str] = set()
    assignment_groups = sorted(
        name_index.sql_assignments.get(id(scope), ()),
        key=lambda group: (getattr(group[0][0], "lineno", 0),
                           getattr(group[0][0], "col_offset", 0)))
    for group in assignment_groups:
        before = available.copy()
        prepared = []
        for target, value in group:
            unwrapped = _rd29_unwrap_await(value)
            prepared.append((target, _rd30_is_cursor_expr(unwrapped, before)))
        for target, is_cursor in prepared:
            for name in _rd30_target_names(target):
                local.discard(name)
                available.discard(name)
                if is_cursor:
                    local.add(name)
                    available.add(name)
    result = frozenset(local)
    name_index.cursor_cache[id(scope)] = result
    return result
_RD30_COMMIT_ATTRS = frozenset({"commit", "rollback"})
_RD30_EMPTY_NAMES: frozenset[str] = frozenset()
_RD30_RAISE_CONTROL_PREFIX = "raise:"
_RD30_IMPLICIT_RAISE_CONTROL = f"{_RD30_RAISE_CONTROL_PREFIX}<implicit>"
# 流分析的状态空间上界：每个分支点都会让状态数相乘，深嵌套 try/if 会指数爆炸；
# 循环不动点又要求状态集合收敛。两者都必须有硬上限，否则单文件即可挂死整个诊断。
_RD30_MAX_FLOW_STATES = 24
_RD30_MAX_LOOP_ITERATIONS = 8
# 单个 scope 的求值次数预算：状态数有界仍不等于总工作量有界（每层子节点都要
# 拿全部状态重算一遍），深嵌套 + 多分支叠加后仍是超线性。超出后停止推进状态。
_RD30_EVAL_BUDGET = 200_000
def _rd30_call_attr(node: ast.AST) -> str:
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
        return node.func.attr
    return ""
class _RD30FlowState(NamedTuple):
    pending: tuple[tuple[str, int, int], ...] = ()
    reachable: bool = True
    bindings: tuple[tuple[str, str], ...] = ()
    sql_text: tuple[tuple[str, str], ...] = ()
    autocommit: frozenset[str] = _RD30_EMPTY_NAMES
    control: str = ""
    exception_stack: tuple[str, ...] = ()
    cursors: frozenset[str] = _RD30_EMPTY_NAMES
def _rd30_exception_name(node: ast.AST | None) -> str:
    expr = node.func if isinstance(node, ast.Call) else node
    return dotted_name(expr) or "" if expr is not None else ""
def _rd30_raise_control(node: ast.Raise) -> str:
    return _RD30_RAISE_CONTROL_PREFIX + _rd30_exception_name(node.exc)
def _rd30_is_raise_control(control: str) -> bool:
    return control.startswith(_RD30_RAISE_CONTROL_PREFIX)
def _rd30_handler_raise_control(handler: ast.ExceptHandler) -> str:
    name = dotted_name(handler.type) if handler.type is not None else ""
    return _RD30_RAISE_CONTROL_PREFIX + (name or "")
#: ``_rd30_exception_definitions`` 的树级缓存。
#:
#: 该函数是树的纯函数（只做一次 ``ast.walk`` 收集类定义），却被
#: ``_RD30FlowAnalyzer.__init__`` 按作用域调用 **237 次**，实测单文件 13.84 s
#: （占整文件检测 11%）——237 次全量遍历只为了得到同一份「类名 → 类定义」表。
#:
#: 用弱引用字典保证不阻止 AST 回收（与 ``build_parent_map`` 同一约定）；
#: 返回的字典只读共享，调用方**不得原地修改**。
_RD30_DEFS_CACHE: WeakKeyDictionary[Any, dict[str, list[ast.ClassDef]]] = (
    WeakKeyDictionary())
_RD30_DEFS_CACHE_MAX = 256


def release_rd30_caches() -> dict[str, int]:
    """清空 RD30 的树级派生缓存（跨文件不可能命中，只钉内存）。"""
    try:
        n = len(_RD30_DEFS_CACHE)
        _RD30_DEFS_CACHE.clear()
        return {"rd30_defs": n}
    except Exception:
        return {"rd30_defs": -1}


def _rd30_exception_definitions(tree: ast.AST) -> dict[str, list[ast.ClassDef]]:
    if tree is None:
        return {}
    try:
        cached = _RD30_DEFS_CACHE.get(tree)
    except TypeError:  # 非弱引用可缓存对象，退回无缓存计算
        cached = None
    if cached is not None:
        return cached
    definitions: dict[str, list[ast.ClassDef]] = {}
    for node in walk_nodes(tree):
        if isinstance(node, ast.ClassDef):
            definitions.setdefault(node.name, []).append(node)
    try:
        _RD30_DEFS_CACHE[tree] = definitions
        while len(_RD30_DEFS_CACHE) > _RD30_DEFS_CACHE_MAX:
            del _RD30_DEFS_CACHE[next(iter(_RD30_DEFS_CACHE))]
    except TypeError:
        pass
    return definitions
def _rd30_builtin_type(name: str) -> type | None:
    if not name or ("." in name and not name.startswith("builtins.")):
        return None
    value = getattr(builtins, name.rsplit(".", 1)[-1], None)
    return value if isinstance(value, type) else None

def _rd30_class_def_subclass(
        cls: ast.ClassDef, handler_name: str, definitions: dict,
        seen: frozenset[int]) -> bool | None:
    if id(cls) in seen:
        return None
    seen = seen | {id(cls)}
    unknown = False
    for base in cls.bases:
        base_name = dotted_name(base) or ""
        base_short = base_name.rsplit(".", 1)[-1]
        if not base_short:
            unknown = True
            continue
        if base_name == handler_name:
            return True
        base_type = _rd30_builtin_type(base_name)
        handler_type = _rd30_builtin_type(handler_name)
        if isinstance(base_type, type):
            if (isinstance(handler_type, type)
                    and issubclass(base_type, handler_type)):
                return True
            continue
        nested = definitions.get(base_short, ()) if "." not in base_name else ()
        if not nested:
            unknown = True
            continue
        verdicts = [_rd30_class_def_subclass(
            nested_cls, handler_name, definitions, seen)
                    for nested_cls in nested]
        if any(verdict is True for verdict in verdicts):
            return True
        if any(verdict is None for verdict in verdicts):
            unknown = True
    return None if unknown else False
def _rd30_local_exception_subclass(
        raised_name: str, handler_name: str, definitions: dict | None,
) -> bool | None:
    if (not definitions or not raised_name or not handler_name
            or "." in raised_name or "." in handler_name):
        return None
    classes = definitions.get(raised_name, ())
    if not classes:
        return None
    verdicts = [_rd30_class_def_subclass(
        cls, handler_name, definitions, frozenset()) for cls in classes]
    if all(verdict is True for verdict in verdicts):
        return True
    if all(verdict is False for verdict in verdicts):
        return False
    return None
def _rd30_raise_is_handled(
        control: str, handlers, class_defs: dict | None = None) -> bool:
    raised_name = control[len(_RD30_RAISE_CONTROL_PREFIX):]
    raised_type = _rd30_builtin_type(raised_name)
    for handler in handlers:
        if handler.type is None:
            return True
        candidates = (handler.type.elts if isinstance(handler.type, ast.Tuple)
                      else (handler.type,))
        for candidate in candidates:
            handler_name = dotted_name(candidate) or ""
            if _rd30_builtin_type(handler_name) is BaseException:
                return True
            if raised_name and raised_name == handler_name:
                return True
            handler_type = _rd30_builtin_type(handler_name)
            if (isinstance(raised_type, type) and isinstance(handler_type, type)
                    and issubclass(raised_type, BaseException)
                    and issubclass(handler_type, BaseException)):
                if issubclass(raised_type, handler_type):
                    return True
                continue
            local_verdict = _rd30_local_exception_subclass(
                raised_name, handler_name, class_defs)
            if local_verdict is True:
                return True
            if local_verdict is False:
                continue
            if (handler_name in {"Exception", "builtins.Exception"}
                    and raised_name):
                return True
    return False
def _rd30_collapse_flow_states(
        groups: dict[tuple, set[tuple[str, int, int]]],
) -> tuple[_RD30FlowState, ...]:
    """状态数超限时的保守折叠：把全部状态并成一条，优先保住 pending。

    RD-30 的产物是「未提交事务点」清单，折叠口径必须保证不漏报：
    pending 取并集；autocommit 取交集（交集更小，即更少 channel 被视为已提交，
    pending 因此更容易保留）；reachable 取 any；bindings/sql_text 保留信息量最大的一组。
    折到单条后下一轮必然不再超限，因此不会反复折叠。
    """
    pending: set[tuple[str, int, int]] = set()
    autocommit: frozenset[str] | None = None
    reachable = False
    bindings: tuple[tuple[str, str], ...] = ()
    sql_text: tuple[tuple[str, str], ...] = ()
    control = ""
    exception_stack: tuple[str, ...] = ()
    cursor_names: set[str] = set()
    for key, points in groups.items():
        pending |= points
        (key_reachable, key_bindings, key_sql, key_auto, key_control,
         key_exc, key_cursors) = key
        reachable = reachable or bool(key_reachable)
        if len(key_bindings) > len(bindings):
            bindings = key_bindings
        if len(key_sql) > len(sql_text):
            sql_text = key_sql
        auto_set = frozenset(key_auto)
        autocommit = auto_set if autocommit is None else (autocommit & auto_set)
        control = control or key_control
        if len(key_exc) > len(exception_stack):
            exception_stack = key_exc
        cursor_names.update(key_cursors)
    if autocommit is None:
        autocommit = _RD30_EMPTY_NAMES
    return (_RD30FlowState(
        pending=tuple(sorted(pending)), reachable=reachable,
        bindings=bindings, sql_text=sql_text, autocommit=autocommit,
        control=control, exception_stack=exception_stack,
        cursors=frozenset(cursor_names)),)

def _rd30_merge_flow_states(states) -> tuple[_RD30FlowState, ...]:
    """按去重口径合并流状态。

    符号执行每处理一条语句都会调用本函数，实测 435K 次里绝大多数只有
    0～1 个状态；``_RD30FlowState`` 的 ``pending`` 在构造时已 ``sorted``
    去重，单状态直接返回即可省掉分组、排序与重建。
    """
    if not isinstance(states, (list, tuple)):
        states = tuple(states)
    if len(states) <= 1:
        if not states:
            return ()
        state = states[0]
        # 0/1 个 pending 点时 ``tuple(sorted(set(...)))`` 是恒等变换（空元组
        # 与单元素元组去重排序后仍是自身），直接返回原对象，省掉每次合并的
        # set/sorted 构造与 NamedTuple 重建。符号执行每处理一条语句都会调用
        # 本函数，实测 43 万次里绝大多数命中这个分支。
        if len(state.pending) <= 1:
            return (state,)
        return (_RD30FlowState(
            pending=tuple(sorted(set(state.pending))),
            reachable=state.reachable, bindings=state.bindings,
            sql_text=state.sql_text, autocommit=state.autocommit,
            control=state.control,
            exception_stack=state.exception_stack, cursors=state.cursors),)
    groups: dict[tuple, set[tuple[str, int, int]]] = {}
    for state in states:
        key = (state.reachable, state.bindings, state.sql_text,
               tuple(sorted(state.autocommit)), state.control,
               state.exception_stack, tuple(sorted(state.cursors)))
        groups.setdefault(key, set()).update(state.pending)
    if len(groups) > _RD30_MAX_FLOW_STATES:
        _log.debug(
            "[RD-30] 流状态数 %d 超过上限 %d，按保守口径折叠（pending 取并集）",
            len(groups), _RD30_MAX_FLOW_STATES)
        return _rd30_collapse_flow_states(groups)
    return tuple(
        _RD30FlowState(
            pending=tuple(sorted(groups[key])), reachable=key[0],
            bindings=key[1], sql_text=key[2],
            autocommit=frozenset(key[3]), control=key[4],
            exception_stack=key[5], cursors=frozenset(key[6]))
        for key in sorted(
            groups,
            key=lambda item: (
                not item[0], item[1], item[2], item[3], item[4], item[5],
                item[6])))
_RD30_DRIVER_RESOURCE_PREFIX = "db:"
_RD30_SESSION_RESOURCE_PREFIX = "session:"
_RD30_SESSION_FACTORY_PREFIX = "session-factory:"
def _rd30_resource_id(node: ast.AST) -> str:
    return f"{_RD30_DRIVER_RESOURCE_PREFIX}{node.lineno}:{node.col_offset}"
def _rd30_sqlalchemy_session_channel(
        node: ast.AST, resolver: _DBConnectResolver,
) -> str:
    if not isinstance(node, ast.Call):
        return ""
    target = _rd29_imported_target(
        node, resolver.import_sources, resolver.index)
    if target is None:
        return ""
    module, attr = target
    if not (module == "sqlalchemy.orm"
            or module.startswith("sqlalchemy.orm.")):
        return ""
    if attr in {"Session", "AsyncSession"}:
        prefix = _RD30_SESSION_RESOURCE_PREFIX
    elif attr in {"sessionmaker", "async_sessionmaker"}:
        prefix = _RD30_SESSION_FACTORY_PREFIX
    else:
        return ""
    return f"{prefix}{node.lineno}:{node.col_offset}"
def _rd30_unknown_resource(node: ast.AST, name: str) -> str:
    line = getattr(node, "lineno", 0)
    column = getattr(node, "col_offset", 0)
    return f"unknown:{line}:{column}:{name}"
_RD30_RESOURCE_BACKREF_ATTRS = frozenset({"connection"})
def _rd30_expression_channel(node: ast.AST | str | None,
                             bindings: dict[str, str]) -> str:
    if node is None:
        return ""
    dotted = node if isinstance(node, str) else dotted_name(node)
    if dotted:
        direct = bindings.get(dotted)
        if direct is not None:
            return direct
        for base, base_channel in sorted(
                bindings.items(), key=lambda item: len(item[0]), reverse=True):
            prefix = f"{base}."
            if not dotted.startswith(prefix):
                continue
            rest = dotted[len(prefix):]
            if rest in _RD30_RESOURCE_BACKREF_ATTRS:
                return base_channel
            return f"{base_channel}.{rest}"
        base, separator, attr = dotted.rpartition(".")
        if separator and attr in _RD30_RESOURCE_BACKREF_ATTRS:
            return base
        return dotted
    if isinstance(node, ast.Call):
        factory = _rd30_expression_channel(node.func, bindings)
        if factory.startswith(_RD30_SESSION_FACTORY_PREFIX):
            return (f"{_RD30_SESSION_RESOURCE_PREFIX}"
                    f"{node.lineno}:{node.col_offset}")
        if (isinstance(node.func, ast.Attribute)
                and (node.func.attr == "cursor"
                     or node.func.attr == "begin"
                     or node.func.attr in _RD30_RESOURCE_BACKREF_ATTRS)):
            return _rd30_expression_channel(node.func.value, bindings)
    return ""
def _rd30_call_channel(call: ast.Call, state: _RD30FlowState) -> str:
    if not isinstance(call.func, ast.Attribute):
        return ""
    return _rd30_expression_channel(call.func.value, dict(state.bindings))
class _RD30FlowAnalyzer:
    def __init__(self, auto_names: set[str], resolver: _DBConnectResolver,
                 autocommit_names: set[str], sql_names: dict[str, str],
                 cursor_names: set[str] | None = None) -> None:
        self.auto_names = auto_names
        self.resolver = resolver
        self.initial_autocommit = frozenset(autocommit_names)
        self.initial_sql_text = tuple(sorted(sql_names.items()))
        self.initial_cursors = frozenset(cursor_names or ())
        self.exception_defs = _rd30_exception_definitions(resolver.index.tree)
        self._eval_budget = _RD30_EVAL_BUDGET
        self._budget_warned = False
    def scan(self, scope: ast.AST) -> tuple[tuple[int, int], ...]:
        initial = _RD30FlowState(
            bindings=tuple(sorted((name, name) for name in self.auto_names)),
            sql_text=self.initial_sql_text,
            autocommit=self.initial_autocommit,
            cursors=self.initial_cursors)
        auto = (True if _rd30_atomic_decorated(scope, self.resolver)
                else frozenset())
        if isinstance(scope, ast.Lambda):
            states = self._eval(scope.body, initial, auto)
        else:
            states = self._exec_body(scope.body, (initial,), auto)
        points = {(line, column) for state in states
                  for _channel, line, column in state.pending}
        return tuple(sorted(points))
    def _exec_body(self, body, states, auto: bool):
        states = _rd30_merge_flow_states(states)
        for stmt in body:
            outcomes = []
            for state in states:
                if state.reachable:
                    outcomes.extend(self._exec_stmt(stmt, state, auto))
                else:
                    outcomes.append(state)
            states = _rd30_merge_flow_states(outcomes)
        return states
    def _exec_stmt(self, stmt: ast.AST, state: _RD30FlowState, auto: bool):
        if isinstance(stmt, _RD30_NESTED_SCOPE_TYPES):
            return (state,)
        if isinstance(stmt, ast.If):
            return self._exec_if(stmt, state, auto)
        if isinstance(stmt, (ast.With, ast.AsyncWith)):
            return self._exec_with(stmt, state, auto)
        if isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
            return self._exec_loop(stmt, state, auto)
        if isinstance(stmt, (ast.Try, getattr(ast, "TryStar", ast.Try))):
            return self._exec_try(stmt, state, auto)
        if hasattr(ast, "Match") and isinstance(stmt, ast.Match):
            return self._exec_match(stmt, state, auto)
        if isinstance(stmt, (ast.Break, ast.Continue)):
            return (state._replace(
                reachable=False,
                control="break" if isinstance(stmt, ast.Break) else "continue"),)
        if isinstance(stmt, (ast.Return, ast.Raise)):
            value = getattr(stmt, "value", None) or getattr(stmt, "exc", None)
            ended = (self._eval(value, state, auto)
                     if value is not None else (state,))
            if isinstance(stmt, ast.Raise) and stmt.cause is not None:
                ended = tuple(
                    result for item in ended
                    for result in self._eval(stmt.cause, item, auto))
            if isinstance(stmt, ast.Return):
                return tuple(item._replace(reachable=False, control="return")
                             for item in ended)
            return tuple(
                item._replace(
                    reachable=False,
                    control=(item.exception_stack[-1]
                             if stmt.exc is None and item.exception_stack
                             else _rd30_raise_control(stmt)))
                for item in ended)
        return self._eval(stmt, state, auto)
    def _exec_if(self, stmt: ast.If, state: _RD30FlowState, auto: bool):
        bases = self._eval(stmt.test, state, auto)
        outcomes = []
        for base in bases:
            outcomes.extend(self._exec_body(stmt.body, (base,), auto))
            outcomes.extend(
                self._exec_body(stmt.orelse, (base,), auto)
                if stmt.orelse else (base,))
        return _rd30_merge_flow_states(outcomes)
    def _exec_with(self, stmt: ast.AST, state: _RD30FlowState, auto):
        bases = (state,)
        for item in stmt.items:
            bases = _rd30_merge_flow_states(
                result for base in bases
                for result in self._eval(item.context_expr, base, auto))
            if item.optional_vars is not None:
                bases = _rd30_merge_flow_states(
                    self._bind_pairs(
                        ((item.optional_vars, item.context_expr),), base, stmt)
                    for base in bases)
        receivers = _rd30_sql_receivers(stmt.body)
        outcomes = []
        for base in bases:
            context_channels: set[str] = set()
            global_tx = False
            for item in stmt.items:
                expr = item.context_expr
                if _rd30_is_django_atomic(expr, self.resolver):
                    global_tx = True
                    continue
                reference_tx = _rd30_is_tx_context_item(
                    expr, receivers, item.optional_vars, base.cursors)
                if not (_rd30_is_auto_tx_expr(
                        expr, self.auto_names, self.resolver, base.cursors)
                        or reference_tx):
                    continue
                if (isinstance(expr, ast.Call)
                        and isinstance(expr.func, ast.Attribute)
                        and expr.func.attr == "begin"):
                    channel = _rd30_call_channel(expr, base)
                else:
                    channel = _rd30_expression_channel(
                        expr, dict(base.bindings))
                if not channel and _driver_connect_call(expr, self.resolver):
                    channel = _rd30_resource_id(expr)
                if channel and not (
                        reference_tx
                        and channel.startswith(_RD30_SESSION_RESOURCE_PREFIX)):
                    context_channels.add(channel)
            body_auto = (True if global_tx or auto is True
                         else auto | frozenset(context_channels))
            finished = self._exec_body(stmt.body, (base,), body_auto)
            outcomes.extend(
                item._replace(pending=tuple(
                    point for point in item.pending
                    if point[0] not in context_channels))
                for item in finished)
        return _rd30_merge_flow_states(outcomes)
    def _exec_loop(self, stmt: ast.AST, state: _RD30FlowState, auto: bool):
        bases = self._eval(
            stmt.iter if not isinstance(stmt, ast.While) else stmt.test,
            state, auto)
        entry = _rd30_merge_flow_states(
            self._bind_pairs(((stmt.target, None),), base, stmt)
            if not isinstance(stmt, ast.While) else base
            for base in bases)
        natural_exit = bases
        break_states: list[_RD30FlowState] = []
        terminal_states: list[_RD30FlowState] = []
        iterations = 0
        while entry:
            # 不动点靠 next_entry == entry 收敛；只要状态带一个单调增长的维度
            # （autocommit 累积、异常栈加深），集合就永不相等，这里必须有硬上限。
            # 超限时保留 entry 原样退出，宁可多算一轮也不挂死整次扫描。
            iterations += 1
            if iterations > _RD30_MAX_LOOP_ITERATIONS:
                _log.debug(
                    "[RD-30] 循环不动点 %d 轮未收敛，已截断: line=%s",
                    iterations - 1, getattr(stmt, "lineno", 0))
                break
            body = self._exec_body(stmt.body, entry, auto)
            loop_back: list[_RD30FlowState] = []
            for item in body:
                if item.control == "break":
                    break_states.append(
                        item._replace(reachable=True, control=""))
                elif item.control == "continue":
                    loop_back.append(item._replace(reachable=True, control=""))
                elif not item.reachable:
                    terminal_states.append(item)
                else:
                    loop_back.append(item)
            if not isinstance(stmt, ast.While):
                loop_back = [
                    self._bind_pairs(((stmt.target, None),), item, stmt)
                    for item in loop_back
                ]
            else:
                loop_back = [
                    result
                    for item in loop_back
                    for result in self._eval(stmt.test, item, auto)
                ]
            next_entry = _rd30_merge_flow_states((*entry, *loop_back))
            if next_entry == entry:
                break
            entry = next_entry
        natural_exit = _rd30_merge_flow_states((*natural_exit, *entry))
        if stmt.orelse:
            natural_exit = self._exec_body(stmt.orelse, natural_exit, auto)
        return _rd30_merge_flow_states(
            (*natural_exit, *break_states, *terminal_states))
    def _exec_finally(self, body, states, auto: bool):
        if not body:
            return states
        outcomes = []
        for incoming in states:
            final_states = self._exec_body(
                body, (incoming._replace(reachable=True, control=""),), auto)
            for final in final_states:
                if not final.reachable or final.control or incoming.reachable:
                    outcomes.append(final)
                else:
                    outcomes.append(final._replace(
                        reachable=False, control=incoming.control))
        return _rd30_merge_flow_states(outcomes)
    def _exec_try_body(self, body, state: _RD30FlowState, auto: bool):
        states = _rd30_merge_flow_states((state,))
        exception_states = (
            states if body and not isinstance(body[0], ast.Raise) else ())
        for stmt in body:
            outcomes = []
            for current in states:
                if current.reachable:
                    outcomes.extend(self._exec_stmt(stmt, current, auto))
                else:
                    outcomes.append(current)
            states = _rd30_merge_flow_states(outcomes)
            if isinstance(stmt, ast.Raise):
                new_exceptions = tuple(
                    item for item in states
                    if _rd30_is_raise_control(item.control))
            else:
                new_exceptions = tuple(
                    item for item in states
                    if item.reachable or _rd30_is_raise_control(item.control))
            exception_states = _rd30_merge_flow_states(
                (*exception_states, *new_exceptions))
        return states, exception_states
    def _exec_try(self, stmt: ast.AST, state: _RD30FlowState, auto: bool):
        body, exception_states = self._exec_try_body(stmt.body, state, auto)
        normal = tuple(item for item in body if item.reachable)
        outcomes: list[_RD30FlowState] = list(normal)
        if stmt.orelse:
            outcomes = list(self._exec_body(stmt.orelse, normal, auto))
        outcomes.extend(
            item for item in body
            if not item.reachable and (
                not stmt.handlers or not _rd30_is_raise_control(item.control)
                or not _rd30_raise_is_handled(
                    item.control, stmt.handlers, self.exception_defs)))
        for item in exception_states:
            if _rd30_is_raise_control(item.control):
                continue
            if any(_rd30_raise_is_handled(
                    _RD30_IMPLICIT_RAISE_CONTROL,
                    (handler,), self.exception_defs)
                   for handler in stmt.handlers):
                continue
            outcomes.append(item._replace(
                reachable=False, control=_RD30_IMPLICIT_RAISE_CONTROL))
        if stmt.handlers:
            handler_entries = [[] for _handler in stmt.handlers]
            for item in exception_states:
                if _rd30_is_raise_control(item.control):
                    for index, handler in enumerate(stmt.handlers):
                        if _rd30_raise_is_handled(
                                item.control, (handler,), self.exception_defs):
                            handler_entries[index].append(item)
                            break
                else:
                    for entries in handler_entries:
                        entries.append(item)
            for handler, entries in zip(
                    stmt.handlers, handler_entries, strict=True):
                handler_entry = tuple(
                    item._replace(
                        reachable=True, control="",
                        exception_stack=(
                            *item.exception_stack,
                            item.control if _rd30_is_raise_control(item.control)
                            else _rd30_handler_raise_control(handler)))
                    for item in entries)
                bases = handler_entry
                if handler.name:
                    pairs = ((ast.Name(id=handler.name, ctx=ast.Store()), None),)
                    bases = _rd30_merge_flow_states(
                        self._bind_pairs(pairs, base, handler)
                        for base in handler_entry)
                handled = self._exec_body(handler.body, bases, auto)
                outcomes.extend(
                    item._replace(exception_stack=item.exception_stack[:-1])
                    for item in handled)
        return self._exec_finally(
            stmt.finalbody, _rd30_merge_flow_states(outcomes), auto)
    def _exec_match(self, stmt: ast.AST, state: _RD30FlowState, auto: bool):
        bases = self._eval(stmt.subject, state, auto)
        outcomes = list(bases)
        for base in bases:
            for case in stmt.cases:
                pairs = tuple(
                    (ast.Name(id=name, ctx=ast.Store()), None)
                    for name in iter_pattern_capture_names(case.pattern))
                case_entry = (self._bind_pairs(pairs, base, case.pattern)
                              if pairs else base)
                case_bases = (self._eval(case.guard, case_entry, auto)
                              if case.guard is not None else (case_entry,))
                for case_base in case_bases:
                    outcomes.extend(
                        self._exec_body(case.body, (case_base,), auto))
        return _rd30_merge_flow_states(outcomes)
    def _eval(self, node: ast.AST | None, state: _RD30FlowState,
              auto: bool) -> tuple[_RD30FlowState, ...]:
        self._eval_budget -= 1
        if self._eval_budget < 0:
            # 预算耗尽：保留 state 原样返回（已收集的 pending 不丢），未求值的
            # 子表达式不再产出新证据。用一次告警留痕，不静默降级。
            if not self._budget_warned:
                self._budget_warned = True
                _log.warning(
                    "[RD-30] 求值预算 %d 耗尽，该 scope 后续表达式按保守口径"
                    "跳过（未提交事务点可能漏报）", _RD30_EVAL_BUDGET)
            return (state,)
        if node is None or isinstance(node, _RD30_NESTED_SCOPE_TYPES):
            return (state,)
        if isinstance(node, ast.IfExp):
            return self._eval_if_expression(node, state, auto)
        if isinstance(node, ast.BoolOp):
            return self._eval_bool_expression(node, state, auto)
        children = ast.iter_child_nodes(node)
        if isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
            targets = (node.targets if isinstance(node, ast.Assign)
                       else (node.target,))
            children = (node.value, *targets)
        elif isinstance(node, ast.Dict):
            children = tuple(
                child
                for key, value in zip(node.keys, node.values, strict=True)
                for child in ((key, value) if key is not None else (value,)))
        elif isinstance(node, ast.Call):
            arguments = sorted(
                (*node.args, *node.keywords),
                key=lambda child: (getattr(child, "lineno", 0),
                                   getattr(child, "col_offset", 0)))
            children = (node.func, *arguments)
        return self._eval_ordered(node, children, state, auto)
    def _eval_ordered(self, node: ast.AST, children, state: _RD30FlowState,
                      auto: bool) -> tuple[_RD30FlowState, ...]:
        states = (state,)
        for child in children:
            if child is None or isinstance(child, _RD30_NESTED_SCOPE_TYPES):
                continue
            states = _rd30_merge_flow_states(
                result for current in states
                for result in self._eval(child, current, auto))
        return _rd30_merge_flow_states(
            self._eval_current(node, current, auto) for current in states)
    def _eval_if_expression(self, node: ast.IfExp, state: _RD30FlowState,
                            auto: bool) -> tuple[_RD30FlowState, ...]:
        outcomes = []
        for base in self._eval(node.test, state, auto):
            outcomes.extend(self._eval(node.body, base, auto))
            outcomes.extend(self._eval(node.orelse, base, auto))
        return _rd30_merge_flow_states(outcomes)
    def _eval_bool_expression(self, node: ast.BoolOp, state: _RD30FlowState,
                              auto: bool) -> tuple[_RD30FlowState, ...]:
        continuing = (state,)
        outcomes = []
        last = len(node.values) - 1
        for index, value in enumerate(node.values):
            next_states = []
            for current in continuing:
                evaluated = self._eval(value, current, auto)
                outcomes.extend(evaluated)
                if index < last:
                    next_states.extend(evaluated)
            continuing = _rd30_merge_flow_states(next_states)
        return _rd30_merge_flow_states(outcomes)
    def _eval_current(self, node: ast.AST, state: _RD30FlowState,
                      auto: bool) -> _RD30FlowState:
        if isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
            return self._bind_assignment(node, state)
        if isinstance(node, ast.AugAssign):
            combined = ast.BinOp(
                left=node.target, op=node.op, right=node.value)
            return self._bind_pairs(((node.target, combined),), state, node)
        if isinstance(node, ast.Delete):
            return self._bind_pairs(
                tuple((target, None) for target in node.targets), state, node)
        if not isinstance(node, ast.Call):
            return state
        call_attr = _rd30_call_attr(node)
        if call_attr in _RD30_COMMIT_ATTRS:
            channel = _rd30_call_channel(node, state)
            if not channel:
                return state
            return state._replace(pending=tuple(
                point for point in state.pending if point[0] != channel))
        if not _rd30_call_is_write(node, call_attr, dict(state.sql_text)):
            return state
        channel = _rd30_call_channel(node, state)
        if auto is True:
            if not (channel.startswith(
                    (_RD30_DRIVER_RESOURCE_PREFIX,
                     _RD30_SESSION_RESOURCE_PREFIX))
                    or channel in self.auto_names):
                return state
        elif channel in auto:
            return state
        if channel and channel in state.autocommit:
            return state
        point = (channel, node.lineno, node.col_offset)
        return state._replace(
            pending=tuple(sorted(set(state.pending) | {point})))
    def _bind_assignment(self, node: ast.AST,
                         state: _RD30FlowState) -> _RD30FlowState:
        value = node.value
        if value is None:
            return state
        pairs: list[tuple[ast.AST, ast.AST]] = []
        targets = node.targets if isinstance(node, ast.Assign) else [node.target]
        for target in targets:
            unpacked = _unpack_pairs(target, value)
            pairs.extend(unpacked or [(target, value)])
        return self._bind_pairs(pairs, state, node)
    def _bind_pairs(self, pairs, state: _RD30FlowState,
                    anchor: ast.AST) -> _RD30FlowState:
        bindings = dict(state.bindings)
        sql_bindings = dict(state.sql_text)
        autocommit = set(state.autocommit)
        cursors = set(state.cursors)
        prepared: list[
            tuple[str, str, bool, ast.AST | None, str, bool]] = []
        autocommit_updates: list[tuple[str, bool | None]] = []
        for target, value in pairs:
            names = list(_rd30_target_names(target))
            if not names:
                continue
            unwrapped = _rd29_unwrap_await(value)
            autocommit_update = _rd30_autocommit_attr_update(
                target, unwrapped, bindings)
            if autocommit_update is not None:
                autocommit_updates.append(autocommit_update)
                continue
            is_connection = _driver_connect_call(unwrapped, self.resolver)
            session_channel = _rd30_sqlalchemy_session_channel(
                unwrapped, self.resolver)
            is_cursor = _rd30_is_cursor_expr(unwrapped, cursors)
            for name in names:
                if is_connection:
                    channel = _rd30_resource_id(unwrapped)
                elif session_channel:
                    channel = session_channel
                else:
                    channel = _rd30_expression_channel(unwrapped, bindings)
                if not channel:
                    channel = _rd30_unknown_resource(anchor, name)
                sql_value = (_rd30_static_sql_text(unwrapped, sql_bindings)
                             if unwrapped is not None else "")
                prepared.append((
                    name, channel, is_connection, unwrapped, sql_value,
                    is_cursor))
        for (name, channel, is_connection, unwrapped, sql_value,
             is_cursor) in prepared:
            previous = bindings.get(name)
            stale_prefix = f"{name}."
            stale = [(key, old) for key, old in bindings.items()
                     if key.startswith(stale_prefix)]
            for key, old in stale:
                del bindings[key]
                sql_bindings.pop(key, None)
                if old not in bindings.values():
                    autocommit.discard(old)
            cursors.difference_update(
                key for key in tuple(cursors)
                if key == name or key.startswith(stale_prefix))
            bindings[name] = channel
            if is_cursor:
                cursors.add(name)
            sql_bindings.pop(name, None)
            if sql_value:
                sql_bindings[name] = sql_value
            if is_connection and _rd30_is_autocommit_call(unwrapped):
                autocommit.add(channel)
            if previous and previous not in bindings.values():
                autocommit.discard(previous)
        for channel, enabled in autocommit_updates:
            if enabled is True:
                autocommit.add(channel)
            else:
                autocommit.discard(channel)
        return state._replace(
            bindings=tuple(sorted(bindings.items())),
            sql_text=tuple(sorted(sql_bindings.items())),
            autocommit=frozenset(autocommit),
            cursors=frozenset(cursors))
class _RD30TxEvidence(NamedTuple):
    scope_desc: str
    pending_points: tuple[tuple[int, int], ...]
def _rd30_atomic_decorated(
        scope: ast.AST, resolver: _DBConnectResolver,
) -> bool:
    if not isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return False
    return any(_rd30_is_django_atomic(decorator, resolver)
               for decorator in scope.decorator_list)
def _rd30_tx_finding(filepath: Any,
                     evidence: _RD30TxEvidence) -> FindingRecord | None:
    write_line = min(evidence.pending_points, default=(0, 0))[0]
    if not write_line:
        return None
    return db_finding(
        "RD-30", "P1", write_line, filepath,
        title="事务未关闭: 写操作后缺少commit/rollback",
        description=f"{evidence.scope_desc} 执行了数据库写操作但未调用 commit() 或 rollback(), "
                    f"异常路径下事务可能悬挂未关闭",
        suggestion=(
            "根因: 执行了INSERT/UPDATE/DELETE写操作但未调用commit/rollback, "
            "异常退出时事务悬挂, 导致数据库锁未释放、数据不一致。\n"
            "修复策略(按优先级):\n"
            "1. try-except-finally(标准模式):\n"
            "   try:\n"
            "       cursor.execute('INSERT INTO ... VALUES (?)', (data,))\n"
            "       conn.commit()\n"
            "   except Exception as e:\n"
            "       conn.rollback()\n"
            "       raise\n"
            "2. with语句自动提交(Django ORM):\n"
            "   from django.db import transaction\n"
            "   with transaction.atomic():\n"
            "       obj = Model.objects.create(...)\n"
            "3. 装饰器模式(Django): @transaction.atomic\n"
            "4. SQLAlchemy会话: session.commit() / session.rollback() 配合try-except\n"
            "5. 上下文管理器: 自定义 @contextmanager 封装事务开始/提交/回滚\n"
            "参考: CWE-362 (Race Condition) / OWASP A04:2021"
        ),
    )
def _rd30_iter_scan_targets(tree: ast.AST) -> Iterator[tuple[ast.AST, str]]:
    yield tree, "模块级代码"
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield node, f"函数 '{node.name}'"
        elif isinstance(node, ast.ClassDef):
            yield node, f"类 '{node.name}'"
        elif isinstance(node, ast.Lambda):
            yield node, "Lambda 表达式"
def check_RD30(tree: Any, source_lines: Any, filepath: Any) -> list[FindingRecord]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[FindingRecord] = []
    if tree is None:
        return issues
    resolver = _make_db_connect_resolver(tree, _RD30_AUTO_TX_CONNECT_MODULES)
    name_index = _rd30_bound_name_index(tree, resolver)
    for scope, scope_desc in _rd30_iter_scan_targets(tree):
        auto_names, autocommit_names = _rd30_visible_conn_names(
            scope, resolver, name_index)
        sql_names = _rd30_visible_sql_text(scope, resolver, name_index)
        cursor_names = _rd30_visible_cursor_names(
            scope, resolver, name_index)
        initial_autocommit = (
            autocommit_names - name_index.bound.get(id(scope), set()))
        finding = _rd30_tx_finding(
            filepath, _RD30TxEvidence(
                scope_desc,
                _RD30FlowAnalyzer(
                    auto_names, resolver, initial_autocommit,
                    sql_names, cursor_names).scan(scope)))
        if finding is not None:
            issues.append(finding)
    if issues:
        _log.debug("[RD-30] transaction_unclosed 命中 %d 处: %s", len(issues), filepath)
    return issues
_SQL_CHECKERS = (
    ("RD-28", check_RD28), ("RD-30", check_RD30),
    ("RD-32", check_RD32),
)
def _register_detector_catalogs() -> None:
    register_detector_catalog("diag4_direct", dict(_SQL_CHECKERS))
_register_detector_catalogs()

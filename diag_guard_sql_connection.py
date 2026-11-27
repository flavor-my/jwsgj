from __future__ import annotations  # noqa: I001
import ast
import logging
import os
import re
from collections.abc import Iterator
from typing import Any, NamedTuple
from jwsgj.diag_detectors_registry import register_detector_catalog
from jwsgj.diag_shared_ast_bindings import collect_binding_names
from jwsgj.diag_shared_ast_nodes import (
    build_parent_map,
    collect_param_names,
    dotted_name,
    iter_pattern_capture_names,
    node_position,
    walk_stmts,
)
from jwsgj.diag_shared_ast_nodes import get_call_name as _get_call_name
from jwsgj.diag_shared_source_core import aligned_source_lines, read_source_tree
from jwsgj.diag_types_defs import (
    FindingRecord,
    finding_scan_exempt,
)
from jwsgj.prevention_scope_facts import walk_nodes
_log = logging.getLogger("jwsgj.diag_guard_sql_connection")
__all__ = [
    "check_DB06",
    "check_RD29",
    "check_RD31",
    "connection_call_name",
    "db_finding",
    "is_url_create_call",
]
_log.info(
    "diag_guard_sql_connection RD-29/RD-31 + DB-06 数据库连接安全族"
    "（连接识别内核 + 生命周期 + 凭证 + 连接管理）"
    "已加载: %d 项导出",
    len(__all__),
)
def is_url_create_call(call: ast.Call) -> bool:
    if not (isinstance(call.func, ast.Attribute) and call.func.attr == "create"):
        return False
    return dotted_name(call.func.value).rpartition(".")[2] == "URL"
def connection_call_name(call: ast.Call) -> str:
    if is_url_create_call(call):
        return "URL.create"
    if isinstance(call.func, ast.Attribute):
        return call.func.attr
    if isinstance(call.func, ast.Name):
        return call.func.id
    return ""
def db_finding(rule_id: str, severity: str, line: int, filepath: Any, *,
                title: str, description: str,
                suggestion: str) -> FindingRecord:
    return FindingRecord(
        id=rule_id,
        severity=severity,
        dimension="security",
        file=filepath,
        line=line,
        title=title,
        description=description,
        suggestion=suggestion,
    )
def _closing_channel_names(tree: ast.AST) -> set:
    closing_names: set = {'closing', 'contextlib.closing'}
    for _ch in walk_nodes(tree):
        if isinstance(_ch, ast.ImportFrom) and _ch.module == 'contextlib':
            closing_names.update(_closing_from_import_names(_ch))
        elif isinstance(_ch, ast.Import):
            closing_names.update(_closing_module_names(_ch))
    return closing_names
def _closing_from_import_names(node: ast.ImportFrom) -> set[str]:
    return {_al.asname or 'closing' for _al in node.names
            if _al.name == 'closing'}
def _closing_module_names(node: ast.Import) -> set[str]:
    return {f"{_al.asname or 'contextlib'}.closing" for _al in node.names
            if _al.name == 'contextlib'}
def _closing_call_argument(
        node: ast.AST, closing_names: set,
        resolver: _DBConnectResolver | None = None,
) -> ast.AST | None:
    if not isinstance(node, ast.Call):
        return None
    name = _get_call_name(node)
    if resolver is None:
        if name not in closing_names:
            return None
    else:
        target = _rd29_imported_target(
            node, resolver.import_sources, resolver.index)
        if target is not None:
            if target != ("contextlib", "closing"):
                return None
        else:
            if name not in closing_names:
                return None
            base = name.partition(".")[0]
            scope = _rd29_binding_scope(
                base, _rd29_evaluation_scope(node, resolver.index),
                resolver.index)
            if base in resolver.index.scope_binds.get(id(scope), ()):
                return None
    if node.args:
        return node.args[0]
    return next((kw.value for kw in node.keywords if kw.arg == "thing"), None)
def _unpack_pairs(target: ast.AST | None,
                  value: ast.AST | None) -> list[tuple[ast.AST, ast.AST]]:
    if not (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))):
        return []
    if len(target.elts) != len(value.elts):
        return []
    if any(isinstance(elt, ast.Starred) for elt in target.elts):
        return []
    pairs: list[tuple[ast.AST, ast.AST]] = []
    for sub_target, sub_value in zip(target.elts, value.elts, strict=True):
        if isinstance(sub_target, (ast.Tuple, ast.List)):
            pairs.extend(_unpack_pairs(sub_target, sub_value))
            continue
        pairs.append((sub_target, sub_value))
    return pairs
def _scope_local_binds(scope: ast.AST) -> set:
    local: set = set()
    if not isinstance(scope, ast.ClassDef):
        local.update(collect_param_names(scope))
    decls: set = set()
    if isinstance(scope, ast.Lambda):
        for _sub in walk_nodes(scope.body):
            if (isinstance(_sub, ast.NamedExpr)
                    and isinstance(_sub.target, ast.Name)):
                local.add(_sub.target.id)
    else:
        for _stmt in walk_stmts(scope.body):
            collect_binding_names(_stmt, local)
            if isinstance(_stmt, (ast.Global, ast.Nonlocal)):
                decls.update(_stmt.names)
    return local - decls
_RD31_DB_URL_SCHEMES = (
    "postgresql", "postgres", "psql",
    "mysql", "mariadb", "memsql",
    "sqlite", "sqlite3", "duckdb",
    "oracle", "oracledb", "mssql", "sqlserver", "pymssql",
    "db2", "ibm_db", "firebird", "tidb", "oceanbase",
    "redis", "rediss", "mongodb", "cassandra", "couchbase", "neo4j",
    "cockroachdb", "clickhouse", "snowflake", "teradata",
    "trino", "presto", "hive", "impala", "starrocks", "doris",
    "influxdb", "prometheus",
)
_RD31_DB_URL_PATTERN = re.compile(
    r"(?<![a-z0-9_+.\-])"
    r"(?:" + "|".join(_RD31_DB_URL_SCHEMES) + r")"
    r"(?:\+[a-z0-9_]+)?:"
    r"[^:\s]*:([^@\s]{3,})@", re.IGNORECASE
)
_RD31_PASSWORD_KWARGS = frozenset({"password", "passwd", "pwd", "pass"})
_RD31_PLACEHOLDER_PATTERNS = (
    re.compile(r"\$\{[^{}]*\}"),
    re.compile(r"\$\([^()]*\)"),
    re.compile(r"^<[A-Za-z_][\w.\- ]*>$"),
    re.compile(r"^\{\{?\s*[A-Za-z_][\w.]*\s*\}?\}$"),
)
_RD31_ENV_PLACEHOLDER_RE = re.compile(r"\b(?:os\.environ|os\.getenv|getenv)\b")
_RD31_PLACEHOLDER_WORDS = frozenset({
    "secret", "example", "placeholder", "changeme", "change_me",
    "your_password", "yourpassword", "xxx", "xxxx", "***", "****",
    "config", "settings",
}) | _RD31_PASSWORD_KWARGS
_RD31_CODE_SAMPLE_TOKENS = ("def ", "import ", "class ", "return ")
_RD31_CONN_KW_METHODS = ("connect", "create_engine", "create_async_engine")
_RD31_URL_SUGGESTION = (
    "根因: 数据库连接字符串或password参数使用硬编码明文, "
    "代码泄露(git push/日志/异常堆栈)时直接暴露数据库凭证。\n"
    "修复策略(按优先级):\n"
    "1. 环境变量(基础):\n"
    "   import os\n"
    "   password = os.environ['DB_PASSWORD']\n"
    "   conn = psycopg2.connect(password=password)\n"
    "2. .env文件+python-dotenv(推荐):\n"
    "   from dotenv import load_dotenv\n"
    "   load_dotenv()  # 从.env文件加载\n"
    "   password = os.getenv('DB_PASSWORD')\n"
    "3. 配置管理(团队): 使用pydantic-settings或dynaconf统一管理配置\n"
    "4. 密钥管理服务(生产): AWS Secrets Manager / HashiCorp Vault / Azure Key Vault\n"
    "5. 连接字符串模板: 'postgresql://user:${DB_PASSWORD}@host/db'\n"
    "注意: .env文件必须加入.gitignore, 切勿提交到版本控制\n"
    "参考: OWASP A07:2021 / CWE-798 / Bandit B105"
)
def _rd31_is_placeholder(value: str) -> bool:
    return (any(pattern.search(value) for pattern in _RD31_PLACEHOLDER_PATTERNS)
            or bool(_RD31_ENV_PLACEHOLDER_RE.search(value.lower())))
def _rd31_is_hardcoded_secret(value: str) -> bool:
    _low = value.lower()
    return (len(value) >= 3
            and _low not in _RD31_PLACEHOLDER_WORDS
            and not _rd31_is_placeholder(value))
def _rd31_static_string_value(node: ast.AST) -> str | None:
    if isinstance(node, ast.Constant):
        return node.value if isinstance(node.value, str) else None
    if not isinstance(node, ast.JoinedStr):
        return None
    parts: list[str] = []
    for part in node.values:
        if isinstance(part, ast.Constant) and isinstance(part.value, str):
            parts.append(part.value)
            continue
        if (isinstance(part, ast.FormattedValue)
                and part.conversion == -1 and part.format_spec is None):
            if isinstance(part.value, ast.Constant):
                parts.append(str(part.value.value))
                continue
            nested = _rd31_static_string_value(part.value)
            if nested is not None:
                parts.append(nested)
                continue
        return None
    return "".join(parts)
def _rd31_is_literal_secret(node: ast.AST) -> bool:
    value = _rd31_static_string_value(node)
    return value is not None and _rd31_is_hardcoded_secret(value)
def _rd31_url_has_hardcoded_secret(value: str) -> bool:
    if _rd31_is_code_sample(value):
        return False
    return any(_rd31_is_hardcoded_secret(match.group(1))
               for match in _RD31_DB_URL_PATTERN.finditer(value))
def _rd31_is_code_sample(value: str) -> bool:
    return "\n" in value and any(
        token in value for token in _RD31_CODE_SAMPLE_TOKENS)
def _rd31_password_name(name: str | None) -> str | None:
    return name if name is not None and name in _RD31_PASSWORD_KWARGS else None
def _rd31_password_key(key: ast.AST, value: ast.AST) -> str | None:
    if not (isinstance(key, ast.Constant) and isinstance(key.value, str)):
        return None
    name = _rd31_password_name(key.value)
    if name is None or not _rd31_is_literal_secret(value):
        return None
    return name
def _rd31_kwarg_suggestion(subject: str, env_hint: str) -> str:
    return (
        f"根因: {subject}"
        f"代码泄露(git push/日志/异常堆栈)时直接暴露数据库凭证。\n"
        "修复策略(按优先级):\n"
        f"1. 环境变量(基础): {env_hint}\n"
        "2. .env文件+python-dotenv(推荐): load_dotenv()后os.getenv()\n"
        "3. 配置管理(团队): pydantic-settings或dynaconf统一管理\n"
        "4. 密钥管理服务(生产): AWS Secrets Manager / HashiCorp Vault\n"
        "注意: .env文件必须加入.gitignore\n"
        "参考: OWASP A07:2021 / CWE-798 / Bandit B105"
    )
def _rd31_url_constant_finding(node: ast.AST,
                               filepath: Any) -> FindingRecord | None:
    value = _rd31_static_string_value(node)
    if value is None or not _rd31_url_has_hardcoded_secret(value):
        return None
    return db_finding(
        "RD-31", "P0", node.lineno, filepath,
        title="硬编码数据库凭证: 连接字符串包含明文密码",
        description="数据库连接字符串中包含明文密码, "
                    "代码泄露或日志记录时将暴露数据库凭证 (OWASP A07:2021)",
        suggestion=_RD31_URL_SUGGESTION,
    )
def _db_shadowed_import(node: ast.Call,
                        resolver: _DBConnectResolver) -> bool:
    base_node = node.func
    while isinstance(base_node, ast.Attribute):
        base_node = base_node.value
    if not isinstance(base_node, ast.Name):
        return False
    base = base_node.id
    index = resolver.index
    position = _rd29_node_position(node, index)
    cur = _rd29_binding_scope(
        base, _rd29_nearest_scope_in(
            node, index.parent, index.scope_ids, index.tree), index)
    in_function = isinstance(cur, _RD29_CALLABLE_SCOPES)
    shadowed = False
    while cur is not None:
        cur = _rd29_visible_scope(cur, in_function, index)
        if cur is None:
            break
        active = _rd29_active_import_source(
            base, cur, position, resolver.import_sources, index)
        if base in resolver.import_sources.get(id(cur), {}):
            return shadowed or active is None
        if base in index.scope_binds.get(id(cur), ()) and active is None:
            shadowed = True
        in_function = in_function or isinstance(cur, _RD29_CALLABLE_SCOPES)
        cur = index.parent.get(id(cur))
    return False
def _rd31_conn_call_disp(node: ast.Call,
                         resolver: _DBConnectResolver,
                         local_defs: dict) -> str | None:
    local_verdict = _rd29_local_conn_def_verdict(
        node, local_defs, resolver.index)
    if local_verdict is False:
        return None
    if local_verdict is True:
        name = connection_call_name(node)
        return (name if name == "URL.create" or name in _RD31_CONN_KW_METHODS
                else None)
    target = _rd29_imported_target(
        node, resolver.import_sources, resolver.index)
    if target is not None:
        source, attr = target
        if attr == "create" and source.rpartition(".")[2] == "URL":
            return "URL.create"
        if attr in _RD31_CONN_KW_METHODS:
            return attr
    if _db_shadowed_import(node, resolver):
        return None
    name = connection_call_name(node)
    if name == "URL.create" or name in _RD31_CONN_KW_METHODS:
        return name
    return None
def _rd31_password_kwarg_finding(node: ast.Call, kw: ast.keyword,
                                 method_disp: str,
                                 filepath: Any) -> FindingRecord | None:
    arg_name = _rd31_password_name(kw.arg)
    if arg_name is None or not _rd31_is_literal_secret(kw.value):
        return None
    return db_finding(
        "RD-31", "P0", node.lineno, filepath,
        title=f"硬编码数据库凭证: {arg_name}参数为明文字符串",
        description=f"{method_disp}()调用的 {arg_name} 参数使用了硬编码字符串, "
                    f"代码泄露时将暴露数据库凭证",
        suggestion=_rd31_kwarg_suggestion(
            f"{method_disp}()调用的 {arg_name} 参数使用硬编码明文字符串, ",
            f"{arg_name}=os.environ.get('DB_PASSWORD')"),
    )
def _rd31_mapping_items(node: ast.AST) -> Iterator[tuple[ast.AST, ast.AST]]:
    if isinstance(node, ast.Dict):
        for key_node, value_node in zip(
                node.keys, node.values, strict=True):
            if key_node is None:
                yield from _rd31_mapping_items(value_node)
            else:
                yield key_node, value_node
        return
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name) and node.func.id == "dict"):
        return
    for arg in node.args:
        if not isinstance(arg, ast.Starred):
            yield from _rd31_mapping_items(arg)
    for kw in node.keywords:
        if kw.arg is None:
            yield from _rd31_mapping_items(kw.value)
        else:
            yield ast.Constant(value=kw.arg), kw.value
def _rd31_connect_args_findings(node: ast.Call, kw: ast.keyword,
                                filepath: Any) -> list:
    if kw.arg != "connect_args":
        return []
    findings = []
    for key_node, value_node in _rd31_mapping_items(kw.value):
        finding = _rd31_connect_arg_finding(
            node, key_node, value_node, filepath)
        if finding is not None:
            findings.append(finding)
    return findings
def _rd31_connect_arg_finding(node: ast.Call, key_node: ast.AST,
                              value_node: ast.AST,
                              filepath: Any) -> FindingRecord | None:
    key = _rd31_password_key(key_node, value_node)
    if key is None:
        return None
    return db_finding(
        "RD-31", "P0", node.lineno, filepath,
        title=f"硬编码数据库凭证: connect_args[{key!r}]为明文字符串",
        description=f"连接调用的 connect_args[{key!r}] 使用了硬编码字符串, "
                    f"代码泄露时将暴露数据库凭证",
        suggestion=_rd31_kwarg_suggestion(
            f"connect_args[{key!r}] 使用硬编码明文字符串, ",
            f"connect_args={{{key!r}: os.environ.get('DB_PASSWORD')}}"),
    )
def _rd31_keyword_findings(node: ast.Call, kw: ast.keyword,
                          method_disp: str,
                          filepath: Any) -> list[FindingRecord]:
    findings: list[FindingRecord] = []
    finding = _rd31_password_kwarg_finding(node, kw, method_disp, filepath)
    if finding is not None:
        findings.append(finding)
    findings.extend(_rd31_connect_args_findings(node, kw, filepath))
    return findings
def _rd31_unpacked_kwarg_findings(node: ast.Call, kw: ast.keyword,
                                 method_disp: str,
                                 filepath: Any) -> list[FindingRecord]:
    if kw.arg is not None:
        return []
    findings: list[FindingRecord] = []
    for key_node, value_node in _rd31_mapping_items(kw.value):
        if not (isinstance(key_node, ast.Constant)
                and isinstance(key_node.value, str)):
            continue
        findings.extend(_rd31_keyword_findings(
            node, ast.keyword(arg=key_node.value, value=value_node),
            method_disp, filepath))
    return findings
def _rd31_conn_call_findings(node: ast.Call, filepath: Any,
                             resolver: _DBConnectResolver,
                             local_defs: dict) -> list[FindingRecord]:
    method_disp = _rd31_conn_call_disp(node, resolver, local_defs)
    if method_disp is None:
        return []
    findings: list[FindingRecord] = []
    for kw in node.keywords:
        findings.extend(_rd31_keyword_findings(
            node, kw, method_disp, filepath))
        findings.extend(_rd31_unpacked_kwarg_findings(
            node, kw, method_disp, filepath))
    return findings
def _rd31_collect(tree: ast.AST, filepath: Any) -> list[FindingRecord]:
    url_issues: list[FindingRecord] = []
    kwarg_issues: list[FindingRecord] = []
    resolver = _make_db_connect_resolver(tree, ())
    local_defs = _rd29_local_conn_defs_by_scope(
        tree, resolver.index, resolver.import_sources)
    static_fstring_children = {
        id(child)
        for parent in walk_nodes(tree)
        if isinstance(parent, ast.JoinedStr)
        and _rd31_static_string_value(parent) is not None
        for child in walk_nodes(parent)
        if child is not parent
    }
    for node in walk_nodes(tree):
        if isinstance(node, (ast.Constant, ast.JoinedStr)):
            if id(node) in static_fstring_children:
                continue
            finding = _rd31_url_constant_finding(node, filepath)
            if finding is not None:
                url_issues.append(finding)
        elif isinstance(node, ast.Call):
            kwarg_issues.extend(_rd31_conn_call_findings(
                node, filepath, resolver, local_defs))
    return url_issues + kwarg_issues
def check_RD31(tree: Any, source_lines: Any, filepath: Any) -> list[FindingRecord]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[FindingRecord] = []
    if tree is None:
        return issues
    issues.extend(_rd31_collect(tree, filepath))
    if issues:
        _log.debug("[RD-31] hardcoded_credentials 命中 %d 处: %s", len(issues), filepath)
    return issues
_RD29_CONNECT_METHODS = {"connect", "create_engine", "create_async_engine"}
_RD29_CLOSE_METHODS = frozenset({"close", "dispose"})
_SQLITE_CONNECT_MODULES = frozenset({"sqlite3", "sqlite3.dbapi2"})
_RD29_DB_DRIVER_MODULES = frozenset({
    "sqlite3", "aiosqlite", "psycopg2", "psycopg", "psycopg2cffi",
    "pymysql", "MySQLdb", "aiomysql", "asyncmy",
    "pyodbc", "pymssql", "cx_Oracle", "oracledb", "sqlalchemy", "mysql",
    "asyncpg", "motor", "pymongo", "redis", "duckdb",
    "clickhouse_driver", "clickhouse_connect", "snowflake", "teradata",
    "trino", "presto", "pyhive", "impala", "ibm_db", "ibm_db_dbi",
    "firebird", "fdb", "neo4j", "cassandra", "elasticsearch",
    "opensearchpy",
})
def _rd29_namespace_roots(node: ast.AST) -> set:
    roots = set()
    for child in walk_nodes(node):
        if not isinstance(child, ast.Call):
            continue
        func = child.func
        while isinstance(func, ast.Attribute):
            func = func.value
        if isinstance(func, ast.Name):
            roots.add(func.id)
    return roots
def _rd29_is_db_driver_module(module: str) -> bool:
    return any(module == driver or module.startswith(driver + ".")
               for driver in _RD29_DB_DRIVER_MODULES)
def _rd29_conn_def_is_db(node: ast.AST, import_sources=None,
                         index=None) -> bool:
    if _rd29_namespace_roots(node) & _RD29_DB_DRIVER_MODULES:
        return True
    if import_sources is None or index is None:
        return False
    for child in walk_nodes(node):
        if not isinstance(child, ast.Call):
            continue
        target = _rd29_imported_target(child, import_sources, index)
        if target is not None:
            module, attr = target
            if (_rd29_is_db_driver_module(module)
                    and attr in _RD29_CONNECT_METHODS):
                return True
    return False
def _rd29_local_conn_defs(tree: ast.AST, import_sources=None,
                           index=None) -> dict:
    defs = {}
    for node in getattr(tree, "body", []) or []:
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if node.name not in _RD29_CONNECT_METHODS:
            continue
        defs[node.name] = _rd29_conn_def_is_db(
            node, import_sources, index)
    return defs
def _rd29_local_conn_defs_by_scope(tree: ast.AST, index,
                                   import_sources=None) -> dict:
    definitions = {}
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if node.name not in _RD29_CONNECT_METHODS:
                continue
            anchor = index.parent.get(id(node))
            if anchor is None:
                continue
            scope = _rd29_nearest_scope_in(
                anchor, index.parent, index.scope_ids, index.tree)
            sites = ((node.name, node),)
        elif (isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr))
              and isinstance(node.value, ast.Lambda)):
            targets = (node.targets if isinstance(node, ast.Assign)
                       else [node.target])
            sites = tuple(
                (target.id, node.value) for target in targets
                if isinstance(target, ast.Name)
                and target.id in _RD29_CONNECT_METHODS)
            if not sites:
                continue
            scope = _rd29_assignment_scope(node, index)
        else:
            continue
        for name, definition in sites:
            definitions.setdefault(id(scope), {}).setdefault(name, []).append(
                (node_position(node),
                 _rd29_conn_def_is_db(definition, import_sources, index)))
    return definitions
def _rd29_local_conn_def_verdict(call: ast.Call, local_defs: dict,
                                 index) -> bool | None:
    func = call.func
    if not isinstance(func, ast.Name):
        return None
    call_scope = _rd29_nearest_scope_in(
        call, index.parent, index.scope_ids, index.tree)
    scope = _rd29_binding_scope(func.id, call_scope, index)
    definitions = local_defs.get(id(scope), {}).get(func.id, ())
    if not definitions:
        return None
    if call_scope is not scope and isinstance(call_scope, _RD29_FUNCTION_SCOPES):
        return max(definitions, key=lambda entry: entry[0])[1]
    call_pos = _rd29_node_position(call, index)
    prior = [entry for entry in definitions if entry[0] <= call_pos]
    if not prior:
        return None
    return max(prior, key=lambda entry: entry[0])[1]
def _rd29_iter_import_bindings(node: ast.AST):
    if isinstance(node, ast.Import):
        for alias in node.names:
            bound = alias.asname or alias.name.split(".")[0]
            source = alias.name if alias.asname else bound
            yield bound, source
    elif isinstance(node, ast.ImportFrom):
        for alias in node.names:
            if alias.name == "*":
                continue
            if node.module:
                source = f"{'.' * node.level}{node.module}.{alias.name}"
            else:
                source = f"{'.' * node.level}{alias.name}"
            yield alias.asname or alias.name, source
def _rd29_import_sources_by_scope(tree: ast.AST, index) -> dict:
    sources = {}
    for node in walk_nodes(tree):
        for bound, source in _rd29_iter_import_bindings(node):
            scope = _rd29_binding_scope(
                bound, _rd29_nearest_scope_in(
                    node, index.parent, index.scope_ids, index.tree), index)
            sources.setdefault(id(scope), {})[bound] = source
    return sources
def _rd29_find_module_file(base: str, module_rel: str) -> str | None:
    current = base
    module_files = (module_rel + ".py",
                    os.path.join(module_rel, "__init__.py"))
    while True:
        for module_file in module_files:
            candidate = os.path.join(current, module_file)
            if os.path.isfile(candidate):
                return candidate
        parent = os.path.dirname(current)
        if parent == current:
            return None
        current = parent
def _rd29_module_def_non_db(module: str, attr: str, filepath: Any) -> bool:
    if not module or _rd29_is_db_driver_module(module):
        return False
    try:
        raw_path = str(filepath or "").strip()
        base = (os.path.dirname(os.path.abspath(raw_path))
                if raw_path else os.getcwd())
        module_path = os.path.join(*module.split("."))
        path = _rd29_find_module_file(base, module_path)
        if path is None:
            return False
        mod_tree = read_source_tree(path)
    except (OSError, SyntaxError, ValueError) as exc:
        _log.debug("[RD-29] 兄弟模块解析失败 %s: %s", module, exc)
        return False
    if mod_tree is None:
        _log.debug("[RD-29] 兄弟模块不可读或语法损坏: %s", module)
        return False
    module_index = _build_rd29_scope_index(mod_tree)
    module_imports = _rd29_import_sources_by_scope(mod_tree, module_index)
    return _rd29_local_conn_defs(
        mod_tree, module_imports, module_index).get(attr) is False
def _rd29_alias_import_source(value: ast.AST, scope: ast.AST,
                              position: tuple[int, int],
                              import_sources: dict, index) -> str | None:
    if isinstance(value, ast.Name):
        source_scope = _rd29_binding_scope(value.id, scope, index)
        return _rd29_active_import_source(
            value.id, source_scope, position, import_sources, index,
            before=True)
    if isinstance(value, ast.Attribute) and isinstance(value.value, ast.Name):
        source_scope = _rd29_binding_scope(value.value.id, scope, index)
        module = _rd29_active_import_source(
            value.value.id, source_scope, position, import_sources, index,
            before=True)
        return f"{module}.{value.attr}" if module else None
    return None
def _rd29_active_import_source(name: str, scope: ast.AST,
                               position: tuple[int, int],
                               import_sources: dict, index, *,
                               before: bool = False) -> str | None:
    events = index.binding_events.get(id(scope), {}).get(name, ())
    if not events:
        return import_sources.get(id(scope), {}).get(name)
    current = None
    for event_pos, source, value in events:
        if event_pos > position or (before and event_pos == position):
            break
        if source is not None:
            current = source
        elif value is not None:
            current = _rd29_alias_import_source(
                value, scope, event_pos, import_sources, index)
        else:
            current = None
    return current
def _rd29_imported_target(call: ast.Call | ast.Name | ast.Attribute,
                          import_sources: dict, index) -> tuple[str, str] | None:
    func = call.func if isinstance(call, ast.Call) else call
    position = _rd29_node_position(call, index)
    if isinstance(func, ast.Attribute):
        parts: list[str] = []
        base: ast.AST = func
        while isinstance(base, ast.Attribute):
            parts.append(base.attr)
            base = base.value
        if not isinstance(base, ast.Name):
            return None
        parts.reverse()
        scope = _rd29_binding_scope(
            base.id, _rd29_nearest_scope_in(
                call, index.parent, index.scope_ids, index.tree), index)
        module = _rd29_active_import_source(
            base.id, scope, position, import_sources, index)
        if not module:
            return None
        *module_attrs, attr = parts
        if module_attrs:
            module = ".".join((module, *module_attrs))
        return module, attr
    if not isinstance(func, ast.Name):
        return None
    scope = _rd29_binding_scope(
        func.id, _rd29_nearest_scope_in(
            call, index.parent, index.scope_ids, index.tree), index)
    source = _rd29_active_import_source(
        func.id, scope, position, import_sources, index)
    module, sep, attr = (source or "").rpartition(".")
    return (module, attr) if sep and module and attr else None
def _rd29_is_imported_non_db_call(call: ast.Call, filepath: Any,
                                  import_sources: dict, index) -> bool:
    target = _rd29_imported_target(call, import_sources, index)
    if target is None:
        return False
    return _rd29_module_def_non_db(target[0], target[1], filepath)
class _RD29ScopeIndex(NamedTuple):
    tree: ast.AST
    parent: dict
    scope_ids: set
    scope_binds: dict
    global_decls: dict
    nonlocal_decls: dict
    binding_events: dict
    referenced_scope_ids: frozenset[int]
    referenced_scope_positions: dict[int, tuple[tuple[int, int], ...]]
class _RD29Evidence(NamedTuple):
    connect_nodes: list
    with_managed_conn_ids: set
    closed_dotted: list
    closed_simple: list
    conn_assign_targets: dict
    conn_assign_scope: dict
    rebind_events: list
def _rd29_is_conn_call(
        call: ast.Call, resolver: _DBConnectResolver | None = None) -> bool:
    if isinstance(call.func, ast.Attribute):
        if call.func.attr in _RD29_CONNECT_METHODS:
            return True
    elif isinstance(call.func, ast.Name) and call.func.id in _RD29_CONNECT_METHODS:
        return True
    if resolver is None:
        return False
    target = _rd29_imported_target(
        call, resolver.import_sources, resolver.index)
    if target is None:
        return False
    module, attr = target
    return (attr in _RD29_CONNECT_METHODS
            and _rd29_is_db_driver_module(module))
def _rd29_nearest_scope_in(node: ast.AST, parent: dict, scope_ids: set,
                           root: ast.AST, *,
                           skip_comprehensions: bool = False) -> ast.AST:
    cur: ast.AST | None = node
    while cur is not None:
        if (id(cur) in scope_ids
                and not (skip_comprehensions
                         and isinstance(cur, _RD29_COMPREHENSION_SCOPES))):
            return cur
        cur = parent.get(id(cur))
    return root
def _rd29_unwrap_await(value: ast.AST | None) -> ast.AST | None:
    while isinstance(value, ast.Await):
        value = value.value
    return value
def _rd29_unwrap_closing(
        node: ast.AST, closing_names: set,
        resolver: _DBConnectResolver | None = None,
) -> ast.AST:
    node = _rd29_unwrap_await(node)
    while True:
        argument = _closing_call_argument(node, closing_names, resolver)
        if argument is None:
            return node
        node = _rd29_unwrap_await(argument)
def _rd29_nonlocal_hop(cur: ast.AST, index: _RD29ScopeIndex) -> ast.AST:
    outer = index.parent.get(id(cur))
    while (outer is not None and not isinstance(
            outer, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))):
        outer = index.parent.get(id(outer))
    return outer if outer is not None else index.tree
_RD29_FUNCTION_SCOPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
_RD29_COMPREHENSION_SCOPES = (ast.ListComp, ast.SetComp, ast.DictComp,
                              ast.GeneratorExp)
_RD29_CALLABLE_SCOPES = (*_RD29_FUNCTION_SCOPES, *_RD29_COMPREHENSION_SCOPES)
def _rd29_in_outermost_iter(
        node: ast.AST, scope: ast.AST, index: _RD29ScopeIndex) -> bool:
    child = None
    cur: ast.AST | None = node
    while cur is not scope:
        parent = index.parent.get(id(cur))
        if parent is None:
            return False
        if parent is scope:
            first_generator = scope.generators[0]
            return cur is first_generator and child is first_generator.iter
        child, cur = cur, parent
    return False
def _rd29_evaluation_scope(
        node: ast.AST, index: _RD29ScopeIndex) -> ast.AST:
    scope = _rd29_nearest_scope_in(
        node, index.parent, index.scope_ids, index.tree)
    while (isinstance(scope, _RD29_COMPREHENSION_SCOPES)
            and _rd29_in_outermost_iter(node, scope, index)):
        scope = _rd29_nearest_scope_in(
            index.parent.get(id(scope)), index.parent,
            index.scope_ids, index.tree)
    return scope
def _rd29_decl_hop(name: str, cur: ast.AST,
                   index: _RD29ScopeIndex) -> ast.AST | None:
    if name in index.global_decls.get(id(cur), ()):
        return index.tree
    if name in index.nonlocal_decls.get(id(cur), ()):
        return _rd29_nonlocal_hop(cur, index)
    return None
def _rd29_visible_scope(cur: ast.AST | None, in_function: bool,
                        index: _RD29ScopeIndex) -> ast.AST | None:
    while cur is not None and in_function and isinstance(cur, ast.ClassDef):
        cur = index.parent.get(id(cur))
    return cur
def _rd29_binding_scope(name: str, scope: ast.AST, index: _RD29ScopeIndex) -> ast.AST:
    cur: ast.AST | None = scope
    in_function = isinstance(scope, _RD29_CALLABLE_SCOPES)
    while cur is not None:
        cur = _rd29_visible_scope(cur, in_function, index)
        if cur is None:
            break
        hop = _rd29_decl_hop(name, cur, index)
        if hop is not None and hop is not cur:
            cur, in_function = hop, True
            continue
        if name in index.scope_binds.get(id(cur), ()):
            return cur
        in_function = in_function or isinstance(cur, _RD29_CALLABLE_SCOPES)
        cur = index.parent.get(id(cur))
    return index.tree
class _DBConnectResolver(NamedTuple):
    index: _RD29ScopeIndex
    import_sources: dict
    modules: frozenset[str]
def _make_db_connect_resolver(tree: ast.AST, modules) -> _DBConnectResolver:
    index = _build_rd29_scope_index(tree)
    return _DBConnectResolver(
        index, _rd29_import_sources_by_scope(tree, index), frozenset(modules))
def _driver_connect_call(node: ast.AST,
                         resolver: _DBConnectResolver) -> bool:
    if not isinstance(node, ast.Call):
        return False
    target = _rd29_imported_target(
        node, resolver.import_sources, resolver.index)
    if target is not None:
        module, attr = target
        return attr == "connect" and module in resolver.modules
    func = node.func
    if not (isinstance(func, ast.Attribute) and func.attr == "connect"
            and isinstance(func.value, ast.Name)):
        return False
    base = func.value.id
    scope = _rd29_binding_scope(
        base, _rd29_nearest_scope_in(
            node, resolver.index.parent, resolver.index.scope_ids,
            resolver.index.tree), resolver.index)
    if base in resolver.index.scope_binds.get(id(scope), ()):
        return False
    return base in resolver.modules
_RD29_SELF_BASES = frozenset({"self", "cls"})
def _rd29_nearest_class(node: ast.AST, index: _RD29ScopeIndex) -> ast.AST | None:
    cur = index.parent.get(id(node))
    while cur is not None:
        if isinstance(cur, ast.ClassDef):
            return cur
        cur = index.parent.get(id(cur))
    return None
def _rd29_dotted_owner(dotted: str, node: ast.AST,
                       index: _RD29ScopeIndex) -> int:
    base = dotted.split(".", 1)[0]
    if base in _RD29_SELF_BASES:
        cls = _rd29_nearest_class(node, index)
        if cls is not None:
            return id(cls)
    return id(_rd29_binding_scope(
        base, _rd29_evaluation_scope(node, index), index))
def _rd29_dotted_identity(dotted: str) -> str:
    base, sep, rest = dotted.partition(".")
    if sep and base in _RD29_SELF_BASES:
        return f"<class>.{rest}"
    return dotted
def _rd29_collect_scope_ids(tree: ast.AST) -> set[int]:
    return {id(tree)} | {
        id(node) for node in walk_nodes(tree)
        if isinstance(node, (*_RD29_CALLABLE_SCOPES, ast.ClassDef))
    }
def _rd29_node_position(node: ast.AST,
                        index: _RD29ScopeIndex) -> tuple[int, int]:
    cur: ast.AST | None = node
    while cur is not None:
        line = getattr(cur, "lineno", None)
        if isinstance(line, int):
            return line, getattr(cur, "col_offset", 0)
        cur = index.parent.get(id(cur))
    return 0, 0
class _RD29BindCollector:
    def __init__(self, tree: ast.AST, parent: dict, scope_ids: set) -> None:
        self._tree = tree
        self._parent = parent
        self._scope_ids = scope_ids
        self.scope_binds: dict[int, set[str]] = {}
        self.global_decls: dict[int, set[str]] = {}
        self.nonlocal_decls: dict[int, set[str]] = {}
        self.binding_events: list[tuple] = []
    def feed(self, node: ast.AST) -> None:
        self._feed_binding_event(node)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            self._feed_def_name(node)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            self._feed_args(node)
            return
        if isinstance(node, (ast.Global, ast.Nonlocal)):
            self._feed_decl(node)
            return
        if isinstance(node, (ast.Import, ast.ImportFrom, ast.ExceptHandler)):
            self._feed_scoped_name(node)
            return
        if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                             ast.NamedExpr)):
            self._feed_assign(node)
            return
        if isinstance(node, (ast.With, ast.AsyncWith, ast.For, ast.AsyncFor,
                             ast.comprehension)):
            self._feed_target_owner(node)
            return
        if isinstance(node, ast.Match):
            self._feed_match(node)
    def _event_position(self, node: ast.AST) -> tuple[int, int]:
        cur: ast.AST | None = node
        while cur is not None:
            line = getattr(cur, "lineno", None)
            if isinstance(line, int):
                return line, getattr(cur, "col_offset", 0)
            cur = self._parent.get(id(cur))
        return 0, 0
    def _feed_binding_event(self, node: ast.AST) -> None:
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            scope = _rd29_nearest_scope_in(
                node, self._parent, self._scope_ids, self._tree)
            for name, source in _rd29_iter_import_bindings(node):
                self.binding_events.append((
                    name, scope, self._event_position(node), source, None))
            return
        if isinstance(node, ast.AnnAssign) and node.value is None:
            return
        names: set[str] = set()
        collect_binding_names(node, names, include_imports=False)
        if not names:
            return
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda)):
            anchor = self._parent.get(id(node)) or node
        else:
            anchor = node
        scope = _rd29_nearest_scope_in(
            anchor, self._parent, self._scope_ids, self._tree,
            skip_comprehensions=isinstance(node, ast.NamedExpr))
        value = (node.value if isinstance(
            node, (ast.Assign, ast.AnnAssign, ast.AugAssign, ast.NamedExpr))
            else None)
        position = self._event_position(node)
        for name in names:
            self.binding_events.append((
                name, scope, position, None, value))
    def _feed_match(self, node: ast.Match) -> None:
        scope = _rd29_nearest_scope_in(
            node, self._parent, self._scope_ids, self._tree)
        for case in node.cases:
            for name in iter_pattern_capture_names(case.pattern):
                self._bind(scope, name)
    def _bind(self, scope: ast.AST, name: str) -> None:
        self.scope_binds.setdefault(id(scope), set()).add(name)
    def _bind_target(self, node: ast.AST, target: ast.AST,
                     scope: ast.AST | None = None) -> None:
        if scope is None:
            scope = _rd29_nearest_scope_in(
                node, self._parent, self._scope_ids, self._tree)
        if isinstance(target, ast.Name):
            self._bind(scope, target.id)
        elif isinstance(target, ast.Starred):
            self._bind_target(node, target.value, scope)
        elif isinstance(target, (ast.Tuple, ast.List)):
            for elt in target.elts:
                self._bind_target(node, elt, scope)
    def _feed_def_name(self, node: ast.AST) -> None:
        anchor = self._parent.get(id(node))
        if anchor is not None:
            scope = _rd29_nearest_scope_in(
                anchor, self._parent, self._scope_ids, self._tree)
            self._bind(scope, node.name)
    def _feed_args(self, node: ast.AST) -> None:
        args = node.args
        for arg in (*args.posonlyargs, *args.args, *args.kwonlyargs):
            self._bind(node, arg.arg)
        if args.vararg:
            self._bind(node, args.vararg.arg)
        if args.kwarg:
            self._bind(node, args.kwarg.arg)
    def _feed_decl(self, node: ast.AST) -> None:
        decls = self.global_decls if isinstance(node, ast.Global) else self.nonlocal_decls
        scope = _rd29_nearest_scope_in(
            node, self._parent, self._scope_ids, self._tree)
        decls.setdefault(id(scope), set()).update(node.names)
    def _feed_scoped_name(self, node: ast.AST) -> None:
        if isinstance(node, ast.ExceptHandler):
            if node.name:
                scope = _rd29_nearest_scope_in(
                    node, self._parent, self._scope_ids, self._tree)
                self._bind(scope, node.name)
        else:
            for alias in node.names:
                if alias.name == "*":
                    continue
                scope = _rd29_nearest_scope_in(
                    node, self._parent, self._scope_ids, self._tree)
                self._bind(scope, alias.asname or alias.name.split(".")[0])
    def _feed_assign(self, node: ast.AST) -> None:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                self._bind_target(node, target)
            return
        frame = (_rd29_nearest_scope_in(
            node, self._parent, self._scope_ids, self._tree,
            skip_comprehensions=True)
            if isinstance(node, ast.NamedExpr) else None)
        self._bind_target(node, node.target, frame)
    def _feed_target_owner(self, node: ast.AST) -> None:
        if isinstance(node, (ast.With, ast.AsyncWith)):
            for item in node.items:
                if item.optional_vars is not None:
                    self._bind_target(node, item.optional_vars)
        else:
            self._bind_target(node, node.target)
def _rd29_callable_definition_scope(
        name: str, definition: ast.AST, index: _RD29ScopeIndex,
) -> ast.AST:
    anchor = index.parent.get(id(definition))
    if anchor is None:
        return index.tree
    if isinstance(definition, ast.Lambda):
        while (anchor is not None and not isinstance(
                anchor, (ast.Assign, ast.AnnAssign, ast.NamedExpr))):
            anchor = index.parent.get(id(anchor))
        if anchor is None:
            return index.tree
        raw_scope = _rd29_assignment_scope(anchor, index)
    else:
        raw_scope = _rd29_nearest_scope_in(
            anchor, index.parent, index.scope_ids, index.tree)
    return _rd29_binding_scope(name, raw_scope, index)



def _rd29_reference_definitions(
        name: str, definitions: list[ast.AST], ref: ast.AST,
        index: _RD29ScopeIndex,
) -> list[ast.AST]:
    evaluation_scope = _rd29_evaluation_scope(ref, index)
    reference_scope = _rd29_binding_scope(name, evaluation_scope, index)
    candidates = [
        definition for definition in definitions
        if (_rd29_callable_definition_scope(name, definition, index)
            is reference_scope)
    ]
    if (evaluation_scope is not reference_scope
            and isinstance(evaluation_scope, _RD29_FUNCTION_SCOPES)):
        return candidates
    ref_pos = _rd29_node_position(ref, index)
    prior = [
        definition for definition in candidates
        if _rd29_node_position(definition, index) <= ref_pos
    ]
    if not prior:
        return []
    latest_pos = max(_rd29_node_position(definition, index)
                     for definition in prior)
    return [definition for definition in prior
            if _rd29_node_position(definition, index) == latest_pos]


def _rd29_referenced_callable_sites(
        tree: ast.AST, parent: dict, index: _RD29ScopeIndex,
) -> dict[int, tuple[tuple[int, int], ...]]:
    named_definitions: dict[str, list[ast.AST]] = {}
    class_definitions: dict[str, list[ast.ClassDef]] = {}
    lambdas: list[ast.Lambda] = []
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            named_definitions.setdefault(node.name, []).append(node)
        elif isinstance(node, ast.ClassDef):
            class_definitions.setdefault(node.name, []).append(node)
        elif isinstance(node, ast.Lambda):
            lambdas.append(node)
        elif (isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr))
              and isinstance(node.value, ast.Lambda)):
            targets = (node.targets if isinstance(node, ast.Assign)
                       else [node.target])
            for target in targets:
                if isinstance(target, ast.Name):
                    named_definitions.setdefault(target.id, []).append(node.value)
    referenced: dict[int, list[tuple[int, int]]] = {}
    indirect_callers: dict[int, set[int]] = {}

    def record_reference(definition: ast.AST, ref: ast.AST) -> None:
        definition_scope = _rd29_nearest_scope_in(
            parent.get(id(definition)), parent, index.scope_ids, index.tree)
        reference_scope = _rd29_evaluation_scope(ref, index)
        if (reference_scope is not definition_scope
                and isinstance(reference_scope, _RD29_FUNCTION_SCOPES)):
            indirect_callers.setdefault(id(definition), set()).add(
                id(reference_scope))
            return
        referenced.setdefault(id(definition), []).append(node_position(ref))

    for node in lambdas:
        callable_node: ast.AST = node
        owner = parent.get(id(callable_node))
        while isinstance(owner, ast.NamedExpr) and owner.value is callable_node:
            callable_node = owner
            owner = parent.get(id(callable_node))
        if isinstance(owner, ast.Call) and owner.func is callable_node:
            referenced.setdefault(id(node), []).append(node_position(owner))
    for ref in walk_nodes(tree):
        if not isinstance(ref, ast.Name) or not isinstance(ref.ctx, ast.Load):
            continue
        owner = parent.get(id(ref))
        if not (isinstance(owner, ast.Call) and owner.func is ref):
            continue
        definitions = _rd29_reference_definitions(
            ref.id, named_definitions.get(ref.id, ()), ref, index)
        for definition in definitions:
            cur: ast.AST | None = ref
            while cur is not None and cur is not definition:
                cur = parent.get(id(cur))
            if cur is None:
                record_reference(definition, ref)
    for ref in walk_nodes(tree):
        if not (isinstance(ref, ast.Call)
                and isinstance(ref.func, ast.Attribute)):
            continue
        receiver = ref.func.value
        if (isinstance(receiver, ast.Call)
                and isinstance(receiver.func, ast.Name)):
            class_name = receiver.func.id
        elif isinstance(receiver, ast.Name):
            class_name = receiver.id
        else:
            continue
        classes = _rd29_reference_definitions(
            class_name, class_definitions.get(class_name, ()), ref, index)
        for cls in classes:
            for definition in cls.body:
                if (not isinstance(definition,
                                   (ast.FunctionDef, ast.AsyncFunctionDef))
                        or definition.name != ref.func.attr):
                    continue
                cur: ast.AST | None = ref
                while cur is not None and cur is not definition:
                    cur = parent.get(id(cur))
                if cur is None:
                    record_reference(definition, ref)
    positions_by_scope = {
        scope_id: set(positions)
        for scope_id, positions in referenced.items()
    }
    changed = True
    while changed:
        changed = False
        for scope_id, caller_ids in indirect_callers.items():
            positions = positions_by_scope.setdefault(scope_id, set())
            inherited = {
                position
                for caller_id in caller_ids
                for position in positions_by_scope.get(caller_id, ())
            }
            if inherited - positions:
                positions.update(inherited)
                changed = True
    return {
        scope_id: tuple(sorted(positions))
        for scope_id, positions in positions_by_scope.items()
        if positions
    }
def _rd29_unreferenced_nested_cleanup(assign_scope: ast.AST | None,
                                      closed_scope: ast.AST,
                                      index: _RD29ScopeIndex) -> bool:
    if (assign_scope is None or closed_scope is assign_scope
            or not isinstance(closed_scope, _RD29_FUNCTION_SCOPES)
            or id(closed_scope) in index.referenced_scope_ids):
        return False
    cur: ast.AST | None = closed_scope
    while cur is not None:
        if cur is assign_scope:
            return True
        cur = index.parent.get(id(cur))
    return False
def _build_rd29_scope_index(tree: ast.AST) -> _RD29ScopeIndex:
    parent = build_parent_map(tree)
    scope_ids = _rd29_collect_scope_ids(tree)
    collector = _RD29BindCollector(tree, parent, scope_ids)
    for node in walk_nodes(tree):
        collector.feed(node)
    binding_events: dict[int, dict[str, list[tuple]]] = {}
    index = _RD29ScopeIndex(
        tree=tree, parent=parent, scope_ids=scope_ids,
        scope_binds=collector.scope_binds,
        global_decls=collector.global_decls,
        nonlocal_decls=collector.nonlocal_decls,
        binding_events=binding_events,
        referenced_scope_ids=frozenset(),
        referenced_scope_positions={},
    )
    for name, raw_scope, position, source, value in collector.binding_events:
        scope = _rd29_binding_scope(name, raw_scope, index)
        events = binding_events.setdefault(id(scope), {}).setdefault(name, [])
        events.append((position, source, value))
    for by_name in binding_events.values():
        for events in by_name.values():
            events.sort(key=lambda event: event[0])
    referenced_scope_positions = _rd29_referenced_callable_sites(
        tree, parent, index)
    return index._replace(
        referenced_scope_ids=frozenset(referenced_scope_positions),
        referenced_scope_positions=referenced_scope_positions,
    )
def _rd29_rebind_targets(node: ast.AST) -> list[ast.AST]:
    if isinstance(node, ast.Assign):
        return list(node.targets)
    if isinstance(node, ast.AnnAssign):
        return [node.target] if node.value is not None else []
    if isinstance(node, (ast.AugAssign, ast.NamedExpr, ast.Delete)):
        return [node.target] if not isinstance(node, ast.Delete) else list(node.targets)
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return [item.optional_vars for item in node.items
                if item.optional_vars is not None]
    if isinstance(node, (ast.For, ast.AsyncFor, ast.comprehension)):
        return [node.target]
    return []
def _rd29_is_self_rebind(node: ast.AST, target: ast.AST) -> bool:
    if not isinstance(node, (ast.Assign, ast.AnnAssign)) or node.value is None:
        return False
    target_name = dotted_name(target)
    return bool(target_name) and target_name == dotted_name(node.value)
def _rd29_is_self_rebind_value(value: ast.AST | None, target: ast.AST) -> bool:
    if value is None:
        return False
    target_name = dotted_name(target)
    return bool(target_name) and target_name == dotted_name(value)
def _rd29_rebound_names(node: ast.AST):
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        for alias in node.names:
            if alias.name != "*":
                yield alias.asname or alias.name.split(".")[0], False
    elif isinstance(node, ast.ExceptHandler):
        if node.name:
            yield node.name, False
    elif isinstance(node, ast.Match):
        for case in node.cases:
            for name in iter_pattern_capture_names(case.pattern):
                yield name, False
    elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        yield node.name, True
def _rd29_iter_target_leaves(target: ast.AST):
    if isinstance(target, ast.Starred):
        yield from _rd29_iter_target_leaves(target.value)
    elif isinstance(target, (ast.Tuple, ast.List)):
        for elt in target.elts:
            yield from _rd29_iter_target_leaves(elt)
    else:
        yield target
def _rd29_returned_elements(value: ast.AST | None) -> Iterator[ast.AST]:
    value = _rd29_unwrap_await(value)
    if value is None:
        return
    if isinstance(value, ast.IfExp):
        yield from _rd29_returned_elements(value.body)
        yield from _rd29_returned_elements(value.orelse)
        return
    if isinstance(value, ast.BoolOp):
        for branch in value.values:
            yield from _rd29_returned_elements(branch)
        return
    if isinstance(value, ast.NamedExpr):
        yield from _rd29_returned_elements(value.target)
        yield from _rd29_returned_elements(value.value)
        return
    if isinstance(value, (ast.Tuple, ast.List, ast.Set)):
        for element in value.elts:
            yield from _rd29_returned_elements(element)
        return
    if isinstance(value, ast.Dict):
        for key, sub_value in zip(value.keys, value.values, strict=True):
            if key is not None:
                yield from _rd29_returned_elements(key)
            yield from _rd29_returned_elements(sub_value)
        return
    if isinstance(value, _RD29_COMPREHENSION_SCOPES):
        if isinstance(value, ast.DictComp):
            yield from _rd29_returned_elements(value.key)
            yield from _rd29_returned_elements(value.value)
        else:
            yield from _rd29_returned_elements(value.elt)
        return
    yield value
def _rd29_returned_targets(value: ast.AST | None) -> Iterator[ast.AST]:
    for element in _rd29_returned_elements(value):
        if isinstance(element, (ast.Name, ast.Attribute)):
            yield element
class _RD29EvidenceCollector:
    def __init__(self, resolver: _DBConnectResolver, closing_names: set) -> None:
        self._index = resolver.index
        self._connect_resolver = resolver
        self._closing_names = closing_names
        self.connect_nodes: list[ast.Call] = []
        self.with_managed_conn_ids: set[int] = set()
        self.closed_dotted: list[tuple[int, str, ast.AST, int]] = []
        self.closed_simple: list[tuple[str, ast.AST, int]] = []
        self.conn_assign_targets: dict[int, list[tuple[str, int]]] = {}
        self.conn_assign_scope: dict[int, ast.AST] = {}
        self.rebind_events: list[tuple[str, int, ast.AST, int]] = []
    def feed(self, node: ast.AST) -> None:
        self._feed_rebind(node)
        if isinstance(node, ast.Call):
            self._feed_call(node)
        elif isinstance(node, (ast.With, ast.AsyncWith)):
            self._feed_with(node)
        elif isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
            self._feed_assign(node)
        elif isinstance(node, (ast.Return, ast.Lambda)):
            self._feed_transfer(node)
    def _feed_transfer(self, node: ast.AST) -> None:
        value = node.body if isinstance(node, ast.Lambda) else node.value
        self._mark_direct_conn_returns(value)
        for target in _rd29_returned_targets(value):
            self._record_managed_name(
                target, node, self.closed_dotted, self.closed_simple,
                scope_anchor=target)
    def _mark_direct_conn_returns(self, value: ast.AST | None) -> None:
        for element in _rd29_returned_elements(value):
            if isinstance(element, ast.Call) and _rd29_is_conn_call(element, self._connect_resolver):
                self.with_managed_conn_ids.add(id(element))
    def finish(self) -> _RD29Evidence:
        return _RD29Evidence(
            connect_nodes=self.connect_nodes,
            with_managed_conn_ids=self.with_managed_conn_ids,
            closed_dotted=self.closed_dotted,
            closed_simple=self.closed_simple,
            conn_assign_targets=self.conn_assign_targets,
            conn_assign_scope=self.conn_assign_scope,
            rebind_events=self.rebind_events,
        )
    def _feed_rebind(self, node: ast.AST) -> None:
        if isinstance(node, ast.Assign):
            # 并行元组/列表解包（如 ``conn, cur = conn, conn.cursor()``）必须
            # 逐元素判断自赋值：整体 target/value 的 dotted_name 恒为空，
            # 旧逻辑会把 ``conn`` 误记为重绑定，导致其后的 close() 证据失效。
            for target in node.targets:
                unpacked = _unpack_pairs(target, node.value)
                if unpacked:
                    for sub_target, sub_value in unpacked:
                        for leaf in _rd29_iter_target_leaves(sub_target):
                            if _rd29_is_self_rebind_value(sub_value, leaf):
                                continue
                            self._record_rebind_target(leaf, node)
                    continue
                for leaf in _rd29_iter_target_leaves(target):
                    if _rd29_is_self_rebind(node, leaf):
                        continue
                    self._record_rebind_target(leaf, node)
        else:
            for target in _rd29_rebind_targets(node):
                for leaf in _rd29_iter_target_leaves(target):
                    if _rd29_is_self_rebind(node, leaf):
                        continue
                    self._record_rebind_target(leaf, node)
        for name, enclosing in _rd29_rebound_names(node):
            self._record_rebind_name(name, node, enclosing=enclosing)
    def _record_rebind_target(self, target: ast.AST, node: ast.AST) -> None:
        dn = dotted_name(target)
        if not dn:
            return
        owner = _rd29_dotted_owner(dn, target, self._index)
        self.rebind_events.append((
            _rd29_dotted_identity(dn), owner,
            _rd29_assignment_scope(node, self._index),
            _rd29_node_position(node, self._index)))
    def _record_rebind_name(self, name: str, node: ast.AST,
                            enclosing: bool = False) -> None:
        anchor = self._index.parent.get(id(node)) if enclosing else node
        scope = (
            _rd29_nearest_scope_in(
                anchor, self._index.parent, self._index.scope_ids,
                self._index.tree)
            if anchor is not None else self._index.tree)
        owner = id(_rd29_binding_scope(name, scope, self._index))
        if name in _RD29_SELF_BASES:
            cls = _rd29_nearest_class(node, self._index)
            if cls is not None:
                owner = id(cls)
        self.rebind_events.append(
            (name, owner, scope, (node.lineno, node.col_offset)))
    def _feed_call(self, node: ast.Call) -> None:
        func = node.func
        if (isinstance(func, ast.Attribute)
                and func.attr in _RD29_CLOSE_METHODS):
            self._feed_close(node, func.value)
        elif _rd29_is_conn_call(node, self._connect_resolver):
            self.connect_nodes.append(node)
    def _feed_close(self, node: ast.Call, target: ast.AST) -> None:
        target = _rd29_unwrap_await(target)
        if isinstance(target, ast.NamedExpr):
            direct = _rd29_unwrap_await(target.value)
            if isinstance(direct, ast.Call) and _rd29_is_conn_call(direct, self._connect_resolver):
                self.with_managed_conn_ids.add(id(direct))
                return
            target = target.target
        if isinstance(target, ast.Call) and _rd29_is_conn_call(target, self._connect_resolver):
            self.with_managed_conn_ids.add(id(target))
            return
        self._record_managed_name(
            target, node, self.closed_dotted, self.closed_simple)
    def _record_managed_name(self, target: ast.AST, node: ast.AST,
                             dotted: list, simple: list, *,
                             scope_anchor: ast.AST | None = None) -> None:
        dn = dotted_name(target)
        if not dn:
            return
        anchor = scope_anchor if scope_anchor is not None else node
        scope = _rd29_evaluation_scope(anchor, self._index)
        if "." in dn:
            dotted.append((_rd29_dotted_owner(dn, anchor, self._index),
                           _rd29_dotted_identity(dn), scope,
                           (node.lineno, node.col_offset)))
            return
        simple.append((dn, scope, (node.lineno, node.col_offset)))
    def _feed_with(self, node: ast.AST) -> None:
        for item in node.items:
            ce = item.context_expr
            if _driver_connect_call(ce, self._connect_resolver):
                self._bind_sqlite_as_target(item, ce, node)
                continue
            self._bind_closing_target(ce, node)
            self._mark_managed_calls(ce)
    def _bind_closing_target(self, ce: ast.AST, node: ast.AST) -> None:
        target = _closing_call_argument(
            ce, self._closing_names, self._connect_resolver)
        if target is None:
            return
        self._record_managed_name(target, node, self.closed_dotted,
                                  self.closed_simple)
    def _bind_sqlite_as_target(self, item: ast.withitem, ce: ast.AST,
                               node: ast.AST) -> None:
        if item.optional_vars is None:
            return
        if not _rd29_record_target(self.conn_assign_targets, id(ce),
                                   item.optional_vars, self._index):
            return
        self.conn_assign_scope.setdefault(
            id(ce), _rd29_nearest_scope_in(
                node, self._index.parent, self._index.scope_ids,
                self._index.tree))
    def _mark_managed_calls(self, ce: ast.AST) -> None:
        target = _rd29_unwrap_closing(
            ce, self._closing_names, self._connect_resolver)
        if isinstance(target, ast.Call) and _rd29_is_conn_call(target, self._connect_resolver):
            self.with_managed_conn_ids.add(id(target))
    def _feed_assign(self, node: ast.AST) -> None:
        value = _rd29_unwrap_await(node.value)
        if isinstance(value, ast.Call) and _rd29_is_conn_call(value, self._connect_resolver):
            targets = (node.targets if isinstance(node, ast.Assign)
                       else [node.target])
            if self._record_targets(value, targets):
                self.conn_assign_scope[id(value)] = _rd29_assignment_scope(
                    node, self._index)
            return
        if isinstance(node, ast.Assign):
            self._feed_unpacked_assign(node, value)
    def _feed_unpacked_assign(self, node: ast.Assign,
                              value: ast.AST | None) -> None:
        for target in node.targets:
            for sub_target, sub_value in _unpack_pairs(target, value):
                call = _rd29_unwrap_await(sub_value)
                if not (isinstance(call, ast.Call)
                        and _rd29_is_conn_call(call, self._connect_resolver)):
                    continue
                if _rd29_record_target(self.conn_assign_targets, id(call),
                                       sub_target, self._index):
                    self.conn_assign_scope.setdefault(
                        id(call), _rd29_assignment_scope(node, self._index))
    def _record_targets(self, value: ast.Call, targets: list[ast.AST]) -> bool:
        named = False
        for target in targets:
            if _rd29_record_target(self.conn_assign_targets, id(value),
                                   target, self._index):
                named = True
        return named
def _rd29_assignment_scope(node: ast.AST,
                           index: _RD29ScopeIndex) -> ast.AST:
    if isinstance(node, ast.NamedExpr):
        return _rd29_nearest_scope_in(
            node, index.parent, index.scope_ids, index.tree,
            skip_comprehensions=True)
    return _rd29_nearest_scope_in(
        node, index.parent, index.scope_ids, index.tree)
def _rd29_record_target(targets: dict[int, list[tuple[str, int]]],
                        call_id: int, target: ast.AST,
                        index: _RD29ScopeIndex) -> bool:
    dn = dotted_name(target)
    if not dn:
        return False
    targets.setdefault(call_id, []).append(
        (_rd29_dotted_identity(dn), _rd29_dotted_owner(dn, target, index)))
    return True
def _collect_rd29_evidence(resolver: _DBConnectResolver,
                           closing_names: set) -> _RD29Evidence:
    collector = _RD29EvidenceCollector(resolver, closing_names)
    for node in walk_nodes(resolver.index.tree):
        collector.feed(node)
    return collector.finish()
def _rd29_has_close_evidence(conn_node: ast.Call, ev: _RD29Evidence,
                             index: _RD29ScopeIndex) -> bool:
    assign_scope = ev.conn_assign_scope.get(id(conn_node))
    conn_pos = (conn_node.lineno, conn_node.col_offset)
    for name, owner in ev.conn_assign_targets.get(id(conn_node)) or []:
        if "." in name:
            if _rd29_dotted_closed(
                    name, owner, ev, conn_pos, assign_scope, index):
                return True
        elif _rd29_simple_closed(name, assign_scope, ev, index, conn_pos):
            return True
    return False
def _rd29_dotted_rebound_between(name: str, owner: int,
                                 ev: _RD29Evidence, conn_pos: tuple[int, int],
                                 closed_pos: tuple[int, int]) -> bool:
    base = name.partition(".")[0]
    root_names = _RD29_SELF_BASES if base == "<class>" else {base}
    return any(
        rebind_owner == owner
        and (rebind_name == name or rebind_name in root_names
             or name.startswith(rebind_name + "."))
        and conn_pos < rebind_pos < closed_pos
        for rebind_name, rebind_owner, _scope, rebind_pos in ev.rebind_events
    )
def _rd29_close_positions(closed_scope: ast.AST,
                          closed_pos: tuple[int, int],
                          assign_scope: ast.AST | None,
                          index: _RD29ScopeIndex,
                          ) -> tuple[tuple[int, int], ...]:
    if (closed_scope is not assign_scope
            and isinstance(closed_scope, _RD29_FUNCTION_SCOPES)):
        positions = index.referenced_scope_positions.get(id(closed_scope))
        if positions:
            return positions
    return (closed_pos,)
def _rd29_dotted_closed(name: str, owner: int, ev: _RD29Evidence,
                        conn_pos: tuple[int, int], assign_scope: ast.AST | None,
                        index: _RD29ScopeIndex) -> bool:
    for closed_owner, closed_name, closed_scope, closed_pos in ev.closed_dotted:
        if closed_owner != owner or closed_name != name:
            continue
        if _rd29_unreferenced_nested_cleanup(assign_scope, closed_scope, index):
            continue
        for effective_pos in _rd29_close_positions(
                closed_scope, closed_pos, assign_scope, index):
            if effective_pos < conn_pos:
                continue
            if _rd29_dotted_rebound_between(
                    name, owner, ev, conn_pos, effective_pos):
                continue
            return True
    return False
def _rd29_simple_rebound_between(name: str, bind_scope: ast.AST,
                                 assign_scope: ast.AST, closed_scope: ast.AST,
                                 ev: _RD29Evidence, index: _RD29ScopeIndex,
                                 conn_pos: tuple[int, int],
                                 closed_pos: tuple[int, int]) -> bool:
    for rebind_name, _owner, scope, pos in ev.rebind_events:
        if rebind_name != name or pos <= conn_pos:
            continue
        if _rd29_binding_scope(name, scope, index) is not bind_scope:
            continue
        if pos >= closed_pos:
            continue
        return True
    return False
def _rd29_simple_closed(name: str, assign_scope: ast.AST,
                        ev: _RD29Evidence, index: _RD29ScopeIndex,
                        conn_pos: tuple[int, int]) -> bool:
    bind_scope = _rd29_binding_scope(name, assign_scope, index)
    for closed_name, closed_scope, closed_pos in ev.closed_simple:
        if closed_name != name:
            continue
        if _rd29_unreferenced_nested_cleanup(assign_scope, closed_scope, index):
            continue
        if _rd29_binding_scope(closed_name, closed_scope, index) is not bind_scope:
            continue
        for effective_pos in _rd29_close_positions(
                closed_scope, closed_pos, assign_scope, index):
            if effective_pos < conn_pos:
                continue
            if _rd29_simple_rebound_between(
                    name, bind_scope, assign_scope, closed_scope, ev, index,
                    conn_pos, effective_pos):
                continue
            return True
    return False
def _rd29_finding(method: str, conn_node: ast.Call, filepath: Any) -> FindingRecord:
    return db_finding(
        "RD-29", "P1", conn_node.lineno, filepath,
        title=f"数据库连接泄漏风险: {method}()无with上下文或.close()管理证据",
        description=f"数据库连接 {method}() 创建后未被 with/async with 上下文表达式托管, "
                    f"也未检测到赋值目标对应变量的 .close() 调用, "
                    f"异常路径下可能导致连接泄漏",
        suggestion=(
            "根因: 数据库连接创建后无管理证据(未在 with 上下文中创建, 也未显式 .close()), "
            "异常路径下连接不会被释放, 长期运行导致连接池耗尽。\n"
            "修复策略(按优先级):\n"
            "1. with语句(首选):\n"
            "   with contextlib.closing(sqlite3.connect('db.db')) as conn:\n"
            "       cursor = conn.cursor()\n"
            "       cursor.execute('SELECT 1')\n"
            "   注意: with sqlite3.connect() 管理的是事务而非连接关闭,\n"
            "   须以 contextlib.closing 包裹(或用连接池引擎的 with engine.connect())\n"
            "2. try-finally(兼容旧代码):\n"
            "   conn = sqlite3.connect('db.db')\n"
            "   try:\n"
            "       cursor = conn.cursor()\n"
            "       cursor.execute('SELECT 1')\n"
            "   finally:\n"
            "       conn.close()\n"
            "3. 连接池(生产环境): 使用SQLAlchemy的create_engine(pool_size=10)自动管理连接生命周期\n"
            "4. 上下文管理器装饰器: 使用 @contextmanager 封装连接获取/释放逻辑\n"
            "参考: CWE-404 (Resource Exhaustion) / PEP 343 (with语句)"
        ),
    )
def check_RD29(tree: Any, source_lines: Any, filepath: Any) -> list[FindingRecord]:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    index = _build_rd29_scope_index(tree)
    import_sources = _rd29_import_sources_by_scope(tree, index)
    resolver = _DBConnectResolver(index, import_sources, _SQLITE_CONNECT_MODULES)
    ev = _collect_rd29_evidence(resolver, _closing_channel_names(tree))
    if not ev.connect_nodes:
        return issues
    local_defs = _rd29_local_conn_defs_by_scope(
        tree, index, import_sources)
    for conn_node in ev.connect_nodes:
        if id(conn_node) in ev.with_managed_conn_ids:
            continue
        local_verdict = _rd29_local_conn_def_verdict(
            conn_node, local_defs, index)
        if local_verdict is False:
            continue
        if local_verdict is not True and _db_shadowed_import(conn_node, resolver):
            continue
        if _rd29_is_imported_non_db_call(
                conn_node, filepath, import_sources, index):
            continue
        if _rd29_has_close_evidence(conn_node, ev, index):
            continue
        issues.append(_rd29_finding(connection_call_name(conn_node), conn_node, filepath))
    if issues:
        _log.debug("[RD-29] connection_leak 命中 %d 处: %s", len(issues), filepath)
    return issues
def _db06_connect_bindings(
        child: Any, resolver: _DBConnectResolver,
) -> list[tuple[ast.Name, ast.AST]]:
    if isinstance(child, ast.Assign):
        if _driver_connect_call(child.value, resolver):
            return [(target, child.value) for target in child.targets
                    if isinstance(target, ast.Name)]
        bindings = []
        for target in child.targets:
            for sub_target, sub_value in _unpack_pairs(target, child.value):
                if (isinstance(sub_target, ast.Name)
                        and _driver_connect_call(sub_value, resolver)):
                    bindings.append((sub_target, sub_value))
        return bindings
    if (isinstance(child, (ast.AnnAssign, ast.NamedExpr))
            and isinstance(child.target, ast.Name)
            and _driver_connect_call(child.value, resolver)):
        return [(child.target, child.value)]
    return []
def _db06_function_connections(
        node: Any, resolver: _DBConnectResolver,
) -> dict[ast.Call, list[str]]:
    connections: dict[ast.Call, list[str]] = {}
    for child in walk_stmts(node.body):
        for target, connect_call in _db06_connect_bindings(child, resolver):
            connections.setdefault(connect_call, []).append(target.id)
        if not isinstance(child, ast.With):
            continue
        for item in child.items:
            connect_call = item.context_expr
            if not _driver_connect_call(connect_call, resolver):
                continue
            target = item.optional_vars
            name = target.id if isinstance(target, ast.Name) else '<anonymous>'
            connections.setdefault(connect_call, []).append(name)
    return connections

def check_DB06(tree: Any, source: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    _log.debug("规则入口 check_DB06 执行")
    issues: list[dict[str, Any]] = []
    if tree is None:
        return issues
    resolver = _make_db_connect_resolver(tree, _SQLITE_CONNECT_MODULES)
    evidence = _collect_rd29_evidence(resolver, _closing_channel_names(tree))
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            issues.extend(_db06_function_issues(
                node, source, filepath, resolver, evidence))
    return issues

def _db06_function_issues(
        node: Any, source: Any, filepath: Any,
        resolver: _DBConnectResolver, evidence: _RD29Evidence,
) -> list[dict[str, Any]]:
    connections = _db06_function_connections(node, resolver)
    issues: list[dict[str, Any]] = []
    for connect_call, names in connections.items():
        if id(connect_call) in evidence.with_managed_conn_ids:
            continue
        if _rd29_has_close_evidence(connect_call, evidence, resolver.index):
            continue
        issues.append(_db06_make_issue(
            names[0], connect_call.lineno, source, filepath))
    return issues

def _db06_code_snippet(source: Any, lineno: int, context: int = 2) -> str:
    if isinstance(source, str):
        lines = aligned_source_lines(source)
    elif isinstance(source, (list, tuple)):
        lines = source
    else:
        return ""
    if not 1 <= lineno <= len(lines):
        return ""
    start = max(0, lineno - context - 1)
    end = min(len(lines), lineno + context)
    return "\n".join(
        f"{'>>>' if idx == lineno - 1 else '   '} {idx + 1}: {str(lines[idx]).rstrip()}"
        for idx in range(start, end)
    )
def _db06_make_issue(var_name: str, lineno: int, source: Any,
                     filepath: Any) -> dict[str, Any]:
    return {
        "rule_id": "DB-06", "severity": "P1", "dimension": "database",
        "file": filepath, "line": lineno,
        "message": f"sqlite3.connect() 返回值 '{var_name}' 未调用 .close()",
        "description": (
            f"第{lineno}行创建的数据库连接 '{var_name}' 在同一作用域内"
            "未调用 .close()，也未通过 contextlib.closing 包装或 return 转交"
            "（sqlite3 的 with 只提交/回滚事务，不关闭连接）。"
            "未关闭的连接可能导致锁竞争和资源泄露。"
        ),
        "code_snippet": _db06_code_snippet(source, lineno),
        "suggestion": ("根因: 数据库连接生命周期未闭合。\n"
                       f"修复策略: 调用 {var_name}.close()（finally 显式关闭或 contextlib.closing 包装；sqlite3 的 with 只提交/回滚事务、不关闭连接）\n"
                       "参考标准: PEP 8 / sqlite3 上下文管理"),
    }
_SQL_CHECKERS = (
    ("RD-29", check_RD29), ("RD-31", check_RD31),
)
def _register_detector_catalogs() -> None:
    register_detector_catalog("diag4_direct", dict(_SQL_CHECKERS))
    register_detector_catalog("rule_bindings", {'DB06': check_DB06})
_register_detector_catalogs()

from __future__ import annotations

import ast
import logging
import re
import string
from collections.abc import Iterator
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_nodes import node_position
from jwsgj.prevention_scope_facts import (
    TRY_NODES,
    assigned_names,
    block_exits,
    bound_names_of,
    definition_outer_node_ids,
    deref_root_name,
    has_starred_arg,
    imported_module_aliases,
    int_literal,
    is_none_constant,
    make_issue,
    nearest_scope,
    parent_map_of,
    preceding_statements,
    prior_statements,
    same_expr,
    scan_body_no_funcs,
    scope_body_stmts,
    scope_local_bindings,
    shadowed_binding_at,
    snippet_of,
    source_lines,
    stmt_siblings,
    subtree_contains,
    target_binding_names,
    walk_ast_nodes,
    walk_nodes,
)

__all__ = [
    'check_LV05',
    'check_LV08',
    'check_LV14',
    'check_LV15',
    'check_LV16',
    'check_LV23',
    'check_LV26',
    'check_LV28',
    'check_LV34',
    'check_LV35',
    'check_LV40',
    'check_LV41',
    'check_LV42',
    'check_LV48',
    'check_LV49',
    'check_LV51',
    'check_LV57',
    'check_LV60',
]
_log = logging.getLogger(__name__)
_log.info("prevention_arg_checks 实参形态与内建调用协议域检测器已加载：%d 项导出", len(__all__))
def _is_path_constructor(node: ast.AST) -> bool:
    if not (isinstance(node, ast.Call) and not node.keywords
            and len(node.args) == 1):
        return False
    func = node.func
    return ((isinstance(func, ast.Name) and func.id == 'Path')
            or (isinstance(func, ast.Attribute) and func.attr == 'Path'))
_ImportEntry = tuple[ast.Import | ast.ImportFrom, ast.alias]
_ImportIndex = dict[int, dict[str, list[_ImportEntry]]]
_IMPORT_SCOPE_NODES = (ast.FunctionDef, ast.AsyncFunctionDef,
                       ast.ClassDef, ast.Lambda)
def _is_pure_annotation_store(
        node: ast.AST, parents: dict[int, ast.AST]) -> bool:
    if not isinstance(node, ast.Name):
        return False
    parent = parents.get(id(node))
    return (isinstance(parent, ast.AnnAssign) and parent.value is None
            and parent.target is node)
def _runtime_bind_counts(
        tree: ast.AST, parents: dict[int, ast.AST]) -> dict[tuple[int, str], int]:
    bind_counts: dict[tuple[int, str], int] = {}
    for node in walk_nodes(tree):
        if _is_pure_annotation_store(node, parents):
            continue
        scope = nearest_scope(parents, node)
        if scope is None:
            continue
        for name in bound_names_of(node):
            key = (id(scope), name)
            bind_counts[key] = bind_counts.get(key, 0) + 1
    return bind_counts
def _import_index(tree: ast.AST,
                  parents: dict[int, ast.AST]) -> _ImportIndex:
    index: _ImportIndex = {}
    for imp in walk_ast_nodes(tree):
        if not isinstance(imp, (ast.Import, ast.ImportFrom)):
            continue
        scope = nearest_scope(parents, imp)
        if scope is None:
            continue
        by_name = index.setdefault(id(scope), {})
        for alias in imp.names:
            if alias.name == '*':
                continue
            bound_name = alias.asname or alias.name.split('.')[0]
            by_name.setdefault(bound_name, []).append((imp, alias))
    return index
def _import_scope_chain(
        node: ast.AST, parents: dict[int, ast.AST],
) -> Iterator[ast.AST]:
    cur = parents.get(id(node))
    in_function = False
    class_checked = False
    while cur is not None:
        if isinstance(cur, _LV05_COMP_SCOPES):
            generators = cur.generators
            if (not generators
                    or not subtree_contains(generators[0].iter, node)):
                in_function = True
        if (isinstance(cur, _IMPORT_SCOPE_NODES)
                and id(node) in definition_outer_node_ids(cur)):
            cur = parents.get(id(cur))
            continue
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda)):
            in_function = True
            yield cur
        elif isinstance(cur, ast.ClassDef):
            if not in_function and not class_checked:
                yield cur
            class_checked = True
        elif isinstance(cur, ast.Module):
            yield cur
            return
        cur = parents.get(id(cur))
def _import_execution_deferred(
        node: ast.AST, scope: ast.AST, parents: dict[int, ast.AST],
) -> bool:
    cur = node
    while cur is not scope:
        parent = parents.get(id(cur))
        if parent is None or parent is scope:
            return False
        if (isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda))
                and id(node) not in definition_outer_node_ids(parent)):
            return True
        if isinstance(parent, ast.GeneratorExp):
            first_iter = parent.generators[0].iter
            if not subtree_contains(first_iter, node):
                return True
        cur = parent
    return False

def _visible_import_origin(
        node: ast.AST, binding: str, parents: dict[int, ast.AST],
        imports: _ImportIndex,
) -> _ImportEntry | None:
    for scope in _import_scope_chain(node, parents):
        entries = imports.get(id(scope), {}).get(binding)
        if not entries:
            continue
        if _import_execution_deferred(node, scope, parents):
            visible_entries = entries
        else:
            visible_entries = [
                entry for entry in entries
                if node_position(entry[0]) < node_position(node)
            ]
        if visible_entries:
            return max(visible_entries,
                       key=lambda entry: node_position(entry[0]))
        if not isinstance(scope, ast.ClassDef):
            return None
    return None
def _import_origin_matches(
        origin: _ImportEntry, module_name: str,
        imported_names: frozenset[str] | set[str] | None = None,
) -> bool:
    imp, alias = origin
    if imported_names is None:
        if not isinstance(imp, ast.Import):
            return False
        return (alias.name == module_name
                or (alias.asname is None
                    and alias.name.startswith(module_name + '.')))
    return (isinstance(imp, ast.ImportFrom) and not imp.level
            and imp.module == module_name and alias.name in imported_names)
def _visible_pathlib_constructor(
        node: ast.AST, parents: dict[int, ast.AST],
        imports: _ImportIndex, shadow_cache: dict[tuple, set[str]],
) -> bool:
    if not isinstance(node, ast.Call) or node.keywords:
        return False
    func = node.func
    if not (isinstance(func, ast.Name)
            or (isinstance(func, ast.Attribute) and func.attr == 'Path')):
        return False
    binding = (func.id if isinstance(func, ast.Name)
               else deref_root_name(func.value))
    if (binding is None or shadowed_binding_at(
            node, binding, parents, shadow_cache, include_imports=False)):
        return False
    origin = _visible_import_origin(node, binding, parents, imports)
    if origin is None:
        return False
    if isinstance(func, ast.Name):
        return _import_origin_matches(
            origin, 'pathlib', frozenset({'Path'}))
    return _import_origin_matches(origin, 'pathlib')
def _json_recv_ok(
        node: ast.AST, bare: str | None,
        bare_names: dict[str, str], module_aliases: set) -> bool:
    if bare is not None:
        return bare in bare_names
    recv = node.func.value
    return (isinstance(recv, ast.Name)
            and recv.id in module_aliases)
_LV26_FIRST_PARAMS = {'load': 'fp', 'loads': 's'}
_LV26_JSON_ATTRS = frozenset(_LV26_FIRST_PARAMS)
_LV26_CONSTANT_KINDS: dict[type, str] = {
    str: 'str', bytes: 'bytes', bytearray: 'bytes',
    bool: 'bool', int: 'int', float: 'float', complex: 'complex',
    type(None): 'None',
}
_LITERAL_NODE_KINDS: dict[type[ast.AST], str] = {
    ast.List: 'list', ast.Tuple: 'tuple', ast.Set: 'set', ast.Dict: 'dict',
}
_TEXT_CARRIER_CTORS: dict[str, str] = {
    'str': 'str', 'bytes': 'bytes', 'bytearray': 'bytes',
}
_TEXT_CARRIER_NAMES = frozenset(_TEXT_CARRIER_CTORS)
def _text_carrier_kind(
        node: ast.AST, shadowed: frozenset[str] | set[str] = frozenset(),
) -> str | None:
    if isinstance(node, ast.JoinedStr):
        return 'str'
    if isinstance(node, ast.Constant):
        if isinstance(node.value, str):
            return 'str'
        return 'bytes' if isinstance(node.value, (bytes, bytearray)) else None
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in _TEXT_CARRIER_CTORS
            and node.func.id not in shadowed):
        return _TEXT_CARRIER_CTORS[node.func.id]
    return None
def _fixed_positional_count(call: ast.Call) -> int:
    return sum(not isinstance(arg, ast.Starred) for arg in call.args)
def _json_call_parts(
        node: ast.AST, attrs: frozenset,
        bare_names: dict[str, str]) -> tuple[str, str | None] | None:
    if not isinstance(node, ast.Call):
        return None
    func = node.func
    if isinstance(func, ast.Attribute):
        return (func.attr, None) if func.attr in attrs else None
    if isinstance(func, ast.Name) and func.id in bare_names:
        return bare_names[func.id], func.id
    return None
def _json_bare_names_of(node: ast.AST, attrs: frozenset) -> dict[str, str]:
    imp = _json_from_import(node)
    if imp is None:
        return {}
    return {alias.asname or alias.name: alias.name
            for alias in imp.names if alias.name in attrs}
def _json_from_import(node: ast.AST) -> ast.ImportFrom | None:
    if (isinstance(node, ast.ImportFrom) and node.module == 'json'
            and not node.level):
        return node
    return None
def _json_import_faces(
        tree: ast.AST, attrs: frozenset,
) -> tuple[set[str], dict[str, str]]:
    module_aliases = imported_module_aliases(tree, 'json')
    bare_names: dict[str, str] = {}
    if not isinstance(tree, ast.AST):
        return module_aliases, bare_names
    for node in walk_nodes(tree):
        bare_names.update(_json_bare_names_of(node, attrs))
    return module_aliases, bare_names
def _json_calls(tree: Any, attrs: frozenset) -> Iterator[tuple[ast.Call, str]]:
    module_aliases, bare_names = _json_import_faces(tree, attrs)
    parents = parent_map_of(tree)
    imports = _import_index(tree, parents)
    shadow_cache: dict[tuple, set[str]] = {}
    for node in walk_ast_nodes(tree):
        parts = _json_call_parts(node, attrs, bare_names)
        if parts is None:
            continue
        fname, bare = parts
        if not _json_recv_ok(node, bare, bare_names, module_aliases):
            continue
        binding = bare if bare is not None else node.func.value.id
        if shadowed_binding_at(
            node, binding, parents, shadow_cache, include_imports=False):
            continue
        origin = _visible_import_origin(node, binding, parents, imports)
        if origin is None:
            continue
        if bare is None:
            if not _import_origin_matches(origin, 'json'):
                continue
        else:
            if not _import_origin_matches(origin, 'json', attrs):
                continue
            fname = origin[1].name
        yield node, fname
def _lv26_literal_kind(node: ast.expr) -> str | None:
    if isinstance(node, ast.JoinedStr):
        return 'str'
    for node_type, kind in _LITERAL_NODE_KINDS.items():
        if isinstance(node, node_type):
            return kind
    if not isinstance(node, ast.Constant):
        return None
    if node.value is Ellipsis:
        return 'Ellipsis'
    return _LV26_CONSTANT_KINDS.get(type(node.value), '常量')
def _lv26_read_call(node: ast.expr) -> bool:
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == 'read')
_LV26_FILE_OPEN_MODULES = frozenset({
    'io', 'builtins', 'gzip', 'bz2', 'lzma', 'codecs',
})
def _lv26_open_call(
        node: ast.expr, open_shadowed: bool,
        file_open_modules: frozenset[str] | set[str] = _LV26_FILE_OPEN_MODULES,
        path_open: bool = False,
) -> bool:
    if not isinstance(node, ast.Call):
        return False
    func = node.func
    if isinstance(func, ast.Name):
        return func.id == 'open' and not open_shadowed
    if not (isinstance(func, ast.Attribute) and func.attr == 'open'):
        return False
    receiver = func.value
    if isinstance(receiver, ast.Name):
        return receiver.id in file_open_modules
    return path_open
def _lv26_load_mismatch(
        first: ast.expr, path_constructor: bool = False) -> str:
    kind = _lv26_literal_kind(first)
    if kind is not None:
        return (
            f'json.load 首参为 {kind} 字面量（该类型无 .read()，'
            'load 只消费文件对象；字符串内容用 loads）'
        )
    if _lv26_read_call(first):
        return ('json.load 首参为 .read() 调用——read() 返回 '
                'str，load 只消费文件对象（loads 才消费 str）')
    if path_constructor:
        return ('json.load 首参为 Path 构造调用——Path 无 .read()，'
                'load 只消费文件对象（先 Path.open 取得句柄）')
    return ''
_LV26_TEXT_KINDS = frozenset({'str', 'bytes'})
def _lv26_loads_mismatch(
        first: ast.expr, open_shadowed: bool,
        file_open_modules: frozenset[str] | set[str] = _LV26_FILE_OPEN_MODULES,
        path_constructor: bool = False, path_open: bool = False,
) -> str:
    kind = _lv26_literal_kind(first)
    if kind is not None and kind not in _LV26_TEXT_KINDS:
        return (f'json.loads 首参为 {kind} 字面量——loads 只消费 '
                'str/bytes（该载体不带 JSON 文本，文件对象用 load）')
    if _lv26_open_call(
            first, open_shadowed, file_open_modules, path_open):
        return ('json.loads 首参为文件打开调用——其返回文件对象，'
                'loads 只消费 str/bytes（load 才消费文件对象）')
    if path_constructor:
        return ('json.loads 首参为 Path 构造调用——Path 不是 '
                'str/bytes，loads 只消费 str/bytes（先 Path.read_text）')
    return ''
def _lv26_first_arg(node: ast.Call, param: str) -> ast.expr | None:
    keyword = next((kw.value for kw in node.keywords
                    if kw.arg == param), None)
    if node.args:
        return None if keyword is not None else node.args[0]
    if any(kw.arg is None for kw in node.keywords):
        return None
    return keyword
def check_LV26(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    parents = parent_map_of(tree)
    imports = _import_index(tree, parents)
    shadow_cache: dict[tuple, set[str]] = {}
    file_open_modules = set(_LV26_FILE_OPEN_MODULES)
    for module_name in _LV26_FILE_OPEN_MODULES:
        file_open_modules.update(imported_module_aliases(tree, module_name))
    for node, fname in _json_calls(tree, _LV26_JSON_ATTRS):
        first = _lv26_first_arg(node, _LV26_FIRST_PARAMS[fname])
        if first is None:
            continue
        open_shadowed = shadowed_binding_at(first, 'open', parents, shadow_cache)
        visible_open_modules = set()
        for name in file_open_modules:
            if shadowed_binding_at(
                    first, name, parents, shadow_cache, include_imports=False):
                continue
            origin = _visible_import_origin(first, name, parents, imports)
            if origin is not None and any(
                    _import_origin_matches(origin, module_name)
                    for module_name in _LV26_FILE_OPEN_MODULES):
                visible_open_modules.add(name)
        path_constructor = _visible_pathlib_constructor(
            first, parents, imports, shadow_cache)
        path_open = (
            isinstance(first, ast.Call)
            and isinstance(first.func, ast.Attribute)
            and _visible_pathlib_constructor(
                first.func.value, parents, imports, shadow_cache)
        )
        mismatch = (_lv26_load_mismatch(first, path_constructor)
                    if fname == 'load' else _lv26_loads_mismatch(
                        first, open_shadowed, visible_open_modules,
                        path_constructor, path_open))
        if not mismatch:
            continue
        issues.append(make_issue(
            'LV-26', 'P2', 'logic_correctness', filepath, node.lineno,
            f'json.{fname} 实参形态反转：{mismatch}',
            (
                f'``json.{fname}`` 的实参形态与函数契约相反——'
                f'``json.load(fp)`` 消费文件对象、``json.loads(s)`` 消费'
                f' str/bytes。load 收 str 时无 ``read`` 方法，首调抛 '
                "``AttributeError: 'str' object has no attribute 'read'``；"
                'loads 收文件对象时抛 ``TypeError: the JSON object must '
                'be str, bytes or bytearray``，解析入口当步崩溃。变量'
                '承载形态无静态证据已放行，本命中为字面量/调用形态的'
                '可确证错配。'
            ),
            snippet_of(src_lines, node.lineno),
            (
                '根因：load/loads 语义按字面直觉反记（load=加载字符串\n'
                'loads=加载流是错误直觉；正确口诀——loads 里的 s 是\n'
                '"string"）。\n'
                '修复策略：str 入参用 ``json.loads(text)``；文件对象用\n'
                '``with open(p, encoding="utf-8") as f: json.load(f)``；\n'
                '关键字写法同口径（``load(fp=..)`` / ``loads(s=..)``）。\n'
                '参考标准：Python json.load/json.loads 参数与返回值契约'
            ),
            'json-load-loads-swap',
        ))
    return issues
_LV34_FUNCS = frozenset({'isinstance', 'issubclass'})
def _lv34_arity_not_applicable(node: ast.Call) -> bool:
    return _fixed_positional_count(node) <= 2
def _lv34_candidate(node: ast.AST) -> str | None:
    if not isinstance(node, ast.Call):
        return None
    func = node.func
    if not (isinstance(func, ast.Name) and func.id in _LV34_FUNCS):
        return None
    if _lv34_arity_not_applicable(node):
        return None
    return func.id
def check_LV34(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    parents = parent_map_of(tree)
    shadow_cache: dict[tuple, set[str]] = {}
    for node in roots:
        fname = _lv34_candidate(node)
        if (fname is None or shadowed_binding_at(
                node, fname, parents, shadow_cache)):
            continue
        n = _fixed_positional_count(node)
        at_least = has_starred_arg(node)
        count_text = f'至少 {n}' if at_least else f'{n}'
        issues.append(make_issue(
            'LV-34', 'P1', 'logic_correctness', filepath, node.lineno,
            f'{fname} 位置实参 {count_text} 个：必抛 TypeError（expected 2 arguments）',
            (
                f'``{fname}(x, str, int)`` 形态——{fname} 只接受两个位置'
                f'实参（对象 + 类信息），{count_text} 个固定位置实参在调用时必抛 '
                f'TypeError: {fname} expected 2 arguments, got {count_text}；'
                '关键字与星号展开不改变已经超出的固定位置实参数量；'
                '多类型判断须把类信息打包为元组第二实参。'
            ),
            snippet_of(src_lines, node.lineno),
            (
                '根因：把 isinstance 当作可变参数接口逐个罗列类型。\n'
                '修复策略：多类型传元组——``isinstance(x, (str, int))``；\n'
                'issubclass 同口径 ``issubclass(cls, (A, B))``。\n'
                '参考标准：CPython builtins isinstance/issubclass 参数\n'
                '签名契约（恰好两个位置实参，第二实参接受类型元组）'
            ),
            'isinstance-extra-positional-args',
        ))
    return issues
_LV40_KEYED_FUNCS = frozenset({'sorted', 'max', 'min'})
_LV40_KEYED_METHODS = frozenset({'sort', 'nlargest', 'nsmallest'})
_LV40_NONCALLABLE_RETURNS = frozenset({
    'len', 'any', 'all', 'sorted', 'list', 'set', 'dict', 'tuple',
    'frozenset', 'str', 'int', 'float', 'bool', 'bytes', 'bytearray',
    'hash', 'ord', 'chr', 'repr', 'ascii', 'bin', 'oct', 'hex',
    'format', 'id', 'dir',
})
_LV05_ARITH_OPS = (ast.Add, ast.Sub, ast.Mult, ast.Div,
                   ast.FloorDiv, ast.Mod, ast.Pow, ast.MatMult)
_LV05_UNARY_OPS = (ast.USub, ast.UAdd, ast.Invert)
_LV05_ORDER_OPS = (ast.Lt, ast.LtE, ast.Gt, ast.GtE)
_LV05_COMP_SCOPES = (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
def _lv05_single_get_call(node: ast.AST) -> bool:
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == 'get'
            and 1 <= len(node.args) <= 2
            and not any(isinstance(arg, ast.Starred) for arg in node.args)
            and (len(node.args) == 1 or is_none_constant(node.args[1]))
            and not node.keywords)
def _lv05_isnot_none_guard(expr: ast.Compare, get_call: ast.Call) -> bool:
    if not (len(expr.ops) == 1 and isinstance(expr.ops[0], ast.IsNot)
            and len(expr.comparators) == 1):
        return False
    left, right = expr.left, expr.comparators[0]
    if is_none_constant(right):
        return same_expr(left, get_call)
    if is_none_constant(left):
        return same_expr(right, get_call)
    return False
def _lv05_is_none_guard_for(expr: ast.AST, get_call: ast.Call) -> bool:
    if same_expr(expr, get_call):
        return True
    if isinstance(expr, ast.Compare) and _lv05_isnot_none_guard(expr, get_call):
        return True
    return _lv05_is_isinstance_guard(expr, get_call)
def _lv05_none_safe_type_expr(node: ast.AST) -> bool:
    if isinstance(node, ast.Name):
        return node.id not in {'object', 'NoneType'}
    if isinstance(node, ast.Attribute):
        return node.attr != 'NoneType'
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        return (_lv05_none_safe_type_expr(node.left)
                and _lv05_none_safe_type_expr(node.right))
    return (isinstance(node, ast.Tuple) and bool(node.elts)
            and all(_lv05_none_safe_type_expr(elt) for elt in node.elts))
def _lv05_is_isinstance_guard(expr: ast.AST, get_call: ast.Call) -> bool:
    return (isinstance(expr, ast.Call)
            and isinstance(expr.func, ast.Name)
            and expr.func.id == 'isinstance'
            and len(expr.args) == 2 and not expr.keywords
            and same_expr(expr.args[0], get_call)
            and _lv05_none_safe_type_expr(expr.args[1]))
def _lv05_guard_input_names(get_call: ast.Call) -> set[str]:
    return {node.id for node in walk_nodes(get_call)
            if isinstance(node, ast.Name)}

def _lv05_subscript_writes_guard_value(
        target: ast.AST, get_call: ast.Call,
) -> bool:
    if isinstance(target, (ast.Tuple, ast.List)):
        return any(_lv05_subscript_writes_guard_value(elt, get_call)
                   for elt in target.elts)
    if isinstance(target, ast.Starred):
        return _lv05_subscript_writes_guard_value(target.value, get_call)
    if not isinstance(target, ast.Subscript):
        return False
    return (same_expr(target.value, get_call.func.value)
            and same_expr(target.slice, get_call.args[0]))

def _lv05_statement_writes_guard_value(
        stmt: ast.AST, get_call: ast.Call,
) -> bool:
    if isinstance(stmt, ast.Assign):
        targets = stmt.targets
    elif isinstance(stmt, (ast.AnnAssign, ast.AugAssign)):
        targets = [stmt.target]
    elif isinstance(stmt, ast.Delete):
        targets = stmt.targets
    else:
        return False
    return any(_lv05_subscript_writes_guard_value(target, get_call)
               for target in targets)
def _lv05_expression_rebinds_guard_inputs(
        expression: ast.AST, get_call: ast.Call) -> bool:
    names = _lv05_guard_input_names(get_call)
    rebound = {
        name
        for node in walk_nodes(expression)
        if isinstance(node, ast.NamedExpr)
        for name in target_binding_names(node.target)
    }
    return bool(names & rebound)
def _lv05_fallthrough_rebinds_guard_inputs(
        stmts: list[ast.stmt], get_call: ast.Call) -> bool:
    names = _lv05_guard_input_names(get_call)
    rebound = False
    for stmt in stmts:
        if isinstance(stmt, ast.If):
            rebound |= _lv05_expression_rebinds_guard_inputs(
                stmt.test, get_call)
            for branch in (stmt.body, stmt.orelse):
                if (not block_exits(branch)
                        and _lv05_fallthrough_rebinds_guard_inputs(
                            branch, get_call)):
                    rebound = True
        else:
            bound = set(assigned_names([stmt]))
            if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef)):
                bound.add(stmt.name)
            rebound |= (bool(names & bound)
                        or _lv05_statement_writes_guard_value(stmt, get_call))
        if block_exits([stmt]):
            return False
    return rebound
def _lv05_statement_rebinds_before_hit(
        stmt: ast.AST, hit: ast.AST, get_call: ast.Call) -> bool:
    names = _lv05_guard_input_names(get_call)
    if not isinstance(stmt, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
        return (bool(names & assigned_names([stmt]).keys())
                or _lv05_statement_writes_guard_value(stmt, get_call))
    value = stmt.value
    if value is not None and subtree_contains(value, hit):
        return _lv05_expression_rebinds_guard_inputs(value, get_call)
    targets = (stmt.targets if isinstance(stmt, ast.Assign)
               else [stmt.target])
    for index, target in enumerate(targets):
        if not subtree_contains(target, hit):
            continue
        if (not isinstance(stmt, ast.AugAssign) and value is not None
                and _lv05_expression_rebinds_guard_inputs(value, get_call)):
            return True
        earlier_bindings = {
            name
            for previous in targets[:index]
            for node in walk_nodes(previous)
            for name in bound_names_of(node)
        }
        return (bool(names & earlier_bindings)
                or any(_lv05_subscript_writes_guard_value(previous, get_call)
                       for previous in targets[:index]))
    return (bool(names & assigned_names([stmt]).keys())
            or _lv05_statement_writes_guard_value(stmt, get_call))
def _lv05_operand_index(parent: ast.BoolOp, cur: ast.AST) -> int:
    for k, v in enumerate(parent.values):
        if v is cur:
            return k
    return -1
def _lv05_flatten_and_operands(node: ast.AST) -> list[ast.AST]:
    if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And):
        flat: list[ast.AST] = []
        for value in node.values:
            flat.extend(_lv05_flatten_and_operands(value))
        return flat
    return [node]
def _lv05_earlier_and_operands(parent: ast.BoolOp, idx: int) -> list[ast.AST]:
    earlier: list[ast.AST] = []
    for v in parent.values[:idx]:
        earlier.extend(_lv05_flatten_and_operands(v))
    return earlier
def _lv05_branch_guards(test: ast.AST, get_call: ast.Call,
                        truth: bool) -> bool:
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _lv05_branch_guards(test.operand, get_call, not truth)
    if isinstance(test, ast.BoolOp):
        distributes = ((truth and isinstance(test.op, ast.And))
                       or (not truth and isinstance(test.op, ast.Or)))
        if distributes:
            return any(_lv05_branch_guards(value, get_call, truth)
                       for value in test.values)
        return False
    if truth:
        return _lv05_is_none_guard_for(test, get_call)
    target = _lv05_get_call_guard_target(test)
    return target is not None and same_expr(target, get_call)
def _lv05_prior_operands_guard(
        operands: list[ast.AST], get_call: ast.Call) -> bool:
    for index in range(len(operands) - 1, -1, -1):
        guard = operands[index]
        if not _lv05_is_none_guard_for(guard, get_call):
            continue
        if _lv05_expression_rebinds_guard_inputs(guard, get_call):
            continue
        if any(_lv05_expression_rebinds_guard_inputs(operand, get_call)
               for operand in operands[index + 1:]):
            continue
        return True
    return False
def _lv05_guard_targets_for(
        test: ast.AST, truth: bool,
) -> tuple[ast.AST, ...]:
    return tuple(
        node for node in walk_nodes(test)
        if _lv05_single_get_call(node)
        and _lv05_branch_guards(test, node, truth)
    )
def _lv05_branch_guarded(cur: ast.AST, parent: ast.AST,
                         get_call: ast.Call, hit: ast.AST) -> bool:
    if isinstance(parent, (ast.If, ast.While)):
        body_hit = any(stmt is cur for stmt in parent.body)
        else_hit = (isinstance(parent, ast.If)
                    and any(stmt is cur for stmt in parent.orelse))
        if not body_hit and not else_hit:
            return False
        truth = body_hit
        if (not _lv05_branch_guards(parent.test, get_call, truth)
                or _lv05_expression_rebinds_guard_inputs(
                    parent.test, get_call)):
            return False
        stmts = parent.body if body_hit else parent.orelse
        return not (
            _lv05_fallthrough_rebinds_guard_inputs(
                prior_statements(stmts, cur), get_call)
            or _lv05_statement_rebinds_before_hit(cur, hit, get_call))
    if isinstance(parent, ast.IfExp):
        if cur is parent.body:
            truth = True
        elif cur is parent.orelse:
            truth = False
        else:
            return False
        return (_lv05_branch_guards(parent.test, get_call, truth)
                and not _lv05_expression_rebinds_guard_inputs(
                    parent.test, get_call))
    return False
def _lv05_enters_deferred_body(
        cur: ast.AST, parent: ast.AST, get_call: ast.Call) -> bool:
    if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return any(stmt is cur for stmt in parent.body)
    if isinstance(parent, ast.Lambda):
        return cur is parent.body
    if isinstance(parent, ast.GeneratorExp):
        first_iter = parent.generators[0].iter
        return not any(node is get_call for node in walk_nodes(first_iter))
    return False
def _lv05_elt_nodes(comp: ast.AST) -> tuple[ast.AST, ...]:
    if isinstance(comp, ast.DictComp):
        return (comp.key, comp.value)
    return (getattr(comp, 'elt', None),)
def _lv05_comprehension_guards(
        parent: ast.AST, cur: ast.AST, get_call: ast.Call) -> bool:
    if not isinstance(parent, _LV05_COMP_SCOPES):
        return False
    guards: list[ast.AST] = []
    for gen in parent.generators:
        if gen.iter is cur or any(cond is cur for cond in gen.ifs):
            return _lv05_prior_operands_guard(guards, get_call)
        guards.extend(gen.ifs)
    if any(node is cur for node in _lv05_elt_nodes(parent)):
        return _lv05_prior_operands_guard(guards, get_call)
    return False
def _lv05_none_guarded(get_call: ast.Call, node: ast.AST,
                       parents: dict[int, ast.AST]) -> bool:
    cur = node
    parent = parents.get(id(cur))
    while parent is not None:
        if _lv05_comprehension_guards(parent, cur, get_call):
            return True
        if _lv05_enters_deferred_body(cur, parent, get_call):
            return False
        if (isinstance(parent, ast.BoolOp)
                and isinstance(parent.op, ast.And)
                and _lv05_and_chain_guards(parent, cur, get_call)):
            return True
        if _lv05_branch_guarded(cur, parent, get_call, node):
            return True
        cur = parent
        parent = parents.get(id(cur))
    return False
def _lv05_and_chain_guards(parent: ast.BoolOp, cur: ast.AST,
                           get_call: ast.Call) -> bool:
    idx = _lv05_operand_index(parent, cur)
    if idx <= 0:
        return False
    return _lv05_prior_operands_guard(
        _lv05_earlier_and_operands(parent, idx), get_call)
def _lv05_get_call_guard_target(test: ast.AST) -> ast.AST | None:
    target: ast.AST | None = None
    if (isinstance(test, ast.Compare) and len(test.ops) == 1
            and isinstance(test.ops[0], ast.Is)
            and len(test.comparators) == 1):
        left, right = test.left, test.comparators[0]
        if is_none_constant(right):
            target = left
        elif is_none_constant(left):
            target = right
    elif isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        target = test.operand
    if target is None or not _lv05_single_get_call(target):
        return None
    return target
def _lv05_scope_id(
        node: ast.AST, parents: dict[int, ast.AST],
        outer_cache: dict[int, set[int]]) -> int:
    cur: ast.AST = node
    scope = nearest_scope(parents, cur)
    while scope is not None:
        outer = outer_cache.get(id(scope))
        if outer is None:
            outer = definition_outer_node_ids(scope)
            outer_cache[id(scope)] = outer
        if id(cur) not in outer:
            break
        cur = scope
        scope = nearest_scope(parents, cur)
    return id(scope) if scope is not None else id(node)
def _lv05_early_exit_guards(
        tree: ast.AST,
        parents: dict[int, ast.AST],
        outer_cache: dict[int, set[int]]) -> dict[int, dict[str, list[ast.AST]]]:
    guards: dict[int, dict[str, list[ast.AST]]] = {}
    for node in walk_ast_nodes(tree):
        if isinstance(node, ast.Assert):
            truth = True
        elif isinstance(node, ast.If) and block_exits(node.body):
            truth = False
        elif isinstance(node, ast.If) and block_exits(node.orelse):
            truth = True
        else:
            continue
        targets = _lv05_guard_targets_for(node.test, truth)
        if not targets:
            continue
        scope_id = _lv05_scope_id(node, parents, outer_cache)
        for target in targets:
            if _lv05_expression_rebinds_guard_inputs(node.test, target):
                continue
            by_scope = guards.setdefault(scope_id, {})
            by_scope.setdefault(ast.dump(target), []).append(node)
    return guards
def _lv05_guard_dominates(guard: ast.AST, node: ast.AST,
                          parents: dict[int, ast.AST]) -> bool:
    cur: ast.AST = node
    parent = parents.get(id(cur))
    while parent is not None:
        if isinstance(cur, ast.stmt):
            siblings = stmt_siblings(parent, cur)
            if siblings is not None:
                guard_idx = cur_idx = -1
                for idx, stmt in enumerate(siblings):
                    if stmt is guard:
                        guard_idx = idx
                    if stmt is cur:
                        cur_idx = idx
                if guard_idx >= 0:
                    return 0 <= guard_idx < cur_idx
        cur = parent
        parent = parents.get(id(cur))
    return False
def _lv05_loop_backedge_invalidates_guard(
        loop: ast.AST, cur: ast.AST, get_call: ast.Call,
) -> bool:
    in_body = cur in loop.body
    in_test = isinstance(loop, ast.While) and cur is loop.test
    if not in_body and not in_test:
        return False
    following = (loop.body if in_test
                 else loop.body[loop.body.index(cur) + 1:])
    if _lv05_fallthrough_rebinds_guard_inputs(following, get_call):
        return True
    if (isinstance(loop, ast.While)
            and _lv05_expression_rebinds_guard_inputs(loop.test, get_call)):
        return True
    return (isinstance(loop, (ast.For, ast.AsyncFor))
            and bool(_lv05_guard_input_names(get_call)
                     & target_binding_names(loop.target)))

def _lv05_guard_inputs_invalidated_between(
        guard: ast.AST, get_call: ast.Call, node: ast.AST,
        parents: dict[int, ast.AST]) -> bool:
    continuation: list[ast.stmt] = []
    if isinstance(guard, ast.If):
        if block_exits(guard.body):
            continuation = guard.orelse
        elif block_exits(guard.orelse):
            continuation = guard.body
    if _lv05_fallthrough_rebinds_guard_inputs(continuation, get_call):
        return True
    cur = node
    parent = parents.get(id(cur))
    while parent is not None:
        if (isinstance(parent, (ast.For, ast.AsyncFor, ast.While))
                and not subtree_contains(parent, guard)
                and _lv05_loop_backedge_invalidates_guard(
                    parent, cur, get_call)):
            return True
        preceding = preceding_statements(parent, cur)
        if guard in preceding:
            index = preceding.index(guard)
            return (
                _lv05_fallthrough_rebinds_guard_inputs(
                    preceding[index + 1:], get_call)
                or _lv05_statement_rebinds_before_hit(cur, node, get_call))
        cur = parent
        parent = parents.get(id(cur))
    return False
def _lv05_guarded_by_early_exit(
        get_call: ast.Call, node: ast.AST,
        parents: dict[int, ast.AST],
        guards: dict[int, dict[str, list[ast.AST]]],
        outer_cache: dict[int, set[int]]) -> bool:
    by_scope = guards.get(_lv05_scope_id(node, parents, outer_cache))
    if not by_scope:
        return False
    return any(
        _lv05_guard_dominates(guard, node, parents)
        and not _lv05_guard_inputs_invalidated_between(
            guard, get_call, node, parents)
        for guard in by_scope.get(ast.dump(get_call), ()))
_LV05_NONE_SAFE_CONVERSIONS = frozenset('sra')
def _lv05_none_safe_percent_template(fmt: str) -> bool:
    conversions: list[str] = []
    for match in _LV23_PLACEHOLDER_RE.finditer(fmt):
        groups = match.groupdict()
        if groups['pct'] is not None:
            continue
        if any(groups[name] is not None
               for name in _LV23_UNJUDGEABLE_GROUPS):
            return False
        conversion = groups['conv']
        if conversion is None:
            return False
        conversions.append(conversion)
    return (len(conversions) == 1
            and conversions[0] in _LV05_NONE_SAFE_CONVERSIONS)
def _lv05_percent_formats_value(left: ast.AST) -> bool | None:
    if isinstance(left, ast.JoinedStr):
        parts: list[str] = []
        dynamic = False
        for value in left.values:
            if isinstance(value, ast.Constant) and isinstance(value.value, str):
                parts.append(value.value)
            elif isinstance(value, ast.FormattedValue):
                dynamic = True
        template = ''.join(parts)
        if not dynamic:
            return _lv05_none_safe_percent_template(template)
        parsed = _scan_percent_template(template)
        return parsed is not None and not parsed[1] and parsed[0] < 2
    if isinstance(left, ast.Constant):
        return (_lv05_none_safe_percent_template(left.value)
                if isinstance(left.value, str) else False)
    return None
def _lv05_node_operands(node: ast.AST) -> tuple[tuple[ast.expr, ...], str] | None:
    if isinstance(node, ast.BinOp) and isinstance(node.op, _LV05_ARITH_OPS):
        if (isinstance(node.op, ast.Mod)
                and _lv05_percent_formats_value(node.left) is not False):
            return None
        return (node.left, node.right), '算术运算'
    if isinstance(node, ast.AugAssign) and isinstance(node.op, _LV05_ARITH_OPS):
        return (node.value,), '算术运算'
    if (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, _LV05_UNARY_OPS)):
        return (node.operand,), '一元运算'
    if _lv05_is_order_compare(node):
        return (node.left, *node.comparators), '序比较'
    return None
def _lv05_is_order_compare(node: ast.AST) -> bool:
    return (isinstance(node, ast.Compare)
            and all(isinstance(op, _LV05_ORDER_OPS) for op in node.ops))
def _lv05_reportable(node: ast.AST,
                     parents: dict[int, ast.AST],
                     guards: dict[int, dict[str, list[ast.AST]]],
                     outer_cache: dict[int, set[int]]) -> str | None:
    hit = _lv05_node_operands(node)
    if hit is None:
        return None
    operands, kind = hit
    gets = [o for o in operands if _lv05_single_get_call(o)]
    if not gets:
        return None
    if all(_lv05_none_guarded(g, node, parents)
           or _lv05_guarded_by_early_exit(
               g, node, parents, guards, outer_cache)
           for g in gets):
        return None
    return kind
def _lv05_issue(node: ast.AST, kind: str, filepath: Any,
                src_lines: list[str]) -> dict[str, Any]:
    return make_issue(
        'LV-05', 'P1', 'null_safety', filepath, node.lineno,
        f'dict.get 缺默认值参与{kind}：键缺失返回 None 将触发 TypeError',
        (
            '``d.get(k)`` 未提供第二参（default），键缺失时返回 None——'
            f'None 参与{kind}直接 TypeError。计数场景应 ``d.get(k, 0)``，'
            '文本场景应 ``d.get(k, "")``。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：get 的「键缺失容错」语义与「参与运算」语义叠加时'
            '漏掉了默认值参数。\n'
            '修复策略：``d.get(k, 0) + 1``（数值域默认 0）/ '
            '``d.get(k, "") + suffix``（文本域默认空串）；键必须存在'
            '时直接用 ``d[k]``（KeyError 响亮失败优于 None 静默）。\n'
            '参考标准：dict.get(key) 缺省返回 None 的契约'
        ),
        'get-without-default-arith',
    )
def check_LV05(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    seen: set[tuple[int, int]] = set()
    parents: dict[int, ast.AST] = parent_map_of(tree)
    outer_cache: dict[int, set[int]] = {}
    guards = _lv05_early_exit_guards(tree, parents, outer_cache)
    for node in roots:
        kind = _lv05_reportable(node, parents, guards, outer_cache)
        if kind is None:
            continue
        anchor = node_position(node)
        if anchor in seen:
            continue
        seen.add(anchor)
        issues.append(_lv05_issue(node, kind, filepath, src_lines))
    return issues
def _lv40_list_producer(
        node: ast.AST, parents: dict[int, ast.AST],
        shadow_cache: dict[tuple, set[str]]) -> bool:
    if isinstance(node, (ast.List, ast.ListComp)):
        return True
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in {'list', 'sorted'}):
        return False
    return not shadowed_binding_at(
        node, node.func.id, parents, shadow_cache)
def _lv40_list_bindings(
        tree: ast.AST, parents: dict[int, ast.AST],
        shadow_cache: dict[tuple, set[str]]) -> dict[tuple[int, str], tuple[int, int]]:
    bind_counts = _runtime_bind_counts(tree, parents)
    positions: dict[tuple[int, str], tuple[int, int]] = {}
    for node in walk_ast_nodes(tree):
        if isinstance(node, ast.Assign):
            targets, value = node.targets, node.value
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            targets, value = [node.target], node.value
        else:
            continue
        if not _lv40_list_producer(value, parents, shadow_cache):
            continue
        for target in targets:
            if not isinstance(target, ast.Name):
                continue
            scope = nearest_scope(parents, target)
            if scope is None:
                continue
            key = (id(scope), target.id)
            if bind_counts.get(key) == 1:
                positions[key] = node_position(node)
    return positions
def _lv40_attribute_contract(
        node: ast.Call, parents: dict[int, ast.AST], imports: _ImportIndex,
        shadow_cache: dict[tuple, set[str]],
        list_bindings: dict[tuple[int, str], tuple[int, int]]) -> bool:
    func = node.func
    if not isinstance(func, ast.Attribute):
        return True
    receiver = func.value
    if func.attr == 'sort':
        if _lv40_list_producer(receiver, parents, shadow_cache):
            return True
        if not isinstance(receiver, ast.Name):
            return False
        scope = nearest_scope(parents, receiver)
        position = (list_bindings.get((id(scope), receiver.id))
                    if scope is not None else None)
        return position is not None and position < node_position(node)
    if not isinstance(receiver, ast.Name) or shadowed_binding_at(
            node, receiver.id, parents, shadow_cache, include_imports=False):
        return False
    origin = _visible_import_origin(node, receiver.id, parents, imports)
    return (origin is not None
            and _import_origin_matches(origin, 'heapq'))
def check_LV40(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    parents = parent_map_of(tree)
    imports = _import_index(tree, parents)
    shadow_cache: dict[tuple, set[str]] = {}
    list_bindings = _lv40_list_bindings(tree, parents, shadow_cache)
    for node in roots:
        if not isinstance(node, ast.Call):
            continue
        inner_id = _lv40_noncallable_key_call(node)
        if (inner_id is None
                or not _lv40_attribute_contract(
                    node, parents, imports, shadow_cache, list_bindings)
                or _lv40_key_never_called(node)
                or shadowed_binding_at(
                    node, inner_id, parents, shadow_cache)):
            continue
        if (isinstance(node.func, ast.Name) and shadowed_binding_at(
                node, node.func.id, parents, shadow_cache)):
            continue
        issues.append(make_issue(
            'LV-40', 'P1', 'logic_correctness', filepath, node.lineno,
            f'key 实参传 {inner_id}(...) 调用结果：非 callable 必 TypeError',
            (
                f'``key={inner_id}(items)`` 形态——key 实参须是 '
                'callable（每元素调用一次），而 '
                f'``{inner_id}(...)`` 的返回值不可调用，首个元素'
                '比较时即抛 TypeError: object is not callable；'
                f'意图是传函数本身 ``key={inner_id}``（无实参括号）。'
            ),
            snippet_of(src_lines, node.lineno),
            (
                '根因：key 消费契约是「函数对象」而非「预计算\n'
                '值」，误把键函数的一次调用结果当键函数传入。\n'
                f'修复策略：传函数本身 ``key={inner_id}``；需要\n'
                '组合/多级键用 ``lambda x: (x.a, x.b)`` 或\n'
                '``operator.itemgetter(...)``（其调用结果可调用，\n'
                '不在本条报出域）。\n'
                '参考标准：CPython sorted/min/max key 参数契约\n'
                '（callable，逐元素调用）'
            ),
            'key-argument-call-result',
        ))
    return issues
def _lv40_is_keyed_call(f: ast.expr) -> bool:
    return ((isinstance(f, ast.Name) and f.id in _LV40_KEYED_FUNCS)
            or (isinstance(f, ast.Attribute)
                and f.attr in _LV40_KEYED_METHODS))
def _lv40_key_kw_value(node: ast.Call) -> ast.expr | None:
    for kw in node.keywords:
        if kw.arg == 'key' and isinstance(kw.value, ast.Call):
            return kw.value
    return None
def _lv40_noncallable_key_call(node: ast.AST) -> str | None:
    if not isinstance(node, ast.Call):
        return None
    if not _lv40_is_keyed_call(node.func):
        return None
    v = _lv40_key_kw_value(node)
    if v is None:
        return None
    return _lv40_noncallable_name(v.func)
def _lv40_noncallable_name(func: ast.expr) -> str | None:
    if isinstance(func, ast.Name) and func.id in _LV40_NONCALLABLE_RETURNS:
        return func.id
    return None
def _lv40_empty_literal(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant):
        return isinstance(node.value, (str, bytes)) and not node.value
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return not node.elts
    return isinstance(node, ast.Dict) and not node.keys
def _lv40_key_never_called(node: ast.Call) -> bool:
    func = node.func
    if isinstance(func, ast.Name) and func.id in _LV40_KEYED_FUNCS:
        return (len(node.args) == 1
                and not isinstance(node.args[0], ast.Starred)
                and _lv40_empty_literal(node.args[0]))
    if not isinstance(func, ast.Attribute):
        return False
    if func.attr == 'sort':
        return (not node.args and isinstance(func.value, ast.List)
                and not func.value.elts)
    if func.attr not in {'nlargest', 'nsmallest'}:
        return False
    if (len(node.args) > 2
            or any(isinstance(arg, ast.Starred) for arg in node.args)
            or any(kw.arg is None for kw in node.keywords)):
        return False
    keywords: dict[str, ast.expr] = {}
    for kw in node.keywords:
        if kw.arg in keywords:
            return False
        keywords[kw.arg] = kw.value
    if (node.args and 'n' in keywords) or (
            len(node.args) > 1 and 'iterable' in keywords):
        return False
    n_expr = node.args[0] if node.args else keywords.get('n')
    iterable_expr = (node.args[1] if len(node.args) > 1
                     else keywords.get('iterable'))
    if n_expr is None or iterable_expr is None:
        return False
    n = int_literal(n_expr, allow_bool=True)
    return ((n is not None and n <= 0)
            or _lv40_empty_literal(iterable_expr))
_LV48_JSON_ATTRS = frozenset({'dump', 'dumps'})
def check_LV48(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    parents = parent_map_of(tree)
    imports = _import_index(tree, parents)
    shadow_cache: dict[tuple, set[str]] = {}
    for node, fname in _json_calls(tree, _LV48_JSON_ATTRS):
        mismatch = _lv48_mismatch(
            fname, node, parents, imports, shadow_cache)
        if not mismatch:
            continue
        issues.append(make_issue(
            'LV-48', 'P2', 'logic_correctness', filepath, node.lineno,
            f'json.{fname} 实参形态错配：{mismatch}',
            (
                f'``json.{fname}`` 的实参契约与调用形态错配——'
                '``json.dump(obj, fp)`` 序列化直写文件对象（fp 必填、'
                '须句柄）、``json.dumps(obj)`` 序列化返回 str（仅单位置'
                '实参，其余选项走关键字）。错配一执行即 TypeError/'
                "AttributeError，落盘入口当步崩溃。变量承载形态无静态"
                '证据已放行。'
            ),
            snippet_of(src_lines, node.lineno),
            (
                '根因：dump/dumps 语义按字面直觉混淆（dump=落盘、\n'
                'dumps=到 str，s 同 LV-26 的 string 口诀）；与路径\n'
                'API 的「传路径字符串」习惯叠加成 fp 位传 str。\n'
                '修复策略：序列化到文件 ``with open(p, "w") as f:\n'
                'json.dump(obj, f)``；序列化到字符串 ``json.dumps(obj)``；\n'
                '格式选项走关键字实参（``json.dumps(obj, indent=2)``）。\n'
                '参考标准：json 序列化 API 契约（dump=流式、dumps=str）'
            ),
            'json-dump-dumps-arity-mismatch',
        ))
    return issues
def _lv48_fp_kind(
        arg: ast.expr, path_constructor: bool = False) -> str | None:
    if path_constructor:
        return 'Path 构造调用'
    if isinstance(arg, ast.JoinedStr):
        return 'f-string'
    for node_type, kind in _LITERAL_NODE_KINDS.items():
        if isinstance(arg, node_type):
            return f'{kind} 字面量'
    if isinstance(arg, ast.Constant):
        if isinstance(arg.value, str):
            return 'str 字面量'
        if isinstance(arg.value, (bytes, bytearray)):
            return 'bytes 字面量'
        return f'{type(arg.value).__name__} 字面量'
    return None
def _lv48_obj_mismatch(
        pos_args: list[ast.expr], keywords: dict[str, ast.expr],
        dynamic_positional: bool, dynamic_keywords: bool) -> str:
    if pos_args and 'obj' in keywords:
        return ("obj 位置与关键字重复传入：got multiple values for "
                "argument 'obj'（序列化对象只能给一次）")
    if (not pos_args and not dynamic_positional
            and not dynamic_keywords and 'obj' not in keywords):
        return ('缺必需实参 obj：序列化对象必填（TypeError: missing '
                "required positional argument: 'obj'）")
    return ''
def _lv48_dump_mismatch(
        pos_args: list[ast.expr], keywords: dict[str, ast.expr],
        dynamic_positional: bool, dynamic_keywords: bool,
        path_constructor: bool) -> str:
    if len(pos_args) > 2:
        count_text = (f'至少 {len(pos_args)}' if dynamic_positional
                      else f'{len(pos_args)}')
        return (f'多位置实参 {count_text} 个：dump 只收 (obj, fp) 两个'
                '位置实参（TypeError: takes 2 positional arguments but '
                f'{count_text} were given）——格式选项走关键字')
    obj_mismatch = _lv48_obj_mismatch(
        pos_args, keywords, dynamic_positional, dynamic_keywords)
    if obj_mismatch:
        return obj_mismatch
    if len(pos_args) >= 2 and 'fp' in keywords:
        return ("fp 位置与关键字重复传入：dump() got multiple values for "
                "argument 'fp'（文件句柄只能给一次）")
    if len(pos_args) < 2:
        if 'fp' in keywords:
            kind = _lv48_fp_kind(keywords['fp'], path_constructor)
            if kind is not None:
                return (f'fp 关键字实参传 {kind}：dump 的 fp 须文件对象'
                        '（无 write 方法）——序列化到字符串用 dumps')
            return ''
        if dynamic_positional or dynamic_keywords:
            return ''
        return ('缺必需实参 fp：dump 序列化目标文件句柄必填'
                '（TypeError: missing required '
                "positional argument: 'fp'）")
    kind = _lv48_fp_kind(pos_args[1], path_constructor)
    if kind is None:
        return ''
    return (f'fp 位传 {kind}：dump 第二实参须文件对象'
            '（无 write 方法）——序列化到字符串用 dumps')
def _lv48_dumps_mismatch(
        pos_args: list[ast.expr], keywords: dict[str, ast.expr],
        dynamic_positional: bool, dynamic_keywords: bool) -> str:
    obj_mismatch = _lv48_obj_mismatch(
        pos_args, keywords, dynamic_positional, dynamic_keywords)
    if obj_mismatch:
        return obj_mismatch
    if len(pos_args) < 2:
        return ''
    count_text = (f'至少 {len(pos_args)}' if dynamic_positional
                  else f'{len(pos_args)}')
    return (f'多位置实参 {count_text} 个：dumps 只收单位置实参 obj'
            '（TypeError: takes 1 positional argument'
            f' but {count_text} were given）——写文件用 dump(obj, fp)')
def _lv48_mismatch(
        fname: str, node: ast.Call, parents: dict[int, ast.AST],
        imports: _ImportIndex, shadow_cache: dict[tuple, set[str]]) -> str:
    pos_args = [arg for arg in node.args if not isinstance(arg, ast.Starred)]
    dynamic_positional = has_starred_arg(node)
    dynamic_keywords = any(kw.arg is None for kw in node.keywords)
    keywords = {kw.arg: kw.value for kw in node.keywords
                if kw.arg is not None}
    if fname == 'dump':
        fp = pos_args[1] if len(pos_args) >= 2 else keywords.get('fp')
        path_constructor = (
            fp is not None and _visible_pathlib_constructor(
                fp, parents, imports, shadow_cache)
        )
        return _lv48_dump_mismatch(
            pos_args, keywords, dynamic_positional, dynamic_keywords,
            path_constructor)
    return _lv48_dumps_mismatch(
        pos_args, keywords, dynamic_positional, dynamic_keywords)
def _lv49_expected_kind_ok(expected: str, value: object) -> bool:
    if expected == 'str':
        return isinstance(value, str)
    return isinstance(value, (bytes, bytearray))
def _lv49_join_expected(
        node: ast.AST, shadowed: frozenset[str] | set[str]) -> str | None:
    if not isinstance(node, ast.Call):
        return None
    func = node.func
    if not (isinstance(func, ast.Attribute) and func.attr == 'join'):
        return None
    if has_starred_arg(node):
        return None
    return _text_carrier_kind(func.value, shadowed)
def check_LV49(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    parents = parent_map_of(tree)
    shadow_cache: dict[tuple, set[str]] = {}
    for node in roots:
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == 'join'):
            continue
        shadowed = {
            name for name in _TEXT_CARRIER_NAMES | {'range'}
            if shadowed_binding_at(node, name, parents, shadow_cache)
        }
        expected = _lv49_join_expected(node, shadowed)
        if expected is None:
            continue
        if not _lv49_arg_bad(expected, node.args, shadowed):
            continue
        issues.append(make_issue(
            'LV-49', 'P1', 'logic_correctness', filepath, node.lineno,
            f'{expected}.join 元素非 {expected}：首个异族元素即 TypeError',
            (
                f'``{expected}.join(iterable)`` 要求元素全部为 '
                f'{expected}——异族元素在首个位置即抛 ``TypeError: '
                f'sequence item 0: expected {expected} instance``。'
                '数字字段拼接须先转 str（``str(x)`` / f-string）；'
                'bytes 流拼接须 encode。'
            ),
            snippet_of(src_lines, node.lineno),
            (
                '根因：join 的元素类型契约按「可迭代即可拼」直觉\n'
                '放宽（实际 join 只做族内连接，无隐式转换）。\n'
                '修复策略：转换元素族 ``",".join(str(x) for x in '
                'items)``；int 列表用 ``"".join(map(str, nums))``；\n'
                'bytes 流拼接先 ``x.encode()`` 或用 ``b"".join``。\n'
                '参考标准：CPython str.join 实现（逐元素 PyUnicode_'
                'Check 失败即 TypeError）'
            ),
            'join-non-string-elements',
        ))
    return issues
_LV49_CONTAINER_NODES = (ast.List, ast.Tuple, ast.Set, ast.Dict)
def _lv49_text_carrier_empty(arg: ast.AST) -> bool | None:
    if isinstance(arg, ast.Constant):
        return arg.value in ('', b'')
    if isinstance(arg, ast.JoinedStr):
        if any(not isinstance(value, ast.Constant)
               or not isinstance(value.value, str)
               for value in arg.values):
            return None
        return not ''.join(value.value for value in arg.values)
    if not (isinstance(arg, ast.Call) and isinstance(arg.func, ast.Name)
            and arg.func.id in _TEXT_CARRIER_CTORS and not arg.keywords):
        return None
    if not arg.args:
        return True
    if len(arg.args) != 1 or isinstance(arg.args[0], ast.Starred):
        return None
    try:
        value = ast.literal_eval(arg.args[0])
    except (ValueError, TypeError, SyntaxError, RecursionError):
        return None
    if arg.func.id == 'str':
        return value == ''
    if isinstance(value, int):
        return value == 0 if value >= 0 else None
    if isinstance(value, bytes):
        return not value
    if isinstance(value, (list, tuple, set, dict)):
        elements = value.keys() if isinstance(value, dict) else value
        if not elements:
            return True
        return (False
                if all(isinstance(element, int) and 0 <= element <= 255
                       for element in elements)
                else None)
    return None
def _lv49_arg_bad(expected: str, pos_args: list,
                  shadowed: frozenset[str] | set[str]) -> bool:
    if len(pos_args) != 1:
        return False
    arg = pos_args[0]
    carrier_kind = _text_carrier_kind(arg, shadowed)
    if carrier_kind is not None:
        if expected == 'str' and carrier_kind == 'str':
            return False
        return _lv49_text_carrier_empty(arg) is False
    if isinstance(arg, (ast.List, ast.Tuple, ast.Set)):
        return _lv49_literal_bad(expected, arg.elts, shadowed)
    if isinstance(arg, ast.Dict):
        return _lv49_literal_bad(
            expected, [key for key in arg.keys if key is not None], shadowed)
    return _lv49_range_call(arg, shadowed)
def _lv49_element_bad(expected: str, elt: ast.AST,
                      shadowed: frozenset[str] | set[str]) -> bool:
    if isinstance(elt, ast.Constant):
        return not _lv49_expected_kind_ok(expected, elt.value)
    if isinstance(elt, _LV49_CONTAINER_NODES):
        return True
    kind = _text_carrier_kind(elt, shadowed)
    return kind is not None and kind != expected
def _lv49_literal_bad(expected: str, elts: list,
                      shadowed: frozenset[str] | set[str]) -> bool:
    return any(_lv49_element_bad(expected, elt, shadowed) for elt in elts)
def _lv49_range_call(arg: ast.expr,
                     shadowed: frozenset[str] | set[str]) -> bool:
    if not (isinstance(arg, ast.Call)
            and isinstance(arg.func, ast.Name)
            and arg.func.id == 'range' and 'range' not in shadowed
            and not arg.keywords and 1 <= len(arg.args) <= 3):
        return False
    values = [int_literal(value, allow_bool=True) for value in arg.args]
    if any(value is None for value in values):
        return False
    if len(values) == 1:
        start, stop, step = 0, values[0], 1
    elif len(values) == 2:
        start, stop = values
        step = 1
    else:
        start, stop, step = values
    if step == 0:
        return False
    return ((step > 0 and start < stop)
            or (step < 0 and start > stop))
def _percent_literal_parts(node: ast.AST) -> tuple[str, ast.expr] | None:
    if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mod)):
        return None
    left = node.left
    if not (isinstance(left, ast.Constant) and isinstance(left.value, str)):
        return None
    return left.value, node.right
_LV23_PLACEHOLDER_RE = re.compile(
    r'%(?P<pct>%)'
    r'|%\((?P<named>[^)]*)\)[#0\- +]*(?:\*|\d+)?(?:\.(?:\*|\d+))?[hlL]*'
    r'(?P<named_conv>[diouxXeEfFgGcrsa])'
    r'|%(?:[#0\- +]*)(?P<star>\*)(?:\.(?:\*|\d+))?[hlL]*[diouxXeEfFgGcrsa]'
    r'|%(?:[#0\- +]*)(?:\d+)?(?:\.(?:(?P<prec_star>\*)|\d+))?[hlL]*'
    r'(?P<conv>[diouxXeEfFgGcrsa])'
)
_PERCENT_NUMERIC_CONVERSIONS = frozenset('diouxXeEfFgG')
_LV23_UNJUDGEABLE_GROUPS = ('named', 'named_conv', 'star', 'prec_star')
def _lv23_percent_tokens_valid(fmt: str) -> bool:
    cursor = 0
    for match in _LV23_PLACEHOLDER_RE.finditer(fmt):
        if '%' in fmt[cursor:match.start()]:
            return False
        cursor = match.end()
    return '%' not in fmt[cursor:]
def _scan_percent_template(fmt: str) -> tuple[int, list[int]] | None:
    if not _lv23_percent_tokens_valid(fmt):
        return None
    positions: list[int] = []
    total = 0
    for match in _LV23_PLACEHOLDER_RE.finditer(fmt):
        groups = match.groupdict()
        if any(groups[name] is not None for name in _LV23_UNJUDGEABLE_GROUPS):
            return None
        if groups['pct'] is not None:
            continue
        if groups['conv'] in _PERCENT_NUMERIC_CONVERSIONS:
            positions.append(total)
        total += 1
    return total, positions
def _lv23_count_placeholders(fmt: str) -> int | None:
    parsed = _scan_percent_template(fmt)
    return None if parsed is None else parsed[0]
def _lv23_named_slot_count(fmt: str) -> int:
    return sum(1 for match in _LV23_PLACEHOLDER_RE.finditer(fmt)
               if match.group('named') is not None)
def _lv23_mixed_mapping_arity(
        fmt: str, right: ast.AST,
) -> tuple[int, int] | None:
    if not isinstance(right, ast.Dict):
        return None
    matches = list(_LV23_PLACEHOLDER_RE.finditer(fmt))
    names = {match.group('named') for match in matches
             if match.group('named') is not None}
    if not names:
        return None
    keys = {key.value for key in right.keys
            if isinstance(key, ast.Constant) and isinstance(key.value, str)}
    before = after = 0
    seen_named = False
    for match in matches:
        groups = match.groupdict()
        if groups['pct'] is not None:
            continue
        if groups['named'] is not None:
            if '*' in match.group(0):
                return None
            seen_named = True
            continue
        if groups['star'] is not None or groups['prec_star'] is not None:
            return None
        if seen_named:
            after += 1
        else:
            before += 1
    if not after and before < 2:
        return None
    seen_named = False
    before_seen = 0
    for match in matches:
        groups = match.groupdict()
        if groups['pct'] is not None:
            continue
        if groups['named'] is not None:
            if groups['named'] not in keys:
                return None
            seen_named = True
            continue
        if seen_named or before_seen:
            return before + after, int(bool(before))
        before_seen += 1
    return None
def _lv23_unconsumed_carrier(node: ast.AST) -> bool:
    if isinstance(node, (ast.List, ast.ListComp, ast.Dict, ast.DictComp)):
        return True
    return _text_carrier_kind(node) == 'bytes'
def _lv23_non_mapping_carrier(node: ast.AST) -> bool:
    if isinstance(node, (ast.Dict, ast.DictComp)):
        return False
    return isinstance(node, (
        ast.Constant, ast.JoinedStr, ast.Tuple, ast.List, ast.Set,
        ast.ListComp, ast.SetComp, ast.GeneratorExp,
    ))
def _lv23_mismatch_text(n_place: int, n_args: int) -> tuple[str, str]:
    if n_place > n_args:
        return '多于', 'not enough arguments for format string'
    return '少于', 'not all arguments converted during string formatting'
def _lv23_single_value_literal(node: ast.expr) -> bool:
    if isinstance(node, ast.Constant):
        return True
    return isinstance(node, (
        ast.JoinedStr, ast.List, ast.Set, ast.Dict,
        ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
    ))
def _lv23_make_arity_issue(
        n_place: int, n_args: int, node: ast.AST, filepath: Any,
        src_lines: list[str]) -> dict[str, Any]:
    rel, detail = _lv23_mismatch_text(n_place, n_args)
    return make_issue(
        'LV-23', 'P1', 'logic_correctness', filepath, node.lineno,
        f'% 格式化数量错配：{n_place} 个占位符{rel} {n_args} 个实参，调用即 TypeError',
        (
            f'模板含 {n_place} 个位置占位符，实参数量可确证为 {n_args} 个——'
            f'数量不等时 ``%`` 格式化必抛 TypeError（{detail}），'
            f'消息拼接/日志格式化行一执行即崩。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：模板字符串与实参在多次编辑中各自演化，'
            '占位符与实参未同步增删。\n'
            f'修复策略：对齐数量——补齐实参到 {n_place} 个，或删'
            f'减多余占位符；也可改用 f-string（插值就地可见、IDE '
            f'可静态核对），避免模板与实参两处维护。\n'
            '参考标准：% 格式化实参契约（CPython Unicode.String '
            '格式化语义）'
        ),
        'percent-format-arity-mismatch',
    )
def _lv23_make_mapping_issue(
        n_named: int, node: ast.AST, filepath: Any,
        src_lines: list[str]) -> dict[str, Any]:
    return make_issue(
        'LV-23', 'P1', 'logic_correctness', filepath, node.lineno,
        f'% 具名占位符 {n_named} 个配非映射实参：format requires a mapping',
        (
            f'模板含 {n_named} 个具名占位符 ``%(name)s``，右侧实参是可确证的'
            '非映射载体（标量/序列/f-string 等）——具名槽位按映射键取值，'
            '非映射实参一执行即抛 ``TypeError: format requires a mapping``'
            '（序列载体抛 ``TypeError: list indices must be integers``）。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：模板从位置占位符改成具名占位符后，实参仍停在'
            '「单值/序列」形态，两侧载体契约未同步。\n'
            '修复策略：传映射 ``"%(name)s" % {"name": value}``；'
            '或模板改回位置占位符 ``"%s" % value``。\n'
            '参考标准：CPython % 格式化具名槽位契约（Mapping 取值，'
            '缺映射即 TypeError）'
        ),
        'percent-named-slot-non-mapping',
    )
def _lv23_make_single_issue(n_place: int, node: ast.AST, filepath: Any,
                            src_lines: list[str]) -> dict[str, Any]:
    return make_issue(
        'LV-23', 'P1', 'logic_correctness', filepath, node.lineno,
        f'% {n_place} 个占位符配单值实参：not enough arguments',
        (
            f'模板含 {n_place} 个位置占位符，右侧是可确证的单一非元组值——'
            '``%`` 格式化只展开元组，单值仅满足 1 个占位符，'
            f'{n_place} 个占位符必抛 TypeError: not enough arguments '
            'for format string，一执行即崩；多值格式化须用元组'
            '（圆括号）或 f-string。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：把「单值右操作数」当成多值容器（或漏写元组\n'
            '外括号），与 LV-42「列表整体作单值」同源。\n'
            '修复策略：改元组 ``"%s-%s" % (a, b)``；数量固定且\n'
            '就近可读时优先 f-string。\n'
            '参考标准：CPython % 格式化右操作数契约（仅 tuple '
            '展开，其余类型整体作单值）'
        ),
        'percent-single-value-multi-placeholder',
    )
def check_LV23(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    for node in walk_ast_nodes(tree):
        parts = _percent_literal_parts(node)
        if parts is None:
            continue
        template, right = parts
        if not _lv23_percent_tokens_valid(template):
            continue
        named = _lv23_named_slot_count(template)
        if named:
            if _lv23_non_mapping_carrier(right):
                issues.append(_lv23_make_mapping_issue(
                    named, node, filepath, src_lines))
            else:
                mixed_arity = _lv23_mixed_mapping_arity(template, right)
                if mixed_arity is not None:
                    issues.append(_lv23_make_arity_issue(
                        *mixed_arity, node, filepath, src_lines))
            continue
        n_place = _lv23_count_placeholders(template)
        if n_place is None:
            continue
        if not isinstance(right, ast.Tuple):
            if not _lv23_single_value_literal(right) or n_place == 1:
                continue
            if n_place == 0 and _lv23_unconsumed_carrier(right):
                continue
            if isinstance(right, ast.List) and n_place >= 2:
                continue
            if n_place >= 2:
                issues.append(_lv23_make_single_issue(
                    n_place, node, filepath, src_lines))
            else:
                issues.append(_lv23_make_arity_issue(
                    n_place, 1, node, filepath, src_lines))
            continue
        if any(isinstance(elt, ast.Starred) for elt in right.elts):
            continue
        n_args = len(right.elts)
        if n_place == n_args:
            continue
        issues.append(_lv23_make_arity_issue(
            n_place, n_args, node, filepath, src_lines))
    return issues
def _lv41_numeric_slot_mismatch(
        node: ast.AST, shadowed: frozenset[str] | set[str]) -> bool:
    return _text_carrier_kind(node, shadowed) is not None
def _lv41_tuple_bad_index(right: ast.Tuple, num_positions: list[int],
                          total: int,
                          shadowed: frozenset[str] | set[str]
                          ) -> int | None:
    if any(isinstance(e, ast.Starred) for e in right.elts):
        return None
    if total != len(right.elts):
        return None
    return next(
        (i for i in num_positions
         if _lv41_numeric_slot_mismatch(right.elts[i], shadowed)), None)
def _lv41_make_issue(node: ast.BinOp, filepath: Any,
                     src_lines: list[str],
                     bad_idx: int | None = None) -> dict[str, Any]:
    if bad_idx is not None:
        title = f'% 数字转换符配字符串实参（第 {bad_idx + 1} 位）：必 TypeError'
        detail = (
            '模板第 %d/%f 等数字族转换符位配 str/bytes 实参——'
            f'元组第 {bad_idx + 1} 位是字符串，格式化执行到该'
            '位必抛 TypeError: a real number is required, '
            'not str，计数/金额拼装行一执行即崩。'
        )
    else:
        title = '% 数字转换符配字符串实参：必 TypeError'
        detail = (
            '模板占位符全部为数字族转换符（%d/%f 等），实参是 '
            'str/bytes——格式化必抛 TypeError: a real number is '
            'required, not str，一执行即崩。'
        )
    return make_issue(
        'LV-41', 'P1', 'logic_correctness', filepath, node.lineno,
        title, detail,
        snippet_of(src_lines, node.lineno),
        (
            '根因：数字占位符与字符串字段错位配对（字段序\n'
            '或类型假设漂移）。\n'
            '修复策略：数字位喂数字实参；字符串内容用 %s 或\n'
            'f-string（插值就地可见）；确需字符串转数字先显式\n'
            '``int(x)`` 并处理 ValueError。\n'
            '参考标准：CPython printf 风格转换符类型契约\n'
            '（diouxXeEfFgG 要求数字实参）'
        ),
        'percent-numeric-conversion-str-arg',
    )
def check_LV41(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    parents = parent_map_of(tree)
    shadow_cache: dict[tuple, set[str]] = {}
    for node in roots:
        parts = _percent_literal_parts(node)
        if parts is None:
            continue
        template, right = parts
        shadowed = {
            name for name in _TEXT_CARRIER_NAMES
            if shadowed_binding_at(right, name, parents, shadow_cache)
        }
        parsed = _scan_percent_template(template)
        if parsed is None:
            continue
        total, num_positions = parsed
        if not num_positions:
            continue
        if isinstance(right, ast.Tuple):
            bad_idx = _lv41_tuple_bad_index(
                right, num_positions, total, shadowed)
            if bad_idx is not None:
                issues.append(_lv41_make_issue(
                    node, filepath, src_lines, bad_idx))
            continue
        if total != 1 or total != len(num_positions):
            continue
        if not _lv41_numeric_slot_mismatch(right, shadowed):
            continue
        issues.append(_lv41_make_issue(node, filepath, src_lines))
    return issues
def check_LV42(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    for node in walk_ast_nodes(tree):
        parts = _percent_literal_parts(node)
        if parts is None:
            continue
        template, right = parts
        n_place = _lv23_count_placeholders(template)
        if n_place is None or n_place < 2:
            continue
        if not isinstance(right, ast.List):
            continue
        issues.append(make_issue(
            'LV-42', 'P1', 'logic_correctness', filepath, node.lineno,
            f'% {n_place} 个占位符配列表实参：列表整体作单值，必 TypeError',
            (
                f'模板含 {n_place} 个位置占位符，实参是列表字面量——'
                '% 格式化仅展开元组，列表作为单个值整体消费，'
                f'{n_place} 个占位符配 1 个实参必抛 TypeError: not '
                'enough arguments for format string，一执行即崩；'
                '意图多值格式化须用元组（圆括号）。'
            ),
            snippet_of(src_lines, node.lineno),
            (
                '根因：方括号/圆括号笔误（列表与元组字面量仅括号形\n'
                '态之差），把「多实参打包」误写为「单值容器」。\n'
                '修复策略：改元组 ``"%s-%s" % (a, b)``；推荐 f-string\n'
                '消除括号语义歧义。\n'
                '参考标准：CPython % 格式化右侧实参契约（仅 tuple '
                '展开，其余类型整体作单值）'
            ),
            'percent-list-instead-of-tuple',
        ))
    return issues
_LV15_MKDIR_METHODS = ('makedirs', 'mkdir')
_LV15_EXIST_OK_ARG_INDEX = 2
def _lv15_is_test_file(filepath: Any) -> bool:
    if not filepath:
        return False
    name = str(filepath).replace('\\', '/').rsplit('/', 1)[-1].lower()
    return name.startswith('test_') or name.endswith('_test.py') or name == 'conftest.py'
_LV15_FILE_EXISTS_HANDLERS = frozenset({
    'FileExistsError', 'OSError', 'IOError', 'EnvironmentError',
    'Exception', 'BaseException',
})
def _lv15_exc_type_covers(node: ast.expr | None) -> bool:
    if node is None:
        return True
    if isinstance(node, ast.Tuple):
        return any(_lv15_exc_type_covers(elt) for elt in node.elts)
    if isinstance(node, ast.Attribute):
        return node.attr in _LV15_FILE_EXISTS_HANDLERS
    if isinstance(node, ast.Name):
        return node.id in _LV15_FILE_EXISTS_HANDLERS
    return False
def _lv15_handler_reraises(handler: ast.ExceptHandler) -> bool:
    return bool(handler.body) and isinstance(handler.body[-1], ast.Raise)
def _lv15_within_try(node: ast.Call, parents: dict) -> bool:
    child: ast.AST = node
    cur = parents.get(id(node))
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda)):
            return False
        if (isinstance(cur, TRY_NODES)
                and any(_lv15_exc_type_covers(h.type)
                        and not _lv15_handler_reraises(h)
                        for h in cur.handlers)
                and any(stmt is child for stmt in cur.body)):
            return True
        child = cur
        cur = parents.get(id(cur))
    return False
_LV15_GUARD_ATTRS = ('exists', 'isdir')
def _lv15_is_path_guard(scan: ast.AST, aliases: set[str]) -> bool:
    if not (isinstance(scan, ast.Call)
            and isinstance(scan.func, ast.Attribute)
            and scan.func.attr in _LV15_GUARD_ATTRS
            and not scan.keywords):
        return False
    if not scan.args:
        return True
    if len(scan.args) != 1:
        return False
    recv = scan.func.value
    return (isinstance(recv, ast.Attribute) and recv.attr == 'path'
            and isinstance(recv.value, ast.Name) and recv.value.id in aliases)
def _lv15_guard_operand(scan: ast.AST, aliases: set[str]) -> ast.expr | None:
    if not _lv15_is_path_guard(scan, aliases):
        return None
    return scan.args[0] if scan.args else scan.func.value
def _lv15_mkdir_operand(node: ast.Call) -> ast.expr | None:
    if node.args and not isinstance(node.args[0], ast.Starred):
        return node.args[0]
    for kw in node.keywords:
        if kw.arg in {'name', 'path'}:
            return kw.value
    return None
def _lv15_path_assignments(
        scope_body: Any,
) -> list[tuple[str, tuple[int, int], ast.expr | None]]:
    events = []
    for sub in scan_body_no_funcs(scope_body):
        if isinstance(sub, ast.Assign):
            for target in sub.targets:
                if isinstance(target, ast.Name):
                    events.append((target.id, node_position(sub.value), sub.value))
                else:
                    events.extend(
                        (name, node_position(target), None)
                        for name in target_binding_names(target))
            continue
        if isinstance(sub, ast.AnnAssign):
            if sub.value is not None and isinstance(sub.target, ast.Name):
                events.append((sub.target.id, node_position(sub.value), sub.value))
            continue
        if isinstance(sub, (ast.For, ast.AsyncFor)):
            value = None
            if (isinstance(sub.target, ast.Name)
                    and isinstance(sub.iter, (ast.List, ast.Tuple))
                    and len(sub.iter.elts) == 1
                    and not isinstance(sub.iter.elts[0], ast.Starred)):
                value = sub.iter.elts[0]
            events.extend(
                (name, node_position(sub.target), value)
                for name in target_binding_names(sub.target))
            continue
        if isinstance(sub, (ast.With, ast.AsyncWith)):
            for item in sub.items:
                if item.optional_vars is not None:
                    events.extend(
                        (name, node_position(item.optional_vars), None)
                        for name in target_binding_names(item.optional_vars))
            continue
        if isinstance(sub, ast.ExceptHandler):
            if sub.name:
                events.append((sub.name, node_position(sub), None))
            continue
        if isinstance(sub, (ast.AugAssign, ast.NamedExpr)):
            events.extend(
                (name, node_position(sub), None)
                for name in target_binding_names(sub.target))
    return events
def _lv15_path_key(
        expr: ast.expr,
        assignments: list[tuple[str, tuple[int, int], ast.expr | None]],
        pos: tuple[int, int]) -> str:
    current = expr
    current_pos = pos
    seen: set[str] = set()
    for _ in range(len(assignments) + 1):
        while _is_path_constructor(current):
            current = current.args[0]
        if not isinstance(current, ast.Name) or current.id in seen:
            break
        seen.add(current.id)
        candidates = [event for event in assignments
                      if event[0] == current.id and event[1] < current_pos]
        if not candidates:
            break
        name, event_pos, value = max(candidates, key=lambda event: event[1])
        if value is None:
            return f'<rebound:{name}:{event_pos}>'
        current_pos, current = event_pos, value
    return ast.dump(current, include_attributes=False)
def _lv15_guard_absent(test: ast.AST, truth: bool, key: str,
                       assignments: list, aliases: set[str]) -> bool | None:
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _lv15_guard_absent(
            test.operand, not truth, key, assignments, aliases)
    if isinstance(test, ast.BoolOp):
        distributes = ((truth and isinstance(test.op, ast.And))
                       or (not truth and isinstance(test.op, ast.Or)))
        if distributes:
            states = [_lv15_guard_absent(
                value, truth, key, assignments, aliases)
                for value in test.values]
            return True if any(state is True for state in states) else None
        return None
    operand = _lv15_guard_operand(test, aliases)
    if operand is None:
        return None
    guard_key = _lv15_path_key(operand, assignments, node_position(test))
    return (not truth) if guard_key == key else None
def _lv15_branch_guard_present(cur: ast.AST, child: ast.AST, key: str,
                               assignments: list, aliases: set[str]) -> bool:
    if not isinstance(cur, ast.If):
        return False
    return any(
        child in body and _lv15_guard_absent(
            cur.test, truth, key, assignments, aliases)
        for body, truth in ((cur.body, True), (cur.orelse, False))
    )
def _lv15_if_exits_or_guards(stmt: ast.If, key: str,
                             assignments: list, aliases: set[str]) -> bool:
    states = [_lv15_guard_absent(stmt.test, truth, key, assignments, aliases)
              for truth in (True, False)]
    exits = [block_exits(stmt.body), block_exits(stmt.orelse)]
    return all(exit_ or state
               for exit_, state in zip(exits, states, strict=True))
def _lv15_prior_if_guard_present(cur: ast.AST, child: ast.AST, key: str,
                                 assignments: list, aliases: set[str]) -> bool:
    for field in ('body', 'orelse'):
        body = getattr(cur, field, None)
        if not isinstance(body, list) or child not in body:
            continue
        for stmt in body[:body.index(child)]:
            if (isinstance(stmt, ast.If)
                    and _lv15_if_exits_or_guards(
                        stmt, key, assignments, aliases)):
                return True
    return False
def _lv15_has_prior_exists_guard(node: ast.Call, parents: dict,
                                 aliases: set[str]) -> bool:
    scope = nearest_scope(parents, node)
    scope_body = scope_body_stmts(scope) if scope is not None else []
    mkdir_operand = _lv15_mkdir_operand(node)
    if mkdir_operand is None:
        return False
    assignments = _lv15_path_assignments(scope_body)
    key = _lv15_path_key(mkdir_operand, assignments, node_position(node))
    child: ast.AST = node
    cur = parents.get(id(node))
    while cur is not None:
        if (_lv15_branch_guard_present(
                cur, child, key, assignments, aliases)
                or _lv15_prior_if_guard_present(
                    cur, child, key, assignments, aliases)):
            return True
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef, ast.Lambda)):
            break
        child, cur = cur, parents.get(id(cur))
    return False
def _lv15_bare_methods(tree: Any) -> dict[str, str]:
    methods: dict[str, str] = {}
    if not isinstance(tree, ast.AST):
        return methods
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.ImportFrom)
                and node.module == 'os' and not node.level):
            continue
        for alias in node.names:
            if alias.name in _LV15_MKDIR_METHODS:
                methods[alias.asname or alias.name] = alias.name
    return methods
def _lv15_mkdir_call(node: ast.AST, aliases: set[str],
                     bare_methods: dict[str, str]) -> str | None:
    if not isinstance(node, ast.Call):
        return None
    func = node.func
    if isinstance(func, ast.Attribute):
        if (func.attr in _LV15_MKDIR_METHODS
                and isinstance(func.value, ast.Name)
                and func.value.id in aliases):
            return func.attr
        return None
    if isinstance(func, ast.Name):
        return bare_methods.get(func.id)
    return None
def _lv15_callee_name(node: ast.Call) -> str | None:
    func = node.func
    if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        return func.value.id
    if isinstance(func, ast.Name):
        return func.id
    return None
def _lv15_exist_ok_truthy(value: ast.AST) -> bool | None:
    try:
        literal = ast.literal_eval(value)
    except (ValueError, TypeError, SyntaxError, RecursionError):
        return None
    return bool(literal)
def _lv15_exist_ok_passed(node: ast.Call, method_name: str) -> bool:
    for kw in node.keywords:
        if kw.arg == 'exist_ok':
            return (method_name == 'makedirs'
                    and _lv15_exist_ok_truthy(kw.value) is True)
    if (method_name != 'makedirs'
            or len(node.args) <= _LV15_EXIST_OK_ARG_INDEX):
        return False
    return _lv15_exist_ok_truthy(node.args[_LV15_EXIST_OK_ARG_INDEX]) is True
def _lv15_call_exempted(node: ast.Call, parents: dict, method_name: str,
                        aliases: set[str]) -> bool:
    if _lv15_exist_ok_passed(node, method_name):
        return True
    if any(kw.arg is None for kw in node.keywords) or any(
            isinstance(a, ast.Starred) for a in node.args):
        return True
    return (_lv15_within_try(node, parents)
            or _lv15_has_prior_exists_guard(node, parents, aliases))
def _lv15_texts(method_name: str) -> tuple[str, str]:
    if method_name == 'makedirs':
        return (
            f'{method_name}() 缺 exist_ok：目录已存在时 FileExistsError',
            ('``os.makedirs(path)`` 未传 ``exist_ok=True``，'
             '所在容器也无 ``os.path.exists/isdir`` 前置判断或捕获 '
             'FileExistsError/OSError 的 try/except（含 except*）容错——'
             '目录已存在（重跑/恢复场景）时'
             'FileExistsError，破坏幂等性。'),
        )
    return (
        f'{method_name}() 无幂等守卫：目录已存在时 FileExistsError',
        ('``os.mkdir(path)`` 不支持 ``exist_ok`` 参数（传参即 '
         'TypeError），所在容器也无 ``os.path.exists/isdir`` 前置'
         '判断或捕获 FileExistsError/OSError 的 try/except（含 except*）'
         '容错——目录已存在（重跑/'
         '恢复场景）时 FileExistsError，破坏幂等性，应改用 '
         '``os.makedirs(path, exist_ok=True)``。'),
    )
def check_LV15(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    if _lv15_is_test_file(filepath):
        return issues
    nodes = walk_ast_nodes(tree)
    if not nodes:
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    imports = _import_index(tree, parents)
    aliases = imported_module_aliases(tree, 'os')
    bare_methods = _lv15_bare_methods(tree)
    shadow_cache: dict[tuple, set[str]] = {}
    for node in nodes:
        method_name = _lv15_mkdir_call(node, aliases, bare_methods)
        if method_name is None:
            continue
        callee_name = _lv15_callee_name(node)
        if (callee_name is not None and shadowed_binding_at(
                node, callee_name, parents, shadow_cache, include_imports=False)):
            continue
        origin = _visible_import_origin(
            node, callee_name, parents, imports)
        if origin is None:
            continue
        if isinstance(node.func, ast.Attribute):
            if not _import_origin_matches(origin, 'os'):
                continue
        else:
            if not _import_origin_matches(
                    origin, 'os', frozenset(_LV15_MKDIR_METHODS)):
                continue
            method_name = origin[1].name
        if _lv15_call_exempted(node, parents, method_name, aliases):
            continue
        title, desc = _lv15_texts(method_name)
        issues.append(make_issue(
            'LV-15', 'P2', 'robustness', filepath, node.lineno,
            title,
            desc,
            snippet_of(src_lines, node.lineno),
            (
                '根因：目录创建默认对「已存在」抛异常，一次性验证'
                '时未暴露，幂等重跑场景必崩。\n'
                '修复策略：``os.makedirs(path, exist_ok=True)``（递归'
                '建目录推荐 makedirs 而非逐级 mkdir）；或先 '
                '``os.path.isdir(path)`` 判断再建（本检测放行该形态）。\n'
                '参考标准：幂等性缺陷模式（Python 语言参考 os.makedirs exist_ok 语义）'
            ),
            'makedirs-no-exist-ok',
        ))
    return issues
_OPEN_MODE_ARG_INDEX = 1
_WRITE_CALL_METHODS = frozenset({'write'})
_OPEN_MODE_CHARS = frozenset('rwxabt+')
_OPEN_PRIMARY_CHARS = frozenset('rwxa')
class _OpenModeFacts(NamedTuple):
    text: str
    binary: bool
    access: str
def _parse_open_mode(mode_text: str) -> _OpenModeFacts | None:
    if (not mode_text
            or any(char not in _OPEN_MODE_CHARS for char in mode_text)
            or any(mode_text.count(char) > 1 for char in _OPEN_MODE_CHARS)):
        return None
    primary = _OPEN_PRIMARY_CHARS.intersection(mode_text)
    updating = '+' in mode_text
    binary = 'b' in mode_text
    if (len(primary) > 1 or (binary and 't' in mode_text)
            or not primary):
        return None
    if updating:
        access = 'update'
    elif primary == {'r'}:
        access = 'read'
    else:
        access = 'write'
    return _OpenModeFacts(mode_text, binary, access)
_LV51_READ_METHODS = frozenset({'read', 'readline', 'readlines'})
_LV51_WRITE_METHODS = _WRITE_CALL_METHODS | {'writelines', 'truncate'}
def _open_call_node(node: ast.expr) -> ast.Call | None:
    if not isinstance(node, ast.Call):
        return None
    if not (isinstance(node.func, ast.Name) and node.func.id == 'open'):
        return None
    return node
def _open_mode_expr(call: ast.Call) -> ast.expr | None:
    for kw in call.keywords:
        if kw.arg == 'mode':
            return kw.value
    if len(call.args) > _OPEN_MODE_ARG_INDEX:
        return call.args[_OPEN_MODE_ARG_INDEX]
    return None
def _stmts_bound_names(stmts: list[ast.stmt]) -> set[str]:
    scope = ast.Module(body=stmts, type_ignores=[])
    return scope_local_bindings(scope)
def _is_handle_call(sub: ast.AST, fname: str, methods) -> bool:
    if not (isinstance(sub, ast.Call)
            and isinstance(sub.func, ast.Attribute)
            and sub.func.attr in methods):
        return False
    receiver = sub.func.value
    return isinstance(receiver, ast.Name) and receiver.id == fname
def _comprehension_binds(comp: ast.AST, node: ast.AST, fname: str) -> bool:
    if not any(fname in target_binding_names(gen.target)
               for gen in comp.generators):
        return False
    return not any(sub is node
                   for sub in walk_nodes(comp.generators[0].iter))
def _handle_scope_shadowed(
        node: ast.AST, fname: str, with_node: ast.AST,
        parents: dict[int, ast.AST]) -> bool:
    cur = parents.get(id(node))
    in_function = False
    while cur is not None and cur is not with_node:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            in_function = True
            if fname in scope_local_bindings(cur):
                return True
        elif ((isinstance(cur, ast.ClassDef) and not in_function
               and fname in scope_local_bindings(cur))
              or (isinstance(cur, _LV05_COMP_SCOPES)
                  and _comprehension_binds(cur, node, fname))):
            return True
        cur = parents.get(id(cur))
    return False
def _handle_deferred_body(
        node: ast.AST, with_node: ast.AST,
        parents: dict[int, ast.AST]) -> bool:
    cur = parents.get(id(node))
    while cur is not None and cur is not with_node:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda)):
            return True
        if (isinstance(cur, ast.GeneratorExp)
                and not subtree_contains(cur.generators[0].iter, node)):
            return True
        cur = parents.get(id(cur))
    return False
def _assignment_value_before_rebind(
        stmt: ast.stmt, fname: str) -> ast.expr | None:
    if isinstance(stmt, ast.Assign):
        targets = stmt.targets
    elif isinstance(stmt, (ast.AnnAssign, ast.AugAssign)):
        targets = [stmt.target]
    else:
        return None
    if not any(fname in target_binding_names(target) for target in targets):
        return None
    value = stmt.value
    if value is None:
        return None
    if any(isinstance(sub, ast.NamedExpr)
           and fname in target_binding_names(sub.target)
           for sub in walk_nodes(value)):
        return None
    return value

def _body_call_nodes(
        body: list, fname: str, with_node: ast.AST,
        parents: dict[int, ast.AST]):
    bound_anywhere = fname in _stmts_bound_names(body)
    for stmt in body:
        bound_here = fname in _stmts_bound_names([stmt])
        roots = [stmt]
        if bound_here:
            value = _assignment_value_before_rebind(stmt, fname)
            if value is None:
                break
            roots = [value]
        for root in roots:
            for sub in walk_nodes(root):
                if (isinstance(sub, ast.Call)
                        and not _handle_scope_shadowed(
                            sub, fname, with_node, parents)
                        and (not bound_anywhere or not _handle_deferred_body(
                            sub, with_node, parents))):
                    yield sub
        if bound_here:
            break
def _open_handle_items(tree: ast.AST, parents: dict[int, ast.AST],
                       shadow_cache: dict[tuple[int, frozenset[int]], set[str]]):
    for node in walk_ast_nodes(tree):
        if not isinstance(node, (ast.With, ast.AsyncWith)):
            continue
        for item in node.items:
            call = _open_call_node(item.context_expr)
            if call is None:
                continue
            if shadowed_binding_at(call, 'open', parents, shadow_cache):
                continue
            if has_starred_arg(call) or any(
                    kw.arg is None for kw in call.keywords):
                continue
            yield node, item, call
def _open_handle_name(item: ast.withitem) -> str | None:
    handle = item.optional_vars
    return handle.id if isinstance(handle, ast.Name) else None
def _open_handle_mode_calls(tree: ast.AST, mode_of: Any):
    if not isinstance(tree, ast.AST):
        return
    parents = parent_map_of(tree)
    shadow_cache: dict[tuple[int, frozenset[int]], set[str]] = {}
    for node, item, call in _open_handle_items(tree, parents, shadow_cache):
        mode = mode_of(call)
        if mode is None:
            continue
        fname = _open_handle_name(item)
        if fname is None:
            continue
        yield node, call, fname, mode
def _lv51_mode_of(call: ast.Call) -> str | None:
    mode_arg = _open_mode_expr(call)
    if mode_arg is None:
        return 'read'
    if not (isinstance(mode_arg, ast.Constant)
            and isinstance(mode_arg.value, str)):
        return None
    facts = _parse_open_mode(mode_arg.value)
    if facts is None or facts.access == 'update':
        return None
    return facts.access
class _Lv51Hit(NamedTuple):
    call: ast.Call
    fname: str
    mode_label: str
    sub: ast.Call
def _lv51_desc(hit: _Lv51Hit) -> str:
    default_mode = _open_mode_expr(hit.call) is None
    detail = (
        'truncate' if hit.sub.func.attr == 'truncate'
        else f'not {"writable" if hit.mode_label == "read" else "readable"}'
    )
    return (
        f'句柄 ``{hit.fname}`` 以'
        f'{"缺省 " if default_mode else ""}'
        f'{"纯读" if hit.mode_label == "read" else "纯写"}'
        '模式打开——'
        f'{hit.sub.func.attr}() 属'
        f'{"写" if hit.mode_label == "read" else "读"}'
        '操作，首次调用即抛 '
        f'``io.UnsupportedOperation: {detail}``。'
    )
def _lv51_fix_text(mode_label: str) -> str:
    read_only = mode_label == 'read'
    need_op = '写' if read_only else '读'
    target_mode = 'w' if read_only else 'r+'
    mode_note = '（覆盖写）' if read_only else '（读改写保留原内容）'
    return (
        '根因：mode 实参与块内操作集的契约错位（r\n'
        '只读、w/a/x 只写、r+ 才读写双开）。\n'
        f'修复策略：需要{need_op}操作时打开模式改为 '
        f'``"{target_mode}"``{mode_note}'
        '；确属误加操作则删除该调用。\n'
        '参考标准：CPython io 模块分层（只读层拒绝\n'
        'write、只写层拒绝 read，错误在首次调用抛出）'
    )
def _lv51_issue(filepath: Any, src_lines: list[str],
                hit: _Lv51Hit) -> dict[str, Any]:
    return make_issue(
        'LV-51', 'P1', 'logic_correctness', filepath,
        hit.sub.lineno,
        f'open 模式 {hit.mode_label} 与操作 {hit.sub.func.attr} 错配'
        '：io.UnsupportedOperation',
        _lv51_desc(hit),
        snippet_of(src_lines, hit.sub.lineno),
        _lv51_fix_text(hit.mode_label),
        'open-mode-io-operation-mismatch',
    )
def check_LV51(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    if not isinstance(tree, ast.AST):
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    for node, call, fname, mode_label in _open_handle_mode_calls(
            tree, _lv51_mode_of):
        forbidden = (_LV51_READ_METHODS if mode_label == 'write'
                     else _LV51_WRITE_METHODS)
        issues.extend(
            _lv51_issue(filepath, src_lines,
                        _Lv51Hit(call, fname, mode_label, sub))
            for sub in _body_call_nodes(node.body, fname, node, parents)
            if _is_handle_call(sub, fname, forbidden))
    return issues
def _lv60_mismatch_writes(
        body: list, fname: str, binary: bool, with_node: ast.AST,
        parents: dict[int, ast.AST], shadow_cache: dict[tuple, set[str]]):
    wrong_kind = 'str' if binary else 'bytes'
    for sub in _body_call_nodes(body, fname, with_node, parents):
        if not (_is_handle_call(sub, fname, _WRITE_CALL_METHODS)
                and sub.args):
            continue
        shadowed = {
            name for name in _TEXT_CARRIER_NAMES
            if shadowed_binding_at(sub, name, parents, shadow_cache)
        }
        if _text_carrier_kind(sub.args[0], shadowed) == wrong_kind:
            yield sub
def _lv60_mode_of(call: ast.Call) -> tuple[str, bool] | None:
    mode_arg = _open_mode_expr(call)
    if mode_arg is None:
        return None
    if not (isinstance(mode_arg, ast.Constant)
            and isinstance(mode_arg.value, str)):
        return None
    facts = _parse_open_mode(mode_arg.value)
    if facts is None or facts.access == 'read':
        return None
    return facts.text, facts.binary
class _Lv60Mode(NamedTuple):
    fname: str
    text: str
    binary: bool
def _lv60_issue(mode: _Lv60Mode, sub: ast.Call, filepath: Any,
                src_lines: list[str]) -> dict[str, Any]:
    exp = ('a bytes-like object is required'
           if mode.binary else
           'write() argument must be str, not bytes')
    fix = ('``payload.encode(encoding)`` 转 bytes 后写入'
           if mode.binary else
           '``data.decode(encoding)`` 转 str 后写入')
    return make_issue(
        'LV-60', 'P1', 'logic_correctness', filepath,
        sub.lineno,
        f'open 模式 {"二进制" if mode.binary else "文本"}与 write '
        f'实参 {"str" if mode.binary else "bytes"} '
        '载体错配：首次 write 即 TypeError',
        (
            f'句柄 ``{mode.fname}`` 以 ``{mode.text!r}`` 模式'
            '打开——write 的实参类型契约与流类型绑死：'
            f'{"二进制流只收 bytes" if mode.binary else "文本流只收 str"}'
            f'，首调即 ``TypeError: {exp}``。可确证载体含 str/bytes 常量、'
            'f-string 与 ``str()``/``bytes()``/``bytearray()`` 构造调用。'
        ),
        snippet_of(src_lines, sub.lineno),
        (
            '根因：流类型与 payload 类型两套契约错位\n'
            '（b 模式消不掉编码义务；文本模式吃不下\n'
            'bytes）。\n'
            f'修复策略：{fix}，或使模式与数据类型\n'
            '对齐（b 配 bytes / 文本配 str）。\n'
            '参考标准：CPython io 模块类型契约——\n'
            'RawIOBase.write 与 TextIOWrapper.write 各\n'
            '只收同族类型'
        ),
        'open-mode-write-literal-type-mismatch',
    )
def check_LV60(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    if not isinstance(tree, ast.AST):
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    shadow_cache: dict[tuple, set[str]] = {}
    for node, _call, fname, mode in _open_handle_mode_calls(
            tree, _lv60_mode_of):
        mode_text, binary = mode
        issues.extend(
            _lv60_issue(_Lv60Mode(fname, mode_text, binary),
                        sub, filepath, src_lines)
            for sub in _lv60_mismatch_writes(
                node.body, fname, binary, node, parents, shadow_cache))
    return issues
_FORMATTER = string.Formatter()
_MAX_FORMAT_SPEC_DEPTH = 1
def _lv_slot_root(field_name: str) -> str:
    return field_name.split('.')[0].split('[')[0]
class _FormatSlots(NamedTuple):
    roots: tuple[str, ...]
    automatic: int
    manual: bool
def _scan_format_slots(fmt: str, depth: int) -> _FormatSlots | None:
    if depth > _MAX_FORMAT_SPEC_DEPTH:
        return None
    try:
        parts = list(_FORMATTER.parse(fmt))
    except ValueError:
        return None
    roots: list[str] = []
    automatic = 0
    manual = False
    for _lit, field_name, format_spec, _conv in parts:
        if field_name is not None:
            root = _lv_slot_root(field_name)
            roots.append(root)
            if root == '':
                automatic += 1
            elif root.isdecimal():
                manual = True
        if not format_spec:
            continue
        nested = _scan_format_slots(format_spec, depth + 1)
        if nested is None:
            return None
        roots.extend(nested.roots)
        automatic += nested.automatic
        manual = manual or nested.manual
    return _FormatSlots(tuple(roots), automatic, manual)
def _str_format_call(node: ast.AST) -> tuple[ast.Call, str] | None:
    if not isinstance(node, ast.Call):
        return None
    func = node.func
    if not (isinstance(func, ast.Attribute) and func.attr == 'format'):
        return None
    recv = func.value
    if not (isinstance(recv, ast.Constant) and isinstance(recv.value, str)):
        return None
    return node, recv.value
def _lv35_mixed_issue(filepath: Any, src_lines: list[str],
                      call: ast.Call) -> dict[str, Any]:
    return make_issue(
        'LV-35', 'P1', 'logic_correctness', filepath, call.lineno,
        'format 自动槽位与显式编号槽位混用：必抛 ValueError',
        (
            '同一模板内既有 ``{}`` 自动编号槽位又有 ``{0}`` 显式编号'
            '槽位——CPython 严格禁止两种编号模式混用，调用即抛 '
            'ValueError: cannot switch from manual field specification '
            'to automatic field numbering，消息拼装行一执行即崩。'
        ),
        snippet_of(src_lines, call.lineno),
        (
            '根因：模板拼装时部分槽位手写编号、部分依赖自动编号，\n'
            '两种模式在同一字符串里不能共存。\n'
            '修复策略：统一采用自动编号（删掉 ``{0}`` 中的数字）或\n'
            '全部显式编号；推荐改 f-string（插值就地可见，编译期\n'
            '不可错配）。\n'
            '参考标准：CPython str.format 编号模式约束（PEP 3101，\n'
            '混用必抛 ValueError）'
        ),
        'str-format-slot-arity-mismatch',
    )
def check_LV35(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    if not isinstance(tree, ast.AST):
        return []
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    for node in walk_nodes(tree):
        shape = _str_format_call(node)
        if shape is None:
            continue
        call, template = shape
        scanned = _scan_format_slots(template, 0)
        n_auto = scanned.automatic if scanned is not None else 0
        manual = scanned.manual if scanned is not None else False
        if n_auto and manual:
            issues.append(_lv35_mixed_issue(filepath, src_lines, call))
            continue
        if has_starred_arg(call) or not n_auto:
            continue
        n_args = len(call.args)
        if n_auto <= n_args:
            continue
        issues.append(make_issue(
            'LV-35', 'P1', 'logic_correctness', filepath, call.lineno,
            f'format 自动槽位 {n_auto} 个多于实参 {n_args} 个：调用即 IndexError',
            (
                f'模板含 {n_auto} 个自动槽位 ``{{}}``，位置实参仅 '
                f'{n_args} 个——str.format 按位置喂值，越界槽位必抛 '
                'IndexError: Replacement index out of range，消息拼'
                '装/文案渲染行一执行即崩。'
            ),
            snippet_of(src_lines, call.lineno),
            (
                '根因：模板字符串与实参列表各自演化（追加槽位未同步\n'
                '补实参），或意图插值的变量被遗漏。\n'
                f'修复策略：补齐实参到 {n_auto} 个，或删减多余槽位；\n'
                '推荐改 f-string（插值就地可见，编译期不可错配）。\n'
                '参考标准：str.format 自动编号语义（CPython format '
                'specification Mini-Language）'
            ),
            'str-format-slot-arity-mismatch',
        ))
    return issues
def _lv57_named_slot_missing(root: str, kw_names: set[str]) -> bool:
    return bool(root) and not root.isdecimal() and root not in kw_names
def _lv57_index_slot_missing(root: str, n_args: int) -> bool:
    if not root.isdecimal() or len(root) > 20:
        return False
    try:
        return int(root) >= n_args
    except ValueError:
        return False
def _lv57_missing_slots(template: str,
                        call: ast.Call) -> tuple[list[str], list[int]]:
    slots = _scan_format_slots(template, 0)
    if slots is None or (slots.automatic and slots.manual):
        return [], []
    roots = slots.roots
    kw_names = {kw.arg for kw in call.keywords if kw.arg is not None}
    dynamic_named = any(kw.arg is None for kw in call.keywords)
    dynamic_index = has_starred_arg(call)
    missing_named = [] if dynamic_named else sorted({
        r for r in roots if _lv57_named_slot_missing(r, kw_names)})
    missing_index = [] if dynamic_index else sorted({
        int(r) for r in roots
        if _lv57_index_slot_missing(r, _fixed_positional_count(call))})
    return missing_named, missing_index
def _lv57_named_issue(node: ast.Call, missing: list[str], src_lines: list[str],
                      filepath: Any) -> dict[str, Any]:
    kw_names = {kw.arg for kw in node.keywords if kw.arg is not None}
    return make_issue(
        'LV-57', 'P1', 'logic_correctness', filepath, node.lineno,
        f'format 具名槽位 {missing} 缺关键字实参：必 KeyError',
        (
            f'模板含具名槽位 ``{missing}``，关键字实参'
            f'仅 {sorted(kw_names)}——str.format 按名取参，'
            f'缺失名必抛 ``KeyError: {missing[0]!r}``'
            '，消息拼装一执行即崩。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：模板槽位名与 .format(...) 关键字实参列表\n'
            '各自演化不同步（改名漏单侧/删实参漏槽位）。\n'
            f'修复策略：补齐 ``{missing}=...`` 关键字实参，'
            '或删改模板槽位；推荐改 f-string（插值就地可见，\n'
            '编译期不可错配）。\n'
            '参考标准：str.format Map-keyword lookup 契约\n'
            '（PEP 3101，缺名 KeyError）'
        ),
        'str-format-named-slot-missing',
    )
def _lv57_index_issue(node: ast.Call, missing: list[int], src_lines: list[str],
                       filepath: Any) -> dict[str, Any]:
    return make_issue(
        'LV-57', 'P1', 'logic_correctness', filepath, node.lineno,
        f'format 编号槽位 {missing} 超位置实参数：必 IndexError',
        (
            f'模板含编号槽位 ``{missing}``，固定位置实参仅 '
            f'{_fixed_positional_count(node)} 个——越界槽位必抛 ``IndexError: '
            'Replacement index out of range``，消息拼装一执行'
            '即崩。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            f'根因：编号槽位与位置实参数量错配（槽位参照的下\n'
            '标超出实参序列长度）。\n'
            f'修复策略：补齐位置实参到 ≥{max(missing) + 1} '
            '个，或裁减/改写槽位编号；推荐改 f-string。\n'
            '参考标准：str.format positional lookup 契约\n'
            '（PEP 3101，越界 IndexError）'
        ),
        'str-format-index-slot-missing',
    )
def check_LV57(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    if not isinstance(tree, ast.AST):
        return []
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    for node in walk_nodes(tree):
        shape = _str_format_call(node)
        if shape is None:
            continue
        _call, template = shape
        missing_named, missing_index = _lv57_missing_slots(template, node)
        if missing_named:
            issues.append(_lv57_named_issue(
                node, missing_named, src_lines, filepath))
        if missing_index:
            issues.append(_lv57_index_issue(
                node, missing_index, src_lines, filepath))
    return issues
_LV08_DRIVE_RE = re.compile(r'^[A-Za-z]:')
def _lv08_abs_prefix(s: str) -> bool:
    drive = _LV08_DRIVE_RE.match(s)
    return (s.startswith(('/', '\\'))
            or bool(drive and len(s) > 2 and s[2] in '/\\'))
def _lv08_joined_str_head(node: ast.AST) -> str | None:
    if not isinstance(node, ast.JoinedStr) or not node.values:
        return None
    head = node.values[0]
    if not isinstance(head, ast.Constant):
        return None
    return head.value if isinstance(head.value, str) else None
def _lv08_static_str(node: ast.AST) -> str | None:
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    if isinstance(node, ast.JoinedStr):
        parts = [value.value for value in node.values
                 if isinstance(value, ast.Constant)
                 and isinstance(value.value, str)]
        return ''.join(parts) if len(parts) == len(node.values) else None
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        left = _lv08_static_str(node.left)
        right = _lv08_static_str(node.right)
        if left is not None and right is not None:
            return left + right
    return None
def _lv08_leftmost_str(node: ast.AST) -> str | None:
    static = _lv08_static_str(node)
    if static is not None:
        return static
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        left = _lv08_leftmost_str(node.left)
        if left is None:
            return None
        return left or _lv08_leftmost_str(node.right)
    return _lv08_joined_str_head(node)
def _lv08_drive_reset(args: list[ast.AST], index: int, left: str) -> bool:
    drive = _LV08_DRIVE_RE.match(left)
    if drive is None:
        return False
    current_drive = ''
    drive_known = True
    for previous in args[:index]:
        previous_left = _lv08_leftmost_str(previous)
        if previous_left is None:
            current_drive = ''
            drive_known = False
            continue
        previous_drive = _LV08_DRIVE_RE.match(previous_left)
        if previous_drive is not None:
            current_drive = previous_drive.group(0).lower()
            drive_known = True
    return drive_known and current_drive != drive.group(0).lower()
def _lv08_is_path_join_call(node: ast.AST, os_aliases: set[str]) -> bool:
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)):
        return False
    f = node.func
    if f.attr != 'join':
        return False
    return (isinstance(f.value, ast.Attribute) and f.value.attr == 'path'
            and isinstance(f.value.value, ast.Name)
            and f.value.value.id in os_aliases)
def _lv08_reset_args(node: ast.AST,
                     os_aliases: set[str]) -> list[tuple[ast.AST, str]]:
    if not _lv08_is_path_join_call(node, os_aliases) or len(node.args) < 2:
        return []
    hits: list[tuple[ast.AST, str]] = []
    for index, arg in enumerate(node.args[1:], 1):
        left = _lv08_leftmost_str(arg)
        if left is not None and (
                _lv08_abs_prefix(left)
                or _lv08_drive_reset(node.args, index, left)):
            hits.append((arg, left))
    return hits
def _lv08_issue(arg: ast.AST, left: str, filepath: Any,
                src_lines: list[str]) -> dict[str, Any]:
    shown = left if len(left) <= 40 else left[:40] + '...'
    return make_issue(
        'LV-08', 'P1', 'path_safety', filepath, arg.lineno,
        'os.path.join 后续参数重置路径：前缀参数被静默丢弃',
        (
            f'join 参数 ``{shown}`` 是绝对路径或异盘符路径——'
            f'os.path.join 会丢弃之前全部参数，base 前缀静默失效'
            f'（无告警），落盘位置失控。'
        ),
        snippet_of(src_lines, arg.lineno),
        (
            '根因：绝对路径资源名被直接塞进 join 后段。\n'
            '修复策略：改用相对段 ``os.path.join(base, "data", '
            'name)``；确需锚定绝对路径时应显式判断（不再依赖 '
            'base），并校验解析后的路径仍位于预期根目录内。\n'
            '参考标准：os.path.join 遇绝对路径段丢弃全部前缀参数'
        ),
        'join-absolute-arg-reset',
    )
def check_LV08(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    os_aliases = imported_module_aliases(tree, 'os')
    parents = parent_map_of(tree)
    imports = _import_index(tree, parents)
    shadow_cache: dict[tuple, set[str]] = {}
    for node in roots:
        receiver = (deref_root_name(node.func)
                    if isinstance(node, ast.Call) else None)
        if receiver in os_aliases:
            if shadowed_binding_at(
                    node, receiver, parents, shadow_cache, include_imports=False):
                continue
            origin = _visible_import_origin(node, receiver, parents, imports)
            if (origin is None
                    or not _import_origin_matches(origin, 'os')):
                continue
        for arg, left in _lv08_reset_args(node, os_aliases):
            issues.append(_lv08_issue(arg, left, filepath, src_lines))
    return issues
_LV14_STR_PREFIX_METHODS = ('endswith', 'startswith')
def _lv14_list_arg_method(node: ast.AST) -> str:
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in _LV14_STR_PREFIX_METHODS):
        return ''
    if not node.args or not isinstance(node.args[0], ast.List):
        return ''
    return node.func.attr
def _lv14_issue(node: ast.AST, method: str, filepath: Any,
                src_lines: list[str]) -> dict[str, Any]:
    return make_issue(
        'LV-14', 'P1', 'logic_correctness', filepath, node.lineno,
        f'{method}() 首参传 list 字面量：调用即 TypeError',
        (
            f'``str.{method}`` 只接受 str 或 tuple，首参为列表'
            f'字面量时调用必抛 ``TypeError: {method} first arg '
            f'must be str or a tuple of str``——多后缀判断应改传'
            f'元组。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：从列表数据出发组装多值判断时，把 list 直接'
            '传给了只收 str/tuple 的内建方法。\n'
            f'修复策略：改传元组 ``s.{method}((ext_a, ext_b))``；'
            '或对动态 list 调 ``tuple(exts)`` 转换后再传。\n'
            '参考标准：str.startswith/endswith 只接受 str 或 str 元组'
        ),
        'str-prefix-method-list-arg',
    )
def check_LV14(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    for node in walk_ast_nodes(tree):
        method = _lv14_list_arg_method(node)
        if not method:
            continue
        issues.append(_lv14_issue(node, method, filepath, src_lines))
    return issues
_LV16_STRIP_METHODS = ('strip', 'lstrip', 'rstrip')
_LV16_SUFFIX_LIKE_RE = re.compile(r'(?:\.[A-Za-z0-9]+)+')
def _lv16_strip_call(node: ast.AST) -> tuple[str, str] | None:
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr in _LV16_STRIP_METHODS):
        return None
    if not node.args:
        return None
    first = node.args[0]
    if not (isinstance(first, ast.Constant) and isinstance(first.value, str)):
        return None
    return node.func.attr, first.value
def _lv16_strip_suffix_literal(node: ast.AST) -> tuple[str, str] | None:
    hit = _lv16_strip_call(node)
    if hit is None or not _LV16_SUFFIX_LIKE_RE.fullmatch(hit[1]):
        return None
    return hit
def _lv16_issue(node: ast.AST, method: str, val: str, filepath: Any,
                src_lines: list[str]) -> dict[str, Any]:
    return make_issue(
        'LV-16', 'P2', 'logic_correctness', filepath, node.lineno,
        f'{method}("{val}") 按字符集剥离而非去前后缀：结果静默错误',
        (
            f'``{method}()`` 实参是要剥离的**字符集合**：'
            f'``"{val}"`` 会被拆成字符 ``{"".join(sorted(set(val)))}`` '
            f'逐个剥离两端，而非去除整个前后缀 ``{val}``——'
            f'两端恰好由集合内字符组成的合法内容会被连带剥掉，'
            f'结果静默错误（无异常）。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：把 removesuffix/removeprefix 的「前后缀字符串」'
            '参数语义套到了 strip 家族的「字符集合」参数上。\n'
            f'修复策略：去后缀用 ``s.removesuffix("{val}")``（3.9+），'
            '去前缀用 ``removeprefix``；低版本用切片 '
            '``s[:-len(suffix)] if s.endswith(suffix) else s``。\n'
            '参考标准：str.strip 参数为字符集合，非前后缀字符串'
        ),
        'strip-suffix-misuse',
    )
def check_LV16(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    for node in walk_ast_nodes(tree):
        hit = _lv16_strip_suffix_literal(node)
        if hit is None:
            continue
        method, val = hit
        issues.append(_lv16_issue(node, method, val, filepath, src_lines))
    return issues
def _lv28_module_aliases_of(node: ast.AST) -> set[str]:
    if not isinstance(node, ast.Import):
        return set()
    return {alias.asname or alias.name for alias in node.names
            if alias.name == 'threading'}
def _lv28_bare_aliases_of(node: ast.AST) -> set[str]:
    if not (isinstance(node, ast.ImportFrom)
            and node.module in ('threading', '_thread') and not node.level):
        return set()
    return {alias.asname or alias.name for alias in node.names
            if alias.name == 'Thread'}
def _lv28_thread_evidence(tree: ast.AST) -> tuple[set[str], set[str]]:
    bare_aliases: set[str] = set()
    module_aliases: set[str] = set()
    for node in walk_nodes(tree):
        module_aliases |= _lv28_module_aliases_of(node)
        bare_aliases |= _lv28_bare_aliases_of(node)
    return bare_aliases, module_aliases
def _lv28_thread_ctor_evidenced(
        value: ast.AST, bare_aliases: set[str], module_aliases: set[str],
        parents: dict[int, ast.AST], cache: dict[tuple, set[str]],
        imports: _ImportIndex) -> bool:
    if not isinstance(value, ast.Call):
        return False
    func = value.func
    binding: str | None = None
    if isinstance(func, ast.Name) and func.id in bare_aliases:
        binding = func.id
    elif (isinstance(func, ast.Attribute) and func.attr == 'Thread'
            and isinstance(func.value, ast.Name)
            and func.value.id in module_aliases):
        binding = func.value.id
    if binding is None or shadowed_binding_at(
            value, binding, parents, cache, include_imports=False):
        return False
    origin = _visible_import_origin(value, binding, parents, imports)
    if origin is None:
        return False
    if isinstance(func, ast.Name):
        return any(_import_origin_matches(
            origin, module_name, frozenset({'Thread'}))
            for module_name in ('threading', '_thread'))
    return _import_origin_matches(origin, 'threading')
def _lv28_thread_assign_targets(node: ast.AST) -> list[ast.Name]:
    if isinstance(node, ast.Assign):
        return [t for t in node.targets if isinstance(t, ast.Name)]
    if isinstance(node, ast.AnnAssign) and node.value is not None:
        return [node.target] if isinstance(node.target, ast.Name) else []
    return []
def _lv28_collect_thread_vars(
        tree: ast.AST, bare_aliases: set[str], module_aliases: set[str],
        bind_counts: dict[tuple[int, str], int], parents: dict[int, ast.AST],
        cache: dict[tuple, set[str]], imports: _ImportIndex,
) -> set[tuple[int, str]]:
    thread_vars: set[tuple[int, str]] = set()
    for node in walk_nodes(tree):
        targets = _lv28_thread_assign_targets(node)
        if not targets:
            continue
        if not _lv28_thread_ctor_evidenced(
                node.value, bare_aliases, module_aliases, parents, cache,
                imports):
            continue
        for target in targets:
            scope = nearest_scope(parents, target)
            if scope is None:
                continue
            key = (id(scope), target.id)
            if bind_counts.get(key, 0) == 1:
                thread_vars.add(key)
    return thread_vars
def _lv28_thread_run_call(node: ast.AST) -> bool:
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == 'run')
def _lv28_thread_target_evidenced(
        target: ast.AST, bare_aliases: set[str], module_aliases: set[str],
        thread_vars: set[tuple[int, str]], parents: dict[int, ast.AST],
        cache: dict[tuple, set[str]], imports: _ImportIndex) -> bool:
    if isinstance(target, ast.Call):
        return _lv28_thread_ctor_evidenced(
            target, bare_aliases, module_aliases, parents, cache, imports)
    if not isinstance(target, ast.Name):
        return False
    scope = nearest_scope(parents, target)
    return scope is not None and (id(scope), target.id) in thread_vars
def check_LV28(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    src_lines = source_lines(source)
    bare_aliases, module_aliases = _lv28_thread_evidence(tree)
    parents = parent_map_of(tree)
    imports = _import_index(tree, parents)
    shadow_cache: dict[tuple, set[str]] = {}
    bind_counts = _runtime_bind_counts(tree, parents)
    thread_vars = _lv28_collect_thread_vars(
        tree, bare_aliases, module_aliases, bind_counts, parents,
        shadow_cache, imports)
    for node in roots:
        if not _lv28_thread_run_call(node):
            continue
        if not _lv28_thread_target_evidenced(
                node.func.value, bare_aliases, module_aliases, thread_vars,
                parents, shadow_cache, imports):
            continue
        issues.append(make_issue(
            'LV-28', 'P2', 'logic_correctness', filepath, node.lineno,
            'Thread 实例 .run() 直调：目标函数同步执行，多线程意图'
            '静默失效',
            (
                '``Thread.run()`` 在当前线程内同步执行目标函数——与'
                '普通函数调用无差异，不创建新线程、不并发、无异常'
                '信号；启动线程必须调 ``.start()``。直接链与同名变量'
                '两种形态均已确证命中，业务并发设计整体落空。'
            ),
            snippet_of(src_lines, node.lineno),
            (
                '根因：run 是线程体入口方法（start 内部在新线程中调用它），\n'
                '外部直调绕过线程启动协议。\n'
                '修复策略：改调 ``t.start()``（异步启动）；需等待完成\n'
                '再 ``t.join()``。需返回值用 ``concurrent.futures.\n'
                'ThreadPoolExecutor``。\n'
                '参考标准：threading.Thread.start 启动协议（run 为线程体入口）'
            ),
            'thread-run-direct-call',
        ))
    return issues

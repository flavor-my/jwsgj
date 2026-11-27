from __future__ import annotations

import ast
import builtins
import logging
import os as _os
import re
import sys
from functools import lru_cache
from typing import Any, NamedTuple

from jwsgj.diag_detectors_registry import register_detector_catalog
from jwsgj.diag_shared_ast_bindings import (
    ScopeNameResolver,
    _import_alias_paths,
)
from jwsgj.diag_shared_ast_nodes import (
    TRY_NODE_TYPES,
    ast_name,
    dotted_name,
    handler_exc_names,
    is_docstring_stmt,
    iter_handler_scope,
    iter_module_scope_nodes,
)
from jwsgj.diag_shared_ast_views import (
    collect_lexical_scope_table,
    definition_time_expressions,
    parent_map,
    subtree_nodes,
    tree_nodes,
)
from jwsgj.diag_shared_source_core import (
    ast_split_lines,
    coerce_source_text,
    count_effective_lines,
    load_source_tree,
    resolve_module_name,
    source_line_count,
    source_lines_or,
)
from jwsgj.diag_shared_source_scan import (
    string_comment_spans,
)
from jwsgj.diag_types_defs import DiagnoseIssue, finding_scan_exempt
from jwsgj.diag_types_vocab import (
    D_ARCH_RULE_SUGGESTIONS,
    HARD_MAX_FILE_LINES,
    HARD_MAX_FUNC_LINES,
    PARSE_DEGRADE_EXC,
    DiagnoseSeverity,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes

logger = logging.getLogger(__name__)
__all__ = [
    'D_ARCH_CONSTRAINTS',
    'GATE_DETECTORS',
    'check_AS09',
    'check_SZ02',
    'detect_all_overwrite',
    'detect_d01_lazy_import',
    'detect_d02_degradation',
    'detect_d03_fallback',
    'detect_d04_circular_module',
    'detect_d06_dynamic_import',
    'detect_d07_dead_code',
    'detect_d08_circular_dep',
    'detect_d13_import_chain',
    'detect_d15_static_register',
    'detect_d18_stub_function',
    'detect_d23_self_catch',
    'detect_d24_unreachable_except',
    'detect_d25_fullwidth_chars',
    'detect_d27_dead_import',
    'detect_d29_syntax_error',
    'detect_star_import',
    'handler_exc_names',
    'nearest_owning_handler',
]
_DEFAULT_SOURCE_LINES: list[str] | None = None
_DEFAULT_FILEPATH = ''
logger.info("diag_gate_arch D 族单文件规则域已加载: %d 项导出", len(__all__))
def _filepath_text(filepath: Any) -> str:
    return '' if filepath is None else _os.fsdecode(filepath)
def _ensure_source_tree(tree, filepath):
    if tree is not None:
        return tree
    if not filepath:
        return None
    parsed = load_source_tree(filepath)
    return parsed[1] if parsed is not None else None
def _prepared_tree(tree: Any, filepath: str) -> ast.Module | None:
    tree = _ensure_source_tree(tree, filepath)
    return tree if isinstance(tree, ast.Module) else None
def _import_issue(check_id: str, severity: DiagnoseSeverity, message: str,
                  line: int, suggestion: str) -> DiagnoseIssue:
    return DiagnoseIssue(check_id=check_id, severity=severity, message=message,
                         line=line, suggestion=suggestion)
def detect_d01_lazy_import(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH,
                           d01_cycle_exempt: set[tuple[str, str]] | frozenset[tuple[str, str]] = frozenset()) -> list[DiagnoseIssue]:
    tree = _prepared_tree(tree, filepath)
    if tree is None:
        return []
    issues = []
    source_lines = source_lines_or(code, source_lines)
    cur_mod = _module_stem(filepath) if filepath else ''
    _parent_map = parent_map(tree)
    for node in tree_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for child in _d01_owned_imports(node, _parent_map):
            for tgt_mod in _d01_target_modules(child, filepath):
                kind = _d01_exempt_kind(
                    child, tgt_mod, cur_mod, d01_cycle_exempt,
                    source_lines, _parent_map)
                if kind in ('marked', 'optional', 'stdlib'):
                    continue
                severity, message, suggestion = _D01_KIND_SPECS[kind]
                issues.append(_import_issue(
                    'D01', severity, message.format(fn=node.name, mod=tgt_mod),
                    child.lineno, suggestion))
    return issues
def _d01_owned_imports(node, pmap):
    for child in subtree_nodes(node):
        if child is node or not isinstance(child, (ast.Import, ast.ImportFrom)):
            continue
        if not (node.lineno <= child.lineno <= node.end_lineno):
            continue
        owner = _nearest_ancestor(
            child, pmap, (ast.FunctionDef, ast.AsyncFunctionDef))
        if owner is node:
            yield child
def _nearest_ancestor(node: ast.AST, pmap: dict,
                     target_types: tuple[type, ...],
                     stop_types: tuple[type, ...] = ()) -> ast.AST | None:
    cur = pmap.get(node)
    while cur is not None:
        if isinstance(cur, stop_types):
            return None
        if isinstance(cur, target_types):
            return cur
        cur = pmap.get(cur)
    return None
def _d01_target_modules(child: ast.AST, filepath: str) -> list[str]:
    if not isinstance(child, (ast.Import, ast.ImportFrom)):
        return []
    if isinstance(child, ast.ImportFrom) and child.module:
        if not child.level:
            _current, package_parts = _package_context(filepath)
            module_parts = child.module.split('.')
            if (package_parts and len(module_parts) <= len(package_parts)
                    and module_parts == package_parts[:len(module_parts)]):
                return [
                    alias.name.rsplit('.', 1)[-1]
                    for alias in child.names
                    if alias.name and alias.name != '*'
                ]
        return [child.module.rsplit('.', 1)[-1]]
    return [
        alias.name.rsplit('.', 1)[-1]
        for alias in child.names
        if alias.name and alias.name != '*'
    ]
_D01_KIND_SPECS: dict[str, tuple[DiagnoseSeverity, str, str]] = {
    'cycle': (
        DiagnoseSeverity.INFO,
        "函数 '{fn}' 内延迟导入 {mod} (lazy import)——组合图环断路器，提升到顶部有硬环风险，属合法模式",
        '保留；若要消除需先重构断开模块环',
    ),
    'optional': (
        DiagnoseSeverity.INFO,
        "函数 '{fn}' 内延迟导入 {mod} (lazy import)——可选依赖容错模式（try/except 降级），属合法模式",
        '保留；若依赖为必装项，可移到模块顶部并删除容错降级',
    ),
    'marked': (
        DiagnoseSeverity.INFO,
        "函数 '{fn}' 内延迟导入 {mod} (lazy import)——显式设计标记（lazy-by-design），属有意保留",
        '保留；设计理由见行内注释',
    ),
    'stdlib': (
        DiagnoseSeverity.INFO,
        "函数 '{fn}' 内延迟导入标准库 {mod}——标准库已随解释器加载，"
        "函数级 import 无启动收益也无失败风险，属合法模式",
        '保留；仅当需要减少模块级命名空间污染时再上移',
    ),
    'plain': (
        DiagnoseSeverity.ERROR,
        "函数 '{fn}' 内存在延迟导入 {mod} (lazy import)",
        '将 import 语句移至模块顶部',
    ),
}
def _d01_exempt_kind(child: ast.Import | ast.ImportFrom, tgt_mod: str,
                     cur_mod: str, exempt: set[tuple[str, str]], source_lines: list[str],
                     pmap: dict) -> str:
    if cur_mod and (cur_mod, tgt_mod) in exempt:
        return 'cycle'
    if _is_optional_dep_fallback_import(child, pmap, tgt_mod):
        return 'optional'
    if _is_marked_lazy_import(child, source_lines):
        return 'marked'
    # 历史缺陷：标准库的延迟导入此前落到 'plain' 被报 ERROR「门禁错误」，
    # 而 ``weakref`` 这类 C 内置模块早已随解释器加载，函数级 import 既无
    # 启动收益也无失败风险（实测 diag_wiring_symbol_scan.py:418、
    # prevention_flow_exit_checks.py:1020 两处 P1 误报）。
    # 二次缺陷：此前按 ``tgt_mod``（``import os.path`` 的叶子名 ``path``）
    # 直接比对 stdlib_module_names，点号标准库导入永不命中仍报 ERROR；
    # 反之 ``from mypkg import json`` 又会按叶子名误豁免。改用与
    # ``_is_optional_dep_fallback_import`` 同一 root 感知判定，消除双口径。
    if _d01_tgt_is_stdlib(child, tgt_mod):
        return 'stdlib'
    return 'plain'


def _is_marked_lazy_import(child: ast.Import | ast.ImportFrom,
                           source_lines: list[str]) -> bool:
    for _ln in range(child.lineno, (child.end_lineno or child.lineno) + 1):
        if (0 < _ln <= len(source_lines)
                and 'lazy-by-design' in str(source_lines[_ln - 1])):
            return True
    return False
def _known_exception_name(node: ast.AST) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if (isinstance(node, ast.Attribute)
            and isinstance(node.value, ast.Name)
            and node.value.id == 'builtins'):
        return node.attr
    return dotted_name(node) if isinstance(node, ast.Attribute) else ''
def _import_root_specs(node: ast.AST) -> list[str]:
    if isinstance(node, ast.Import):
        return [a.name for a in node.names if a.name]
    if isinstance(node, ast.ImportFrom) and node.module:
        return [node.module]
    return []
def _is_optional_dep_fallback_import(import_node: ast.AST, parent_map: dict, tgt_mod: str) -> bool:
    if not tgt_mod:
        return False
    if _d01_tgt_is_stdlib(import_node, tgt_mod):
        return False
    return _try_protected_degradation(import_node, parent_map)
def _d01_tgt_is_stdlib(import_node: ast.AST, tgt_mod: str) -> bool:
    if isinstance(import_node, ast.ImportFrom) and import_node.level:
        return False
    _tgt_specs = [spec for spec in _import_root_specs(import_node)
                  if spec.split('.')[-1] == tgt_mod]
    return bool(_tgt_specs) and any(
        spec.split('.')[0] in sys.stdlib_module_names for spec in _tgt_specs)
_IMPORT_FAMILY_EXC = ('Exception', 'BaseException', 'ImportError',
                      'ModuleNotFoundError')
def _handler_digests_import_error(handler: ast.ExceptHandler) -> bool:
    if not any(n in _IMPORT_FAMILY_EXC
               for n in handler_exc_names(handler)):
        return False
    return not any(isinstance(s, ast.Raise)
                   for s in iter_handler_scope(handler))
def _enclosing_try_chain(import_node: ast.AST, parent_map: dict):
    cur, prev = import_node, import_node
    while cur in parent_map:
        cur = parent_map[cur]
        if isinstance(
            cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
        ):
            return
        if isinstance(cur, TRY_NODE_TYPES) and prev in cur.body:
            yield cur
        prev = cur
def _try_protected_degradation(import_node: ast.AST, parent_map: dict) -> bool:
    return any(
        _handler_digests_import_error(handler)
        for enclosing in _enclosing_try_chain(import_node, parent_map)
        for handler in enclosing.handlers
    )
def _handler_catches_import_error(handler: ast.ExceptHandler) -> bool:
    return any(n in ('ImportError', 'ModuleNotFoundError')
               for n in handler_exc_names(handler))
def nearest_owning_handler(node: ast.AST, pmap: dict) -> ast.ExceptHandler | None:
    return _nearest_ancestor(
        node, pmap, (ast.ExceptHandler,),
        (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef))
_TRACE_CALL_NAMES = frozenset({
    'log_swallowed', 'log_swallowed_entries', '_swallow',
    'safe_stderr_write', '_emit_cli_error',
    '_warn_fallback', '_log_fallback',
})
_TRACE_LOG_METHODS = frozenset({
    'debug', 'info', 'warning', 'warn', 'error', 'exception', 'critical',
})
_SILENT_OK_RE = re.compile(r'#\s*[A-Za-z_][\w.\-]*:silent-ok\b')
def _trace_call_node(node: ast.AST) -> bool:
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)):
        return False
    fn = node.value.func
    if isinstance(fn, ast.Name):
        return fn.id in _TRACE_CALL_NAMES
    if isinstance(fn, ast.Attribute):
        return (fn.attr in _TRACE_LOG_METHODS
                or fn.attr in _TRACE_CALL_NAMES)
    return False
def _d02_stmt_reraises_caught(stmt: ast.stmt,
                               handler: ast.ExceptHandler) -> bool:
    if not isinstance(stmt, ast.Raise):
        return False
    if stmt.exc is None:
        return True
    return bool(handler.name and isinstance(stmt.exc, ast.Name)
                and stmt.exc.id == handler.name)
def _d02_block_observes_or_reraises(stmts: list[ast.stmt],
                                    handler: ast.ExceptHandler) -> bool:
    for stmt in stmts:
        if (_trace_call_node(stmt)
                or _d02_stmt_reraises_caught(stmt, handler)):
            return True
        if (isinstance(stmt, ast.If)
                and _d02_block_observes_or_reraises(stmt.body, handler)
                and _d02_block_observes_or_reraises(stmt.orelse, handler)):
            return True
        if (isinstance(stmt, TRY_NODE_TYPES)
                and _d02_block_observes_or_reraises(stmt.finalbody, handler)):
            return True
    return False
def _d02_assignment_path_exempt(node: ast.AST, handler: ast.ExceptHandler,
                                pmap: dict) -> bool:
    current = node
    while current is not handler:
        parent = pmap.get(current)
        if parent is None:
            return False
        for field in ('body', 'orelse', 'finalbody'):
            block = getattr(parent, field, None)
            if isinstance(block, list) and current in block:
                if _d02_block_observes_or_reraises(block, handler):
                    return True
                break
        current = parent
    return False
def _handler_marked_silent_ok(handler: ast.ExceptHandler,
                              source_lines: list[str]) -> bool:
    start = handler.lineno
    end = getattr(handler, 'end_lineno', None) or start
    for ln in range(start, end + 1):
        if (0 < ln <= len(source_lines)
                and _SILENT_OK_RE.search(str(source_lines[ln - 1]))):
            return True
    return False
def detect_d02_degradation(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    tree = _prepared_tree(tree, filepath)
    if tree is None:
        return []
    issues = []
    pmap = parent_map(tree)
    source_lines = source_lines_or(code, source_lines)
    for node in tree_nodes(tree):
        _names = _d02_none_binding_targets(node)
        if not _names:
            continue
        handler = nearest_owning_handler(node, pmap)
        if handler is None or not _handler_catches_import_error(handler):
            continue
        if (_handler_marked_silent_ok(handler, source_lines)
                or _d02_assignment_path_exempt(node, handler, pmap)):
            continue
        for target_id in _names:
            issues.append(_import_issue(
                'D02', DiagnoseSeverity.INFO,
                f"可选依赖降级: except ImportError 将 '{target_id}' 设为 None(合法容错模式)",
                node.lineno,
                '保留该容错降级模式；如需依赖缺失即报错，可移除 fallback'))
    return issues
def _d02_none_binding_targets(node: ast.AST) -> list[str]:
    if isinstance(node, ast.Assign):
        value, targets = node.value, node.targets
    elif isinstance(node, ast.AnnAssign) and node.value is not None:
        value, targets = node.value, [node.target]
    else:
        return []
    if not (isinstance(value, ast.Constant) and value.value is None):
        return []
    return [t.id for t in targets if isinstance(t, ast.Name)]
def _module_stem(filepath: str) -> str:
    base = _os.path.basename(_filepath_text(filepath))
    return base[:-3] if base.lower().endswith('.py') else base
def _relative_module_name(filepath: str) -> str:
    filepath = _filepath_text(filepath)
    if not filepath or _os.path.isabs(filepath):
        return ''
    path = filepath.replace('\\', '/').strip('/')
    if path.lower().endswith('.py'):
        path = path[:-3]
    return path.replace('/', '.')
def _package_context(filepath: str) -> tuple[str, list[str]]:
    relative = _relative_module_name(filepath)
    resolved = resolve_module_name(_filepath_text(filepath))
    current = relative or resolved
    if current == _module_stem(filepath) and resolved != current:
        current = resolved
    if not current:
        return '', []
    package_parts = current.split('.')
    if (_module_stem(filepath) != '__init__'
            or package_parts[-1] == '__init__'):
        package_parts.pop()
    return current, package_parts
def _self_module_candidates(filepath: str) -> set[str]:
    return {c for c in (resolve_module_name(_filepath_text(filepath)),
                        _relative_module_name(filepath)) if c}
def _self_reference_context(filepath: str) -> tuple[set[str], str]:
    resolved = resolve_module_name(_filepath_text(filepath))
    stem = _module_stem(filepath)
    bare = stem if resolved and resolved == stem else ''
    return _self_module_candidates(filepath), bare
def _d04_effective_import_module(node: ast.ImportFrom,
                                  filepath: str) -> str:
    module = node.module or ''
    if not node.level:
        return module
    current, package_parts = _package_context(filepath)
    if not current:
        return ''
    parents_to_drop = node.level - 1
    if parents_to_drop >= len(package_parts):
        return ''
    if parents_to_drop:
        package_parts = package_parts[:-parents_to_drop]
    if module:
        package_parts.append(module)
    return '.'.join(package_parts)
def detect_d04_circular_module(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    tree = _prepared_tree(tree, filepath)
    if tree is None or not filepath:
        return []
    issues = []
    reported: set[str] = set()
    candidates, bare_self = _self_reference_context(filepath)
    for node in iter_module_scope_nodes(tree, descend_classes=False):
        if not isinstance(node, ast.ImportFrom):
            continue
        imp_mod = _d04_effective_import_module(node, filepath)
        if not imp_mod or imp_mod in reported:
            continue
        if _d04_has_parent_target(
                node, imp_mod, bare_self, candidates):
            issues.append(_import_issue(
                'D04', DiagnoseSeverity.WARN,
                f'可能的鸡与蛋问题: 从父包 {imp_mod} 导入，可能是循环依赖',
                node.lineno, _CONSTRAINT_SUGGESTIONS.get(
                    'D04', '检查导入链并收敛依赖方向')))
            reported.add(imp_mod)
    return issues
def _d04_is_parent_package(imp_mod: str, candidates: set[str]) -> bool:
    return any(_m.startswith(imp_mod + '.') for _m in candidates if _m)
def _d04_has_parent_target(node: ast.ImportFrom, imp_mod: str,
                           bare_self: str, candidates: set[str]) -> bool:
    if not _d04_is_parent_package(imp_mod, candidates):
        return False
    if _d13_is_self_ref(imp_mod, bare_self, candidates):
        return False
    for alias in node.names:
        if alias.name == '*':
            return True
        if not _d13_is_self_ref(
                f'{imp_mod}.{alias.name}', bare_self, candidates):
            return True
    return False
def detect_d06_dynamic_import(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    source_lines = source_lines_or(code, source_lines)
    tree = _prepared_tree(tree, filepath)
    if isinstance(tree, ast.Module):
        return _d06_ast_issues(tree, source_lines, code, filepath)
    return _text_pattern_issues(
        source_lines, 'D06', _D06_TEXT_PATTERNS,
        string_comment_spans(code))
def _d06_ast_issues(
        tree: ast.Module,
        source_lines: list[str],
        code: str,
        filepath: str,
) -> list[DiagnoseIssue]:
    issues = []
    _lines = source_lines or []
    table = collect_lexical_scope_table(tree)
    scopes = _node_lexical_scopes(tree, table)
    bindings = _d06_binding_names(tree, table, scopes)
    resolver = ScopeNameResolver(code, filepath, tree, set())
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        _callee = _d06_dynamic_callee(
            node.func, scopes[node], table, bindings, resolver)
        if _callee is None:
            continue
        if _lines and _is_marked_lazy_import(node, _lines):
            continue
        issues.append(_import_issue(
            'D06', DiagnoseSeverity.WARN,
            f'动态导入: {_callee}() — 确认是否有意为之(插件/延迟加载是合法模式)',
            node.lineno,
            '若为插件/延迟加载等合法用途可忽略；若为可静态化的固定模块,考虑模块级 import'))
    return issues
class _D06Bindings(NamedTuple):
    by_scope: dict[ast.AST, dict[str, str]]
    recognized: dict[tuple[str, str], str]
def _d06_binding_names(tree: ast.Module, table,
                       scopes: dict[ast.AST, ast.AST]) -> _D06Bindings:
    bindings: dict[ast.AST, dict[str, str]] = {}
    recognized: dict[tuple[str, str], str] = {}
    for node in tree_nodes(tree):
        if not isinstance(node, (ast.Import, ast.ImportFrom)):
            continue
        scope = scopes[node]
        for alias in node.names:
            if alias.name == '*':
                continue
            if isinstance(node, ast.Import):
                name = alias.asname or alias.name.split('.')[0]
                if alias.name == 'importlib' or (
                        alias.asname is None
                        and alias.name.startswith('importlib.')):
                    kind = 'module'
                elif alias.name == 'builtins' or (
                        alias.asname is None
                        and alias.name.startswith('builtins.')):
                    kind = 'builtins_module'
                else:
                    kind = ''
            else:
                name = alias.asname or alias.name
                if (not node.level and node.module == 'importlib'
                        and alias.name == 'import_module'):
                    kind = 'from'
                elif (not node.level and node.module == 'builtins'
                      and alias.name == '__import__'):
                    kind = 'builtin'
                else:
                    kind = ''
            binding_scope = _import_binding_scope(table, scope, name)
            bindings.setdefault(binding_scope, {})[name] = kind
            source = {
                'module': 'importlib',
                'builtins_module': 'builtins',
                'from': 'importlib.import_module',
                'builtin': 'builtins.__import__',
            }.get(kind)
            if source is not None:
                recognized[(name, source)] = kind
    return _D06Bindings(bindings, recognized)
def _d06_visible_import_kind(root: str, scope: ast.AST, table,
                             bindings: _D06Bindings) -> str | None:
    direct = scope
    while scope is not None:
        visible = not (isinstance(scope, ast.ClassDef) and scope is not direct)
        if visible:
            if root in table.shadow_bound.get(scope, frozenset()):
                return ''
            imports = bindings.by_scope.get(scope, {})
            if root in imports:
                return imports[root]
            if root in table.bound.get(scope, frozenset()):
                return ''
        scope = table.parent.get(scope)
    return None
def _d06_dynamic_callee(func: ast.expr, scope: ast.AST, table,
                        bindings: _D06Bindings,
                        resolver: ScopeNameResolver) -> str | None:
    root = _d06_callee_root(func)
    if not root:
        return None
    kind = _d06_visible_import_kind(root, scope, table, bindings)
    root_node = (func if isinstance(func, ast.Name)
                 else func.value if isinstance(func, ast.Attribute)
                 and isinstance(func.value, ast.Name) else None)
    if root_node is not None:
        import_path = resolver.import_path(root_node)
        if import_path is not None:
            kind = bindings.recognized.get((root, import_path), '')
        elif kind is not None:
            kind = ''
    if isinstance(func, ast.Name):
        if kind in ('from', 'builtin'):
            return func.id
        if func.id == '__import__':
            return func.id if kind is None else None
        return None
    if not isinstance(func, ast.Attribute):
        return None
    if func.attr == 'import_module':
        recognized = kind == 'module' or (kind is None and root == 'importlib')
    elif func.attr == '__import__':
        recognized = (kind == 'builtins_module'
                      or (kind is None and root == 'builtins'))
    else:
        return None
    if not recognized:
        return None
    _chain = dotted_name(func.value)
    return f'{_chain}.{func.attr}' if _chain == root else None
def _d06_callee_root(func: ast.expr) -> str:
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        return func.value.id
    return ''
_D06_TEXT_PATTERNS: tuple[tuple[re.Pattern, str, str], ...] = (
    (re.compile(r'(?<![\w.])importlib\.import_module'),
     '动态导入: importlib.import_module() — 确认是否有意为之(插件/延迟加载是合法模式)',
     '若为插件/延迟加载等合法用途可忽略；若为可静态化的固定模块,考虑模块级 import'),
    (re.compile(r'(?<![\w.])__import__\s*\('),
     '动态导入: __import__() — 确认是否有意为之(动态加载是合法模式)',
     '若为合法动态加载可忽略；若为固定模块,考虑模块级 import'),
)
def _hit_in_code(line_no: int, col: int, spans: dict[int, list[tuple[int, int]]] | None) -> bool:
    if spans is None:
        return True
    return not any(s <= col < e for s, e in spans.get(line_no, ()))
def _text_pattern_issues(
        source_lines: list[str], check_id: str,
        patterns: tuple[tuple[re.Pattern, str, str], ...],
        spans: dict[int, list[tuple[int, int]]] | None) -> list[DiagnoseIssue]:
    issues: list[DiagnoseIssue] = []
    for line_no, line in enumerate(source_lines, 1):
        for pattern, message, suggestion in patterns:
            for match in pattern.finditer(line):
                if not _hit_in_code(line_no, match.start(), spans):
                    continue
                issues.append(_import_issue(
                    check_id, DiagnoseSeverity.WARN, message,
                    line_no, suggestion))
                break
    return issues
def detect_d08_circular_dep(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    tree = _prepared_tree(tree, filepath)
    if tree is None or not filepath:
        return []
    issues = []
    candidates, bare_self = _self_reference_context(filepath)
    for node in tree_nodes(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                if _d13_is_self_ref(alias.name, bare_self, candidates):
                    issues.append(_import_issue(
                        'D08', DiagnoseSeverity.ERROR,
                        f'循环依赖: 模块导入自身 import {alias.name}',
                        node.lineno, D_ARCH_RULE_SUGGESTIONS['D08']))
        elif isinstance(node, ast.ImportFrom) and not node.level:
            subject = _self_from_import_subject(
                node, node.module or '', bare_self, candidates)
            if subject:
                issues.append(_import_issue(
                    'D08', DiagnoseSeverity.ERROR,
                    f'循环依赖: 模块导入自身 {subject}',
                    node.lineno, D_ARCH_RULE_SUGGESTIONS['D08']))
    return issues
def detect_d13_import_chain(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    tree = _prepared_tree(tree, filepath)
    if tree is None:
        return []
    issues = []
    self_candidates: set[str] = set()
    bare_self = ''
    if filepath:
        self_candidates, bare_self = _self_reference_context(filepath)
    for node in tree_nodes(tree):
        if isinstance(node, ast.ImportFrom) and node.level:
            issues.extend(
                _d13_from_issues(node, bare_self, self_candidates, filepath))
    return issues
def _d13_is_self_ref(module_name: str, bare_self: str,
                     self_candidates: set) -> bool:
    return module_name in self_candidates or (
        bool(bare_self) and module_name == bare_self)
def _self_from_import_subject(node: ast.ImportFrom, imported_module: str,
                              bare_self: str,
                              self_candidates: set[str]) -> str:
    if not imported_module:
        return ''
    direct_self = (
        not (node.level and not node.module)
        and _d13_is_self_ref(imported_module, bare_self, self_candidates))
    alias_self = ''
    for alias in node.names:
        if alias.name == '*':
            continue
        target = f'{imported_module}.{alias.name}'
        if _d13_is_self_ref(target, bare_self, self_candidates):
            alias_self = alias.name
            break
    if not (direct_self or alias_self):
        return ''
    module_text = '.' * (node.level or 0) + (node.module or '')
    return (f'from {module_text} import {alias_self}'
            if alias_self and not direct_self
            else f'from {module_text} import ...')
def _d13_from_issues(node: ast.ImportFrom, bare_self: str,
                     self_candidates: set[str], filepath: str) -> list[DiagnoseIssue]:
    imported_module = _d04_effective_import_module(node, filepath)
    if not imported_module:
        if filepath and _package_context(filepath)[0]:
            return [_import_issue(
                'D13', DiagnoseSeverity.ERROR,
                '相对导入越出顶层包或当前模块没有父包',
                node.lineno, '改为包内合法相对导入或绝对导入')]
        depth_issue = _d13_relative_depth_issue(node)
        return [depth_issue] if depth_issue is not None else []
    issues = []
    depth_issue = _d13_relative_depth_issue(node)
    if depth_issue is not None:
        issues.append(depth_issue)
    subject = _self_from_import_subject(
        node, imported_module, bare_self, self_candidates)
    if subject:
        issues.append(_import_issue(
            'D13', DiagnoseSeverity.ERROR,
            f'模块导入自身: {subject}（相对导入自引用）',
            node.lineno, '移除自身的导入'))
    return issues
def _d13_relative_depth_issue(node: ast.ImportFrom) -> DiagnoseIssue | None:
    if not (node.level and node.level > 3):
        return None
    return _import_issue(
        'D13', DiagnoseSeverity.WARN,
        '相对导入层级过深(' + str(node.level) + '级)',
        node.lineno, '减少相对导入层级,考虑使用绝对导入')
_D15_MESSAGE = ('动态注册: 使用 {kind} 动态注入 — 应改为静态注册表')
_D15_SUGGESTION = '若为动态注册框架模式可保留；若可改为显式注册表则重构'
def _d15_matches_canonical_name(
        node: ast.Name,
        resolver: ScopeNameResolver,
        name: str,
        import_path: str,
) -> bool:
    resolved = resolver.import_path(node)
    if resolved is not None:
        return resolved == import_path
    return node.id == name and not resolver.is_bound(node)
def _d15_is_globals_call(node: ast.AST,
                         resolver: ScopeNameResolver) -> bool:
    if not isinstance(node, ast.Call):
        return False
    func = node.func
    if isinstance(func, ast.Name):
        return _d15_matches_canonical_name(
            func, resolver, 'globals', 'builtins.globals')
    return (isinstance(func, ast.Attribute)
            and func.attr == 'globals'
            and isinstance(func.value, ast.Name)
            and resolver.import_path(func.value) == 'builtins')
def _d15_is_globals_subscript(target: ast.expr,
                              resolver: ScopeNameResolver) -> bool:
    return (isinstance(target, ast.Subscript)
            and _d15_is_globals_call(target.value, resolver))
def _d15_mentions_self_name(expr: ast.expr) -> bool:
    return any(isinstance(node, ast.Name) and node.id == '__name__'
               for node in walk_nodes(expr))
def _d15_is_sys_modules_self(target: ast.expr,
                             resolver: ScopeNameResolver) -> bool:
    if not isinstance(target, ast.Subscript):
        return False
    base = target.value
    if isinstance(base, ast.Name):
        return (resolver.import_path(base) == 'sys.modules'
                and _d15_mentions_self_name(target.slice))
    if not (isinstance(base, ast.Attribute) and base.attr == 'modules'
            and isinstance(base.value, ast.Name)):
        return False
    receiver = base.value
    return (_d15_matches_canonical_name(receiver, resolver, 'sys', 'sys')
            and _d15_mentions_self_name(target.slice))
def _d15_is_globals_update(node: ast.AST,
                           resolver: ScopeNameResolver) -> bool:
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == 'update'
            and _d15_is_globals_call(node.func.value, resolver))
def detect_d15_static_register(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    tree = _prepared_tree(tree, filepath)
    if tree is None:
        return []
    issues: list[DiagnoseIssue] = []
    resolver = ScopeNameResolver(code, filepath, tree, set())
    for node in tree_nodes(tree):
        targets: list[ast.expr] = []
        kind = ''
        if isinstance(node, ast.Assign):
            targets = list(node.targets)
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
            targets = [node.target]
        elif _d15_is_globals_update(node, resolver):
            issues.append(_import_issue(
                'D15', DiagnoseSeverity.WARN,
                _D15_MESSAGE.format(kind='globals().update()'),
                node.lineno, _D15_SUGGESTION))
            continue
        for target in targets:
            if _d15_is_globals_subscript(target, resolver):
                kind = 'globals()'
            elif _d15_is_sys_modules_self(target, resolver):
                kind = 'sys.modules'
            else:
                continue
            issues.append(_import_issue(
                'D15', DiagnoseSeverity.WARN,
                _D15_MESSAGE.format(kind=kind),
                node.lineno, _D15_SUGGESTION))
            break
    return issues
_NOQA_F401_DIRECTIVE_RE = re.compile(
    r'#\s*noqa\b\s*(?::\s*(?P<codes>'
    r'[A-Z](?:[A-Z0-9]|\s*,\s*(?=[A-Z]))*))?',
    re.IGNORECASE)
def _noqa_f401_line(line_no: int, source_lines: list[str]) -> bool:
    if not (0 < line_no <= len(source_lines)):
        return False
    _m = _NOQA_F401_DIRECTIVE_RE.search(str(source_lines[line_no - 1]))
    if _m is None:
        return False
    _codes = _m.group('codes')
    if _codes is None:
        return True
    return any(_c.strip().lower() == 'f401' for _c in _codes.split(','))
def _stmt_is_backslash_continued(node: ast.Import | ast.ImportFrom, source_lines: list[str]) -> bool:
    for _ln in range(node.lineno, node.end_lineno or node.lineno):
        if not (0 < _ln <= len(source_lines)):
            continue
        _code = str(source_lines[_ln - 1]).split('#', 1)[0].rstrip()
        if _code.endswith('\\'):
            return True
    return False
_D27_LITERAL_PATHS = frozenset({
    'typing.Literal', 'typing_extensions.Literal',
})
_D27_ANNOTATED_PATHS = frozenset({
    'typing.Annotated', 'typing_extensions.Annotated',
})
_D27_TYPING_MODULE_PATHS = frozenset({'typing', 'typing_extensions'})
class _D27ForwardRefContext(NamedTuple):
    resolver: ScopeNameResolver | None
    table: Any
    imported_names: dict[ast.AST, dict[str, dict[str, int]]]
    scope: ast.AST
def _d27_context_import_path(
        name: str, context: _D27ForwardRefContext,
) -> str:
    import_scope = _d27_resolve_import(
        context.table, context.imported_names, context.scope, name)
    if (import_scope is None
            or name in context.table.shadow_bound.get(
                import_scope, frozenset())):
        return ''
    paths = context.imported_names[import_scope][name]
    return next(iter(paths)) if len(paths) == 1 else ''
def _d27_value_import_path(
        value: ast.expr, context: _D27ForwardRefContext | None,
) -> str:
    if context is None:
        return ''
    root = (value if isinstance(value, ast.Name)
            else value.value if isinstance(value, ast.Attribute)
            and isinstance(value.value, ast.Name) else None)
    if root is None:
        return ''
    resolved = (context.resolver.import_path(root)
                if context.resolver is not None else None)
    if resolved is None:
        resolved = _d27_context_import_path(root.id, context)
    if resolved and isinstance(value, ast.Attribute):
        return f'{resolved}.{value.attr}'
    return resolved or ''
def _d27_subscript_value_position(
        value: ast.expr, index: int,
        context: _D27ForwardRefContext | None = None,
) -> bool:
    import_path = _d27_value_import_path(value, context)
    if import_path:
        if import_path in _D27_LITERAL_PATHS:
            return True
        return import_path in _D27_ANNOTATED_PATHS and index > 0
    _tail = ''
    if isinstance(value, ast.Attribute):
        _tail = value.attr
    elif isinstance(value, ast.Name):
        _tail = value.id
    if _tail == 'Literal':
        return True
    return _tail == 'Annotated' and index > 0
def _d27_collect_subscript_names(
        node: ast.Subscript, used_names: set[str],
        strings_only: bool = False,
        context: _D27ForwardRefContext | None = None,
) -> None:
    _d27_collect_forward_ref_names(
        node.value, used_names, strings_only=strings_only, context=context)
    _slice = node.slice
    _elts = _slice.elts if isinstance(_slice, ast.Tuple) else [_slice]
    for _idx, _elt in enumerate(_elts):
        if (isinstance(_elt, ast.Constant) and isinstance(_elt.value, str)
                and _d27_subscript_value_position(
                    node.value, _idx, context)):
            continue
        _d27_collect_forward_ref_names(
            _elt, used_names, strings_only=strings_only, context=context)
def _d27_collect_forward_ref_names(
        node: ast.expr, used_names: set[str],
        strings_only: bool = False,
        context: _D27ForwardRefContext | None = None,
) -> None:
    if isinstance(node, ast.Name):
        if not strings_only:
            used_names.add(node.id)
        return
    if isinstance(node, ast.Constant):
        if isinstance(node.value, str):
            try:
                forward_ref = ast.parse(node.value, mode='eval')
            except (SyntaxError, ValueError, RecursionError) as _swallowed_exc:
                log_swallowed(
                    __name__, _swallowed_exc, context=f'_d27_collect_forward_ref_names:{type(_swallowed_exc).__name__}')
                for _m in re.findall(r'[A-Za-z_][A-Za-z0-9_]*', node.value):
                    used_names.add(_m)
            else:
                _d27_collect_forward_ref_names(
                    forward_ref.body, used_names, context=context)
        return
    if isinstance(node, ast.Subscript):
        _d27_collect_subscript_names(
            node, used_names, strings_only=strings_only, context=context)
        return
    for _child in ast.iter_child_nodes(node):
        _d27_collect_forward_ref_names(
            _child, used_names, strings_only=strings_only, context=context)
def _d27_register_alias(alias: ast.alias, stmt_lineno: int, name: str,
                        import_path: str, source_lines: list[str],
                        imported_names: dict[str, dict[str, int]]) -> None:
    _alias_ln = getattr(alias, 'lineno', stmt_lineno)
    if _alias_ln != stmt_lineno and _noqa_f401_line(_alias_ln, source_lines):
        return
    imported_names.setdefault(name, {}).setdefault(import_path, _alias_ln)
def _d27_is_submodule_side_effect_import(alias: ast.alias) -> bool:
    return alias.asname is None and '.' in alias.name
def _d27_register_import_aliases(node: ast.Import, source_lines: list[str],
                                 imported_names: dict[str, dict[str, int]]) -> None:
    if _d27_stmt_noqa_exempt(node, source_lines):
        return
    import_paths = _import_alias_paths(node)
    for alias in node.names:
        if _d27_is_submodule_side_effect_import(alias):
            continue
        name = alias.asname or alias.name.split('.')[0]
        _d27_register_alias(alias, node.lineno, name, import_paths[name],
                            source_lines, imported_names)
def _d27_register_from_aliases(node: ast.ImportFrom, source_lines: list[str],
                               imported_names: dict[str, dict[str, int]]) -> None:
    if node.module == '__future__':
        return
    if _d27_stmt_noqa_exempt(node, source_lines):
        return
    import_paths = _import_alias_paths(node)
    for alias in node.names:
        name = alias.asname or alias.name
        if name != '*':
            _d27_register_alias(alias, node.lineno, name, import_paths[name],
                                source_lines, imported_names)
def _d27_stmt_noqa_exempt(node: ast.Import | ast.ImportFrom,
                          source_lines: list[str]) -> bool:
    if _noqa_f401_line(node.lineno, source_lines):
        return True
    return (node.end_lineno != node.lineno
            and _stmt_is_backslash_continued(node, source_lines)
            and _noqa_f401_line(node.end_lineno, source_lines))
def _d27_string_literals(value: ast.expr, consts: dict[str, ast.expr] | None = None,
                         _seen: frozenset[str] = frozenset()):
    if isinstance(value, ast.Constant):
        if isinstance(value.value, str):
            yield value.value
        return
    if isinstance(value, ast.BinOp) and isinstance(value.op, ast.Add):
        yield from _d27_string_literals(value.left, consts, _seen)
        yield from _d27_string_literals(value.right, consts, _seen)
        return
    if isinstance(value, ast.Starred):
        yield from _d27_string_literals(value.value, consts, _seen)
        return
    if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        for elt in value.elts:
            yield from _d27_string_literals(elt, consts, _seen)
        return
    if isinstance(value, ast.Name) and consts is not None and value.id not in _seen:
        target = consts.get(value.id)
        if target is not None:
            yield from _d27_string_literals(target, consts, _seen | {value.id})
def _d27_module_string_consts(tree: ast.Module) -> dict[str, ast.expr]:
    consts: dict[str, ast.expr] = {}
    for node in ast.iter_child_nodes(tree):
        target = value = None
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            target, value = node.targets[0], node.value
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            target, value = node.target, node.value
        if isinstance(target, ast.Name) and value is not None:
            consts.setdefault(target.id, value)
    return consts
def _d27_collect_dunder_all_mutate_call(node: ast.Call, used_names: set[str],
                                        consts: dict[str, ast.expr]) -> None:
    _f = node.func
    if not (isinstance(_f, ast.Attribute)
            and _f.attr in ('append', 'extend', 'insert')):
        return
    if not _d27_is_dunder_all(_f.value):
        return
    for arg in node.args:
        used_names.update(_d27_string_literals(arg, consts))
_D27_FRAME_NODES = (ast.FunctionDef, ast.AsyncFunctionDef,
                    ast.Lambda, ast.ClassDef)
_D27_COMP_SCOPE_NODES = (ast.ListComp, ast.SetComp, ast.DictComp,
                         ast.GeneratorExp)
def _d27_definition_header_nodes(node: ast.AST) -> list[ast.AST]:
    headers = definition_time_expressions(node)
    headers.extend(getattr(node, "type_params", ()) or ())
    return headers
def _node_lexical_scopes(tree: ast.Module, table) -> dict[ast.AST, ast.AST]:
    parents = parent_map(tree)
    header_scopes: dict[ast.AST, ast.AST] = {}
    for scope, outer in table.parent.items():
        if isinstance(scope, _D27_FRAME_NODES):
            headers = _d27_definition_header_nodes(scope)
        elif isinstance(scope, ast.ExceptHandler):
            headers = [scope.type] if scope.type is not None else []
        elif (isinstance(scope, _D27_COMP_SCOPE_NODES)
              and scope.generators):
            headers = [scope.generators[0].iter]
        else:
            continue
        for header in headers:
            stack = [header]
            while stack:
                current = stack.pop()
                if current in table.parent:
                    continue
                header_scopes[current] = outer
                stack.extend(ast.iter_child_nodes(current))
    scopes: dict[ast.AST, ast.AST] = {}
    for node in tree_nodes(tree):
        outer = header_scopes.get(node)
        if outer is not None:
            scopes[node] = outer
            continue
        current = node
        while current is not tree and current not in table.parent:
            parent = parents.get(current)
            if parent is None:
                current = tree
            else:
                current = parent
        scopes[node] = current
    return scopes
def _import_binding_scope(table, scope: ast.AST, name: str) -> ast.AST:
    if name in table.bound.get(scope, frozenset()):
        return scope
    current = table.parent.get(scope)
    while current is not None:
        if name in table.bound.get(current, frozenset()):
            return current
        current = table.parent.get(current)
    return scope
def _d27_resolve_import(table, imported_names: dict, scope: ast.AST,
                        name: str) -> ast.AST | None:
    direct = scope
    while scope is not None:
        visible = not (isinstance(scope, ast.ClassDef) and scope is not direct)
        if visible and name in imported_names.get(scope, {}):
            return scope
        if visible and name in table.shadow_bound.get(scope, frozenset()):
            return None
        scope = table.parent.get(scope)
    return None
def _d27_collect_all_import_bindings(tree, table, scopes):
    imported_names: dict[ast.AST, dict[str, dict[str, int]]] = {}
    for node in tree_nodes(tree):
        node_imports: dict[str, dict[str, int]] = {}
        if isinstance(node, ast.Import):
            _d27_register_import_aliases(node, [], node_imports)
        elif isinstance(node, ast.ImportFrom):
            _d27_register_from_aliases(node, [], node_imports)
        else:
            continue
        for name, paths in node_imports.items():
            binding_scope = _import_binding_scope(table, scopes[node], name)
            bound_paths = imported_names.setdefault(
                binding_scope, {}).setdefault(name, {})
            for import_path, line in paths.items():
                bound_paths.setdefault(import_path, line)
    return imported_names
_D27_MODULE_NOQA_RE = re.compile(
    r'#\s*(?:ruff|flake8)\s*:\s*noqa\b'
    r'(?:\s*:\s*(?P<codes>[A-Z0-9,\s]*))?',
    re.IGNORECASE)
def _d27_module_noqa_f401(source_lines: list[str]) -> bool:
    for line in source_lines[:30]:
        m = _D27_MODULE_NOQA_RE.search(str(line))
        if not m:
            continue
        codes = m.group('codes')
        if codes is None or any(
                code.strip().upper() == 'F401' for code in codes.split(',')):
            return True
    return False
def detect_d27_dead_import(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    if filepath and _os.path.basename(filepath) == '__init__.py':
        return issues
    tree = _prepared_tree(tree, filepath)
    if tree is None:
        return []
    source_lines = source_lines_or(code, source_lines)
    if _d27_module_noqa_f401(source_lines):
        return issues
    resolver = ScopeNameResolver(code, filepath, tree, set())
    table, imported_names, references, exported_names, degraded_names = (
        _d27_collect_bindings_and_refs(tree, source_lines, resolver))
    used_bindings: set[tuple[ast.AST, str, str]] = set()
    for scope, name, reference_node in references:
        import_scope = _d27_resolve_import(
            table, imported_names, scope, name)
        if import_scope is None:
            continue
        # Del 上下文与字符串注解一样是对绑定的整体引用：``_d27_name_ref``
        # 已把 ``del os`` 记为引用（与 ruff/pyflakes F401 口径一致），但
        # ``ScopeNameResolver.import_path`` 仅为 Load 上下文建表，Del 引用
        # 若走路径解析会被静默丢弃而误报死导入；此处按导入作用域整体标已用。
        if (reference_node is None
                or isinstance(reference_node.ctx, ast.Del)):
            for import_path in imported_names[import_scope][name]:
                used_bindings.add((import_scope, name, import_path))
            continue
        import_path = resolver.import_path(reference_node)
        if import_path is not None:
            used_bindings.add((import_scope, name, import_path))
    for name in exported_names:
        for import_path in imported_names.get(tree, {}).get(name, {}):
            used_bindings.add((tree, name, import_path))
    for scope, names in imported_names.items():
        for name, paths in names.items():
            for import_path, line in paths.items():
                if ((scope, name, import_path) in used_bindings
                        or name.startswith('_')):
                    continue
                if (scope, name, import_path) in degraded_names:
                    continue
                issues.append(_import_issue(
                    'D27', DiagnoseSeverity.WARN,
                    f"死导入: '{name}' 已导入但未使用",
                    line, _CONSTRAINT_SUGGESTIONS['D27']))
    return issues
_D27_TYPE_ALIAS_PATHS = frozenset({
    'typing.TypeAlias', 'typing_extensions.TypeAlias',
})
_D27_TYPE_ALIAS_NODE = getattr(ast, 'TypeAlias', None)
def _d27_is_type_alias_annotation(
        node: ast.expr, resolver: ScopeNameResolver | None,
) -> bool:
    if isinstance(node, ast.Name):
        if resolver is None:
            return node.id == 'TypeAlias'
        return resolver.import_path(node) in _D27_TYPE_ALIAS_PATHS
    if not (isinstance(node, ast.Attribute) and node.attr == 'TypeAlias'
            and isinstance(node.value, ast.Name)):
        return False
    if resolver is None:
        return True
    return resolver.import_path(node.value) in _D27_TYPING_MODULE_PATHS
def _d27_type_alias_value(
        node: ast.AST, resolver: ScopeNameResolver | None,
) -> ast.expr | None:
    if (_D27_TYPE_ALIAS_NODE is not None
            and isinstance(node, _D27_TYPE_ALIAS_NODE)):
        return node.value
    if (isinstance(node, ast.AnnAssign) and node.value is not None
            and _d27_is_type_alias_annotation(node.annotation, resolver)):
        return node.value
    return None
def _d27_collect_bindings_and_refs(
        tree: ast.Module, source_lines: list[str],
        resolver: ScopeNameResolver | None = None,
) -> tuple:
    table = collect_lexical_scope_table(tree)
    scopes = _node_lexical_scopes(tree, table)
    all_imported_names = _d27_collect_all_import_bindings(tree, table, scopes)
    imported_names: dict[ast.AST, dict[str, dict[str, int]]] = {}
    references: list[tuple[ast.AST, str]] = []
    exported_names: set[str] = set()
    degraded_names: set[tuple[ast.AST, str, str]] = set()
    consts = _d27_module_string_consts(tree)
    parents = parent_map(tree)
    for node in tree_nodes(tree):
        scope = scopes[node]
        node_imports: dict[str, dict[str, int]] = {}
        if isinstance(node, ast.Import):
            _d27_register_import_aliases(node, source_lines, node_imports)
        elif isinstance(node, ast.ImportFrom):
            _d27_register_from_aliases(node, source_lines, node_imports)
        guarded = (isinstance(node, (ast.Import, ast.ImportFrom))
                   and _d27_is_import_guard(node, parents))
        for name, paths in node_imports.items():
            binding_scope = _import_binding_scope(table, scope, name)
            bound_paths = imported_names.setdefault(
                binding_scope, {}).setdefault(name, {})
            for import_path, line in paths.items():
                bound_paths.setdefault(import_path, line)
                if guarded:
                    degraded_names.add((binding_scope, name, import_path))
        node_names: dict[str, ast.Name] = {}
        _d27_name_ref(node, node_names)
        references.extend(
            (scope, name, reference_node)
            for name, reference_node in node_names.items())
        if scope is tree:
            _d27_dunder_all_ref(node, exported_names, consts)
        annotation = None
        if isinstance(node, (ast.AnnAssign, ast.arg)):
            annotation = node.annotation
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            annotation = node.returns
        if annotation is not None:
            annotation_names: set[str] = set()
            context = _D27ForwardRefContext(
                resolver, table, all_imported_names, scopes[annotation])
            _d27_collect_forward_ref_names(
                annotation, annotation_names, strings_only=True,
                context=context)
            references.extend(
                (scopes[annotation], name, None) for name in annotation_names)
        alias_value = _d27_type_alias_value(node, resolver)
        if alias_value is not None:
            alias_names: set[str] = set()
            context = _D27ForwardRefContext(
                resolver, table, all_imported_names, scopes[alias_value])
            _d27_collect_forward_ref_names(
                alias_value, alias_names, strings_only=True, context=context)
            references.extend(
                (scopes[alias_value], name, None) for name in alias_names)
    return table, imported_names, references, exported_names, degraded_names
def _d27_is_import_guard(node: ast.AST, parents: dict) -> bool:
    current = node
    while True:
        parent = parents.get(current)
        if parent is None:
            return False
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.Lambda)):
            return False
        if (isinstance(parent, TRY_NODE_TYPES) and current in parent.body
                and any(_handler_digests_import_error(h)
                        for h in parent.handlers)):
            return True
        current = parent
def _d27_name_ref(node: ast.AST,
                  used_names: dict[str, ast.Name]) -> None:
    if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Load, ast.Del)):
        used_names[node.id] = node
    elif isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
        used_names[node.value.id] = node.value
def _d27_dunder_all_ref(node: ast.AST, used_names: set[str],
                        consts: dict[str, ast.expr]) -> None:
    _val = _d27_all_assign_value(node)
    if _val is not None:
        used_names.update(_d27_string_literals(_val, consts))
    elif isinstance(node, ast.Call):
        _d27_collect_dunder_all_mutate_call(node, used_names, consts)
def _d27_is_dunder_all(expr: ast.expr) -> bool:
    return isinstance(expr, ast.Name) and expr.id == '__all__'
def _d27_all_assign_value(node: ast.AST) -> ast.expr | None:
    if isinstance(node, ast.AugAssign):
        if not _d27_is_dunder_all(node.target):
            return None
        return node.value if isinstance(node.op, ast.Add) else None
    if isinstance(node, (ast.AnnAssign, ast.Assign)):
        targets = ((node.target,) if isinstance(node, ast.AnnAssign)
                   else node.targets)
        return node.value if any(_d27_is_dunder_all(t) for t in targets) else None
    return None
D_ARCH_CONSTRAINTS: list[dict[str, str]] = [
    {"rule_id": "D01", "name": "函数内延迟导入", "description": "函数体内 import 使导入依赖隐藏，易致运行时 NameError 与性能抖动", "suggestion": "将 import 语句移至模块顶部（有循环依赖时应收敛依赖方向而非下移 import）"},
    {"rule_id": "D02", "name": "静默降级导入", "description": "except ImportError 置 None 属合法容错，但须留痕（日志）或用 silent-ok 注释显式批准", "suggestion": "保留降级模式时注明合法用途；依赖缺失须报错时移除 fallback"},
    {"rule_id": "D03", "name": "兜底默认值返回", "description": "except 块返回硬编码默认值会吞掉真实异常根因", "suggestion": "显式错误处理或重新抛出异常，不静默返回默认值"},
    {"rule_id": "D04", "name": "疑似循环导入", "description": "从父包导入会引发鸡与蛋问题；自引用由 D08/D13 按导入形态唯一报告", "suggestion": "消除环：把共享依赖下沉到既有下层模块或收敛依赖方向；不新增文件/模块边界（GOV-01）"},
    {"rule_id": "D06", "name": "动态导入", "description": "importlib.import_module()/__import__()（含别名绑定）仅限插件或延迟加载等合法场景", "suggestion": "固定模块改为模块级静态导入"},
    {"rule_id": "D07", "name": "空函数体", "description": "仅含 pass 的函数若无文档即疑似未完成实现", "suggestion": "接口占位须加 docstring 说明；否则补全实现"},
    {"rule_id": "D08", "name": "模块自引用导入", "description": "模块通过绝对导入引用自身是典型循环依赖错误", "suggestion": D_ARCH_RULE_SUGGESTIONS['D08']},
    {"rule_id": "D09", "name": "微型文件", "description": "过小文件加剧模块碎片化，抬高导入链维护成本", "suggestion": D_ARCH_RULE_SUGGESTIONS['D09'] + '，未论证不得合并'},
    {"rule_id": "D12", "name": "碎片文件", "description": "行数/函数/类比例失衡的碎片文件难以定位与复用", "suggestion": D_ARCH_RULE_SUGGESTIONS['D12'] + '，未论证不得合并'},
    {"rule_id": "D13", "name": "导入结构违规", "description": "相对导入自引用、越出顶层包或层级过深破坏依赖方向", "suggestion": "移除自导入；使用包内合法相对导入；减少相对导入层级改用绝对导入"},
    {"rule_id": "D14", "name": "门面数量超标", "description": "门面 __init__.py 内自身定义的函数/类超过阈值（9）说明门面在承载实现职责；重导出聚合面不计入该口径", "suggestion": D_ARCH_RULE_SUGGESTIONS['D14']},
    {"rule_id": "D15", "name": "动态注册", "description": "globals()/sys.modules 动态注入绕过静态可分析性", "suggestion": "改为显式静态注册表"},
    {"rule_id": "D18", "name": "桩函数", "description": "仅返回 None 或空值/零值（False、0、''、[]、{}）的桩函数若无文档即疑似未完成", "suggestion": "接口占位须加 docstring；否则补全实现"},
    {"rule_id": "D21", "name": "重复元数据", "description": "__version__ 等元数据多处定义易失同步", "suggestion": "保留一处定义，使用独立 _version.py 作为 SSOT"},
    {"rule_id": "D23", "name": "自抛自接", "description": "try 块 raise 又被同层 except 捕获是无效包装", "suggestion": "移除 try/except 包装或改用不同异常类型"},
    {"rule_id": "D24", "name": "不可达 except", "description": "后置 except 子句的捕获类型全被前序处理器覆盖（裸 except、Exception 家族、同类型/超集重复）时永不可达", "suggestion": "合并 except 子句或调整顺序（具体异常在前）"},
    {"rule_id": "D25", "name": "全角字符", "description": "代码区（字符串/注释之外）的全角标点导致难以排查的语法/比较错误", "suggestion": "代码区一律使用半角字符；字符串/注释内的中文全角标点是合法内容"},
    {"rule_id": "D27", "name": "死导入", "description": "导入的符号/模块未被引用是死代码并掩盖真实依赖", "suggestion": D_ARCH_RULE_SUGGESTIONS['D27'] + '（try/ImportError 可选依赖探测除外）'},
    {"rule_id": "D29", "name": "语法错误", "severity": "BLOCK", "description": "语法错误使整模块不可导入，属最高优先级阻断", "suggestion": "写盘前用 compile(src, name, 'exec') 验证语法"},
    {"rule_id": "D33", "name": "重复文件", "description": "同一模块内顶层语句整段重复（≥3 次）是文件级双副本的前兆，双副本漂移与维护分叉由此扩散", "suggestion": "保留单一 SSOT，其余改为重导出或删除"},
]
_CONSTRAINT_SUGGESTIONS: dict[str, str] = {
    item["rule_id"]: item["suggestion"] for item in D_ARCH_CONSTRAINTS
}
def _is_trystar(node: ast.AST) -> bool:
    _star = getattr(ast, 'TryStar', None)
    return _star is not None and isinstance(node, _star)
_FUNC_NODE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef)
_NON_IMPL_DECORATORS = frozenset({
    'abstractmethod', 'abstractclassmethod', 'abstractstaticmethod',
    'abstractproperty', 'overload',
})
_VALUE_ACCESSOR_DECORATORS = frozenset({'property', 'cached_property'})
def _is_checkable_function(node: ast.AST, *,
                           value_accessor_ok: bool = False) -> bool:
    if not isinstance(node, _FUNC_NODE_TYPES):
        return False
    if node.name.startswith('__') and node.name.endswith('__'):
        return False
    decorators = {ast_name(d) for d in node.decorator_list}
    if decorators & _NON_IMPL_DECORATORS:
        return False
    return not (value_accessor_ok
                and decorators & _VALUE_ACCESSOR_DECORATORS)
def _has_docstring(node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    return bool(node.body) and is_docstring_stmt(node.body[0])
def _is_pass_only_body(node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    if _has_docstring(node):
        return False
    return len(node.body) == 1 and isinstance(node.body[0], ast.Pass)
def detect_d07_dead_code(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    tree = _prepared_tree(tree, filepath)
    if tree is None:
        return []
    return [
        DiagnoseIssue(
            check_id='D07', severity=DiagnoseSeverity.WARN,
            message=f"空函数体: '{node.name}()' 仅含 pass",
            line=node.lineno,
            suggestion='若为接口占位/抽象实现可保留并加 docstring 说明；若确为未完成则实现',
        )
        for node in tree_nodes(tree)
        if _is_checkable_function(node) and _is_pass_only_body(node)
    ]
_ZERO_CONSTANT_TYPES = (int, float, complex)
def _is_falsy_constant(constant: ast.Constant) -> bool:
    v = constant.value
    if isinstance(v, bool):
        return not v
    if isinstance(v, _ZERO_CONSTANT_TYPES):
        return v == 0
    return isinstance(v, (str, bytes)) and not v
def _is_empty_container(value: ast.expr) -> bool:
    if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        return not value.elts
    if isinstance(value, ast.Dict):
        return not value.keys
    return False
def _d18_is_hardcoded_stub_literal(value: ast.expr) -> bool:
    if isinstance(value, ast.Constant):
        return _is_falsy_constant(value)
    return _is_empty_container(value)
def _d18_single_return_stmt(node: ast.FunctionDef | ast.AsyncFunctionDef) -> ast.Return | None:
    if _has_docstring(node):
        return None
    if len(node.body) != 1 or not isinstance(node.body[0], ast.Return):
        return None
    return node.body[0]
def _d18_returns_none(stmt: ast.Return) -> bool:
    return stmt.value is None or (isinstance(stmt.value, ast.Constant)
                                  and stmt.value.value is None)
def _d18_literal_repr(value: ast.expr) -> str:
    return repr(value.value) if isinstance(value, ast.Constant) else ast.unparse(value)
def _d18_issue(node: ast.FunctionDef | ast.AsyncFunctionDef, desc: str,
               suggestion: str) -> DiagnoseIssue:
    return DiagnoseIssue(
        check_id='D18', severity=DiagnoseSeverity.WARN,
        message=f"桩函数: '{node.name}()' {desc}",
        line=node.lineno,
        suggestion=suggestion,
    )
def _d18_stub_issue(node: ast.FunctionDef | ast.AsyncFunctionDef) -> DiagnoseIssue | None:
    if not _is_checkable_function(node, value_accessor_ok=True):
        return None
    stmt = _d18_single_return_stmt(node)
    if stmt is None:
        return None
    if _d18_returns_none(stmt):
        return _d18_issue(node, "仅返回 None",
                          '若为接口占位/抽象方法可保留并加 docstring 说明')
    if not _d18_is_hardcoded_stub_literal(stmt.value):
        return None
    return _d18_issue(node, f"硬编码返回 {_d18_literal_repr(stmt.value)}",
                      '若为接口占位可保留；若确为未完成则实现')
def detect_d18_stub_function(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    tree = _prepared_tree(tree, filepath)
    if tree is None:
        return []
    issues: list[DiagnoseIssue] = []
    for node in tree_nodes(tree):
        issue = _d18_stub_issue(node)
        if issue is not None:
            issues.append(issue)
    return issues
_FULLWIDTH_CHARS_RE = re.compile('[\\uff01-\\uff5e\\u3000\\u3001\\u3002\\u201c\\u201d]')
_D25_INDENT_BLANKS = ' \t\f\v'
def detect_d25_fullwidth_chars(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    source_lines = [ln if isinstance(ln, str) else ''
                    for ln in source_lines_or(code, source_lines)]
    exempt_spans = string_comment_spans(code)
    fallback_spans = (None if exempt_spans is not None
                      else _fallback_string_comment_spans(source_lines))
    for i, line in enumerate(source_lines, 1):
        if line.lstrip(_D25_INDENT_BLANKS).startswith('#'):
            continue
        if not _FULLWIDTH_CHARS_RE.search(line):
            continue
        if _d25_line_exempt(line, i, exempt_spans, fallback_spans):
            continue
        issues.append(DiagnoseIssue(
            check_id='D25', severity=DiagnoseSeverity.WARN,
            message=f'全角字符: 第 {i} 行包含全角标点符号',
            line=i,
            suggestion=_CONSTRAINT_SUGGESTIONS['D25'],
        ))
    return issues
def _d25_line_exempt(line: str, line_no: int,
                     exempt_spans: dict[int, list[tuple[int, int]]] | None,
                     fallback_spans: dict[int, list[tuple[int, int]]] | None) -> bool:
    spans = exempt_spans if exempt_spans is not None else fallback_spans
    if spans is None:
        return False
    return _d25_line_fullwidth_exempt(line, line_no, spans)
def _d25_line_fullwidth_exempt(line: str, line_no: int, spans: dict[int, list[tuple[int, int]]]) -> bool:
    line_spans = spans.get(line_no)
    if not line_spans:
        return False
    for m in _FULLWIDTH_CHARS_RE.finditer(line):
        col_pos = m.start()
        if not any(s <= col_pos < e for s, e in line_spans):
            return False
    return True
def _fallback_string_comment_spans(
        lines: list[str]) -> dict[int, list[tuple[int, int]]]:
    spans: dict[int, list[tuple[int, int]]] = {}
    open_quote = ''
    for line_no, line in enumerate(lines, 1):
        text = str(line)
        cursor = 0
        if open_quote:
            end = _scan_quote_end(text, 0, open_quote)
            if end is None:
                _add_span(spans, line_no, 0, len(text))
                continue
            _add_span(spans, line_no, 0, end)
            cursor = end
            open_quote = ''
        while cursor < len(text):
            char = text[cursor]
            if char == '#':
                _add_span(spans, line_no, cursor, len(text))
                break
            if char in ('"', "'"):
                quote = char * 3 if text.startswith(char * 3, cursor) else char
                end = _scan_quote_end(text, cursor + len(quote), quote)
                if end is None:
                    _add_span(spans, line_no, cursor, len(text))
                    open_quote = quote if len(quote) == 3 else ''
                    break
                _add_span(spans, line_no, cursor, end)
                cursor = end
                continue
            if char == '\\':
                cursor += 2
                continue
            cursor += 1
    return spans
def _add_span(spans: dict[int, list[tuple[int, int]]], line_no: int,
              start: int, end: int) -> None:
    spans.setdefault(line_no, []).append((start, end))
def _scan_quote_end(text: str, start: int, quote: str) -> int | None:
    index = start
    while index < len(text):
        if text.startswith(quote, index):
            return index + len(quote)
        if len(quote) == 1 and text[index] == '\\':
            index += 2
            continue
        index += 1
    return None
def detect_d29_syntax_error(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    source = coerce_source_text(code)
    if source is None:
        return issues
    try:
        compile(source, filepath or '<string>', 'exec')
    except (SyntaxError, ValueError, RecursionError, MemoryError) as e:
        log_swallowed(__name__, e, context=f'detect_d29_syntax_error:{type(e).__name__}')
        msg = getattr(e, 'msg', None) or str(e)
        issues.append(DiagnoseIssue(
            check_id='D29', severity=DiagnoseSeverity.BLOCK,
            message=f'语法错误: {msg}',
            line=getattr(e, 'lineno', 0) or 0,
            col=getattr(e, 'offset', 0) or 0,
            suggestion=f'修复语法错误: {msg}',
        ))
    return issues
def _d03_is_hardcoded_default(value: ast.expr) -> bool:
    if (isinstance(value, ast.UnaryOp)
            and isinstance(value.op, (ast.UAdd, ast.USub))):
        operand = value.operand
        return (isinstance(operand, ast.Constant)
                and isinstance(operand.value, _ZERO_CONSTANT_TYPES))
    if isinstance(value, ast.Constant):
        return True
    return _is_empty_container(value)
def detect_d03_fallback(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    tree = _prepared_tree(tree, filepath)
    if tree is None:
        return []
    issues = []
    pmap = parent_map(tree)
    source_lines = source_lines_or(code, source_lines)
    _exempt_cache: dict[int, bool] = {}
    for node in tree_nodes(tree):
        if not _d03_default_return(node):
            continue
        handler = nearest_owning_handler(node, pmap)
        if handler is None:
            continue
        if (_d03_handler_exempt(handler, _exempt_cache, source_lines)
                or _d03_return_path_exempt(node, handler, pmap)):
            continue
        issues.append(_d03_issue(node))
    return issues
def _d03_default_return(node: ast.AST) -> bool:
    return (isinstance(node, ast.Return) and node.value is not None
            and _d03_is_hardcoded_default(node.value))
def _d03_handler_exempt(handler: ast.ExceptHandler,
                        cache: dict[int, bool],
                        source_lines: list[str]) -> bool:
    hid = id(handler)
    if hid not in cache:
        cache[hid] = _handler_marked_silent_ok(handler, source_lines or [])
    return cache[hid]
def _d03_block_observes_or_exits(stmts: list[ast.stmt]) -> bool:
    for stmt in stmts:
        if (_trace_call_node(stmt)
                or isinstance(stmt, (ast.Raise, ast.Return,
                                     ast.Break, ast.Continue))):
            return True
        if (isinstance(stmt, ast.If)
                and _d03_block_observes_or_exits(stmt.body)
                and _d03_block_observes_or_exits(stmt.orelse)):
            return True
        if (isinstance(stmt, TRY_NODE_TYPES)
                and _d03_block_observes_or_exits(stmt.finalbody)):
            return True
    return False
def _d03_return_path_exempt(node: ast.Return, handler: ast.ExceptHandler,
                            pmap: dict) -> bool:
    current: ast.AST = node
    while current is not handler:
        parent = pmap.get(current)
        if parent is None:
            return False
        if (isinstance(parent, TRY_NODE_TYPES)
                and current not in parent.finalbody
                and _d03_block_observes_or_exits(parent.finalbody)):
            return True
        for field in ('body', 'orelse', 'finalbody'):
            block = getattr(parent, field, None)
            if isinstance(block, list) and current in block:
                prefix = block[:block.index(current)]
                if _d03_block_observes_or_exits(prefix):
                    return True
                break
        current = parent
    return False
def _d03_issue(node: ast.Return) -> DiagnoseIssue:
    val = node.value
    val_desc = (repr(val.value)
                if isinstance(val, ast.Constant) else ast.unparse(val))
    return DiagnoseIssue(
        check_id='D03', severity=DiagnoseSeverity.WARN,
        message=f'兜底行为: except 块返回默认值 {val_desc}',
        line=node.lineno,
        suggestion='考虑显式错误处理或重新抛出异常',
    )
def _raised_exc_name(exc: ast.expr) -> str:
    if isinstance(exc, ast.Call):
        return _known_exception_name(exc.func)
    return _known_exception_name(exc)
@lru_cache(maxsize=256)
def _builtin_exc_lineage(raised: str) -> frozenset[str]:
    exc_type = getattr(builtins, raised, None)
    if not (isinstance(exc_type, type) and issubclass(exc_type, BaseException)):
        return frozenset((raised,))
    return frozenset(
        klass.__name__ for klass in exc_type.__mro__
        if isinstance(klass, type) and issubclass(klass, BaseException))
def _name_caught_by(raised: str, caught: str) -> bool:
    if not raised or not caught:
        return False
    if caught == raised:
        return True
    return caught in _builtin_exc_lineage(raised)
def _d23_matching_raise(node: ast.Try | ast.TryStar, caught: str,
                        pmap: dict,
                        skip: set[ast.Raise] | None = None) -> tuple[ast.Raise | None, str]:
    for stmt in node.body:
        for sub in tree_nodes(stmt):
            raised = _d23_candidate_raise(sub, caught, skip, node, pmap)
            if raised:
                return sub, raised
    return None, ''
_D23_GUARD_NODES: tuple[type, ...] = (
    ast.While, ast.For, ast.AsyncFor)
def _d23_block_terminates(stmts: list[ast.stmt]) -> bool:
    return any(
        isinstance(stmt, (ast.Raise, ast.Return, ast.Break, ast.Continue))
        or (isinstance(stmt, ast.If)
            and _d23_block_terminates(stmt.body)
            and _d23_block_terminates(stmt.orelse))
        for stmt in stmts
    )
def _d23_if_is_guard(node: ast.If, cur: ast.AST) -> bool:
    in_body = cur in node.body
    other = node.orelse if in_body else node.body
    return not other or not _d23_block_terminates(other)
def _d23_is_guard_raise(raise_node: ast.Raise,
                        try_node: ast.Try | ast.TryStar,
                        pmap: dict) -> bool:
    cur: ast.AST | None = raise_node
    while cur is not None:
        parent = pmap.get(cur)
        if parent is None or parent is try_node:
            return False
        if isinstance(parent, ast.If):
            if _d23_if_is_guard(parent, cur):
                return True
        if isinstance(parent, _D23_GUARD_NODES):
            return True
        cur = parent
    return False
def _d23_candidate_raise(sub: ast.AST, caught: str,
                         skip: set[ast.Raise] | None,
                         node: ast.Try | ast.TryStar, pmap: dict) -> str:
    if not (isinstance(sub, ast.Raise) and sub.exc):
        return ''
    if skip is not None and sub in skip:
        return ''
    if _d23_is_guard_raise(sub, node, pmap):
        return ''
    raised = _raised_exc_name(sub.exc)
    if not raised:
        return ''
    if not _name_caught_by(raised, caught):
        return ''
    return raised if _d23_raise_reaches_try(sub, node, raised, pmap) else ''
def detect_d23_self_catch(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    tree = _prepared_tree(tree, filepath)
    if tree is None:
        return []
    issues = []
    _parent_map = parent_map(tree)
    for node in tree_nodes(tree):
        if isinstance(node, TRY_NODE_TYPES):
            issues.extend(_d23_try_issues(node, _parent_map))
    return issues
def _d23_handler_exc_names(handler: ast.ExceptHandler) -> list[str]:
    if handler.type is None:
        return ['BaseException']
    nodes = (handler.type.elts if isinstance(handler.type, ast.Tuple)
             else [handler.type])
    return [name for node in nodes
            if (name := _known_exception_name(node))]
def _d23_try_issues(node: ast.Try | ast.TryStar,
                    pmap: dict) -> list[DiagnoseIssue]:
    issues: list[DiagnoseIssue] = []
    reported: set[ast.Raise] = set()
    for handler in node.handlers:
        for caught in _d23_handler_exc_names(handler):
            _sub, _raised = _d23_matching_raise(
                node, caught, pmap, skip=reported)
            if _sub is None:
                continue
            reported.add(_sub)
            issues.append(DiagnoseIssue(
                check_id='D23', severity=DiagnoseSeverity.WARN,
                message=f'自抛自接: try 块中 raise {_raised},except 捕获 {caught}',
                line=handler.lineno,
                suggestion='移除 try/except 包装或使用不同的异常类型',
            ))
    return issues
def _d23_raise_reaches_try(raise_node: ast.Raise, outer_try: ast.Try | ast.TryStar, raised: str, pmap: dict) -> bool:
    cur = raise_node
    while cur is not None:
        parent = pmap.get(cur)
        if parent is None or parent is outer_try:
            break
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            return False
        if not _d23_passes_intermediate_try(parent, cur, raised):
            return False
        cur = parent
    return True
_D23_FALLTHROUGH = 'fallthrough'
_D23_RERAISE = 'reraise'
_D23_OTHER_EXIT = 'other_exit'
def _d23_stmt_reraise_outcomes(
        stmt: ast.stmt, raised: str, reraise_name: str | None,
) -> frozenset[str]:
    if isinstance(stmt, ast.Raise):
        alias_reraise = (isinstance(stmt.exc, ast.Name)
                         and stmt.exc.id == reraise_name)
        if (stmt.exc is None or alias_reraise
                or _name_caught_by(_raised_exc_name(stmt.exc), raised)):
            return frozenset((_D23_RERAISE,))
        return frozenset((_D23_OTHER_EXIT,))
    if isinstance(stmt, (ast.Return, ast.Break, ast.Continue)):
        return frozenset((_D23_OTHER_EXIT,))
    if isinstance(stmt, ast.If):
        return (_d23_block_reraise_outcomes(
                    stmt.body, raised, reraise_name)
                | _d23_block_reraise_outcomes(
                    stmt.orelse, raised, reraise_name))
    return frozenset((_D23_FALLTHROUGH,))
def _d23_block_reraise_outcomes(
        stmts: list[ast.stmt], raised: str, reraise_name: str | None,
) -> frozenset[str]:
    outcomes = frozenset((_D23_FALLTHROUGH,))
    for stmt in stmts:
        if _D23_FALLTHROUGH not in outcomes:
            break
        outcomes = ((outcomes - {_D23_FALLTHROUGH})
                    | _d23_stmt_reraise_outcomes(
                        stmt, raised, reraise_name))
    return outcomes
def _d23_handler_guarantees_reraise(handler: ast.ExceptHandler,
                                    raised: str) -> bool:
    return _d23_block_reraise_outcomes(
        handler.body, raised, handler.name) == frozenset((_D23_RERAISE,))
def _d23_passes_intermediate_try(parent: ast.AST, cur: ast.AST,
                                 raised: str) -> bool:
    if not isinstance(parent, TRY_NODE_TYPES):
        return True
    final_outcomes = _d23_block_reraise_outcomes(
        parent.finalbody, raised, None)
    if _D23_OTHER_EXIT in final_outcomes:
        return False
    if cur not in parent.body:
        return True
    for h in parent.handlers:
        if any(_name_caught_by(raised, n)
               for n in _d23_handler_exc_names(h)):
            return _d23_handler_guarantees_reraise(h, raised)
    return True
def _d24_catch_spec(handler: ast.ExceptHandler) -> tuple[set[str], bool, bool]:
    t = handler.type
    if t is None:
        return set(), True, True
    if isinstance(t, ast.Tuple):
        names = [name for e in t.elts
                 if (name := _known_exception_name(e))]
        return set(names), False, len(names) == len(t.elts)
    name = _known_exception_name(t)
    return ({name}, False, True) if name else (set(), False, False)
def _d24_shadowed_by_earlier(earlier: ast.ExceptHandler,
                            later: ast.ExceptHandler) -> bool:
    broad_names, broad_bare, _known = _d24_catch_spec(earlier)
    later_names, later_bare, later_known = _d24_catch_spec(later)
    if broad_bare or 'BaseException' in broad_names:
        return True
    if not later_known or not later_names or later_bare:
        return False
    return all(any(_name_caught_by(n, caught) for caught in broad_names)
               for n in later_names)
def detect_d24_unreachable_except(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    tree = _prepared_tree(tree, filepath)
    if tree is None:
        return []
    issues = []
    for node in tree_nodes(tree):
        if isinstance(node, TRY_NODE_TYPES):
            handlers = node.handlers
            kw = 'except*' if _is_trystar(node) else 'except'
            unreachable = _d24_collect_unreachable(handlers)
            if unreachable:
                issues.append(_d24_issue(node, kw, unreachable))
    return issues
def _d24_issue(node: ast.Try | ast.TryStar, kw: str,
               unreachable: list[tuple[ast.ExceptHandler, ast.ExceptHandler]]
               ) -> DiagnoseIssue:
    unreachable.sort(key=lambda pair: pair[1].lineno)
    head = _d24_describe_catch(unreachable[0][0],
                               star=_is_trystar(node))
    lines_desc = ', '.join(str(h.lineno) for _, h in unreachable)
    return DiagnoseIssue(
        check_id='D24', severity=DiagnoseSeverity.WARN,
        message=f'不可达 {kw}: {head} 后的 {kw} 子句不可达（行 {lines_desc}）',
        line=unreachable[0][1].lineno,
        suggestion=f'合并 {kw} 子句或调整顺序',
    )
def _d24_collect_unreachable(
        handlers: list[ast.ExceptHandler],
) -> list[tuple[ast.ExceptHandler, ast.ExceptHandler]]:
    unreachable: list[tuple[ast.ExceptHandler, ast.ExceptHandler]] = []
    seen_ids: set[int] = set()
    for i, curr in enumerate(handlers):
        for h in handlers[i + 1:]:
            if id(h) in seen_ids:
                continue
            if _d24_shadowed_by_earlier(curr, h):
                seen_ids.add(id(h))
                unreachable.append((curr, h))
    return unreachable
def _d24_describe_catch(handler: ast.ExceptHandler, star: bool = False) -> str:
    kw = 'except*' if star else 'except'
    if handler.type is None:
        return '裸 except'
    if isinstance(handler.type, (ast.Name, ast.Attribute)):
        name = _known_exception_name(handler.type)
        if name:
            return f'{kw} {name}'
    if isinstance(handler.type, ast.Tuple):
        names = ', '.join(
            name for e in handler.type.elts
            if (name := _known_exception_name(e)))
        return f'{kw} ({names})'
    return f'{kw} <宽捕获>'
def _is_all_binding_stmt(n: ast.AST) -> bool:
    if isinstance(n, ast.Assign):
        return any(_d27_is_dunder_all(target) for target in n.targets)
    return (isinstance(n, ast.AnnAssign) and n.value is not None
            and _d27_is_dunder_all(n.target))
def _warn_rule_finding(
    rule_id: str, filepath: str, line: int, message: str, suggestion: str,
) -> dict[str, Any]:
    return {
        'rule_id': rule_id,
        'severity': 'WARN',
        'filepath': filepath,
        'line': line,
        'message': message,
        'suggestion': suggestion,
    }
def detect_all_overwrite(tree: ast.AST | None = None, filepath: str = _DEFAULT_FILEPATH) -> list[dict[str, Any]]:
    findings = []
    tree = _ensure_source_tree(tree, filepath)
    if not isinstance(tree, ast.Module):
        return findings
    all_assigns = [n for n in tree.body if _is_all_binding_stmt(n)]
    if len(all_assigns) <= 1:
        return findings
    for i, assign in enumerate(all_assigns[1:], start=2):
        findings.append(_warn_rule_finding(
            'D48', filepath, assign.lineno,
            f'__all__ 第 {i} 次赋值,前 {i-1} 次赋值将被覆盖'
            f' (共 {len(all_assigns)} 次)',
            '合并所有 __all__ 赋值为单次赋值,避免条目丢失'))
    return findings
def detect_star_import(tree: ast.AST | None = None, filepath: str = _DEFAULT_FILEPATH) -> list[dict[str, Any]]:
    findings = []
    tree = _ensure_source_tree(tree, filepath)
    if not isinstance(tree, ast.Module):
        return findings
    for n in tree_nodes(tree):
        if isinstance(n, ast.ImportFrom):
            for alias in n.names:
                if alias.name == '*':
                    mod = '.' * (n.level or 0) + (n.module or '')
                    findings.append(_warn_rule_finding(
                        'D49', filepath, n.lineno,
                        f'星导入 from {mod} import * 污染命名空间',
                        f'使用显式导入: from {mod} import name1, name2'))
    return findings
GATE_DETECTORS: dict[str, Any] = {
    "D02": detect_d02_degradation,
    "D03": detect_d03_fallback,
    "D04": detect_d04_circular_module,
    "D06": detect_d06_dynamic_import,
    "D07": detect_d07_dead_code,
    "D08": detect_d08_circular_dep,
    "D13": detect_d13_import_chain,
    "D15": detect_d15_static_register,
    "D18": detect_d18_stub_function,
    "D23": detect_d23_self_catch,
    "D24": detect_d24_unreachable_except,
    "D25": detect_d25_fullwidth_chars,
    "D27": detect_d27_dead_import,
    "D29": detect_d29_syntax_error,
}
def _register_detector_catalogs() -> None:
    register_detector_catalog("rule_bindings", {
        'D48': detect_all_overwrite, 'D49': detect_star_import,
        'AS09': check_AS09, 'SZ02': check_SZ02,
    })
    register_detector_catalog("gate_bindings", {'D01': detect_d01_lazy_import})
_SPLIT_HIGH_LINES = int(HARD_MAX_FILE_LINES * 1.25)
_SPLIT_SEVERE_LINES = int(HARD_MAX_FILE_LINES * 1.5)
def _call_target_name(node: ast.AST, func_names, class_names,
                      owner_class: str) -> str | None:
    if not isinstance(node, ast.Call):
        return None
    fn = node.func
    if isinstance(fn, ast.Name) and fn.id in func_names:
        return fn.id
    if isinstance(fn, ast.Attribute) and isinstance(fn.value, ast.Name):
        receiver = fn.value.id
        is_internal_receiver = receiver in class_names or (
            bool(owner_class) and receiver in {'self', 'cls'})
        if is_internal_receiver and fn.attr in func_names:
            return fn.attr
    return None
class _SplitCallGraph(NamedTuple):
    by_instance: list
    by_name: dict
def _split_definition_time_nodes(functions: list) -> dict[ast.AST, set[ast.AST]]:
    return {
        func: {
            node
            for header in _d27_definition_header_nodes(func)
            for node in tree_nodes(header)
        }
        for func in functions
    }
def _split_call_owner(call: ast.Call, parents: dict,
                      definition_nodes: dict[ast.AST, set[ast.AST]]) -> ast.AST | None:
    current: ast.AST = call
    while True:
        parent = parents.get(current)
        if parent is None:
            return None
        if (isinstance(parent, _FUNC_NODE_TYPES)
                and call not in definition_nodes.get(parent, frozenset())):
            return parent
        current = parent
def _split_call_graph(
    tree: ast.AST, functions: list, func_names: set[str]
) -> _SplitCallGraph:
    class_names = {
        n.name for n in tree_nodes(tree) if isinstance(n, ast.ClassDef)
    }
    parents = parent_map(tree)
    definition_nodes = _split_definition_time_nodes(functions)
    by_instance: list[tuple[Any, set]] = []
    for func in functions:
        owner = parents.get(func)
        while owner is not None and not isinstance(owner, ast.ClassDef):
            owner = parents.get(owner)
        owner_class = owner.name if owner is not None else ''
        calls = set()
        for node in tree_nodes(func):
            if not isinstance(node, ast.Call):
                continue
            if _split_call_owner(node, parents, definition_nodes) is not func:
                continue
            target = _call_target_name(
                node, func_names, class_names, owner_class)
            if target is not None:
                calls.add(target)
        by_instance.append((func, calls))
    by_name: dict[str, set] = {}
    for func, call_set in by_instance:
        by_name.setdefault(func.name, set()).update(call_set)
    return _SplitCallGraph(by_instance, by_name)
def _risk_coupling_factors(avg_coupling: float) -> tuple[int, list]:
    if avg_coupling > 3:
        return 30, [f"函数间高耦合(平均{avg_coupling:.1f}个内部调用)"]
    if avg_coupling > 2:
        return 15, [f"函数间中等耦合(平均{avg_coupling:.1f}个内部调用)"]
    return 0, []
def _risk_shared_private_factor(internal_calls: dict) -> tuple[int, list]:
    private_called = set()
    for call_set in internal_calls.values():
        private_called.update(c for c in call_set if c.startswith("_"))
    if len(private_called) > 5:
        return 20, [f"{len(private_called)}个共享私有函数,拆分需暴露接口"]
    if len(private_called) > 3:
        return 10, [f"{len(private_called)}个共享私有函数"]
    return 0, []
def _risk_bigfunction_factor(functions: list, total_lines: int) -> tuple[int, list]:
    if len(functions) < 10 and total_lines > HARD_MAX_FILE_LINES:
        return 25, [f"函数数量少({len(functions)}个)但行数多,属大函数问题非文件职责过多"]
    return 0, []
def _risk_bidirectional_factor(internal_calls: dict) -> tuple[int, list]:
    bidirectional = 0
    for f1, calls1 in internal_calls.items():
        for f2 in calls1:
            if f2 != f1 and f2 in internal_calls and f1 in internal_calls[f2]:
                bidirectional += 1
    bidirectional = bidirectional // 2
    if bidirectional > 0:
        return 25, [f"{bidirectional}对函数存在双向调用,拆分易致循环导入"]
    return 0, []
def _sum_factor_channels(channels) -> tuple[int, list[str]]:
    score = 0
    factors: list[str] = []
    for channel_score, channel_factors in channels:
        score += channel_score
        factors.extend(channel_factors)
    return score, factors
def _split_risk_factors(
    functions: list, internal_calls: dict, total_lines: int,
    avg_coupling: float,
) -> tuple[int, list[str]]:
    return _sum_factor_channels((
        _risk_coupling_factors(avg_coupling),
        _risk_shared_private_factor(internal_calls),
        _risk_bigfunction_factor(functions, total_lines),
        _risk_bidirectional_factor(internal_calls),
    ))
def _benefit_lines_factor(total_lines: int) -> tuple[int, list]:
    if total_lines > _SPLIT_SEVERE_LINES:
        return 30, [f"行数{total_lines}远超{HARD_MAX_FILE_LINES}阈值"]
    if total_lines > _SPLIT_HIGH_LINES:
        return 20, [f"行数{total_lines}超过{_SPLIT_HIGH_LINES}"]
    return 0, []
def _benefit_count_factor(functions: list) -> tuple[int, list]:
    if len(functions) > 30:
        return 25, [f"函数数量多({len(functions)}个),职责可能过于集中"]
    if len(functions) > 20:
        return 15, [f"函数数量较多({len(functions)}个)"]
    return 0, []
def _benefit_lowcoupling_factor(avg_coupling: float) -> tuple[int, list]:
    if avg_coupling < 1:
        return 20, ["函数间低耦合,拆分风险小"]
    if avg_coupling < 2:
        return 10, ["函数间耦合度较低"]
    return 0, []
def _benefit_cluster_factor(functions: list) -> tuple[int, list]:
    prefixes = {}
    for f in functions:
        parts = f.name.split("_")
        if len(parts) > 1 and parts[0]:
            prefixes.setdefault(parts[0], []).append(f.name)
    distinct_clusters = sum(1 for funcs in prefixes.values() if len(funcs) >= 3)
    if distinct_clusters >= 2:
        return 20, [f"检测到{distinct_clusters}个功能聚类,可按聚类拆分"]
    return 0, []
def _split_benefit_factors(
    functions: list, total_lines: int, avg_coupling: float
) -> tuple[int, list[str]]:
    return _sum_factor_channels((
        _benefit_lines_factor(total_lines),
        _benefit_count_factor(functions),
        _benefit_lowcoupling_factor(avg_coupling),
        _benefit_cluster_factor(functions),
    ))
def _collect_function_defs(tree: ast.AST) -> list:
    return [node for node in tree_nodes(tree)
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))]
def _avg_internal_coupling(functions: list, graph: _SplitCallGraph) -> float:
    total_internal_calls = sum(
        len(call_set) for _func, call_set in graph.by_instance)
    return total_internal_calls / len(functions)
def _analyze_split_risk_benefit(
    tree: ast.AST, total_lines: int
) -> tuple[int, int, str]:
    functions = _collect_function_defs(tree)
    if len(functions) < 2:
        return (0, 0, "函数数量不足,无需拆分")
    func_names = {f.name for f in functions}
    graph = _split_call_graph(tree, functions, func_names)
    avg_coupling = _avg_internal_coupling(functions, graph)
    risk_score, risk_factors = _split_risk_factors(
        functions, graph.by_name, total_lines, avg_coupling)
    benefit_score, benefit_factors = _split_benefit_factors(
        functions, total_lines, avg_coupling)
    risk_text = "; ".join(risk_factors) if risk_factors else "低"
    benefit_text = "; ".join(benefit_factors) if benefit_factors else "低"
    analysis = f"风险: {risk_text} | 收益: {benefit_text}"
    return (risk_score, benefit_score, analysis)
def _line_sequence_text(source: Any) -> str:
    chunks = [ln if isinstance(ln, str) else "" for ln in source]
    return "".join(
        chunk if index == len(chunks) - 1 or chunk.endswith(("\n", "\r"))
        else chunk + "\n"
        for index, chunk in enumerate(chunks))
def _as09_total_lines(source: Any, filepath: Any) -> int | None:
    if isinstance(source, str):
        return source_line_count(source)
    if isinstance(source, (list, tuple)):
        return source_line_count(_line_sequence_text(source))
    logger.debug("AS-09 source 形态契约外(跳过): %s (%r)",
               filepath, type(source).__name__)
    return None
def _as09_ensure_tree(tree: Any, source: Any, filepath: Any) -> Any:
    if tree is not None:
        return tree
    if isinstance(source, str):
        text = source
    elif isinstance(source, (list, tuple)):
        text = _line_sequence_text(source)
    else:
        return None
    try:
        return ast.parse(text)
    except PARSE_DEGRADE_EXC as _e:
        logger.debug("AS-09 源码补解析失败(跳过): %s (%s)", filepath, _e)
        return None
def _as09_make_issue(filepath: Any, total_lines: int, risk_score: int,
                     benefit_score: int, analysis: str) -> dict[str, Any]:
    return {
        "rule_id": "AS-09",
        "severity": "P2",
        "dimension": "style",
        "file": filepath,
        "line": 1,
        "title": (
            f"文件行数 {total_lines} 行,"
            f"超过{HARD_MAX_FILE_LINES}行需按 GOV-01 非拆分治理"
        ),
        "description": (
            f"当前文件共 {total_lines} 行,"
            f"超过{HARD_MAX_FILE_LINES}行阈值."
            f"规模分析: {analysis}."
            "建议按 GOV-01 简化逻辑/消除重复/迁移无关职责（禁止直接拆分）."
        ),
        "code_snippet": f"文件共 {total_lines} 行 (风险={risk_score}, 收益={benefit_score})",
        "suggestion": ("根因: 代码单元过大, 职责混合, 影响可读性和可维护性。"
                       "该问题属于代码结构类别。\n修复策略: 简化逻辑/消除重复/"
                       "迁移无关职责到既有模块/提取同模块私有实现"
                       "（GOV-01 禁止直接拆分）。\n"
                       "参考标准: PEP 8 / pylint / SonarQube"),
        "rule_ref": "AS-09 (风险收益评估)",
    }
def check_AS09(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[dict[str, Any]] = []
    total_lines = _as09_total_lines(source, filepath)
    if total_lines is None:
        return issues
    if total_lines <= HARD_MAX_FILE_LINES:
        return issues
    tree = _as09_ensure_tree(tree, source, filepath)
    if tree is None:
        return issues
    risk_score, benefit_score, analysis = _analyze_split_risk_benefit(tree, total_lines)
    if benefit_score > risk_score:
        issues.append(_as09_make_issue(filepath, total_lines,
                                       risk_score, benefit_score, analysis))
    return issues
def _indent_width(text: str) -> int:
    prefix = text[: len(text) - len(text.lstrip())]
    return len(prefix.expandtabs())
def _def_match_state(m, i: int) -> tuple[int, int, str]:
    return i, _indent_width(m.group(1)), m.group(2)
def _func_record(name: str, start_line: int, end_line: int,
                 lines: int) -> dict[str, Any]:
    return {
        "name": name,
        "start_line": start_line,
        "end_line": end_line,
        "lines": lines,
    }
def _trim_body_end(source_lines: list, func_start: int,
                   end_exclusive: int) -> int:
    _end = end_exclusive
    while _end > func_start and not _is_code_line(source_lines[_end - 1]):
        _end -= 1
    return _end
def _text_func_record(source_lines: list, func_name: str,
                      func_start: int, end_exclusive: int) -> dict[str, Any]:
    _end = _trim_body_end(source_lines, func_start, end_exclusive)
    return _func_record(func_name, func_start + 1, _end,
                        count_effective_lines(source_lines[func_start:_end]))
def _is_code_line(text: str) -> bool:
    return bool(text.strip()) and not text.lstrip().startswith('#')
def _func_end_hit(stripped: str, in_func: bool, func_indent: int) -> bool:
    return (in_func and _is_code_line(stripped)
            and _indent_width(stripped) <= func_indent)
def _count_function_lines_text(source_lines: list[str]) -> list[dict[str, Any]]:
    funcs = []
    in_func = False
    func_start = 0
    func_indent = 0
    func_name = ""
    for i, line in enumerate(source_lines):
        stripped = line.rstrip()
        match = re.match(r"^(\s*)(?:async\s+)?def\s+(\w+)", stripped)
        if match and not in_func:
            in_func = True
            func_start, func_indent, func_name = _def_match_state(match, i)
        elif _func_end_hit(stripped, in_func, func_indent):
            funcs.append(_text_func_record(
                source_lines, func_name, func_start, i))
            if match:
                func_start, func_indent, func_name = _def_match_state(match, i)
            else:
                in_func = False
    if in_func:
        funcs.append(_text_func_record(
            source_lines, func_name, func_start, len(source_lines)))
    return funcs
def _parse_lines_for_count(source_lines: list[str]) -> ast.Module | None:
    if not source_lines:
        return None
    text = _line_sequence_text(source_lines)
    try:
        return ast.parse(text)
    except PARSE_DEGRADE_EXC as _e:
        logger.debug("SZ-02 行数统计退化为文本扫描: %s", _e)
        return None
def _count_function_lines(source_lines: list[str], tree: ast.Module | None = None) -> list[dict[str, Any]]:
    if tree is None:
        tree = _parse_lines_for_count(source_lines)
    if tree is None:
        return _count_function_lines_text(source_lines)
    return [
        _func_record(
            node.name, node.lineno, node.end_lineno,
            count_effective_lines(source_lines[node.lineno - 1:node.end_lineno]))
        for node in _collect_function_defs(tree)
    ]
_WARN_RATIO = 0.8
_WARN_LIMITS = {
    "file_lines": int(HARD_MAX_FILE_LINES * _WARN_RATIO),
    "function_lines": int(HARD_MAX_FUNC_LINES * _WARN_RATIO),
}
def _sz02_source_lines(source_lines: list[str] | str) -> list[str]:
    if isinstance(source_lines, str):
        return ast_split_lines(source_lines)
    if isinstance(source_lines, (list, tuple)):
        return [ln if isinstance(ln, str) else '' for ln in source_lines]
    logger.debug("SZ-02 source_lines 形态契约外(按空行计): %r",
               type(source_lines).__name__)
    return []
def _in_warn_window(value: int, hard_limit: int, warn_limit: int) -> bool:
    return hard_limit >= value > warn_limit
_SZ02_SUGGESTION = (
    "根因: 代码单元过大, 职责混合, 影响可读性和可维护性。"
    "该问题属于代码规模类别。\n"
    "修复策略: {strategy}\n"
    "参考标准: PEP 8 / SonarQube Cognitive Complexity"
)
def _sz02_issue(line: int, message: str, strategy: str) -> dict[str, Any]:
    return {
        "rule_id": "SZ-02",
        "severity": "P3",
        "category": "size",
        "line": line,
        "message": message,
        "suggestion": _SZ02_SUGGESTION.format(strategy=strategy),
    }
def _sz02_file_issue(file_lines: int) -> list[dict[str, Any]]:
    if not _in_warn_window(file_lines, HARD_MAX_FILE_LINES,
                           _WARN_LIMITS["file_lines"]):
        return []
    return [_sz02_issue(
        1,
        f"文件体积偏高: {file_lines}行 "
        f"(预警阈值{_WARN_LIMITS['file_lines']}行,"
        f"硬上限{HARD_MAX_FILE_LINES}行)",
        "简化逻辑/迁移无关职责到既有模块")]
def _sz02_function_issues(funcs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    for func in funcs:
        if not _in_warn_window(func["lines"], HARD_MAX_FUNC_LINES,
                               _WARN_LIMITS["function_lines"]):
            continue
        issues.append(_sz02_issue(
            func["start_line"],
            f"函数 '{func['name']}' 体积偏高: {func['lines']}行 "
            f"(阈值{_WARN_LIMITS['function_lines']}行)",
            "简化逻辑/提取同模块私有实现/迁移无关职责"))
    return issues
def check_SZ02(tree: Any, source_lines: list[str] | str,
               filepath: str = _DEFAULT_FILEPATH) -> list[dict[str, Any]]:
    if finding_scan_exempt(filepath):
        return []
    source_lines = _sz02_source_lines(source_lines)
    issues = _sz02_file_issue(count_effective_lines(source_lines))
    issues.extend(_sz02_function_issues(
        _count_function_lines(source_lines, tree)))
    return issues

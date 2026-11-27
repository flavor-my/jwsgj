from __future__ import annotations

import ast
import hashlib
import logging
import os
import re
import sys
import time
from collections import Counter, defaultdict
from collections.abc import Callable
from dataclasses import dataclass, field
from types import SimpleNamespace
from typing import Any

from jwsgj.diag_rules_py_syntax import collect_py01_enclosing_bindings
from jwsgj.diag_se_data import (
    CREDENTIAL_PATTERNS,
    check_hardcoded_credentials,
)
from jwsgj.diag_shared_ast_nodes import (
    AST_MATCH_TYPES,
    BUILTIN_CALLABLES,
    TRY_STAR,
    _type_checking_guard_node_polarities,
    all_export_declaration_lines,
    assign_targets_value,
    build_node_parent_map,
    build_parent_map,
    collect_all_export_names,
    count_params,
    dotted_name,
    expr_target_name,
    has_abstractmethod_decorator,
    import_alias_bound_name,
    is_abstract_class_def,
    is_dunder_name,
    is_mutable_default,
    is_none_literal,
    is_package_init_path,
    is_static_method,
    iter_arg_nodes,
    iter_evaluation_scope_chain,
    iter_own_scope,
    iter_unpack_target_names,
    module_postpones_annotations,
)
from jwsgj.diag_shared_ast_nodes import (
    is_placeholder_stmt as _is_placeholder_stmt,
)
from jwsgj.diag_shared_ast_views import shared_walk
from jwsgj.diag_shared_source_core import (
    extract_code_lines,
    redundant_coding_decl_line,
)
from jwsgj.diag_shared_source_scan import (
    NOQA_ANY_RE,
    comment_tokens,
    is_logger_call,
)
from jwsgj.diag_testing_source import (
    FUNCTION_SCOPE_CONTAINERS as _FUNCTION_SCOPE_CONTAINERS,
)
from jwsgj.diag_testing_source import (
    TRY_STAR_T,
    FileCache,
    _collect_annotation_refs,
    _collect_namedexpr_bindings,
    _definition_header_exprs,
    collect_typing_tc_bindings,
    entry_import_node_dotted,
    entry_module_dotted,
    entry_nodes,
    iter_module_level_stmts,
    iter_own_scope_nodes,
    module_entry_indexes,
    module_level_bound_names,
    nodes_where,
    resolve_file_cache,
    type_checking_static_body,
)
from jwsgj.diag_testing_source import (
    entry_class_method_ids as _class_method_ids,
)
from jwsgj.diag_testing_test_index import (
    is_test_function_name,
    iter_collectable_test_functions,
)
from jwsgj.diag_types_defs import (
    TestMethodResult,
    finalize_test_result,
    graded_status_score,
    scan_issue,
    severity_tally,
)
from jwsgj.diag_types_vocab import WIRING_DECLARATION_ATTR
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    is_test_file_path,
)

__all__ = [
    "check_SK01",
    "check_SK02",
    "check_TT01",
    "check_TT02",
    "check_TT03",
    "check_unused_definitions",
    "check_unused_imports",
    "collect_cross_file_imports",
    "run_compatibility_tests",
    "run_contract_tests",
    "run_static_analysis",
]
_log = logging.getLogger(__name__)
_log.info("diag_testing_static 已加载：%d 项导出", len(__all__))
_TODO_PATTERN = re.compile(
    r'#\s*(TODO|FIXME|HACK|XXX|BUG|WARN)(?![A-Za-z0-9_])', re.IGNORECASE)
def _is_docstring_stmt(node: ast.AST) -> bool:
    return (isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Constant)
            and isinstance(node.value.value, (str, bytes)))
def _real_body_no_docstring(node: ast.FunctionDef | ast.AsyncFunctionDef) -> list:
    return [n for n in node.body if not _is_docstring_stmt(n)]
def _is_ellipsis_stmt(node: ast.AST) -> bool:
    return (isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Constant)
            and node.value.value is Ellipsis)
_TTSK_RULE_META: dict[str, tuple[str, str, str]] = {
    "TT-01": (
        "P1", "testing_quality",
        ("根因: 代码实现中存在测试规范方面的问题, 需要规范化处理。\n"
         "修复策略: 实现测试逻辑或标记为 skip.\n"
         "参考标准: pytest / unittest / pylint")),
    "TT-02": (
        "P2", "testing_quality",
        ("根因: 代码使用了不规范或有风险的实现方式。该问题属于测试规范类别。\n"
         "修复策略: 使用 pytest fixture 或 setUp/tearDown 管理测试状态.\n"
         "参考标准: pytest / unittest / pylint")),
    "TT-03": (
        "P2", "testing_quality",
        ("根因: 代码缺少必要的元素, 导致功能不完整或存在风险。该问题属于测试规范类别。\n"
         "修复策略: 添加 assert 语句验证返回值或异常.\n"
         "参考标准: pytest / unittest / pylint")),
    "SK-01": (
        "P1", "shell_stub_detection",
        ("根因: 代码缺少必要的元素, 导致功能不完整或存在风险。该问题属于桩函数类别。\n"
         "修复策略: 补全函数实现, 或如果为接口声明则使用 @abstractmethod 装饰器.\n"
         "参考标准: PEP 8 / @abstractmethod / pylint W0223")),
    "SK-02": (
        "P1", "shell_stub_detection",
        ("根因: 代码缺少必要的元素, 导致功能不完整或存在风险。该问题属于桩函数类别。\n"
         "修复策略: 补全函数返回真实业务值, 或确认 None 是否为预期返回.\n"
         "参考标准: PEP 8 / @abstractmethod / pylint W0223")),
}
def _finding_file_path(filepath: Any) -> str:
    if isinstance(filepath, str):
        return filepath
    if isinstance(filepath, (bytes, bytearray, os.PathLike)):
        try:
            return os.fsdecode(bytes(filepath)
                               if isinstance(filepath, bytearray)
                               else filepath)
        except (TypeError, ValueError):  # jwsgj:silent-ok 纯值降级：入参不可解析时返回安全默认值，无副作用可留痕
            return ""
    return ""
def _ttsk_finding(rule_id: str, locator: ast.AST | int, title: str,
                   description: str, rule_ref: str,
                   source: Any, filepath: Any) -> dict:
    severity, dimension, suggestion = _TTSK_RULE_META[rule_id]
    filepath = _finding_file_path(filepath)
    line = locator if isinstance(locator, int) else locator.lineno
    return {
        "rule_id": rule_id, "severity": severity,
        "dimension": dimension,
        "file": filepath, "line": line,
        "title": title,
        "description": description,
        "code_snippet": extract_code_lines(source, line),
        "suggestion": suggestion,
        "rule_ref": rule_ref,
    }
_TT01_FORM_TEXT = {
    "docstring-only-test": (
        "体为空（仅含 docstring）",
        "测试函数体滤除 docstring 后无任何语句,未实现断言逻辑."),
    "pass-only-test": (
        "仅含 pass",
        "测试函数仅有 pass 占位符,未实现任何断言逻辑."),
    "ellipsis-only-test": (
        "仅含 Ellipsis 占位",
        "测试函数仅有 ... 占位符,未实现任何断言逻辑."),
    "placeholder-only-test": (
        "仅含 pass/Ellipsis 占位",
        "测试函数体仅含 pass 与 ... 占位语句,未实现任何断言逻辑."),
}
def _tt01_body_form(real_body) -> str | None:
    if not real_body:
        return "docstring-only-test"
    if all(isinstance(n, ast.Pass) for n in real_body):
        return "pass-only-test"
    if all(_is_ellipsis_stmt(n) for n in real_body):
        return "ellipsis-only-test"
    if all(_is_placeholder_stmt(n) for n in real_body):
        return "placeholder-only-test"
    return None
def _is_test_file(filepath: Any) -> bool:
    return is_test_file_path(_finding_file_path(filepath))
_FUNC_NODE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef)
def _iter_function_defs(tree: ast.AST):
    for node in walk_nodes(tree):
        if isinstance(node, _FUNC_NODE_TYPES):
            yield node
def _collectable_test_ids(tree: ast.AST) -> set[int] | None:
    if not isinstance(tree, ast.Module):
        return None
    return {id(node) for node in iter_collectable_test_functions(tree)}
def _is_collected_test_node(node: ast.AST,
                            collected_ids: set[int] | None) -> bool:
    if collected_ids is None:
        return is_test_function_name(node.name)
    return id(node) in collected_ids
def _iter_test_functions(tree: ast.AST):
    skipped_class_members: set[int] = set()
    if isinstance(tree, ast.Module):
        if _has_skip_pytestmark(tree.body):
            return
        nodes = iter_collectable_test_functions(tree)
        skipped_class_members = _skipped_class_test_ids(tree)
    elif isinstance(tree, ast.ClassDef):
        nodes = (() if _is_skipped_test_container(tree) else
                 (member for member in tree.body
                  if isinstance(member, _FUNC_NODE_TYPES)
                  and is_test_function_name(member.name)))
    elif (isinstance(tree, _FUNC_NODE_TYPES)
            and is_test_function_name(tree.name)):
        nodes = (tree,)
    else:
        nodes = ()
    for node in nodes:
        if (_is_test_scaffolding(node) or _is_skipped_test(node)
                or id(node) in skipped_class_members):
            continue
        yield node
def check_TT01(tree: Any, source: Any, filepath: Any) -> Any:
    issues = []
    if tree is None:
        return issues
    if not _is_test_file(filepath):
        return issues
    for node in _iter_test_functions(tree):
        form = _tt01_body_form(_real_body_no_docstring(node))
        if form is not None:
            title_tail, desc = _TT01_FORM_TEXT[form]
            issues.append(_ttsk_finding(
                "TT-01", node,
                f"测试函数 '{node.name}' {title_tail}",
                desc, form, source, filepath))
    return issues
_UNPACK_TARGET_TYPES = (ast.Tuple, ast.List)
def _starred_target_index(elts: list[ast.AST]) -> int | None:
    for index, elt in enumerate(elts):
        if isinstance(elt, ast.Starred):
            return index
    return None
def _iter_starred_targets(target: ast.AST):
    if isinstance(target, ast.Starred):
        yield target
        return
    if isinstance(target, _UNPACK_TARGET_TYPES):
        for elt in target.elts:
            yield from _iter_starred_targets(elt)
def _starred_binding_value(lineno: int) -> ast.List:
    node = ast.List(elts=[], ctx=ast.Load())
    node.lineno = lineno
    node.col_offset = 0
    node.end_lineno = lineno
    node.end_col_offset = 0
    return node
def _iter_starred_pairs(elts: list[ast.AST], values: list[ast.AST],
                        lineno: int):
    star = _starred_target_index(elts)
    if star is None:
        return None
    before, after = elts[:star], elts[star + 1:]
    if len(values) < len(before) + len(after):
        return []
    pairs = list(zip(before, values[:len(before)], strict=True))
    tail = values[len(values) - len(after):] if after else []
    pairs.extend(zip(after, tail, strict=True))
    pairs.append((elts[star], _starred_binding_value(lineno)))
    return pairs
def _iter_unpack_pairs(target: ast.AST, value: ast.expr, lineno: int):
    stack: list[tuple[ast.AST, ast.expr]] = [(target, value)]
    while stack:
        _tgt, _val = stack.pop()
        if not isinstance(_tgt, _UNPACK_TARGET_TYPES):
            yield _tgt, _val, lineno
            continue
        if not isinstance(_val, (ast.Tuple, ast.List)):
            starred_targets = list(_iter_starred_targets(_tgt))
            if starred_targets:
                for starred_target in starred_targets:
                    yield (starred_target, _starred_binding_value(lineno),
                           lineno)
                continue
        if isinstance(_val, (ast.Tuple, ast.List)):
            _starred_pairs = _iter_starred_pairs(
                _tgt.elts, _val.elts, lineno)
            if _starred_pairs is not None:
                stack.extend(reversed(_starred_pairs))
            elif len(_tgt.elts) == len(_val.elts):
                stack.extend(reversed(list(
                    zip(_tgt.elts, _val.elts, strict=True))))
            continue
        if (isinstance(_val, ast.Dict)
                and len(_tgt.elts) == len(_val.keys)
                and all(key is not None for key in _val.keys)):
            stack.extend(reversed(list(
                zip(_tgt.elts, _val.keys, strict=True))))
            continue
        if isinstance(_val, (ast.Dict, ast.Set)):
            continue
        yield _tgt, _val, lineno
def _iter_header_namedexprs(expr: ast.AST):
    stack = [expr]
    while stack:
        current = stack.pop()
        if isinstance(current, ast.Lambda):
            stack.extend(_definition_header_exprs(current))
            continue
        if isinstance(current, ast.NamedExpr):
            yield current
        stack.extend(ast.iter_child_nodes(current))
def _iter_module_assign_pairs(tree: ast.AST):
    module_nodes = list(iter_own_scope(
        tree, skip_lambda=True, skip_type_checking_body=True,
        tc_polarities=_type_checking_guard_node_polarities(tree)))
    module_assigns = [
        node for node in module_nodes
        if isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr))
    ]
    seen = {id(node) for node in module_assigns}
    for node in module_nodes:
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef)):
            continue
        for expr in _definition_header_exprs(node):
            for named in _iter_header_namedexprs(expr):
                if id(named) not in seen:
                    module_assigns.append(named)
                    seen.add(id(named))
    module_assigns.sort(key=lambda node: (node.lineno, node.col_offset))
    for node in module_assigns:
        for target in (node.targets if isinstance(node, ast.Assign)
                       else [node.target]):
            yield from _iter_unpack_pairs(target, node.value, node.lineno)
def _tt02_report(target: ast.AST, value: ast.expr, lineno: int,
                 issues: list, source: Any, filepath: Any) -> None:
    if not is_mutable_default(value):
        return
    for _name in iter_unpack_target_names(target):
        if _name == "__all__":
            continue
        issues.append(_ttsk_finding(
            "TT-02", lineno,
            f"测试文件模块级可变对象 '{_name}' 可能污染测试隔离",
            "模块级可变对象在所有测试间共享.一个测试的修改会影响后续测试.",
            "test-module-global-mutable", source, filepath))
def check_TT02(tree: Any, source: Any, filepath: Any) -> Any:
    issues = []
    if tree is None:
        return issues
    if not _is_test_file(filepath):
        return issues
    for target, value, lineno in _iter_module_assign_pairs(tree):
        _tt02_report(target, value, lineno, issues, source, filepath)
    return issues
def _has_named_decorator(node: ast.AST, name_ids: frozenset[str],
                         attribute_ids: frozenset[str]) -> bool:
    for decorator in node.decorator_list:
        target = decorator.func if isinstance(decorator, ast.Call) else decorator
        if (isinstance(target, (ast.Name, ast.Attribute))
                and (getattr(target, "id", None) in name_ids
                     or getattr(target, "attr", None) in attribute_ids)):
            return True
    return False
_ACCESSOR_DECORATOR_NAMES = frozenset(
    {"property", "staticmethod", "classmethod"})
_ACCESSOR_DECORATOR_ATTRS = frozenset({"setter", "getter", "property"})
_NON_COLLECTABLE_ACCESSOR_NAMES = frozenset({"property"})
_TEST_FIXTURE_NAMES = frozenset({"fixture"})
_OVERLOAD_DECORATOR_NAMES = frozenset({"overload"})
_TEST_LIFECYCLE_NAMES = frozenset({
    'setUp', 'tearDown', 'setUpClass', 'tearDownClass',
    'asyncSetUp', 'asyncTearDown', 'setUpModule', 'tearDownModule',
    'setup', 'teardown',
    'setup_method', 'teardown_method', 'setup_class', 'teardown_class',
    'setup_function', 'teardown_function', 'runTest',
})
def _has_accessor_decorator(node: ast.AST) -> bool:
    return _has_named_decorator(
        node, _ACCESSOR_DECORATOR_NAMES, _ACCESSOR_DECORATOR_ATTRS)
def _is_test_fixture(node: ast.AST) -> bool:
    return _has_named_decorator(
        node, _TEST_FIXTURE_NAMES, _TEST_FIXTURE_NAMES)
def _is_typing_overload(node: ast.AST) -> bool:
    return _has_named_decorator(
        node, _OVERLOAD_DECORATOR_NAMES, _OVERLOAD_DECORATOR_NAMES)
_VISITOR_HOOK_PREFIX = 'visit_'
def _is_framework_hook(node: ast.AST) -> bool:
    _name = getattr(node, 'name', '')
    return (_is_test_fixture(node)
            or _name in _TEST_LIFECYCLE_NAMES
            or _name == 'generic_visit'
            or _name.startswith(_VISITOR_HOOK_PREFIX))
def _is_test_scaffolding(node: ast.AST) -> bool:
    return (_has_named_decorator(
        node, _NON_COLLECTABLE_ACCESSOR_NAMES, _ACCESSOR_DECORATOR_ATTRS)
            or _is_framework_hook(node))
_SKIPPED_TEST_DECORATOR_NAMES = frozenset({
    'skip', 'skipif', 'skipIf', 'skipUnless',
})
def _is_skip_marker(node: ast.AST) -> bool:
    target = node.func if isinstance(node, ast.Call) else node
    return (isinstance(target, (ast.Name, ast.Attribute))
            and (getattr(target, 'id', None) in _SKIPPED_TEST_DECORATOR_NAMES
                 or getattr(target, 'attr', None)
                 in _SKIPPED_TEST_DECORATOR_NAMES))
def _is_skipped_test(node: ast.AST) -> bool:
    return any(_is_skip_marker(decorator)
               for decorator in node.decorator_list)
def _pytestmark_assignment_value(node: ast.AST) -> ast.AST | None:
    if isinstance(node, ast.Assign):
        targets = node.targets
    elif isinstance(node, ast.AnnAssign) and node.value is not None:
        targets = (node.target,)
    else:
        return None
    if any(isinstance(target, ast.Name) and target.id == 'pytestmark'
           for target in targets):
        return node.value
    return None
def _value_has_skip_marker(value: ast.AST) -> bool:
    markers = value.elts if isinstance(value, (ast.List, ast.Tuple)) else (value,)
    return any(_is_skip_marker(marker) for marker in markers)
def _has_skip_pytestmark(body: list[ast.stmt]) -> bool:
    skipped = False
    for node in body:
        value = _pytestmark_assignment_value(node)
        if value is not None:
            skipped = _value_has_skip_marker(value)
    return skipped
def _is_skipped_test_container(node: ast.AST) -> bool:
    return ((isinstance(node, ast.ClassDef) and _is_skipped_test(node))
            or _has_skip_pytestmark(node.body))
def _skipped_class_test_ids(tree: ast.AST) -> set[int]:
    skipped: set[int] = set()
    for cls in walk_nodes(tree):
        if not isinstance(cls, ast.ClassDef) or not _is_skipped_test_container(cls):
            continue
        for member in iter_module_level_stmts(cls.body):
            if isinstance(member, _FUNC_NODE_TYPES):
                skipped.add(id(member))
    return skipped
_PYTEST_ASSERT_HELPER_NAMES = frozenset({'raises', 'warns'})
def _pytest_fail_imports(tree) -> tuple[frozenset[str], frozenset[str]]:
    module_aliases: set[str] = set()
    function_aliases: set[str] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            module_aliases.update(
                alias.asname or 'pytest'
                for alias in node.names if alias.name == 'pytest')
        elif (isinstance(node, ast.ImportFrom) and not node.level
              and node.module == 'pytest'):
            function_aliases.update(
                alias.asname or alias.name
                for alias in node.names if alias.name == 'fail')
    return frozenset(module_aliases), frozenset(function_aliases)
def _is_assert_call(func: ast.expr, pytest_modules=(), fail_functions=()) -> bool:
    if isinstance(func, ast.Attribute):
        attr = func.attr
        if attr.lower().startswith('assert'):
            return True
        if attr in _PYTEST_ASSERT_HELPER_NAMES:
            return True
        return (attr == 'fail'
                and isinstance(func.value, ast.Name)
                and (func.value.id in ('self', 'pytest')
                     or func.value.id in pytest_modules))
    if isinstance(func, ast.Name):
        fid = func.id
        return (fid.lower().startswith('assert')
                or fid in _PYTEST_ASSERT_HELPER_NAMES
                or fid in fail_functions)
    return False
def _has_assert_evidence(fn_node, pytest_modules=(), fail_functions=()) -> bool:
    return any(
        isinstance(child, ast.Assert)
        or (isinstance(child, ast.Call) and _is_assert_call(
            child.func, pytest_modules, fail_functions))
        for child in iter_own_scope(fn_node, skip_lambda=True)
    )
def check_TT03(tree: Any, source: Any, filepath: Any) -> Any:
    issues = []
    if tree is None:
        return issues
    if not _is_test_file(filepath):
        return issues
    pytest_modules, fail_functions = _pytest_fail_imports(tree)
    for node in _iter_test_functions(tree):
        real_body = _real_body_no_docstring(node)
        if not real_body or all(_is_placeholder_stmt(n) for n in real_body):
            continue
        if _has_assert_evidence(node, pytest_modules, fail_functions):
            continue
        issues.append(_ttsk_finding(
            "TT-03", node,
            f"测试函数 '{node.name}' 缺少 assert 断言",
            "测试函数无assert/断言语句,无法验证预期行为.",
            "test-no-assert", source, filepath))
    return issues
_LEGAL_EMPTY_BODY_NAMES = frozenset({
    '__init__', '__enter__', '__exit__', '__aexit__',
    '__del__', '__post_init__', '__init_subclass__', '__set_name__',
})
_DECLARATIVE_BASE_NAMES = frozenset({'Protocol', 'ABC', 'ABCMeta'})
_DECLARATIVE_BASE_SOURCES = {
    'typing': frozenset({'Protocol'}),
    'typing_extensions': frozenset({'Protocol'}),
    'abc': frozenset({'ABC', 'ABCMeta'}),
}
def _declarative_base_name_ids(tree: ast.AST) -> frozenset[str]:
    names = set(_DECLARATIVE_BASE_NAMES)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ImportFrom) or node.level:
            continue
        imported = _DECLARATIVE_BASE_SOURCES.get(node.module or '', ())
        names.update(alias.asname or alias.name for alias in node.names
                     if alias.name in imported)
    return frozenset(names)
def _is_declarative_class(
        node: ast.ClassDef,
        base_names: frozenset[str] = _DECLARATIVE_BASE_NAMES) -> bool:
    return (is_abstract_class_def(node)
            or any(expr_target_name(
                base.value if isinstance(base, ast.Subscript) else base)
                in base_names for base in node.bases))
def _declared_interface_ids(tree: ast.AST) -> frozenset[int]:
    ids: set[int] = set()
    base_names = _declarative_base_name_ids(tree)
    for node in walk_nodes(tree):
        if (not isinstance(node, ast.ClassDef)
                or not _is_declarative_class(node, base_names)):
            continue
        ids.update(id(member) for member in node.body
                   if isinstance(member, _FUNC_NODE_TYPES))
    return frozenset(ids)
def _no_op_stripped_body(node) -> list:
    return [
        n for n in node.body
        if not (_is_docstring_stmt(n) or _is_ellipsis_stmt(n))
    ]
def _is_empty_pass_stub(node: ast.AST) -> bool:
    real_body = _no_op_stripped_body(node)
    if real_body and not all(isinstance(n, ast.Pass) for n in real_body):
        return False
    return not (
        has_abstractmethod_decorator(node)
        or _is_typing_overload(node)
        or getattr(node, 'name', '') in _LEGAL_EMPTY_BODY_NAMES
        or _is_framework_hook(node)
    )
def check_SK01(tree: Any, source: Any, filepath: Any) -> Any:
    issues = []
    if tree is None:
        return issues
    _test_ctx = _is_test_file(filepath)
    _collected_ids = _collectable_test_ids(tree) if _test_ctx else None
    _interface_ids = _declared_interface_ids(tree)
    for node in _iter_function_defs(tree):
        if _test_ctx and _is_collected_test_node(node, _collected_ids):
            continue
        if id(node) in _interface_ids:
            continue
        if not _is_empty_pass_stub(node):
            continue
        issues.append(_ttsk_finding(
            "SK-01", node, "空函数体（仅 docstring/pass 占位）",
            f"函数 {node.name} 滤除 docstring 后为空或仅含 pass, 缺少实际逻辑实现.",
            "sk-empty-pass", source, filepath))
    return issues
def _is_return_none_stub(node) -> bool:
    real_body = _no_op_stripped_body(node)
    if len(real_body) != 1 or not isinstance(real_body[0], ast.Return):
        return False
    ret_val = real_body[0].value
    if ret_val is not None and not is_none_literal(ret_val):
        return False
    return not (
        has_abstractmethod_decorator(node)
        or _is_typing_overload(node)
        or node.name in _LEGAL_EMPTY_BODY_NAMES
        or _is_framework_hook(node)
    )
def check_SK02(tree: Any, source: Any, filepath: Any) -> Any:
    issues = []
    if tree is None:
        return issues
    _test_ctx = _is_test_file(filepath)
    _collected_ids = _collectable_test_ids(tree) if _test_ctx else None
    _interface_ids = _declared_interface_ids(tree)
    for node in _iter_function_defs(tree):
        if _test_ctx and _is_collected_test_node(node, _collected_ids):
            continue
        if id(node) in _interface_ids:
            continue
        if not _is_return_none_stub(node):
            continue
        issues.append(_ttsk_finding(
            "SK-02", node, "函数仅返回 None（疑似桩函数）",
            f"函数 {node.name} 体仅含 return None, 可能是未实现的桩函数.",
            "sk-return-none-stub", source, filepath))
    return issues
def wiring_declarations() -> dict:
    return {"catalogs": {"rule_bindings": {
        "TT01": check_TT01, "TT02": check_TT02, "TT03": check_TT03,
        "SK01": check_SK01, "SK02": check_SK02,
    }}}
@dataclass
class _IssueCollector:
    result: TestMethodResult
    issue_types: Counter = field(default_factory=Counter)
    def add(self, findings) -> None:
        for finding in findings:
            self.result.findings.append(finding)
            self.issue_types[finding.get('type', 'unknown')] += 1
_IMPLICIT_METHOD_PARAMS = frozenset({'self', 'cls'})
def _missing_param_annotations(
        node: ast.FunctionDef | ast.AsyncFunctionDef) -> list[str]:
    return [arg.arg for arg in iter_arg_nodes(node.args)
            if arg.annotation is None]
def _public_function_nodes(entry):
    tree = getattr(entry, 'tree', None)
    if tree is None:
        return
    for node in iter_module_level_stmts(tree.body):
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                and not node.name.startswith("_")):
            yield node
def _annotation_findings(node, rel_path: str) -> list[dict]:
    findings = []
    missing_annotations = _missing_param_annotations(node)
    if missing_annotations:
        findings.append({
            "type": "CONTRACT-MISSING-PARAM-ANNOT",
            "severity": "low",
            "file": rel_path,
            "line": node.lineno,
            "message": f"公开函数 {node.name} 参数缺类型注解: "
                       f"{', '.join(missing_annotations)}",
        })
    if node.returns is None:
        findings.append({
            "type": "CONTRACT-MISSING-RETURN-ANNOT",
            "severity": "low",
            "file": rel_path,
            "line": node.lineno,
            "message": f"公开函数 {node.name} 缺返回值类型注解",
        })
    return findings
_CONTRACT_NO_ALL_REPORT_THRESHOLD = 3
def _module_getattr_node(tree: ast.AST | None):
    if tree is None:
        return None
    for node in iter_module_level_stmts(getattr(tree, 'body', [])):
        if isinstance(node, ast.FunctionDef) and node.name == '__getattr__':
            return node
    return None
def _declared_export_names(entry) -> set[str]:
    tree = getattr(entry, 'tree', None)
    if tree is None or not getattr(entry, 'has_all', False):
        return set()
    names: set[str] = set()
    collect_all_export_names(getattr(tree, 'body', []), names, require_str=True)
    return names
def _all_undefined_findings(entry) -> list[dict]:
    declared = _declared_export_names(entry)
    if not declared:
        return []
    if _module_getattr_node(getattr(entry, 'tree', None)) is not None:
        return []
    all_defined = module_level_bound_names(entry.tree, include_imports=True)
    declaration_lines = all_export_declaration_lines(entry)
    return [
        {
            "type": "CONTRACT-ALL-UNDEFINED",
            "severity": "high",
            "file": entry.rel_path,
            "line": declaration_lines.get(name, 0),
            "message": f"__all__ 声明 '{name}' 但未在模块中定义",
        }
        for name in sorted(declared) if name not in all_defined
    ]
def _scan_contract_entry(entry, findings: list[dict]) -> None:
    rel_path = entry.rel_path
    findings.extend(_all_undefined_findings(entry))
    public_count = 0
    for node in _public_function_nodes(entry):
        public_count += 1
        findings.extend(_annotation_findings(node, rel_path))
    if entry.has_all or is_package_init_path(rel_path):
        return
    if public_count > _CONTRACT_NO_ALL_REPORT_THRESHOLD:
        findings.append({
            "type": "CONTRACT-NO-ALL",
            "severity": "medium",
            "file": rel_path,
            "line": 0,
            "message": f"模块有 {public_count} 个公开函数但未声明 __all__",
        })
def _source_parse_error_findings(cache) -> list[dict]:
    findings: list[dict] = []
    for entry in cache.entries:
        if getattr(entry, 'tree', None) is not None:
            continue
        detail = (getattr(entry, 'parse_error', None)
                  or '未生成 AST 且缺少解析错误详情')
        findings.append(scan_issue(
            getattr(entry, 'rel_path', ''), 0,
            'source_parse_error', 'high',
            f'源码读取或解析失败，未执行静态检查: {detail}'))
    return findings
def run_contract_tests(skill_dir: str, **kwargs) -> TestMethodResult:
    start = time.perf_counter()
    result = TestMethodResult(
        method_name="契约测试",
        method_id="contract_test",
    )
    cache = resolve_file_cache(skill_dir, kwargs)
    if cache is None:
        return TestMethodResult.invalid_input(
            skill_dir, "契约测试", "contract_test", "契约检查", start)
    findings = _collect_contract_findings(cache)
    _apply_contract_verdict(result, findings)
    return finalize_test_result(result, cache, start)
def _collect_contract_findings(cache) -> list[dict]:
    findings = _source_parse_error_findings(cache)
    for entry in cache.valid_entries:
        if is_test_file_path(entry.rel_path):
            continue
        _scan_contract_entry(entry, findings)
    return findings
def _apply_contract_verdict(result: TestMethodResult, findings: list[dict]) -> None:
    counts = severity_tally(findings)
    result.findings = findings
    result.metrics = {
        "total_findings": len(findings),
        "high_severity": counts["high"],
        "medium_severity": counts["medium"],
        "low_severity": counts["low"],
    }
    status, score = graded_status_score(counts, len(findings), low_penalty=3)
    result.status = status
    result.score = score
    if not findings:
        result.summary = "API 契约一致性良好"
    elif counts["high"] > 0:
        result.summary = f"检测到 {len(findings)} 个契约违规（{counts['high']} 个高危）"
    else:
        result.summary = f"检测到 {len(findings)} 个低中危契约问题"
def run_static_analysis(skill_dir: str, **kwargs) -> TestMethodResult:
    start = time.perf_counter()
    result = TestMethodResult(
        method_name="静态代码检查",
        method_id="static_analysis",
    )
    cache = resolve_file_cache(skill_dir, kwargs)
    if cache is None:
        return TestMethodResult.invalid_input(
            skill_dir, "静态代码检查", "static_analysis", "静态检查", start)
    sink = _IssueCollector(result=result)
    sink.add(_source_parse_error_findings(cache))
    external_consumers = collect_cross_file_imports(cache)
    _scan_primary_checks(cache, sink, external_consumers)
    _scan_secondary_checks(cache, sink)
    _scan_cross_file_checks(cache, sink, external_consumers)
    total_issues = len(result.findings)
    result.metrics = {
        "total_issues": total_issues,
        "issue_types": dict(sink.issue_types),
        "files_scanned": len(cache.entries),
    }
    result.status, result.score, result.summary = _static_grade_summary(
        total_issues, sink.issue_types)
    return result.finish(start, precision=1)
def _static_grade_summary(
    total_issues: int, issue_types: Counter
) -> tuple[str, int, str]:
    if total_issues == 0:
        return "pass", 100, "静态检查无问题"
    if total_issues <= 20:
        return ("warn", 80,
                f"静态检查发现 {total_issues} 个问题: {dict(issue_types)}")
    if total_issues <= 100:
        return ("warn", 60,
                f"静态检查发现 {total_issues} 个问题: {dict(issue_types)}")
    return ("warn", 30,
            f"静态检查发现 {total_issues} 个问题: {dict(issue_types)}")
def _scan_primary_checks(cache: FileCache, sink: _IssueCollector,
                         external_consumers: dict[str, set[str]]) -> None:
    func_fingerprints: dict[str, list[tuple[str, int, str]]] = defaultdict(list)
    for entry in cache.valid_entries:
        is_np_ctx = any(
            _is_np_pandas_import(node)
            for node in nodes_where(entry, (ast.Import, ast.ImportFrom)))
        is_test = is_test_file_path(entry.rel_path)
        for node in entry_nodes(entry):
            sink.add(_check_exception_handlers(node, entry.rel_path))
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                sink.add(_check_function_definitions(
                    node, entry.rel_path, func_fingerprints))
            sink.add(_check_none_comparison(
                node, entry.rel_path, is_np_ctx, is_test))
        sink.add(check_unused_imports(
            entry, external_consumers.get(entry.rel_path, set())))
        sink.add(_check_mutable_globals(entry))
        sink.add(check_hardcoded_credentials(
            entry.source, entry.rel_path, CREDENTIAL_PATTERNS))
    sink.add(_report_duplicate_code(func_fingerprints))
def _scan_secondary_checks(cache: FileCache, sink: _IssueCollector) -> None:
    for entry in cache.valid_entries:
        sink.add(_check_shadowing_builtins(entry, BUILTIN_CALLABLES))
        sink.add(_check_global_statements(entry))
        sink.add(_check_todo_markers(entry, _TODO_PATTERN))
        sink.add(_check_docstring_coverage(entry))
def _scan_cross_file_checks(cache: FileCache, sink: _IssueCollector,
                            external_consumers: dict[str, set[str]]) -> None:
    sink.add(_check_empty_except_blocks(cache))
    sink.add(_check_self_assignments(cache))
    sink.add(_check_constant_comparisons(cache))
    sink.add(_check_duplicate_strings(cache))
    sink.add(check_unused_definitions(cache, external_consumers))
_NP_PANDAS_ROOTS = frozenset({'numpy', 'pandas'})
def _is_np_pandas_import(node: ast.AST) -> bool:
    if isinstance(node, ast.ImportFrom):
        module = node.module or ''
        return bool(not node.level
                    and module.split('.')[0] in _NP_PANDAS_ROOTS)
    if isinstance(node, ast.Import):
        return any(alias.name.split('.')[0] in _NP_PANDAS_ROOTS
                   for alias in node.names)
    return False
def _exception_name_of(exc_node: ast.AST | None) -> str:
    if isinstance(exc_node, ast.Name):
        return exc_node.id
    if (isinstance(exc_node, ast.Attribute)
            and isinstance(exc_node.value, ast.Name)
            and exc_node.value.id == 'builtins'):
        return exc_node.attr
    return ''
def _resolve_except_exc_name(exc_node: ast.AST | None) -> str:
    if not isinstance(exc_node, ast.Tuple):
        return _exception_name_of(exc_node)
    member_ids = {_exception_name_of(elt) for elt in exc_node.elts}
    if "BaseException" in member_ids:
        return "BaseException"
    return "Exception" if "Exception" in member_ids else ""
def _log_helper_name(func: ast.AST) -> str:
    if isinstance(func, ast.Attribute):
        return func.attr
    return func.id if isinstance(func, ast.Name) else ""
def _is_log_helper_name(name: str) -> bool:
    normalized = name.strip("_").lower()
    return normalized.startswith("log_") or normalized.endswith("_log")
def _is_error_output_call(node: ast.AST) -> bool:
    if not isinstance(node, ast.Call):
        return False
    if is_logger_call(node):
        return True
    _name = _log_helper_name(node.func)
    return _name == "print" or bool(_name) and _is_log_helper_name(_name)
def _except_body_proof_flags(node: ast.ExceptHandler) -> tuple[bool, bool, bool, bool]:
    has_reraise = has_logging = has_return = has_continue = False
    for n in iter_own_scope_nodes(node):
        has_reraise = has_reraise or isinstance(n, ast.Raise)
        has_logging = has_logging or _is_error_output_call(n)
        has_return = has_return or isinstance(n, ast.Return)
        has_continue = has_continue or isinstance(n, ast.Continue)
    return has_reraise, has_logging, has_return, has_continue
def _check_exception_handlers(node: ast.AST, rel_path: str) -> list[dict]:
    findings = []
    if not isinstance(node, ast.ExceptHandler):
        return findings
    if node.type is None:
        findings.append(scan_issue(
            rel_path, node.lineno, "bare_except", "medium",
            "裸 except 会捕获所有异常包括 KeyboardInterrupt"))
        return findings
    exc_name = _resolve_except_exc_name(node.type)
    if exc_name == "BaseException":
        findings.append(scan_issue(
            rel_path, node.lineno, "bare_except", "medium",
            "except BaseException 捕获面与裸 except 全同"
            "（含 KeyboardInterrupt），语义等价应显式收敛"))
        return findings
    if exc_name != "Exception":
        return findings
    _broad = _broad_except_finding(node, rel_path)
    if _broad is not None:
        findings.append(_broad)
    return findings
_COLLECT_METHODS = frozenset({
    "append", "add", "extend", "update", "setdefault", "insert"})


def _handler_exception_names(node: ast.ExceptHandler) -> set[str]:
    name = getattr(node, "name", None)
    return {name} if isinstance(name, str) and name else set()


def _except_body_collects_error(node: ast.ExceptHandler) -> bool:
    """handler 体是否把异常信息收进容器（``failed.append({"error": str(exc)})``）。

    收集进容器与写日志等价：异常细节离开 handler 后仍能被调用方读取，
    不属于「静默吞掉」。"""
    exc_names = _handler_exception_names(node)
    if not exc_names:
        return False
    for n in iter_own_scope_nodes(node):
        if not (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                and n.func.attr in _COLLECT_METHODS):
            continue
        if any(isinstance(sub, ast.Name) and sub.id in exc_names
               for sub in walk_nodes(n)):
            return True
    return False


def _broad_except_finding(node: ast.ExceptHandler, rel_path: str):
    has_reraise, has_logging, has_return, has_continue = (
        _except_body_proof_flags(node))
    # 「异常信息是否离开 handler」才是掩盖风险的本质判据：re-raise、写日志、
    # 收进容器三者任一都保证故障细节可查；只有 continue/return 这类纯控制流
    # 会让异常彻底消失（那才是静默降级，交由 diag_silent_degrade 处置）。
    if (has_reraise or has_logging
            or _except_body_collects_error(node)):
        return None
    _sev = "low" if (has_return or has_continue) else "medium"
    return scan_issue(
        rel_path, node.lineno, "broad_except", _sev,
        "except Exception 无 re-raise、无日志、未收集异常信息，可能掩盖真实错误")
def _find_unreachable(body: list[ast.stmt]) -> tuple[int, str] | None:
    for i, stmt in enumerate(body):
        if not isinstance(stmt, (ast.Return, ast.Break, ast.Continue, ast.Raise)):
            continue
        unreachable = body[i + 1] if i + 1 < len(body) else None
        if unreachable is not None:
            return unreachable.lineno, type(stmt).__name__
        break
    for stmt in body:
        for nested_body in _nested_statement_bodies(stmt):
            unreachable = _find_unreachable(nested_body)
            if unreachable is not None:
                return unreachable
    return None
def _nested_statement_bodies(stmt: ast.AST):
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef, ast.Lambda)):
        return
    for field_name in ('body', 'orelse', 'finalbody'):
        nested = getattr(stmt, field_name, None)
        if (isinstance(nested, list) and nested
                and all(isinstance(item, ast.stmt) for item in nested)):
            yield nested
    for group_name in ('handlers', 'cases'):
        for child in getattr(stmt, group_name, ()):
            nested = getattr(child, 'body', None)
            if isinstance(nested, list) and nested:
                yield nested
_DB_SESSION_CALLS = frozenset((
    'execute', 'executemany', 'executescript', 'fetchall', 'fetchone',
    'fetchmany', 'commit', 'rollback', 'close', 'cursor',
))
def _db_session_call_count(node: ast.AST) -> int:
    return sum(
        isinstance(c, ast.Call) and isinstance(c.func, ast.Attribute)
        and c.func.attr in _DB_SESSION_CALLS
        for c in walk_nodes(node)
    )
def _thin_delegation(node: ast.AST) -> bool:
    """函数体是否只是「转调共享实现」（单条 return 一个调用）。

    ``scan_hlines`` / ``scan_vlines`` 这类成对薄包装：差异只有转置开关，
    真正的实现已经在 ``_scan_lines`` 里共享。把它们判成「重复代码」等于
    要求调用方各自展开实现——那是**反向**的耦合。
    """
    body = [stmt for stmt in getattr(node, "body", ())
            if not (isinstance(stmt, ast.Expr)
                    and isinstance(stmt.value, ast.Constant)
                    and isinstance(stmt.value.value, str))]
    return (len(body) == 1
            and isinstance(body[0], ast.Return)
            and isinstance(body[0].value, ast.Call))

def _fingerprint_collect_exempt(node: ast.AST, func_len: int) -> bool:
    return (_db_session_call_count(node) >= 2
            or func_len < 5
            or _thin_delegation(node)
            or _fingerprint_name_shape_exempt(node))
def _fingerprint_name_shape_exempt(node: ast.AST) -> bool:
    name = node.name
    if name == '__init__' or name.startswith('test_'):
        return True
    if name.startswith('__') and name.endswith('__'):
        return True
    return _has_accessor_decorator(node)
def _check_function_definitions(node: ast.AST, rel_path: str,
                                func_fingerprints: dict) -> list[dict]:
    findings = []
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return findings
    func_len = ((getattr(node, 'end_lineno', None) or node.lineno)
                - node.lineno + 1)
    _long = _long_function_finding(node, rel_path, func_len)
    if _long is not None:
        findings.append(_long)
    findings.extend(_mutable_default_findings(node, rel_path))
    _unreach = _find_unreachable(node.body)
    if _unreach is not None:
        findings.append(scan_issue(
            rel_path, _unreach[0], "unreachable_code", "medium",
            f"函数 {node.name}: {_unreach[1]} 后有不可达代码"))
    _collect_function_fingerprint(
        node, rel_path, func_len, func_fingerprints)
    return findings
_LONG_FUNCTION_MAX_LINES = 300
def _long_function_finding(node, rel_path: str, func_len: int):
    if func_len <= _LONG_FUNCTION_MAX_LINES:
        return None
    return scan_issue(
        rel_path, node.lineno, "long_function", "medium",
        f"函数 {node.name} 过长 ({func_len} 行, 阈值 "
        f"{_LONG_FUNCTION_MAX_LINES})", name=node.name)
def _mutable_default_findings(node, rel_path: str) -> list[dict]:
    return [
        scan_issue(
            rel_path, node.lineno, "mutable_default", "high",
            f"函数 {node.name} 使用可变默认参数（共享状态 bug 风险）")
        for d in (*node.args.defaults, *node.args.kw_defaults)
        if is_mutable_default(d)
    ]
def _collect_function_fingerprint(node, rel_path: str, func_len: int,
                                  func_fingerprints: dict) -> None:
    if _fingerprint_collect_exempt(node, func_len):
        return
    fp = _compute_ast_fingerprint(node)
    if fp:
        func_fingerprints.setdefault(fp, []).append(
            (rel_path, node.lineno, node.name))
def _check_none_comparison(node: ast.AST, rel_path: str,
                           is_np_ctx: bool, is_test: bool) -> list[dict]:
    findings = []
    if is_np_ctx or is_test or not isinstance(node, ast.Compare):
        return findings
    operands = (node.left, *node.comparators)
    for index, op in enumerate(node.ops):
        if not isinstance(op, (ast.Eq, ast.NotEq)):
            continue
        if is_none_literal(operands[index]) or is_none_literal(
                operands[index + 1]):
            _eq = isinstance(op, ast.Eq)
            _op_text = '==' if _eq else '!='
            _fix_text = 'is None' if _eq else 'is not None'
            findings.append(scan_issue(
                rel_path, node.lineno, "none_comparison", "low",
                f"使用 '{_fix_text}' 代替 '{_op_text} None'（PEP 8 推荐身份比较）"))
            break
    return findings
def _mutable_global_convention_exempt(name: str) -> bool:
    return is_dunder_name(name) or _is_upper_const_name(name)
def _is_upper_const_name(name: str) -> bool:
    return len(name) >= 2 and name[0] != '_' and name.isupper()
_MUTATING_METHODS = frozenset((
    'append', 'extend', 'insert', 'pop', 'clear', 'sort', 'reverse',
    'update', 'setdefault', 'popitem', 'add', 'discard', 'remove',
    'difference_update', 'intersection_update', 'symmetric_difference_update',
))
def _receiver_root_name(node: ast.AST) -> str | None:
    cur = node
    while True:
        if isinstance(cur, ast.Name):
            return cur.id
        if isinstance(cur, (ast.Subscript, ast.Attribute)):
            cur = cur.value
            continue
        if isinstance(cur, ast.Call):
            cur = cur.func
            continue
        return None
def _subscript_container_name(target: ast.AST) -> str | None:
    if not isinstance(target, ast.Subscript):
        return None
    return _receiver_root_name(target)
def _iter_subscript_targets(target: ast.AST):
    stack = [target]
    while stack:
        current = stack.pop()
        if isinstance(current, (ast.Tuple, ast.List)):
            stack.extend(reversed(current.elts))
        elif isinstance(current, ast.Starred):
            stack.append(current.value)
        elif isinstance(current, ast.Subscript):
            yield current
def _call_mutation_name(node: ast.Call) -> set[str] | None:
    _func = node.func
    if (isinstance(_func, ast.Attribute)
            and _func.attr in _MUTATING_METHODS):
        _root = _receiver_root_name(_func.value)
        return {_root} if _root else None
    return None
def _subscript_mutation_names(targets) -> set[str]:
    names: set[str] = set()
    for target in targets:
        if target is None:
            continue
        for subscript in _iter_subscript_targets(target):
            name = _subscript_container_name(subscript)
            if name:
                names.add(name)
    return names
def _assign_mutation_names(node: ast.Assign) -> set[str]:
    return _subscript_mutation_names(node.targets)
def _for_mutation_names(node) -> set[str]:
    return _subscript_mutation_names((node.target,))
def _with_mutation_names(node) -> set[str]:
    return _subscript_mutation_names(
        item.optional_vars for item in node.items)
def _annassign_mutation_names(node: ast.AnnAssign) -> set[str] | None:
    if node.value is None:
        return None
    _container = _subscript_container_name(node.target)
    return {_container} if _container else None
def _augassign_mutation_names(node: ast.AugAssign) -> set[str] | None:
    if isinstance(node.target, ast.Name):
        return {node.target.id}
    _container = _subscript_container_name(node.target)
    return {_container} if _container else None
def _delete_mutation_names(node: ast.Delete) -> set[str]:
    names = set(iter_unpack_target_names(node.targets))
    names.update(_subscript_mutation_names(node.targets))
    return names
_MUTATION_NAME_EXTRACTORS = {
    ast.Call: _call_mutation_name,
    ast.Assign: _assign_mutation_names,
    ast.AnnAssign: _annassign_mutation_names,
    ast.AugAssign: _augassign_mutation_names,
    ast.Delete: _delete_mutation_names,
    ast.For: _for_mutation_names,
    ast.AsyncFor: _for_mutation_names,
    ast.With: _with_mutation_names,
    ast.AsyncWith: _with_mutation_names,
    ast.comprehension: _for_mutation_names,
}
def _mutation_names_of(node: ast.AST):
    _extractor = _MUTATION_NAME_EXTRACTORS.get(type(node))
    return _extractor(node) if _extractor is not None else None
_COMP_SCOPE_CONTAINERS = (ast.ListComp, ast.SetComp, ast.DictComp,
                          ast.GeneratorExp)
def _collect_nonlocal_decl(item, bound: set) -> None:
    bound.update(item.names)
def _collect_assign_targets(item, bound: set) -> None:
    targets = (item.targets if isinstance(item, ast.Assign)
               else [item.target])
    for t in targets:
        if t is not None:
            bound.update(iter_unpack_target_names(t))
def _is_actual_scope_binding(scope_node, item) -> bool:
    return not (isinstance(scope_node, ast.ClassDef)
                and isinstance(item, ast.AnnAssign)
                and item.value is None)
def _collect_delete_bindings(item, bound: set) -> None:
    for target in item.targets:
        bound.update(iter_unpack_target_names(target))
def _collect_for_target(item, bound: set) -> None:
    bound.update(iter_unpack_target_names(item.target))
def _collect_with_vars(item, bound: set) -> None:
    for w_item in item.items:
        if w_item.optional_vars is not None:
            bound.update(iter_unpack_target_names(w_item.optional_vars))
def _collect_import_aliases(item, bound: set) -> None:
    for alias in item.names:
        bound.add(alias.asname or alias.name.split('.')[0])
def _collect_except_name(item, bound: set) -> None:
    if item.name:
        bound.add(item.name)
def _collect_walrus_target(item, bound: set) -> None:
    bound.add(item.target.id)
def _collect_match_binding(item, bound: set) -> None:
    for _field in ('name', 'rest'):
        _bound_name = getattr(item, _field, None)
        if isinstance(_bound_name, str) and _bound_name:
            bound.add(_bound_name)
_MATCH_BINDING_TYPES = tuple(
    _t for _t in (getattr(ast, 'MatchAs', None),
                  getattr(ast, 'MatchStar', None),
                  getattr(ast, 'MatchMapping', None))
    if _t is not None)
_SCOPE_BINDING_COLLECTORS = {
    ast.Nonlocal: _collect_nonlocal_decl,
    ast.Assign: _collect_assign_targets,
    ast.AnnAssign: _collect_assign_targets,
    ast.AugAssign: _collect_assign_targets,
    ast.Delete: _collect_delete_bindings,
    ast.For: _collect_for_target,
    ast.AsyncFor: _collect_for_target,
    ast.With: _collect_with_vars,
    ast.AsyncWith: _collect_with_vars,
    ast.Import: _collect_import_aliases,
    ast.ImportFrom: _collect_import_aliases,
    ast.ExceptHandler: _collect_except_name,
    ast.NamedExpr: _collect_walrus_target,
    **{_t: _collect_match_binding for _t in _MATCH_BINDING_TYPES},
}
_TYPE_ALIAS_T = getattr(ast, 'TypeAlias', None)
def _iter_nested_scope_bindings(node):
    stack = list(ast.iter_child_nodes(node))
    while stack:
        cur = stack.pop()
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef)):
            yield cur.name
            continue
        if isinstance(cur, ast.Lambda):
            continue
        if _TYPE_ALIAS_T is not None and isinstance(cur, _TYPE_ALIAS_T):
            _alias_name = getattr(cur, 'name', None)
            if isinstance(_alias_name, ast.Name):
                yield _alias_name.id
            continue
        stack.extend(ast.iter_child_nodes(cur))
def _in_scope_body(scope_node: ast.AST, child: ast.AST | None) -> bool:
    if isinstance(scope_node, ast.Lambda):
        return child is scope_node.body
    return child in getattr(scope_node, 'body', ())
def _iter_scope_body_nodes(scope_node, *, include_definition_nodes=False):
    body = ([scope_node.body] if isinstance(scope_node, ast.Lambda)
            else scope_node.body)
    stack = list(body)
    while stack:
        current = stack.pop()
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef, ast.Lambda)):
            if include_definition_nodes:
                yield current
            continue
        yield current
        stack.extend(ast.iter_child_nodes(current))
def _scope_declarations(scope_node) -> tuple[set, set]:
    bound: set = set()
    global_names: set = set()
    args = getattr(scope_node, 'args', None)
    if args is not None:
        for arg in iter_arg_nodes(args):
            bound.add(arg.arg)
    for item in _iter_scope_body_nodes(scope_node):
        if isinstance(item, ast.Global):
            global_names.update(item.names)
            continue
        if not _is_actual_scope_binding(scope_node, item):
            continue
        _collector = _SCOPE_BINDING_COLLECTORS.get(type(item))
        if _collector is not None:
            _collector(item, bound)
    body = ([scope_node.body] if isinstance(scope_node, ast.Lambda)
            else scope_node.body)
    for statement in body:
        _collect_namedexpr_bindings(statement, bound)
    bound.update(_iter_nested_scope_bindings(scope_node))
    bound.difference_update(global_names)
    return bound, global_names
def _collect_module_level_mutables(tree: ast.AST) -> list[tuple[str, int]]:
    mutables: dict[str, int] = {}
    for target, value, lineno in _iter_module_assign_pairs(tree):
        if not is_mutable_default(value):
            continue
        for name in iter_unpack_target_names(target):
            if name != '__all__':
                mutables.setdefault(name, lineno)
    return list(mutables.items())
def _source_position(node: ast.AST, *, end: bool = False) -> tuple[int, int]:
    line = getattr(node, 'end_lineno' if end else 'lineno', None)
    col = getattr(node, 'end_col_offset' if end else 'col_offset', None)
    if line is None or col is None:
        line = getattr(node, 'lineno', 0)
        col = getattr(node, 'col_offset', 0)
    return line, col
def _class_binding_position(node: ast.AST) -> tuple[int, int]:
    if (isinstance(node, (ast.For, ast.AsyncFor, ast.With, ast.AsyncWith,
                          ast.ExceptHandler)) and node.body):
        return _source_position(node.body[0])
    return _source_position(node, end=True)
def _record_class_binding(positions: dict[str, tuple[int, int]],
                          names, node: ast.AST) -> None:
    position = _class_binding_position(node)
    for name in names:
        previous = positions.get(name)
        if previous is None or position < previous:
            positions[name] = position
def _class_binding_positions(scope_node: ast.ClassDef) -> dict[str, tuple[int, int]]:
    positions: dict[str, tuple[int, int]] = {}
    for item in _iter_scope_body_nodes(scope_node, include_definition_nodes=True):
        if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda)):
            if not isinstance(item, ast.Lambda):
                _record_class_binding(positions, {item.name}, item)
            for expr in _definition_header_exprs(item):
                for named in _iter_header_namedexprs(expr):
                    _record_class_binding(positions, {named.target.id}, named)
            continue
        if _TYPE_ALIAS_T is not None and isinstance(item, _TYPE_ALIAS_T):
            if isinstance(item.name, ast.Name):
                _record_class_binding(positions, {item.name.id}, item)
            continue
        if not _is_actual_scope_binding(scope_node, item):
            continue
        collector = _SCOPE_BINDING_COLLECTORS.get(type(item))
        if collector is None:
            continue
        bound: set[str] = set()
        collector(item, bound)
        _record_class_binding(positions, bound, item)
    return positions
@dataclass(frozen=True)
class _MutationScopeTables:
    parents: dict[int, ast.AST]
    fn_bounds: dict[int, set[str]]
    fn_globals: dict[int, set[str]]
    class_bounds: dict[int, set[str]]
    class_globals: dict[int, set[str]]
    class_binding_positions: dict[int, dict[str, tuple[int, int]]]
    comp_scopes: dict[int, set[str]]
def _build_mutation_scope_tables(entry) -> _MutationScopeTables:
    tree = getattr(entry, 'tree', None)
    parents = build_parent_map(tree) if tree is not None else {}
    fn_bounds: dict[int, set] = {}
    fn_globals: dict[int, set] = {}
    class_bounds: dict[int, set] = {}
    class_globals: dict[int, set] = {}
    class_binding_positions: dict[int, dict[str, tuple[int, int]]] = {}
    comp_scopes: dict[int, set] = {}
    for node in entry_nodes(entry):
        if isinstance(node, _FUNCTION_SCOPE_CONTAINERS):
            fn_bounds[id(node)], fn_globals[id(node)] = _scope_declarations(node)
        elif isinstance(node, ast.ClassDef):
            class_bounds[id(node)], class_globals[id(node)] = (
                _scope_declarations(node))
            class_binding_positions[id(node)] = _class_binding_positions(node)
        if isinstance(node, _COMP_SCOPE_CONTAINERS):
            bound = _comp_scope_names(node)
            if bound:
                comp_scopes[id(node)] = bound
    return _MutationScopeTables(
        parents, fn_bounds, fn_globals, class_bounds, class_globals,
        class_binding_positions, comp_scopes)
def _comp_scope_names(comp_node: ast.AST) -> set[str]:
    bound: set[str] = set()
    for gen in comp_node.generators:
        bound.update(iter_unpack_target_names(gen.target))
    return bound
def _comp_scope_shadows(comp_node: ast.AST, name: str, cur: ast.AST,
                        prev: ast.AST | None,
                        comp_scopes: dict[int, set[str]]) -> bool:
    if name not in comp_scopes.get(id(comp_node), ()):
        return False
    _first_gen = comp_node.generators[0]
    return not (cur is _first_gen and prev is _first_gen.iter)
def _class_name_bound_before(tables: _MutationScopeTables,
                             scope: ast.ClassDef, name: str,
                             node: ast.AST) -> bool:
    position = tables.class_binding_positions.get(id(scope), {}).get(name)
    return position is None or position <= _source_position(node)
def _shadowed_locally(tables: _MutationScopeTables, name: str,
                      node: ast.AST) -> bool:
    cur: ast.AST | None = node
    prev: ast.AST | None = None
    seen_function = False
    while cur is not None and id(cur) in tables.parents:
        _parent = tables.parents[id(cur)]
        if isinstance(_parent, _COMP_SCOPE_CONTAINERS):
            if _comp_scope_shadows(_parent, name, cur, prev,
                                   tables.comp_scopes):
                return True
        elif (isinstance(_parent, _FUNCTION_SCOPE_CONTAINERS)
                and _in_scope_body(_parent, cur)):
            if name in tables.fn_globals.get(id(_parent), ()):
                return False
            if name in tables.fn_bounds.get(id(_parent), ()):
                return True
            seen_function = True
        elif (isinstance(_parent, ast.ClassDef) and not seen_function
                and _in_scope_body(_parent, cur)):
            if name in tables.class_globals.get(id(_parent), ()):
                return False
            if (name in tables.class_bounds.get(id(_parent), ())
                    and _class_name_bound_before(tables, _parent, name, node)):
                return True
        prev, cur = cur, _parent
    return False
def _declared_global_in_scope(tables: _MutationScopeTables, name: str,
                              node: ast.AST) -> bool:
    cur: ast.AST | None = node
    seen_function = False
    while cur is not None and id(cur) in tables.parents:
        parent = tables.parents[id(cur)]
        if (isinstance(parent, _FUNCTION_SCOPE_CONTAINERS)
                and _in_scope_body(parent, cur)):
            if name in tables.fn_globals.get(id(parent), ()):
                return True
            if name in tables.fn_bounds.get(id(parent), ()):
                return False
            seen_function = True
        elif (isinstance(parent, ast.ClassDef) and not seen_function
                and _in_scope_body(parent, cur)):
            if name in tables.class_globals.get(id(parent), ()):
                return True
            if name in tables.class_bounds.get(id(parent), ()):
                return False
        cur = parent
    return False
def _global_rebinding_names(node: ast.AST,
                            tables: _MutationScopeTables) -> set[str]:
    if isinstance(node, (ast.Global, ast.Nonlocal)):
        return set()
    collector = _SCOPE_BINDING_COLLECTORS.get(type(node))
    if collector is None:
        return set()
    bound: set[str] = set()
    collector(node, bound)
    return {
        name for name in bound
        if _declared_global_in_scope(tables, name, node)
    }
def _check_mutable_globals(entry) -> list[dict]:
    tree = entry.tree
    if tree is None:
        return []
    module_level_mutables = _collect_module_level_mutables(tree)
    mutated_names = _mutated_scope_names(
        entry, _build_mutation_scope_tables(entry))
    return [
        scan_issue(
            entry.rel_path, lineno, "mutable_global", "low",
            f"模块级可变全局变量 {name} 可能被意外修改")
        for name, lineno in module_level_mutables
        if name in mutated_names
        and not _mutable_global_convention_exempt(name)
    ]
def _mutated_scope_names(entry, tables: _MutationScopeTables) -> set[str]:
    mutated: set[str] = set()
    for node in entry_nodes(entry):
        mutated.update(
            name
            for name in (_mutation_names_of(node) or ())
            if not _shadowed_locally(tables, name, node)
        )
        mutated.update(_global_rebinding_names(node, tables))
    return mutated
def _report_duplicate_code(func_fingerprints: dict) -> list[dict]:
    findings = []
    for locations in func_fingerprints.values():
        if len(locations) >= 2:
            loc_str = ', '.join(f"{f}:{ln}({n})" for f, ln, n in locations[:5])
            _first_file, _first_line, _first_name = locations[0]
            findings.append({
                "file": _first_file, "line": _first_line,
                "type": "duplicate_code", "severity": "medium",
                "name": _first_name,
                "count": len(locations),
                "message": f"重复代码 ({len(locations)} 处): {loc_str}",
            })
    return findings
_ACCEPTABLE_SHADOWS = frozenset({
    'id', 'type', 'list', 'dict', 'set', 'tuple', 'str', 'int', 'float',
    'bool', 'bytes', 'object', 'input', 'format', 'filter', 'map', 'zip',
    'range', 'print', 'open', 'sum', 'min', 'max', 'abs', 'all', 'any',
    'len', 'sorted', 'reversed', 'enumerate', 'property', 'staticmethod',
    'classmethod', 'super', 'hash', 'dir', 'vars', 'locals', 'globals',
    'repr', 'ascii', 'bin', 'hex', 'oct', 'chr', 'ord', 'round', 'pow',
    'file', 'name', 'help', 'next', 'iter', 'slice', 'frozenset',
})
def _shadow_report_candidate(name: str, builtin_names: frozenset[str] | set[str]) -> bool:
    return name in builtin_names and name not in _ACCEPTABLE_SHADOWS
def _function_name_shadow_issue(entry, node: ast.AST,
                                builtin_names: frozenset[str] | set[str],
                                class_func_ids) -> dict | None:
    if not _shadow_report_candidate(node.name, builtin_names):
        return None
    if class_func_ids is not None and id(node) in class_func_ids:
        return None
    return scan_issue(
        entry.rel_path, node.lineno, "shadowing_builtin", "medium",
        f"函数 {node.name} 遮蔽内建名称")
def _function_param_shadow_issues(entry, node: ast.AST,
                                  builtin_names: frozenset[str] | set[str],
                                  ) -> list[dict]:
    _shadow_args = iter_arg_nodes(node.args)
    return [
        scan_issue(
            entry.rel_path, node.lineno, "shadowing_builtin", "low",
            f"参数 {_arg.arg} 遮蔽内建名称")
        for _arg in _shadow_args
        if _arg.arg not in _ACCEPTABLE_SHADOWS
        and _arg.arg in builtin_names
    ]
def _check_shadowing_builtins(entry,
                              builtin_names: frozenset[str] | set[str],
                              ) -> list[dict]:
    findings = []
    class_func_ids = _class_method_ids(entry)
    for node in entry_nodes(entry):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            name_issue = _function_name_shadow_issue(
                entry, node, builtin_names, class_func_ids)
            if name_issue is not None:
                findings.append(name_issue)
            findings.extend(
                _function_param_shadow_issues(entry, node, builtin_names))
        elif isinstance(node, ast.ClassDef) and node.name in builtin_names:
            findings.append(scan_issue(
                entry.rel_path, node.lineno, "shadowing_builtin", "medium",
                f"类 {node.name} 遮蔽内建名称"))
    return findings
def _check_global_statements(entry) -> list[dict]:
    findings = []
    for node in entry_nodes(entry):
        if isinstance(node, ast.Global):
            findings.append(scan_issue(
                entry.rel_path, node.lineno, "global_statement", "medium",
                f"global 语句使用: {list(node.names)}"))
    return findings
def _todo_finding(rel_path: str, line_num: int, match: re.Match) -> dict:
    return scan_issue(
        rel_path, line_num, "todo_marker", "low",
        f"待处理标记: {match.group()}")
def _check_todo_markers(entry, todo_pattern: re.Pattern) -> list[dict]:
    comments = comment_tokens(entry.source)
    if comments is not None:
        return [
            _todo_finding(entry.rel_path, tok.start[0], match)
            for tok in comments
            for match in (todo_pattern.search(tok.string),)
            if match is not None
        ]
    return [
        _todo_finding(entry.rel_path,
                      entry.source[:match.start()].count('\n') + 1, match)
        for match in todo_pattern.finditer(entry.source)
    ]
def _docstring_flags(entry) -> tuple[dict, set]:
    lookup = {}
    exempt: set[tuple[str, int]] = set()
    for node in entry_nodes(entry):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        key = (node.name, node.lineno)
        lookup[key] = bool(ast.get_docstring(node))
        if has_abstractmethod_decorator(node) or _is_typing_overload(node):
            exempt.add(key)
    return lookup, exempt
def _check_docstring_coverage(entry) -> list[dict]:
    if entry.tree is None:
        return []
    _func_docstring_lookup, _docstring_exempt = _docstring_flags(entry)
    findings = []
    for func in entry.functions:
        if func.get('is_private') or func.get('length', 0) <= 5:
            continue
        key = (func.get('name'), func.get('line'))
        if key in _docstring_exempt:
            continue
        if _func_docstring_lookup.get(key) is False:
            findings.append(scan_issue(
                entry.rel_path, func['line'], "missing_docstring", "low",
                f"函数 {func['name']} 缺少文档字符串"))
    return findings
def _is_silent_pass_handler(node) -> bool:
    return (isinstance(node, ast.ExceptHandler) and node.type is not None
            and len(node.body) == 1 and _is_placeholder_stmt(node.body[0]))
def _comment_line_numbers(source_lines) -> set[int]:
    tokens = comment_tokens('\n'.join(source_lines))
    return {tok.start[0] for tok in tokens or ()}
def _commented_empty_except(node: ast.ExceptHandler, source_lines,
                            comment_lines=None) -> bool:
    if comment_lines is None:
        comment_lines = _comment_line_numbers(source_lines)
    return any(
        lineno in comment_lines
        for lineno in range(node.lineno, node.body[0].lineno + 1)
    )
def _check_empty_except_blocks(cache) -> list[dict]:
    findings = []
    for entry in cache.valid_entries:
        source_lines = entry.source.split('\n')
        comment_lines = _comment_line_numbers(source_lines)
        findings.extend(
            scan_issue(
                entry.rel_path, node.lineno, "empty_except", "medium",
                "空 except 块（仅 pass），静默吞没异常")
            for node in entry_nodes(entry)
            if _is_reportable_empty_except(node, source_lines, comment_lines)
        )
    return findings
def _is_reportable_empty_except(node, source_lines, comment_lines=None) -> bool:
    return (_is_silent_pass_handler(node)
            and not _commented_empty_except(node, source_lines, comment_lines))
def _self_assignment_display(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return dotted_name(node) or None
    return None
def _self_assignment_target(node: ast.AST) -> str | None:
    if not isinstance(node, ast.Assign) or len(node.targets) != 1:
        return None
    target = node.targets[0]
    if not isinstance(target, (ast.Name, ast.Attribute)):
        return None
    if not isinstance(node.value, (ast.Name, ast.Attribute)):
        return None
    target_name = _self_assignment_display(target)
    if target_name is None or target_name != _self_assignment_display(
            node.value):
        return None
    return target_name
def _check_self_assignments(cache) -> list[dict]:
    findings = []
    for entry in cache.valid_entries:
        for node in entry_nodes(entry):
            target_name = _self_assignment_target(node)
            if target_name is None:
                continue
            findings.append(scan_issue(
                entry.rel_path, node.lineno, "self_assignment", "low",
                f"自赋值: {target_name} = {target_name}"))
    return findings
def _is_constant_compare(node) -> bool:
    return (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.left, ast.Constant)
            and isinstance(node.comparators[0], ast.Constant))
def _is_bool_tautology(node) -> bool:
    _left, _right = node.left.value, node.comparators[0].value
    return (isinstance(_left, bool) and isinstance(_right, bool)
            and _left == _right)
def _check_constant_comparisons(cache) -> list[dict]:
    findings = []
    for entry in cache.valid_entries:
        is_test = is_test_file_path(entry.rel_path)
        for node in entry_nodes(entry):
            if (is_test or not _is_constant_compare(node)
                    or _is_bool_tautology(node)):
                continue
            findings.append(scan_issue(
                entry.rel_path, node.lineno, "constant_comparison", "low",
                "常量间比较，结果在编译时即可确定"))
    return findings
def _docstring_first_line(node: ast.AST) -> int | None:
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Module)):
        return None
    _body = getattr(node, 'body', None)
    if not _body or not isinstance(_body[0], ast.Expr):
        return None
    _value = _body[0].value
    if isinstance(_value, ast.Constant) and isinstance(_value.value, str):
        return _value.lineno
    return None
def _dict_key_coords(node: ast.AST) -> set[tuple[int, int]]:
    if not isinstance(node, ast.Dict):
        return set()
    return {(_key.lineno, _key.col_offset)
            for _key in node.keys if _key is not None}
def _literal_skip_coords(entry) -> tuple[set[int], set[tuple[int, int]]]:
    doc_lines: set[int] = set()
    skip_positions: set[tuple[int, int]] = set()
    for node in entry_nodes(entry):
        line = _docstring_first_line(node)
        if line is not None:
            doc_lines.add(line)
        skip_positions.update(_dict_key_coords(node))
        if isinstance(node, ast.JoinedStr):
            skip_positions.update(
                (value.lineno, value.col_offset)
                for value in node.values
                if isinstance(value, ast.Constant))
    return doc_lines, skip_positions
def _collect_literal_skip_maps(cache) -> tuple[dict, dict]:
    _docstring_lines: dict[str, set[int]] = {}
    _dictkey_entries: dict[str, set[tuple[int, int]]] = {}
    for entry in cache.valid_entries:
        _docstring_lines[entry.rel_path], _dictkey_entries[entry.rel_path] = (
            _literal_skip_coords(entry))
    return _docstring_lines, _dictkey_entries
def _duplicate_literal_skipped(node: ast.Constant, _doc_lines: set[int],
                               _dictkey_pairs: set[tuple[int, int]]) -> bool:
    return (node.lineno in _doc_lines
            or (node.lineno, node.col_offset) in _dictkey_pairs)
def _check_duplicate_strings(cache) -> list[dict]:
    literals, locations = _collect_duplicate_literals(cache)
    return _duplicate_string_findings(literals, locations)
_DUP_STRING_MIN_LEN = 15
_DUP_STRING_MIN_COUNT = 5
_DUP_STRING_TOP_N = 10
def _long_string_literal(node: ast.AST) -> str | None:
    if (isinstance(node, ast.Constant) and isinstance(node.value, str)
            and len(node.value) >= _DUP_STRING_MIN_LEN):
        return node.value
    return None
def _collect_duplicate_literals(cache) -> tuple[Counter, dict]:
    docstring_lines, dictkey_entries = _collect_literal_skip_maps(cache)
    literals: Counter = Counter()
    locations: dict[str, list[tuple[str, int]]] = defaultdict(list)
    for entry in cache.valid_entries:
        doc_lines = docstring_lines.get(entry.rel_path, set())
        dictkey_pairs = dictkey_entries.get(entry.rel_path, set())
        for node in entry_nodes(entry):
            text = _long_string_literal(node)
            if text is None or _duplicate_literal_skipped(
                    node, doc_lines, dictkey_pairs):
                continue
            literals[text] += 1
            locations[text].append((entry.rel_path, node.lineno))
    return literals, locations
def _duplicate_string_findings(literals: Counter, locations: dict) -> list[dict]:
    findings = []
    for text, count in literals.most_common(_DUP_STRING_TOP_N):
        if count < _DUP_STRING_MIN_COUNT:
            continue
        coords = ', '.join(
            f'{rel}:{line}' for rel, line in locations[text][:3])
        _first_rel, _first_line = locations[text][0]
        findings.append({
            "file": _first_rel, "line": _first_line,
            "type": "duplicate_string", "severity": "low",
            "count": count, "locations": coords,
            "message": f"重复字符串 '{text[:30]}' 出现 {count} 次，建议提取为常量",
        })
    return findings
def _compute_ast_fingerprint(func_node: ast.AST) -> str:
    parts = []
    for child in walk_nodes(func_node):
        parts.append(type(child).__name__)
    if not parts:
        return ''
    _n_params = count_params(func_node)
    _complexity = 1 + sum(
        isinstance(_n, (ast.If, ast.For, ast.While, ast.Try, TRY_STAR_T,
                        ast.BoolOp, ast.ExceptHandler, ast.With, ast.IfExp))
        for _n in walk_nodes(func_node)
    )
    _calls = sorted({
        name for child in walk_nodes(func_node)
        if isinstance(child, ast.Call)
        for name in (dotted_name(child.func),)
        if name
    })
    return hashlib.md5(
        f"{_n_params}|{_complexity}|{','.join(_calls)}|{'|'.join(parts)}".encode(),
        usedforsecurity=False
    ).hexdigest()[:12]
_EXCEPTION_GROUP_NAMES = frozenset({'ExceptionGroup', 'BaseExceptionGroup'})
_DEPRECATED_STDLIB = frozenset({
    'asynchat', 'asyncore', 'distutils', 'imp',
    'aix_support', 'aifc', 'audioop', 'cgi', 'cgitb', 'chunk', 'crypt',
    'imghdr', 'mailcap', 'msilib', 'nis', 'nntplib', 'ossaudiodev',
    'pipes', 'sndhdr', 'smtpd', 'spwd', 'sunau', 'telnetlib', 'uu',
    'xdrlib',
    'sre_compile', 'sre_constants', 'sre_parse', 'dummy_threading',
})
@dataclass
class _CompatScanTally:
    total_funcs: int = 0
    annotated_funcs: int = 0
    total_files: int = 0
    future_annotations_files: int = 0
    fstring_count: int = 0
    format_count: int = 0
    platform_specific: int = 0
    asyncio_usage: int = 0
_IMPORT_ERROR_NAMES = frozenset({"ImportError", "ModuleNotFoundError"})
def _catches_import_error(node) -> bool:
    if isinstance(node, ast.Name):
        return node.id in _IMPORT_ERROR_NAMES
    if isinstance(node, ast.Attribute):
        return node.attr in _IMPORT_ERROR_NAMES
    if isinstance(node, ast.Tuple):
        return any(_catches_import_error(elt) for elt in node.elts)
    return False
def _importerror_guarded_import_ids(tree) -> set[int]:
    guarded: set[int] = set()
    for node in shared_walk(tree):
        if not isinstance(node, (ast.Try, TRY_STAR)) or not node.handlers:
            continue
        if not any(_catches_import_error(h.type) for h in node.handlers):
            continue
        stack = list(node.body)
        while stack:
            sub = stack.pop()
            if isinstance(sub, _FUNCTION_SCOPE_CONTAINERS):
                continue
            if isinstance(sub, (ast.Import, ast.ImportFrom)):
                guarded.add(id(sub))
            stack.extend(ast.iter_child_nodes(sub))
    return guarded
def _deprecated_import_issue(node, rel_path: str,
                             guarded_ids: frozenset | set
                             ) -> list[dict]:
    if id(node) in guarded_ids:
        return []
    if isinstance(node, ast.Import):
        return [scan_issue(
            rel_path, node.lineno, 'deprecated_stdlib', 'medium',
            f'废弃标准库模块: {alias.name}（Python 3.12/3.13 已移除）')
            for alias in node.names
            if alias.name.split('.')[0] in _DEPRECATED_STDLIB]
    if (isinstance(node, ast.ImportFrom) and node.module and not node.level
            and node.module.split('.')[0] in _DEPRECATED_STDLIB):
        return [scan_issue(
            rel_path, node.lineno, 'deprecated_stdlib', 'medium',
            f'废弃标准库模块: {node.module}（Python 3.12/3.13 已移除）')]
    return []
def _scan_packaging_compat_issues(cache, issues) -> None:
    for entry in cache.valid_entries:
        if not os.path.isfile(entry.path):
            _log.debug("瞬态文件跳过（汇总阶段发现已被外部删除）: %s", entry.path)
            continue
        decl_line = redundant_coding_decl_line(entry.source)
        if decl_line is not None:
            issues.append(scan_issue(
                entry.rel_path, decl_line, 'unnecessary_coding_decl', 'low',
                'Python 3 默认 UTF-8 编码，coding 声明冗余'))
        _guarded = _importerror_guarded_import_ids(entry.tree)
        for node in entry_nodes(entry):
            issues.extend(_deprecated_import_issue(
                node, entry.rel_path, _guarded))
_COMPAT_FINDINGS_LIMIT = 50
def _finalize_compat_results(result, issues, py_version, min_version_str,
                             tally: _CompatScanTally) -> None:
    annotation_rate = ((tally.annotated_funcs / tally.total_funcs * 100)
                       if tally.total_funcs > 0 else 0)
    future_rate = ((tally.future_annotations_files / tally.total_files * 100)
                   if tally.total_files > 0 else 0)
    _type_counts = dict(Counter(issue["type"] for issue in issues))
    result.metrics = {
        "python_version": f"{py_version.major}.{py_version.minor}.{py_version.micro}",
        "min_version_required": min_version_str,
        "total_issues": len(issues),
        "findings_truncated": max(
            0, len(issues) - _COMPAT_FINDINGS_LIMIT),
        "deprecated_api_count": _type_counts.get("deprecated_api", 0),
        "version_incompatibility_count": _type_counts.get("version_incompatibility", 0),
        "missing_annotation_count": _type_counts.get("missing_annotations", 0),
        "annotation_rate": round(annotation_rate, 1),
        "future_annotations_rate": round(future_rate, 1),
        "fstring_count": tally.fstring_count,
        "format_count": tally.format_count,
        "platform_specific_count": tally.platform_specific,
        "asyncio_usage": tally.asyncio_usage,
        "deprecated_stdlib_count": _type_counts.get("deprecated_stdlib", 0),
        "unnecessary_coding_decls": _type_counts.get("unnecessary_coding_decl", 0),
        "version_gap": f"{py_version.major}.{py_version.minor} vs {min_version_str}",
    }
    result.findings = issues[:_COMPAT_FINDINGS_LIMIT]
    critical = sum(1 for i in issues if i["severity"] == "high")
    if critical == 0:
        result.status = "pass"
        result.score = 100 if not issues else 80
        result.summary = (f"Python {py_version.major}.{py_version.minor} 兼容: "
                          f"{len(issues)} 问题, 注解率 {annotation_rate:.0f}%, "
                          f"future {future_rate:.0f}%")
    else:
        result.status = "warn"
        result.score = 30
        result.summary = f"{critical} 个严重兼容性问题"
_PLATFORM_PROBE_ATTRS = frozenset({("sys", "platform"), ("os", "name")})
def _is_platform_probe(node) -> bool:
    if isinstance(node, ast.Call):
        func = node.func
        return (isinstance(func, ast.Attribute) and func.attr == "system"
                and isinstance(func.value, ast.Name)
                and func.value.id == "platform")
    if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
        return (node.value.id, node.attr) in _PLATFORM_PROBE_ATTRS
    return False
def _compare_hits_platform_probe(node: ast.Compare) -> bool:
    return any(_is_platform_probe(side)
               for side in [node.left, *node.comparators])
def _in_self_test_fn(node, parent_map: dict) -> bool:
    cur = node
    while cur in parent_map:
        cur = parent_map[cur]
        if (isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef))
                and cur.name.startswith(('self_test', '_self_test'))):
            return True
    return False
def _annotation_host_verdict(parent, child) -> bool | None:
    if isinstance(parent, ast.arg):
        return parent.annotation is child
    if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return parent.returns is child
    if isinstance(parent, ast.AnnAssign):
        return parent.annotation is child
    return None if isinstance(parent, ast.expr) else False
def _is_annotation_context(node, parent_map: dict) -> bool:
    child = node
    while True:
        parent = parent_map.get(child)
        if parent is None:
            return False
        verdict = _annotation_host_verdict(parent, child)
        if verdict is not None:
            return verdict
        child = parent
def _is_local_annotation_not_evaluated(node, parent_map: dict) -> bool:
    child = node
    while True:
        parent = parent_map.get(child)
        if parent is None:
            return False
        if isinstance(parent, ast.AnnAssign) and parent.annotation is child:
            owner = parent_map.get(parent)
            scope_types = (*_FUNC_NODE_TYPES, ast.ClassDef, ast.Module)
            while owner is not None and not isinstance(owner, scope_types):
                owner = parent_map.get(owner)
            return isinstance(owner, _FUNC_NODE_TYPES)
        verdict = _annotation_host_verdict(parent, child)
        if verdict is not None:
            return False
        child = parent
def _is_typing_self_usage(node, ctx: _VersionRuleContext) -> bool:
    if isinstance(node, ast.Name):
        return _version_import_identity(node, ctx) == 'typing.Self'
    return (isinstance(node, ast.Attribute) and node.attr == 'Self'
            and _version_import_identity(node.value, ctx) == 'typing')
def _verissue_deprecated_calls(node, rel_path: str,
                               ctx: _VersionRuleContext) -> list[dict]:
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)):
        return []
    func = node.func
    module_name = _version_import_identity(func.value, ctx)
    found = []
    if func.attr == "popen" and module_name in ("os", "platform"):
        found.append(scan_issue(
            rel_path, node.lineno, "deprecated_api", "medium",
            "os.popen() 不建议使用，建议使用 subprocess"))
    if func.attr == "get_event_loop" and module_name == "asyncio" \
            and ctx.py_version >= (3, 10):
        found.append(scan_issue(
            rel_path, node.lineno, "deprecated_api", "low",
            "asyncio.get_event_loop() 在 Python 3.10+ 中已废弃"))
    return found
def _verissue_relative_import(node, rel_path: str) -> list[dict]:
    if isinstance(node, ast.ImportFrom) and node.level and node.level > 1:
        return [scan_issue(
            rel_path, node.lineno, "relative_import", "low",
            f"多级相对导入 (level={node.level}) 可能影响可移植性")]
    return []
def _verissue_assert_production(node, rel_path: str, parent_map_fn) -> list[dict]:
    if not isinstance(node, ast.Assert) or is_test_file_path(rel_path):
        return []
    if _in_self_test_fn(node, parent_map_fn()):
        return []
    return [scan_issue(
        rel_path, node.lineno, "assert_in_production", "low",
        "assert 语句在 -O 模式下会被忽略，不应用于生产代码逻辑")]
def _make_lazy_parent_map(tree):
    _pm_ref = [None]
    def _parent_map():
        if _pm_ref[0] is None:
            _pm_ref[0] = build_node_parent_map(tree)
        return _pm_ref[0]
    return _parent_map
def _type_checking_only_node_ids(tree) -> frozenset[int]:
    typing_refs, tc_binds = collect_typing_tc_bindings(tree)
    node_ids: set[int] = set()
    for node in shared_walk(tree):
        body = type_checking_static_body(node, typing_refs, tc_binds)
        if body is None:
            continue
        for statement in body:
            node_ids.update(id(child) for child in walk_nodes(statement))
    return frozenset(node_ids)
_EMPTY_FROZENSET = frozenset()
def _collect_version_module_imports(
        tree, tables: _MutationScopeTables,
        outer_names: dict[int, set[str]],
        guarded_import_ids: frozenset[int] = _EMPTY_FROZENSET,
        guarded_names: set[tuple[int, str]] | None = None
        ) -> dict[tuple[int, str], str]:
    imported: dict[tuple[int, str], str] = {}
    for node in shared_walk(tree):
        if isinstance(node, ast.Import):
            aliases = (
                (alias.asname or alias.name.split('.')[0],
                 alias.name if alias.asname else alias.name.split('.')[0])
                for alias in node.names
            )
        elif (isinstance(node, ast.ImportFrom) and not node.level
                and node.module in {'builtins', 'typing'}):
            aliases = (
                (alias.asname or alias.name, f'{node.module}.{alias.name}')
                for alias in node.names
                if alias.name != '*'
                and (node.module == 'builtins' or alias.name == 'Self')
            )
        else:
            continue
        for bound_name, module_name in aliases:
            scope = _import_binding_scope(
                bound_name, node, tables, outer_names)
            if scope is None:
                continue
            key = (id(scope), bound_name)
            if (isinstance(node, ast.ImportFrom)
                    and id(node) in guarded_import_ids):
                if guarded_names is not None:
                    guarded_names.add(key)
            else:
                imported[key] = module_name
    return imported
@dataclass(frozen=True)
class _VersionRuleContext:
    py_version: tuple[int, ...]
    has_future: bool
    parent_map: Callable[[], dict]
    type_checking_only_ids: frozenset[int]
    tree: ast.AST
    tables: _MutationScopeTables
    outer_names: dict[int, set[str]]
    module_imports: dict[tuple[int, str], str]
    guarded_import_ids: frozenset[int] = _EMPTY_FROZENSET
    guarded_import_names: frozenset[tuple[int, str]] = _EMPTY_FROZENSET
def _version_import_identity(node, ctx: _VersionRuleContext) -> str | None:
    if not isinstance(node, ast.Name):
        return None
    scope = _resolved_name_scope(
        node.id, node, ctx.tables, ctx.outer_names, ctx.tree)
    if scope is None:
        return None
    return ctx.module_imports.get((id(scope), node.id))
def _is_guarded_version_name(node, ctx: _VersionRuleContext) -> bool:
    if not isinstance(node, ast.Name):
        return False
    scope = _resolved_name_scope(
        node.id, node, ctx.tables, ctx.outer_names, ctx.tree)
    return (scope is not None
            and (id(scope), node.id) in ctx.guarded_import_names)
def _exception_group_name(node, ctx: _VersionRuleContext) -> str | None:
    if isinstance(node, ast.Name):
        identity = _version_import_identity(node, ctx)
        if identity and identity.startswith('builtins.'):
            imported_name = identity[len('builtins.'):]
            if imported_name in _EXCEPTION_GROUP_NAMES:
                return imported_name
        return node.id if node.id in _EXCEPTION_GROUP_NAMES else None
    if (isinstance(node, ast.Attribute)
            and node.attr in _EXCEPTION_GROUP_NAMES
            and _version_import_identity(node.value, ctx) == 'builtins'):
        return node.attr
    return None
def _version_rule_context(tree, py_version, *,
                          has_future: bool | None = None
                          ) -> _VersionRuleContext:
    if has_future is None:
        has_future = module_postpones_annotations(tree, require_absolute=True)
    entry = SimpleNamespace(tree=tree)
    tables = _build_mutation_scope_tables(entry)
    outer_names = _outer_scope_declarations(tree)
    guarded_import_ids = frozenset(_importerror_guarded_import_ids(tree))
    guarded_names: set[tuple[int, str]] = set()
    module_imports = _collect_version_module_imports(
        tree, tables, outer_names, guarded_import_ids, guarded_names)
    return _VersionRuleContext(
        py_version=tuple(py_version),
        has_future=has_future,
        parent_map=_make_lazy_parent_map(tree),
        type_checking_only_ids=_type_checking_only_node_ids(tree),
        guarded_import_ids=guarded_import_ids,
        tree=tree,
        tables=tables,
        outer_names=outer_names,
        module_imports=module_imports,
        guarded_import_names=frozenset(guarded_names),
    )
@dataclass(frozen=True)
class _VersionFeatureRule:
    name: str
    min_version: tuple[int, int]
    severity: str
    message: str
    detect: Callable[[ast.AST, _VersionRuleContext], list]
    once_per_file: bool = False
def _detect_walrus(node, ctx) -> list:
    return [node] if isinstance(node, ast.NamedExpr) else []
def _detect_match_stmt(node, ctx) -> list:
    return [node] if isinstance(node, AST_MATCH_TYPES) else []
def _detect_pep604_union(node, ctx) -> list:
    if (ctx.has_future or id(node) in ctx.type_checking_only_ids
            or not isinstance(node, ast.BinOp)
            or not isinstance(node.op, ast.BitOr)):
        return []
    if _is_local_annotation_not_evaluated(node, ctx.parent_map()):
        return []
    if not _is_annotation_context(node, ctx.parent_map()):
        return []
    return [node]
def _detect_exception_group(node, ctx) -> list:
    if _is_local_annotation_not_evaluated(node, ctx.parent_map()):
        return []
    if (isinstance(node, ast.ImportFrom) and node.level == 0
            and node.module == 'builtins'
            and any(alias.name in _EXCEPTION_GROUP_NAMES
                    for alias in node.names)):
        if (id(node) in ctx.type_checking_only_ids
                or id(node) in ctx.guarded_import_ids):
            return []
        return [node]
    if TRY_STAR_T is not ast.Try and isinstance(node, TRY_STAR_T):
        return [node]
    if _is_guarded_version_name(node, ctx):
        return []
    group_name = _exception_group_name(node, ctx)
    if group_name is None:
        return []
    if id(node) in ctx.type_checking_only_ids:
        return []
    if ctx.has_future and _is_annotation_context(node, ctx.parent_map()):
        return []
    if isinstance(node, ast.Name):
        identity = _version_import_identity(node, ctx)
        if identity != f'builtins.{group_name}':
            bound = collect_py01_enclosing_bindings(ctx.parent_map(), node)
            if group_name in bound:
                return []
    return [node]
def _detect_typing_self(node, ctx) -> list:
    if _is_local_annotation_not_evaluated(node, ctx.parent_map()):
        return []
    if (isinstance(node, ast.ImportFrom) and node.level == 0
            and node.module == 'typing'
            and any(alias.name == 'Self' for alias in node.names)):
        if (id(node) in ctx.type_checking_only_ids
                or id(node) in ctx.guarded_import_ids):
            return []
        return [node]
    if _is_guarded_version_name(node, ctx):
        return []
    if not _is_typing_self_usage(node, ctx):
        return []
    if id(node) in ctx.type_checking_only_ids:
        return []
    if ctx.has_future and _is_annotation_context(node, ctx.parent_map()):
        return []
    return [node]
_VERSION_FEATURE_RULES: tuple[_VersionFeatureRule, ...] = (
    _VersionFeatureRule(
        'walrus', (3, 8), 'high', '海象运算符 (:=) 需要 Python 3.8+',
        _detect_walrus),
    _VersionFeatureRule(
        'match_stmt', (3, 10), 'high', 'match 语句需要 Python 3.10+',
        _detect_match_stmt),
    _VersionFeatureRule(
        'pep604_union', (3, 10), 'medium',
        'PEP 604 类型联合 X | Y 需要 Python 3.10+'
        '（或 from __future__ import annotations）',
        _detect_pep604_union, once_per_file=True),
    _VersionFeatureRule(
        'exception_group', (3, 11), 'high',
        'ExceptionGroup 与 except* 语法需要 Python 3.11+',
        _detect_exception_group),
    _VersionFeatureRule(
        'typing_self', (3, 11), 'medium', 'typing.Self 需要 Python 3.11+',
        _detect_typing_self, once_per_file=True),
)
def _version_feature_issues(rule: _VersionFeatureRule, node, rel_path: str,
                            ctx: _VersionRuleContext,
                            reported_once: set[str]) -> list[dict]:
    if rule.min_version <= ctx.py_version:
        return []
    if rule.once_per_file and rule.name in reported_once:
        return []
    hits = rule.detect(node, ctx)
    if not hits:
        return []
    if rule.once_per_file:
        reported_once.add(rule.name)
    return [scan_issue(rel_path, getattr(hit, 'lineno', 0),
                        'version_incompatibility', rule.severity, rule.message)
            for hit in hits]
def _compat_scan_version_issues(tree, rel_path: str, py_version,
                                has_future: bool) -> list[dict]:
    ctx = _version_rule_context(tree, py_version, has_future=has_future)
    issues: list[dict] = []
    reported_once: set[str] = set()
    for node in shared_walk(tree):
        issues.extend(_verissue_deprecated_calls(node, rel_path, ctx))
        for rule in _VERSION_FEATURE_RULES:
            issues.extend(_version_feature_issues(
                rule, node, rel_path, ctx, reported_once))
        issues.extend(_verissue_relative_import(node, rel_path))
        issues.extend(_verissue_assert_production(node, rel_path, ctx.parent_map))
    return issues
def _raise_min_version(node, ctx: _VersionRuleContext,
                       current: tuple[int, int]) -> tuple[int, int]:
    for rule in _VERSION_FEATURE_RULES:
        if rule.min_version <= current:
            continue
        if rule.detect(node, ctx):
            current = rule.min_version
    return current
def _estimate_entry_min_version(entry, current: tuple[int, int]) -> tuple[int, int]:
    tree = entry.tree
    ctx = _version_rule_context(tree, sys.version_info)
    for node in entry_nodes(entry):
        current = _raise_min_version(node, ctx, current)
    return current
def _compat_estimate_min_version(cache) -> str:
    min_version_required = (3, 7)
    for entry in cache.valid_entries:
        if not os.path.isfile(entry.path):
            _log.debug(
                "瞬态文件跳过（最低版本估算阶段发现已被外部删除）: %s", entry.path)
            continue
        min_version_required = _estimate_entry_min_version(entry, min_version_required)
    return f"{min_version_required[0]}.{min_version_required[1]}"
def _any_param_annotated(sig_args) -> bool:
    return any(arg.annotation is not None for arg in iter_arg_nodes(sig_args))
def _annotation_required_params(node, is_method: bool) -> list:
    params = list(iter_arg_nodes(node.args))
    if not is_method:
        return params
    positional = (*node.args.posonlyargs, *node.args.args)
    if positional and positional[0].arg in _IMPLICIT_METHOD_PARAMS:
        implicit = positional[0]
        return [arg for arg in params if arg is not implicit]
    return params
def _all_params_annotated(node, is_method: bool) -> bool:
    return all(arg.annotation is not None
               for arg in _annotation_required_params(node, is_method))
def _fn_annotation_status(node, is_method: bool) -> tuple[bool, bool, bool]:
    has_return = node.returns is not None
    has_any = _any_param_annotated(node.args)
    has_full = _all_params_annotated(node, is_method)
    return has_return, has_any, has_full
def _tally_syntax_features(node, tally: _CompatScanTally) -> None:
    if isinstance(node, ast.Call):
        func = node.func
        if isinstance(func, ast.Attribute) and func.attr == "format":
            tally.format_count += 1
    if isinstance(node, ast.JoinedStr):
        tally.fstring_count += 1
    if (isinstance(node, ast.Compare)
            and _compare_hits_platform_probe(node)):
        tally.platform_specific += 1
    if isinstance(node, (ast.AsyncFunctionDef, ast.Await)):
        tally.asyncio_usage += 1
def _tally_function_annotations(node, rel_path, top_level_public,
                                class_method_ids, tally: _CompatScanTally,
                                issues) -> None:
    tally.total_funcs += 1
    has_return, has_any, has_full = _fn_annotation_status(
        node,
        id(node) in class_method_ids and not is_static_method(node),
    )
    if has_return and has_full:
        tally.annotated_funcs += 1
    elif (not has_return and not has_any
            and top_level_public.get(node.lineno) == node.name
            and node.name != '__init__'
            and not is_test_file_path(rel_path)):
        issues.append(scan_issue(
            rel_path, node.lineno, "missing_annotations", "low",
            f"函数 {node.name} 缺少类型注解"))
def _top_level_public_functions(tree) -> dict[int, str]:
    return {
        node.lineno: node.name
        for node in iter_module_level_stmts(tree.body)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        and not node.name.startswith('_')
    }
def _scan_compat_entry(entry, py_version, tally, issues) -> None:
    tree = entry.tree
    rel_path = entry.rel_path
    has_future = module_postpones_annotations(tree, require_absolute=True)
    if has_future:
        tally.future_annotations_files += 1
    issues.extend(_compat_scan_version_issues(
        tree, rel_path, py_version, has_future))
    top_level_public = _top_level_public_functions(tree)
    class_method_ids = _class_method_ids(entry)
    for node in shared_walk(tree):
        _tally_syntax_features(node, tally)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            _tally_function_annotations(
                node, rel_path, top_level_public, class_method_ids, tally, issues)
def run_compatibility_tests(skill_dir: str, **kwargs) -> TestMethodResult:
    start = time.perf_counter()
    result = TestMethodResult(
        method_name="兼容性测试",
        method_id="compatibility",
    )
    cache = resolve_file_cache(skill_dir, kwargs)
    if cache is None:
        _log.warning("兼容性测试分析目录无效，按 error 终止: %r", skill_dir)
        return TestMethodResult.invalid_input(
            skill_dir, "兼容性测试", "compatibility", "分析", start)
    issues = _source_parse_error_findings(cache)
    py_version = sys.version_info
    tally = _CompatScanTally()
    for entry in cache.valid_entries:
        if not os.path.isfile(entry.path):
            _log.debug("瞬态文件跳过（扫描期间被外部删除）: %s", entry.path)
            continue
        tally.total_files += 1
        _scan_compat_entry(entry, py_version, tally, issues)
    min_version_str = _compat_estimate_min_version(cache)
    _scan_packaging_compat_issues(cache, issues)
    _finalize_compat_results(
        result, issues, py_version, min_version_str, tally)
    return result.finish(start)
def _dotted_has_suffix(dotted: str, suffix: str) -> bool:
    return bool(dotted) and (dotted == suffix
                             or dotted.endswith('.' + suffix))
def _entry_dotted_has_suffix(entry, dotted: str) -> bool:
    return _dotted_has_suffix(entry_module_dotted(entry), dotted)
@dataclass(frozen=True)
class _ModuleResolver:
    by_path: dict[str, Any]
    by_stem: dict[str, list]
    prefixes: frozenset[str]
    def resolve(self, dotted: str | None):
        if dotted is None:
            return None
        if not dotted:
            return self.by_path.get('')
        target = self.by_path.get(dotted)
        if target is not None:
            return target
        for prefix in self._prefix_hits(dotted):
            remainder = dotted[len(prefix) + 1:]
            target = self.by_path.get(remainder) if remainder else self.by_path.get('')
            if target is not None:
                return target
            if remainder:
                hit = self._unique_suffix(remainder)
                if hit is not None:
                    return hit
        return self._unique_suffix(dotted)
    def _prefix_hits(self, dotted: str) -> list[str]:
        hits = [prefix for prefix in self.prefixes
                if dotted == prefix or dotted.startswith(prefix + '.')]
        hits.sort(key=len, reverse=True)
        return hits
    def _unique_suffix(self, dotted: str):
        stem = dotted.rsplit('.', 1)[-1]
        matches = [entry for entry in self.by_stem.get(stem, ())
                   if _entry_dotted_has_suffix(entry, dotted)]
        if not matches:
            matches = [entry for key, entry in self.by_path.items()
                       if _dotted_has_suffix(key, dotted)]
        return matches[0] if len(matches) == 1 else None
def _module_prefixes(by_path, package: str) -> frozenset[str]:
    prefixes = {package} if package else set()
    for dotted in by_path:
        parts = dotted.split('.') if dotted else []
        for end in range(1, len(parts)):
            candidate = '.'.join(parts[:end])
            if candidate not in by_path:
                prefixes.add(candidate)
    return frozenset(prefixes)
def _module_resolver(cache) -> _ModuleResolver:
    by_path, by_stem = module_entry_indexes(cache)
    package = os.path.basename(os.path.normpath(cache.skill_dir))
    return _ModuleResolver(by_path, by_stem, _module_prefixes(by_path, package))
def collect_cross_file_imports(cache) -> dict[str, set[str]]:
    resolver = _module_resolver(cache)
    consumers: dict[str, set[str]] = {}
    for entry in cache.valid_entries:
        _register_from_import_consumers(entry, resolver, consumers)
        _register_module_attribute_consumers(entry, resolver, consumers)
    return consumers
def _resolve_from_import_entry(node: ast.AST, resolver: _ModuleResolver,
                               entry):
    if not isinstance(node, ast.ImportFrom):
        return None
    return resolver.resolve(entry_import_node_dotted(node, entry))
def _star_import_consumed_names(target) -> set[str]:
    tree = getattr(target, 'tree', None)
    if tree is None:
        return set()
    if getattr(target, 'has_all', False):
        exported: set[str] = set()
        collect_all_export_names(tree.body, exported, require_str=True)
        return exported
    return {name for name in module_level_bound_names(
        tree, include_imports=True) if not name.startswith('_')}
def _register_from_import_consumers(entry, resolver: _ModuleResolver,
                                    consumers: dict[str, set[str]]) -> None:
    for node in entry_nodes(entry):
        target = _resolve_from_import_entry(node, resolver, entry)
        if target is None or target is entry:
            continue
        imported = consumers.setdefault(target.rel_path, set())
        for alias in node.names:
            if alias.name == '*':
                imported.update(_star_import_consumed_names(target))
            else:
                imported.add(alias.name)
def _module_import_bindings(entry, resolver: _ModuleResolver,
                            tables: _MutationScopeTables,
                            outer_names: dict[int, set[str]],
                            ) -> list[tuple[str, Any, ast.AST]]:
    bindings: list[tuple[str, Any, ast.AST]] = []
    for node in entry_nodes(entry):
        if isinstance(node, ast.Import):
            for alias in node.names:
                parts = alias.name.split('.')
                module_names = ([alias.name] if alias.asname else
                                ['.'.join(parts[:end])
                                 for end in range(1, len(parts) + 1)])
                bound_name = alias.asname or parts[0]
                scope = _import_binding_scope(
                    bound_name, node, tables, outer_names)
                if scope is None:
                    continue
                for module_name in module_names:
                    target = resolver.resolve(module_name)
                    if target is None or target is entry:
                        continue
                    local_prefix = alias.asname or module_name
                    bindings.append((local_prefix, target, scope))
        elif isinstance(node, ast.ImportFrom):
            base_module = entry_import_node_dotted(node, entry)
            if base_module is None:
                continue
            for alias in node.names:
                if alias.name == '*':
                    continue
                module_name = (f'{base_module}.{alias.name}' if base_module
                               else alias.name)
                target = resolver.resolve(module_name)
                if target is None or target is entry:
                    continue
                bound_name = alias.asname or alias.name
                scope = _import_binding_scope(
                    bound_name, node, tables, outer_names)
                if scope is not None:
                    bindings.append((bound_name, target, scope))
    return bindings
def _register_module_attribute_consumers(
        entry, resolver: _ModuleResolver, consumers: dict[str, set[str]]) -> None:
    tree = getattr(entry, 'tree', None)
    if tree is None:
        return
    tables = _build_mutation_scope_tables(entry)
    outer_names = _outer_scope_declarations(tree)
    bindings = _module_import_bindings(entry, resolver, tables, outer_names)
    if not bindings:
        return
    bindings.sort(key=lambda item: len(item[0]), reverse=True)
    for node in entry_nodes(entry):
        if not isinstance(node, ast.Attribute):
            continue
        dotted = dotted_name(node)
        if not dotted:
            continue
        root_name = dotted.split('.', 1)[0]
        visible_scope = _resolved_name_scope(
            root_name, node, tables, outer_names, tree)
        for prefix, target, binding_scope in bindings:
            if dotted == prefix:
                break
            if not dotted.startswith(prefix + '.'):
                continue
            if visible_scope is not binding_scope:
                continue
            member = dotted[len(prefix) + 1:].split('.', 1)[0]
            if member:
                consumers.setdefault(target.rel_path, set()).add(member)
            break
def _iter_import_binds(node: ast.AST) -> list[tuple[str, int]]:
    is_from = isinstance(node, ast.ImportFrom)
    binds: list[tuple[str, int]] = []
    for alias in node.names:
        if is_from and alias.name == '*':
            continue
        name = import_alias_bound_name(alias, from_import=is_from)
        binds.append((name, getattr(alias, 'lineno', node.lineno) or node.lineno))
    return binds
def _noqa_exempts_line(source_lines: list[str], line: int) -> bool:
    if not 1 <= line <= len(source_lines):
        return False
    if NOQA_ANY_RE.search(source_lines[line - 1]):
        return True
    _prev = line - 1
    return (1 <= _prev <= len(source_lines)
            and source_lines[_prev - 1].strip().startswith('#')
            and bool(NOQA_ANY_RE.search(source_lines[_prev - 1])))
def _is_future_import(node: ast.AST) -> bool:
    return (isinstance(node, ast.ImportFrom) and not node.level
            and node.module == '__future__')
_LEXICAL_SCOPE_CONTAINERS = (*_FUNCTION_SCOPE_CONTAINERS, ast.ClassDef)
def _outer_scope_declarations(tree) -> dict[int, set[str]]:
    declarations: dict[int, set[str]] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, _LEXICAL_SCOPE_CONTAINERS):
            continue
        declarations[id(node)] = {
            name
            for child in iter_own_scope_nodes(node)
            if isinstance(child, ast.Nonlocal)
            for name in child.names
        }
    return declarations
def _import_binding_scope(name, node, tables, outer_names):
    chain = [scope for scope in iter_evaluation_scope_chain(
        node, tables.parents) if not isinstance(scope, _COMP_SCOPE_CONTAINERS)]
    if not chain:
        return None
    scope = chain[0]
    if isinstance(scope, ast.Module):
        return scope
    if isinstance(scope, _FUNCTION_SCOPE_CONTAINERS):
        if name in tables.fn_globals.get(id(scope), ()):
            return chain[-1]
    elif (isinstance(scope, ast.ClassDef)
            and name in tables.class_globals.get(id(scope), ())):
        return chain[-1]
    if name in outer_names.get(id(scope), ()):
        for outer in chain[1:]:
            if not isinstance(outer, _FUNCTION_SCOPE_CONTAINERS):
                continue
            if name in outer_names.get(id(outer), ()):
                continue
            return outer
    return scope
def _comprehension_shadow_scope(name, node, tables):
    cur, prev = node, None
    while cur is not None and id(cur) in tables.parents:
        parent = tables.parents[id(cur)]
        if (isinstance(parent, _COMP_SCOPE_CONTAINERS)
                and _comp_scope_shadows(
                    parent, name, cur, prev, tables.comp_scopes)):
            return parent
        prev, cur = cur, parent
    return None
def _resolved_name_scope(name, node, tables, outer_names, module):
    comp_scope = _comprehension_shadow_scope(name, node, tables)
    outer_chain = (iter_evaluation_scope_chain(comp_scope, tables.parents)
                   if comp_scope is not None else [])
    comp_boundary = outer_chain[0] if outer_chain else None
    nonlocal_lookup = False
    for scope in iter_evaluation_scope_chain(node, tables.parents):
        if isinstance(scope, ast.Module):
            if comp_scope is not None and not nonlocal_lookup:
                return comp_scope
            return module
        if (scope is comp_boundary and comp_scope is not None
                and not nonlocal_lookup):
            return comp_scope
        if isinstance(scope, _FUNCTION_SCOPE_CONTAINERS):
            globals_ = tables.fn_globals.get(id(scope), ())
            bounds = tables.fn_bounds.get(id(scope), ())
        elif isinstance(scope, ast.ClassDef):
            globals_ = tables.class_globals.get(id(scope), ())
            bounds = tables.class_bounds.get(id(scope), ())
        else:
            continue
        if name in globals_:
            return module
        if name in outer_names.get(id(scope), ()):
            nonlocal_lookup = True
            continue
        if name in bounds:
            if (isinstance(scope, ast.ClassDef)
                    and not _class_name_bound_before(tables, scope, name, node)):
                continue
            return scope
    return None
def _collect_import_bind_and_use(
        entry) -> list[
            tuple[ast.AST, set[str], set[str], dict[str, tuple[int, int]]]]:
    tree = getattr(entry, 'tree', None)
    if tree is None:
        return []
    tables = _build_mutation_scope_tables(entry)
    outer_names = _outer_scope_declarations(tree)
    imports: dict[
        int, tuple[ast.AST, set[str], dict[str, tuple[int, int]]]
    ] = {}
    for node in entry_nodes(entry):
        if (not isinstance(node, (ast.Import, ast.ImportFrom))
                or _is_future_import(node)):
            continue
        for name, alias_line in _iter_import_binds(node):
            scope = _import_binding_scope(name, node, tables, outer_names)
            if scope is None:
                continue
            _scope, names, bind_lines = imports.setdefault(
                id(scope), (scope, set(), {}))
            names.add(name)
            bind_lines.setdefault(name, (node.lineno, alias_line or node.lineno))
    used: dict[int, set[str]] = defaultdict(set)
    for node in entry_nodes(entry):
        if not isinstance(node, ast.Name) or not isinstance(node.ctx, ast.Load):
            continue
        scope = _resolved_name_scope(
            node.id, node, tables, outer_names, tree)
        record = imports.get(id(scope)) if scope is not None else None
        if record is not None and node.id in record[1]:
            used[id(scope)].add(node.id)
    for node in entry_nodes(entry):
        if isinstance(node, ast.arg):
            annotation = node.annotation
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            annotation = node.returns
        elif isinstance(node, ast.AnnAssign):
            annotation = node.annotation
        else:
            continue
        if annotation is None:
            continue
        annotation_refs: set[str] = set()
        _collect_annotation_refs(annotation, annotation_refs)
        for name in annotation_refs:
            scope = _resolved_name_scope(
                name, annotation, tables, outer_names, tree)
            record = imports.get(id(scope)) if scope is not None else None
            if record is not None and name in record[1]:
                used[id(scope)].add(name)
    return [(scope, names, used[id(scope)], bind_lines)
            for scope, names, bind_lines in imports.values()]
def _collect_export_and_getattr(tree, imported_names: set[str]) -> set[str]:
    if tree is None:
        return set()
    all_exported: set[str] = set()
    collect_all_export_names(tree.body, all_exported, require_str=True)
    _getattr_node = _module_getattr_node(tree)
    if _getattr_node is None:
        return all_exported
    return all_exported | (set(imported_names) & _getattr_lazy_names(_getattr_node))
def _is_module_dunder(name: str) -> bool:
    return len(name) > 4 and name.startswith('__') and name.endswith('__')
def check_unused_imports(entry, cross_file_imported: set[str]) -> list[dict]:
    findings = []
    rel_path = entry.rel_path
    scope_bindings = _collect_import_bind_and_use(entry)
    module_imported_names = {
        name
        for scope, imported, _used, _bind_lines in scope_bindings
        if scope is entry.tree
        for name in imported
    }
    all_exported = _collect_export_and_getattr(
        entry.tree, module_imported_names)
    _is_init = is_package_init_path(rel_path)
    _reexport_names = all_exported | cross_file_imported
    unused: list[tuple[str, int]] = []
    source_lines = entry.source.splitlines()
    for scope, imported, used_names, bind_lines in scope_bindings:
        reexport_names = (_reexport_names if scope is entry.tree else set())
        if _is_init and scope is entry.tree:
            reexport_names = reexport_names | imported
        for name in imported - used_names - reexport_names:
            if _is_module_dunder(name):
                continue
            stmt_line, alias_line = bind_lines[name]
            if (_noqa_exempts_line(source_lines, stmt_line)
                    or _noqa_exempts_line(source_lines, alias_line)):
                continue
            unused.append((name, alias_line))
    for name, line in sorted(unused):
        findings.append({
            "file": rel_path, "line": line,
            "type": "unused_import", "name": name,
            "severity": "low", "message": f"未使用的导入: {name}",
        })
    return findings
def _entry_defined_names(entry) -> set[str]:
    names = {item.get('name')
             for item in (*entry.functions, *entry.classes)
             if not item.get('scope')}
    return {name for name in names if isinstance(name, str)}
def _entry_module_used_names(entry) -> set[str]:
    tree = getattr(entry, 'tree', None)
    if tree is None:
        return set()
    tables = _build_mutation_scope_tables(entry)
    outer_names = _outer_scope_declarations(tree)
    used: set[str] = set()
    for node in entry_nodes(entry):
        if not isinstance(node, ast.Name) or not isinstance(node.ctx, ast.Load):
            continue
        scope = _resolved_name_scope(
            node.id, node, tables, outer_names, tree)
        if scope is tree:
            used.add(node.id)
    return used
_FRAMEWORK_PREFIXES = ('test_', 'visit_', 'pytest_', 'Test')
_PROTOCOL_HOOK_NAMES = frozenset({WIRING_DECLARATION_ATTR})
_CLASS_PROTOCOL_METHODS = _TEST_LIFECYCLE_NAMES | frozenset(
    {'generic_visit'})
def _collect_protocol_exempt_names(cache) -> set[str]:
    class_methods: set[str] = set()
    fixtures: set[str] = set()
    for entry in cache.valid_entries:
        tree = getattr(entry, 'tree', None)
        if tree is None:
            continue
        for node in walk_nodes(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            if _is_test_fixture(node):
                fixtures.add(node.name)
        for cls in (node for node in walk_nodes(tree)
                    if isinstance(node, ast.ClassDef)):
            for item in cls.body:
                if (isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
                        and item.name in _CLASS_PROTOCOL_METHODS):
                    class_methods.add(item.name)
    return fixtures | class_methods
def _dynamic_reference_name(node) -> str | None:
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in ('getattr', 'hasattr', 'delattr')):
        return None
    if len(node.args) < 2:
        return None
    name_arg = node.args[1]
    if isinstance(name_arg, ast.Constant) and isinstance(name_arg.value, str):
        return name_arg.value
    return None
def _collect_dynamic_attribute_references(cache) -> set[str]:
    referenced: set[str] = set()
    for entry in cache.valid_entries:
        for node in entry_nodes(entry):
            dynamic_name = _dynamic_reference_name(node)
            if dynamic_name is not None:
                referenced.add(dynamic_name)
    return referenced
def _lazy_dict_export_names(targets, value) -> list[str]:
    if not isinstance(value, ast.Dict):
        return []
    names: list[str] = []
    for target in targets:
        if _is_lazy_import_target(target):
            names.extend(_dict_str_keys(value))
    return names
def _is_lazy_import_target(target: ast.AST) -> bool:
    return isinstance(target, ast.Name) and 'LAZY' in target.id.upper()
def _dict_str_keys(dict_node: ast.Dict) -> list[str]:
    return [key.value for key in dict_node.keys
            if isinstance(key, ast.Constant) and isinstance(key.value, str)]
def _getattr_lazy_names(node: ast.FunctionDef) -> set[str]:
    return {inner.value for inner in walk_nodes(node)
            if isinstance(inner, ast.Constant) and isinstance(inner.value, str)}
def _collect_lazy_exported(cache) -> set[str]:
    lazy_exported: set[str] = set()
    for entry in cache.valid_entries:
        if entry.tree is not None:
            lazy_exported |= _entry_lazy_exported(entry)
    return lazy_exported
def _entry_lazy_exported(entry) -> set[str]:
    if entry.tree is None:
        return set()
    names: set[str] = set()
    _getattr_node = _module_getattr_node(entry.tree)
    if _getattr_node is not None:
        names |= _getattr_lazy_names(_getattr_node)
    for node in iter_module_level_stmts(entry.tree.body):
        parts = assign_targets_value(node)
        if parts is not None:
            names.update(_lazy_dict_export_names(*parts))
    return names
def _is_reportable_unused_public(name: str) -> bool:
    return (not name.startswith('_')
            and not any(name.startswith(prefix)
                        for prefix in _FRAMEWORK_PREFIXES))
def _entry_definition_lines(entry) -> dict[str, int]:
    lines: dict[str, int] = {}
    for item in (*entry.functions, *entry.classes):
        name = item.get('name')
        if name:
            lines.setdefault(name, item.get('line', 0) or 0)
    return lines
def check_unused_definitions(
        cache,
        external_consumers: dict[str, set[str]] | None = None,
) -> list[dict]:
    findings = []
    entries = list(cache.valid_entries)
    defined_by_entry = [(entry, _entry_defined_names(entry)) for entry in entries]
    if not any(names for _entry, names in defined_by_entry):
        return findings
    dynamic_referenced = _collect_dynamic_attribute_references(cache)
    lazy_exported = _collect_lazy_exported(cache)
    protocol_exempt = _collect_protocol_exempt_names(cache)
    if external_consumers is None:
        external_consumers = collect_cross_file_imports(cache)
    globally_exempt = (dynamic_referenced | lazy_exported | protocol_exempt
                       | _PROTOCOL_HOOK_NAMES)
    for entry, defined_names in defined_by_entry:
        if not defined_names:
            continue
        exported_names: set[str] = set()
        if entry.tree is not None:
            collect_all_export_names(entry.tree.body, exported_names)
        used_names = (_entry_module_used_names(entry)
                      | external_consumers.get(entry.rel_path, set()))
        unused_public = (defined_names - used_names - exported_names
                         - globally_exempt)
        reportable = {name for name in unused_public
                      if _is_reportable_unused_public(name)}
        definition_lines = _entry_definition_lines(entry)
        for name in sorted(reportable):
            findings.append({
                "file": entry.rel_path,
                "line": definition_lines.get(name, 0),
                "type": "unused_definition", "severity": "low",
                "name": name,
                "message": f"公开函数/类 {name} 在整个项目中未被调用",
            })
    findings.sort(key=lambda item: (item["name"], item["file"], item["line"]))
    return findings

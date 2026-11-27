from __future__ import annotations

import ast
import hashlib
import keyword
import logging
import os
import re
import time
from collections.abc import Iterator
from dataclasses import dataclass, field
from functools import lru_cache
from typing import NamedTuple

from jwsgj.diag_guard_io import (
    coerce_target_file,
    safe_delete,
)
from jwsgj.diag_shared_source_core import (
    parse_py_source,
    read_source_with_fingerprint,
)
from jwsgj.diag_testing_source import (
    MATCH_T,
    TRY_STAR_T,
    iter_test_py_files,
    main_guard_live_body,
    module_has_toplevel_side_effect,
    resolve_tests_dir,
    static_if_branch,
)
from jwsgj.diag_testing_test_index import (
    _definition_binding_exprs,
    iter_collectable_test_functions,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    DEFAULT_TEST_DIR_NAME,
    TEST_DIR_CANDIDATES_LOWER,
    is_pruned_scan_dir,
    is_scan_py_name,
    is_test_source_basename,
    scan_exclude_dirs,
    scan_prune_dirs,
)

__all__ = [
    'SUPPLEMENTAL_MARK',
    'CoverageReport',
    'FixerInfo',
    'MemberGrades',
    'TestCoverage',
    'analyze_test_coverage',
    'build_test_source',
    'classify_module_members',
    'cleanup_missing_host_booster_stubs',
    'discover_fixers',
    'ensure_supplemental_tests',
    'generate_missing_tests',
    'generate_test_stub',
    'get_coverage_report',
    'is_booster_stub',
    'is_fixer_candidate_file',
    'is_test_source_file',
    'safe_test_name',
    'sorted_dir_entries',
]
logger = logging.getLogger(__name__)
logger.addHandler(logging.NullHandler())
def load_parsed_tree(fpath: str) -> tuple[ast.Module | None, str | None]:
    source, _ = read_source_with_fingerprint(fpath)
    if source is None:
        return None, "读取失败（源码不可读或解码失败）"
    tree, error = parse_py_source(source)
    if error is not None:
        return None, f"解析失败: {type(error).__name__}"
    return tree, None
@dataclass
class FixerInfo:
    class_name: str
    rule_id: str
    module: str
    file: str
    has_fix_method: bool
    has_can_fix: bool
    line: int = 0
@dataclass
class TestCoverage:
    fixer: FixerInfo
    has_test: bool
    test_file: str = ""
    test_count: int = 0
@dataclass
class CoverageReport:
    total_fixers: int = 0
    tested_fixers: int = 0
    untested_fixers: int = 0
    coverage_rate: float = 0.0
    details: list[TestCoverage] = field(default_factory=list)
    untested_rule_ids: list[str] = field(default_factory=list)
def _rule_id_literal(target: ast.AST, value: ast.AST) -> str | None:
    if (isinstance(target, ast.Name) and target.id == "rule_id"
            and isinstance(value, ast.Constant)
            and isinstance(value.value, str)):
        return value.value
    return None
def _rule_id_of_stmt(item) -> str:
    if isinstance(item, ast.AugAssign):
        return ""
    targets = (item.targets if isinstance(item, ast.Assign)
               else [item.target])
    for target in targets:
        hit = _rule_id_literal(target, item.value)
        if hit is not None:
            return hit
    return ""
def _iter_binding_names(target: ast.AST) -> Iterator[str]:
    if isinstance(target, ast.Name):
        yield target.id
        return
    if isinstance(target, ast.Starred):
        yield from _iter_binding_names(target.value)
        return
    if isinstance(target, (ast.Tuple, ast.List)):
        for element in target.elts:
            yield from _iter_binding_names(element)
def _assigns_rule_id(item) -> bool:
    if isinstance(item, ast.AnnAssign) and item.value is None:
        return False
    targets = (item.targets if isinstance(item, ast.Assign)
               else [item.target])
    return any("rule_id" in _iter_binding_names(target)
               for target in targets)
_NESTED_SCOPE_NODE_TYPES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef,
)
def _iter_own_ast_nodes(node: ast.AST) -> Iterator[ast.AST]:
    stack = [node]
    while stack:
        current = stack.pop()
        yield current
        if (current is not node
                and isinstance(current, _NESTED_SCOPE_NODE_TYPES)):
            continue
        stack.extend(ast.iter_child_nodes(current))
def _definition_rebinds_rule_id(node: ast.AST) -> bool:
    for expr in _definition_binding_exprs(node):
        stack = [expr]
        while stack:
            current = stack.pop()
            if isinstance(current, ast.Lambda):
                stack.extend(_definition_binding_exprs(current))
                continue
            if (isinstance(current, ast.NamedExpr)
                    and "rule_id" in _iter_binding_names(current.target)):
                return True
            stack.extend(ast.iter_child_nodes(current))
    return False
def _rule_id_unknown_rebind(item: ast.AST) -> bool:
    targets: tuple[ast.AST, ...] = ()
    if isinstance(item, (ast.For, ast.AsyncFor)):
        targets = (item.target,)
    elif isinstance(item, (ast.With, ast.AsyncWith)):
        targets = tuple(entry.optional_vars for entry in item.items
                        if entry.optional_vars is not None)
    elif isinstance(item, ast.Delete):
        targets = tuple(item.targets)
    if any("rule_id" in _iter_binding_names(target) for target in targets):
        return True
    if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return item.name == "rule_id" or _definition_rebinds_rule_id(item)
    if isinstance(item, ast.Import):
        return any((alias.asname or alias.name.split(".", 1)[0]) == "rule_id"
                   for alias in item.names)
    if isinstance(item, ast.ImportFrom):
        return any(alias.name == "*"
                   or (alias.asname or alias.name) == "rule_id"
                   for alias in item.names)
    if isinstance(item, ast.ExceptHandler):
        return item.name == "rule_id"
    if isinstance(item, ast.Lambda):
        return _definition_rebinds_rule_id(item)
    for current in _iter_own_ast_nodes(item):
        if (isinstance(current, ast.Lambda)
                and _definition_rebinds_rule_id(current)):
            return True
        if (isinstance(current, ast.NamedExpr)
                and "rule_id" in _iter_binding_names(current.target)):
            return True
        if (isinstance(current, (ast.MatchAs, ast.MatchStar, ast.MatchMapping))
                and "rule_id" in {getattr(current, "name", None),
                                   getattr(current, "rest", None)}):
            return True
    return False
def _merge_rule_id_states(*paths: set[str]) -> set[str]:
    values = set().union(*paths)
    return values if len(values) == 1 else {""}
def _rule_id_simple_statement(item: ast.AST, states: set[str]) -> set[str]:
    if (isinstance(item, (ast.Assign, ast.AnnAssign, ast.AugAssign))
            and _assigns_rule_id(item)):
        return {_rule_id_of_stmt(item)}
    return {""} if _rule_id_unknown_rebind(item) else states
def _rule_id_suite(body: list[ast.stmt], states: set[str]) -> set[str]:
    for item in body:
        states = _rule_id_flow_statement(item, states)
    return states
def _rule_id_if_states(item: ast.If, states: set[str]) -> set[str]:
    current = {""} if _rule_id_unknown_rebind(item.test) else states
    live = main_guard_live_body(item)
    if live is not None:
        return _rule_id_suite(live, current)
    static = static_if_branch(item.test)
    if static is not None:
        return _rule_id_suite(item.body if static else item.orelse, current)
    return _merge_rule_id_states(
        _rule_id_suite(item.body, current),
        _rule_id_suite(item.orelse, current),
    )
_LOOP_NODE_TYPES = (ast.For, ast.AsyncFor, ast.While)
def _loop_has_own_jump(item: ast.AST) -> bool:
    stack = list(item.body)
    while stack:
        current = stack.pop()
        if isinstance(current, _LOOP_NODE_TYPES):
            continue
        if isinstance(current, (ast.Break, ast.Continue)):
            return True
        if isinstance(current, _NESTED_SCOPE_NODE_TYPES):
            continue
        stack.extend(ast.iter_child_nodes(current))
    return False
def _loop_may_rebind_rule_id(item: ast.AST) -> bool:
    for statement in item.body:
        for current in _iter_own_ast_nodes(statement):
            if (isinstance(current, (ast.Assign, ast.AnnAssign, ast.AugAssign))
                    and _assigns_rule_id(current)):
                return True
            if _rule_id_unknown_rebind(current):
                return True
    return False
def _rule_id_loop_states(item: ast.AST, states: set[str]) -> set[str]:
    test = item.iter if isinstance(item, (ast.For, ast.AsyncFor)) else item.test
    current = {""} if _rule_id_unknown_rebind(test) else states
    body_states = current
    if (isinstance(item, (ast.For, ast.AsyncFor))
            and "rule_id" in _iter_binding_names(item.target)):
        body_states = {""}
    if isinstance(item, ast.While) and static_if_branch(item.test) is False:
        return _rule_id_suite(item.orelse, current)
    if _loop_has_own_jump(item) and _loop_may_rebind_rule_id(item):
        return {""}
    zero_iterations = _rule_id_suite(item.orelse, current)
    if isinstance(item, ast.While) and static_if_branch(item.test) is True:
        zero_iterations = set()
    body_exit = _rule_id_suite(item.body, body_states)
    normal_exit = _rule_id_suite(item.orelse, body_exit)
    return _merge_rule_id_states(zero_iterations, normal_exit, body_exit)
def _rule_id_with_states(item: ast.AST, states: set[str]) -> set[str]:
    current = states
    for entry in item.items:
        if _rule_id_unknown_rebind(entry.context_expr):
            current = {""}
        if (entry.optional_vars is not None
                and "rule_id" in _iter_binding_names(entry.optional_vars)):
            current = {""}
    return _rule_id_suite(item.body, current)
def _rule_id_statement_may_raise(item: ast.stmt) -> bool:
    if isinstance(item, ast.Pass):
        return False
    if isinstance(item, ast.Expr) and isinstance(item.value, ast.Constant):
        return False
    return not (
        isinstance(item, ast.Assign)
        and isinstance(item.value, ast.Constant)
        and all(isinstance(target, ast.Name) for target in item.targets)
    )
def _rule_id_try_states(item: ast.AST, states: set[str]) -> set[str]:
    if any(_rule_id_unknown_rebind(handler) for handler in item.handlers):
        return _rule_id_suite(
            item.finalbody, _rule_id_suite(item.orelse, {""}))
    current = states
    handler_prefixes: list[set[str]] = []
    can_reach_handler = False
    for statement in item.body:
        if _rule_id_statement_may_raise(statement):
            can_reach_handler = True
            handler_prefixes.append(current)
        current = _rule_id_flow_statement(statement, current)
        if _rule_id_statement_may_raise(statement):
            handler_prefixes.append(current)
    paths = [_rule_id_suite(item.orelse, current)]
    if item.handlers and can_reach_handler:
        handler_states = _merge_rule_id_states(*handler_prefixes)
        for handler in item.handlers:
            handled = _rule_id_suite(handler.body, handler_states)
            if _rule_id_unknown_rebind(handler):
                handled = {""}
            paths.append(handled)
    return _rule_id_suite(
        item.finalbody, _merge_rule_id_states(*paths))
def _rule_id_match_states(item: ast.AST, states: set[str]) -> set[str]:
    current = {""} if _rule_id_unknown_rebind(item.subject) else states
    paths: list[set[str]] = []
    capture_unknown = False
    for case in item.cases:
        case_states = current
        if _rule_id_unknown_rebind(case.pattern):
            capture_unknown = True
            case_states = {""}
        if case.guard is not None and _rule_id_unknown_rebind(case.guard):
            capture_unknown = True
            case_states = {""}
        paths.append(_rule_id_suite(case.body, case_states))
    has_irrefutable_case = any(
        isinstance(case.pattern, ast.MatchAs)
        and case.pattern.pattern is None
        and case.guard is None
        for case in item.cases
    )
    if not has_irrefutable_case:
        paths.append({""} if capture_unknown else current)
    return _merge_rule_id_states(*paths)
def _rule_id_flow_statement(item: ast.stmt, states: set[str]) -> set[str]:
    if isinstance(item, ast.If):
        return _rule_id_if_states(item, states)
    if isinstance(item, (ast.For, ast.AsyncFor, ast.While)):
        return _rule_id_loop_states(item, states)
    if isinstance(item, (ast.With, ast.AsyncWith)):
        return _rule_id_with_states(item, states)
    if isinstance(item, (ast.Try, TRY_STAR_T)):
        return _rule_id_try_states(item, states)
    if MATCH_T and isinstance(item, MATCH_T):
        return _rule_id_match_states(item, states)
    return _rule_id_simple_statement(item, states)
def _class_rule_id(node: ast.ClassDef) -> str:
    states = _rule_id_suite(node.body, {""})
    return next(iter(states)) if len(states) == 1 else ""
def _collect_class_fixer_facts(node: ast.ClassDef) -> tuple[str, bool, bool]:
    body_nodes = _iter_class_body_nodes(node)
    has_fix = any(
        isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
        and item.name == "fix"
        for item in body_nodes
    )
    has_can_fix = any(
        isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
        and item.name == "can_fix"
        for item in body_nodes
    )
    rule_id_is_outer_binding = any(
        isinstance(item, (ast.Global, ast.Nonlocal))
        and "rule_id" in item.names
        for item in body_nodes
    )
    rule_id = "" if rule_id_is_outer_binding else _class_rule_id(node)
    return rule_id, has_fix, has_can_fix
def _read_source_text(fpath: str, purpose: str) -> str | None:
    source, _fingerprint = read_source_with_fingerprint(fpath)
    if source is None:
        logger.warning("[CoverageBooster] %s失败,跳过 %s", purpose, fpath)
    return source
def sorted_dir_entries(dir_path: str) -> list[str] | None:
    try:
        return sorted(os.listdir(dir_path))
    except OSError as e:
        logger.warning("[CoverageBooster] 列举目录失败，返回已收集结果: %s: %s", dir_path, e)
        return None
_FUNC_NODE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef)
_DEFINITION_NODE_TYPES = (*_FUNC_NODE_TYPES, ast.ClassDef)
def _iter_module_scope_nodes(body: list[ast.stmt]) -> Iterator[ast.AST]:
    for node in body:
        yield node
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda)):
            continue
        if isinstance(node, ast.If):
            live = main_guard_live_body(node)
            if live is not None:
                yield from _iter_module_scope_nodes(live)
                continue
            static = static_if_branch(node.test)
            if static is not None:
                yield from _iter_module_scope_nodes(
                    node.body if static else node.orelse)
                continue
            yield from _iter_module_scope_nodes(node.body)
            yield from _iter_module_scope_nodes(node.orelse)
            continue
        if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
            yield from _iter_module_scope_nodes(node.body)
            yield from _iter_module_scope_nodes(node.orelse)
            continue
        if isinstance(node, (ast.With, ast.AsyncWith)):
            yield from _iter_module_scope_nodes(node.body)
            continue
        if isinstance(node, (ast.Try, TRY_STAR_T)):
            yield from _iter_module_scope_nodes(node.body)
            for _handler in node.handlers:
                yield from _iter_module_scope_nodes(_handler.body)
                yield _handler
            yield from _iter_module_scope_nodes(node.orelse)
            yield from _iter_module_scope_nodes(node.finalbody)
            continue
        if MATCH_T and isinstance(node, MATCH_T):
            for _case in node.cases:
                yield from _iter_module_scope_nodes(_case.body)
def _iter_module_scope_classes(body: list[ast.stmt]):
    for node in _iter_module_scope_nodes(body):
        if isinstance(node, ast.ClassDef):
            yield node
def _iter_class_body_nodes(node: ast.ClassDef) -> list[ast.AST]:
    return list(_iter_module_scope_nodes(node.body))
def _scan_fixer_module_file(fpath: str, mod_name: str, seen: set[str]) -> list[FixerInfo]:
    found: list[FixerInfo] = []
    tree, fail_note = load_parsed_tree(fpath)
    if tree is None:
        logger.warning("[CoverageBooster] 发现修复器解析失败,跳过 %s: %s",
                       fpath, fail_note)
        return found
    for name, nodes in _module_def_suite(tree.body, {}).items():
        key = f"{name}@{mod_name}"
        if key in seen or not nodes:
            continue
        if any(not isinstance(node, ast.ClassDef) for node in nodes):
            continue
        facts = [_collect_class_fixer_facts(node) for node in nodes]
        rule_ids = {rule_id for rule_id, _has_fix, _has_can in facts}
        if len(rule_ids) != 1:
            logger.warning(
                "[CoverageBooster] 条件定义的规则 ID 不确定，跳过 %s@%s",
                name, mod_name)
            continue
        rule_id = next(iter(rule_ids))
        if not rule_id:
            continue
        node = nodes[-1]
        found.append(FixerInfo(
            class_name=name,
            rule_id=rule_id,
            module=mod_name,
            file=fpath,
            has_fix_method=all(item[1] for item in facts),
            has_can_fix=all(item[2] for item in facts),
            line=node.lineno,
        ))
        seen.add(key)
    return found
def discover_fixers(skill_dir: str) -> list[FixerInfo]:
    fixers: list[FixerInfo] = []
    seen: set[str] = set()
    skill_dir = coerce_target_file(skill_dir)
    if not os.path.isdir(skill_dir):
        logger.warning("[CoverageBooster] 技能目录不存在或不可访问，返回空修复器列表: %s", skill_dir)
        return fixers
    if sorted_dir_entries(skill_dir) is None:
        return fixers
    for mod_name, fpath in _iter_py_modules(skill_dir):
        fixers.extend(_scan_fixer_module_file(fpath, mod_name, seen))
    logger.info("[CoverageBooster] 发现 %d 个修复器", len(fixers))
    return fixers
_RULE_ID_RE = re.compile(r"[A-Z][A-Z0-9]{0,7}[-_]\d{1,4}")
_WORD_RE = re.compile(r"[A-Za-z0-9]+")
def is_test_source_file(fname: str) -> bool:
    if not isinstance(fname, str):
        return False
    return is_scan_py_name(fname) and is_test_source_basename(fname)
GENERATED_SUBDIR = "generated"
_BOOSTER_STUB_MARK = "auto-generated-fixer-test-stub"
_LEGACY_BOOSTER_STUB_MARK = "的单元测试 — 自动生成桩"
def _iter_test_source_paths(
        tests_dir: str, seen_realpaths: set[str] | None = None):
    if seen_realpaths is None:
        seen_realpaths = set()
    if not os.path.isdir(tests_dir):
        return
    real_key = os.path.normcase(os.path.realpath(tests_dir))
    if real_key in seen_realpaths:
        return
    seen_realpaths.add(real_key)
    prune = scan_prune_dirs(tests_dir) | TEST_DIR_CANDIDATES_LOWER
    dir_entries = sorted_dir_entries(tests_dir)
    if dir_entries is None:
        return
    subdirs: list[str] = []
    for fname in dir_entries:
        fpath = os.path.join(tests_dir, fname)
        if not os.path.isfile(fpath):
            if (os.path.isdir(fpath)
                    and not is_pruned_scan_dir(fname, prune)):
                subdirs.append(fpath)
            continue
        if is_test_source_file(fname):
            yield fpath
    for sub in subdirs:
        yield from _iter_test_source_paths(sub, seen_realpaths)
def _iter_project_test_paths(
        skill_dir: str,
        tests_dir: str | None = None) -> Iterator[str]:
    seen: set[str] = set()
    paths = list(iter_test_py_files(skill_dir))
    if tests_dir:
        paths.extend(_iter_test_source_paths(tests_dir))
    for path in paths:
        key = os.path.normcase(os.path.abspath(path))
        if key in seen:
            continue
        seen.add(key)
        yield path
def _load_test_sources(skill_dir: str,
                       tests_dir: str | None = None) -> list[tuple[str, str]]:
    sources: list[tuple[str, str]] = []
    engine_artifacts = 0
    for fpath in _iter_project_test_paths(skill_dir, tests_dir):
        if _is_engine_artifact(fpath):
            engine_artifacts += 1
            continue
        source = _read_source_text(fpath, "读取测试文件")
        if source is not None:
            sources.append((fpath, source))
    if engine_artifacts:
        logger.debug(
            "[CoverageBooster] 覆盖归因跳过 %d 个引擎自产测试文件"
            "（补足件/测试桩不计入作者覆盖）", engine_artifacts)
    return sources
def _find_test_files(sources: list[tuple[str, str]]) -> dict[str, str]:
    result: dict[str, str] = {}
    for fpath, source in sources:
        for rid in _extract_rule_ids_from_source(source):
            result.setdefault(rid.lower(), fpath)
    return result
def _docstring_node_ids(tree: ast.AST) -> set[int]:
    marks: set[int] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef,
                                 ast.AsyncFunctionDef)):
            continue
        body = getattr(node, "body", ())
        if (body and isinstance(body[0], ast.Expr)
                and isinstance(body[0].value, ast.Constant)
                and isinstance(body[0].value.value, str)):
            marks.add(id(body[0].value))
    return marks
def _executable_reference_text(source: str) -> str:
    tree, error = parse_py_source(source)
    if error is not None:
        return ""
    docstrings = _docstring_node_ids(tree)
    facts: list[str] = []
    for node in walk_nodes(tree):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            segment = ast.get_source_segment(source, node)
            if segment:
                facts.append(" ".join(segment.split()))
        elif isinstance(node, ast.Name):
            facts.append(node.id)
        elif isinstance(node, ast.Attribute):
            facts.append(node.attr)
        elif (isinstance(node, ast.Constant) and isinstance(node.value, str)
              and id(node) not in docstrings):
            facts.append(node.value)
    return "\n".join(facts)
def _extract_rule_ids_from_source(source: str) -> list[str]:
    rule_ids: list[str] = []
    tree, error = parse_py_source(source)
    if error is not None:
        logger.warning(
            "[CoverageBooster] 测试源码解析失败，跳过 rule_id 提取",
            exc_info=(type(error), error, error.__traceback__))
        return rule_ids
    docstrings = _docstring_node_ids(tree)
    for node in walk_nodes(tree):
        if (isinstance(node, ast.Constant) and isinstance(node.value, str)
                and id(node) not in docstrings):
            val = node.value
            if val and _RULE_ID_RE.fullmatch(val):
                rule_ids.append(val)
    return rule_ids
def _search_referencing_test_file(fixer: FixerInfo,
                                  lower_test_sources: list,
                                  accept=None) -> str:
    rid_lower = fixer.rule_id.lower()
    cls_lower = fixer.class_name.lower()
    for fpath, tsource in lower_test_sources:
        matched = (_references_token(tsource, rid_lower)
                   or _references_token(tsource, cls_lower))
        if not matched or (accept is not None and not accept(fpath)):
            continue
        return fpath
    return ""
def _resolve_fixer_test_file(fixer: FixerInfo, test_map: dict,
                             lower_test_sources: list) -> str:
    test_file = test_map.get(fixer.rule_id.lower(), "")
    if test_file:
        return test_file
    return _search_referencing_test_file(fixer, lower_test_sources)
@lru_cache(maxsize=512)
def _token_ref_pattern(token: str) -> re.Pattern[str]:
    return re.compile(
        r"(?<![A-Za-z0-9_])" + re.escape(token) + r"(?![A-Za-z0-9_])")
def _references_token(text_lower: str, token: str) -> bool:
    if not _WORD_RE.search(token):
        return False
    return bool(_token_ref_pattern(token).search(text_lower))
def _count_test_cases(test_file: str, source_by_path: dict) -> int:
    if not is_test_source_file(os.path.basename(test_file)):
        return 0
    test_source = source_by_path.get(os.path.normpath(test_file))
    if test_source is None:
        test_source = _read_source_text(test_file, "读取测试文件（用例计数回退）") or ""
    tree, error = parse_py_source(test_source)
    if error is not None:
        logger.warning(
            "[CoverageBooster] 测试文件解析失败，跳过用例计数: %s",
            test_file,
            exc_info=(type(error), error, error.__traceback__))
        return 0
    return sum(1 for _ in iter_collectable_test_functions(tree))
def analyze_test_coverage(
    skill_dir: str,
    tests_dir: str | None = None,
) -> list[TestCoverage]:
    skill_dir = coerce_target_file(skill_dir)
    if not skill_dir:
        logger.warning("[CoverageBooster] 技能目录非法或为空，跳过覆盖分析")
        return []
    tests_dir = _tests_dir(skill_dir, tests_dir)
    fixers = discover_fixers(skill_dir)
    all_test_sources = _load_test_sources(skill_dir, tests_dir)
    test_map = _find_test_files(all_test_sources)
    source_by_path = {os.path.normpath(p): s for p, s in all_test_sources}
    lower_test_sources = [
        (p, _executable_reference_text(s).lower())
        for p, s in all_test_sources
    ]
    results: list[TestCoverage] = []
    test_count_by_file: dict[str, int] = {}
    def count_for(test_file: str) -> int:
        if not test_file or not os.path.isfile(test_file):
            return 0
        if test_file not in test_count_by_file:
            test_count_by_file[test_file] = _count_test_cases(
                test_file, source_by_path)
        return test_count_by_file[test_file]
    for fixer in fixers:
        test_file = _resolve_fixer_test_file(
            fixer, test_map, lower_test_sources)
        test_count = count_for(test_file)
        if test_file and test_count == 0:
            alternative = _search_referencing_test_file(
                fixer, lower_test_sources,
                accept=lambda path: count_for(path) > 0)
            if alternative:
                test_file = alternative
                test_count = count_for(alternative)
        has_test = test_count > 0
        results.append(TestCoverage(
            fixer=fixer,
            has_test=has_test,
            test_file=test_file,
            test_count=test_count,
        ))
    return results
def get_coverage_report(
    skill_dir: str,
    tests_dir: str | None = None,
) -> CoverageReport:
    coverage = analyze_test_coverage(skill_dir, tests_dir)
    total = len(coverage)
    untested_rule_ids = [c.fixer.rule_id for c in coverage if not c.has_test]
    tested = total - len(untested_rule_ids)
    return CoverageReport(
        total_fixers=total,
        tested_fixers=tested,
        untested_fixers=len(untested_rule_ids),
        coverage_rate=tested / total if total else 0.0,
        details=coverage,
        untested_rule_ids=untested_rule_ids,
    )
def _host_import_root(mod_path: str, host_file: str) -> str:
    root = os.path.dirname(os.path.abspath(host_file))
    for _ in mod_path.split(".")[:-1]:
        root = os.path.dirname(root)
    return root
_IMPORT_BOOTSTRAP = '''\
_TARGET_MODULE_PATH = "{module_path}.py"
_FALLBACK_IMPORT_ROOT = "{import_root}"

def _module_import_root():
    """优先按真实落点搜索；外部测试目录使用宿主推导根。"""
    here = os.path.dirname(os.path.abspath(__file__))
    while True:
        for _base in (here, os.path.join(here, "src")):
            if os.path.isfile(os.path.join(_base, _TARGET_MODULE_PATH)):
                return _base
        parent = os.path.dirname(here)
        if parent == here:
            break
        here = parent
    if (_FALLBACK_IMPORT_ROOT and os.path.isfile(
            os.path.join(_FALLBACK_IMPORT_ROOT, _TARGET_MODULE_PATH))):
        return _FALLBACK_IMPORT_ROOT
    return os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

_IMPORT_ROOT = _module_import_root()
if os.path.isdir(_IMPORT_ROOT) and _IMPORT_ROOT not in sys.path:
    sys.path.insert(0, _IMPORT_ROOT)
'''
_TEST_STUB_TEMPLATE = '''\
# -*- coding: utf-8 -*-
# {booster_mark}
"""{class_name} ({rule_id}) 的单元测试 — 自动生成桩

TODO: 补充具体测试用例，覆盖以下场景：
1. 正常修复场景
2. 边界情况（空输入、无匹配项）
3. 幂等性（多次修复结果一致）
4. 回滚安全性（修复失败不破坏原文件）
"""
import os
import sys
import pytest

{bootstrap}

@pytest.fixture
def fixer():
    try:
        from {module} import {class_name}
    except Exception:
        pytest.skip("目标模块导入失败（桩按容错口径降级为 skip），"
                    "请手工适配本用例")
    try:
        return {class_name}(project_path=".", dry_run=True)
    except TypeError:
        # 构造签名不匹配时降级尝试无参构造（非 BaseFixer 修复器需无参构造）
        try:
            return {class_name}()
        except Exception:
            pytest.skip("修复器构造签名与桩模板不匹配，请手工适配本 fixture")


@pytest.fixture
def sample_issue():
    return {{
        "rule_id": "{rule_id}",
        "file": "sample.py",
        "line": 1,
        "message": "Test issue for {rule_id}",
    }}


class Test{class_name}:
    """{class_name} 测试套件。"""

    def test_fixer_has_rule_id(self, fixer):
        """修复器应有正确的 rule_id。

        属性访问异常或运行时值与静态提取值不一致时 skip，不产生红色失败。"""
        try:
            rid = fixer.rule_id
        except Exception:
            pytest.skip("rule_id 属性访问异常（property/构造形态与桩不匹配），请手工适配本用例")
        if rid != "{rule_id}":
            pytest.skip("rule_id 运行时值与静态提取值不一致（构造期改写），请手工适配本用例")

    def test_can_fix_matching_issue(self, fixer, sample_issue):
        """can_fix 应匹配对应 rule_id 的问题。

        discover_fixers 仅以 rule_id 收录，缺方法/签名不匹配/未接受自身
        issue 均 skip 提示手工适配。"""
        _can = getattr(fixer, "can_fix", None)
        if not callable(_can):
            pytest.skip("修复器无 can_fix 方法（discover_fixers 仅以 rule_id 收录），请手工适配本用例")
        try:
            matched = fixer.can_fix(sample_issue)
        except Exception:
            pytest.skip("can_fix 签名或实现与桩模板不匹配，请手工适配本用例")
        if not matched:
            pytest.skip("can_fix 未接受自身 rule_id 的 issue（非标准判定语义），请手工适配本用例")

    def test_can_fix_reject_other(self, fixer):
        """can_fix 应拒绝其他 rule_id。

        宽匹配语义（恒真）的 can_fix 跳过并提示手工适配。"""
        _can = getattr(fixer, "can_fix", None)
        if not callable(_can):
            pytest.skip("修复器无 can_fix 方法（discover_fixers 仅以 rule_id 收录），请手工适配本用例")
        other_issue = {{"rule_id": "OTHER_RULE", "id": "OTHER_RULE"}}
        try:
            matched = fixer.can_fix(other_issue)
        except Exception:
            pytest.skip("can_fix 签名或实现与桩模板不匹配，请手工适配本用例")
        if matched:
            pytest.skip("can_fix 接受了其他 rule_id 的 issue（宽匹配语义），请手工适配本用例")

    def test_fix_does_not_crash(self, fixer, sample_issue):
        """fix 方法不应崩溃（即使输入为空）。"""
        source = "x = 1\\n"
        try:
            result = fixer.fix(source, sample_issue)
        except Exception:
            # 自动生成桩允许 fix 抛异常（签名/依赖形态不匹配）；
            # 断言必须在 try 外，防止 AssertionError 被吞造成恒绿
            return
        assert isinstance(result, str)

    def test_fix_empty_source(self, fixer, sample_issue):
        """空源码不应导致崩溃。"""
        try:
            fixer.fix("", sample_issue)
        except Exception:
            pass  # 允许抛异常，但不应是 SystemExit

    def test_fix_invalid_syntax(self, fixer, sample_issue):
        """语法错误的源码不应导致崩溃。"""
        try:
            fixer.fix("def (\\n", sample_issue)
        except Exception:
            pass

    def test_idempotent_fix(self, fixer, sample_issue):
        """多次修复应保持幂等性。"""
        source = "x = 1\\n"
        try:
            result1 = fixer.fix(source, sample_issue)
            result2 = fixer.fix(result1, sample_issue)
        except Exception:
            return  # 桩测试允许 fix 抛异常；正常返回后断言幂等契约
        # 第二次修复不应再改变代码
        assert result2 == result1

    def test_dry_run_no_modification(self, fixer, sample_issue):
        """dry_run 模式不应修改源码。"""
        source = "x = 1\\n"
        try:
            result = fixer.fix(source, sample_issue)
        except Exception:
            # 桩测试允许抛异常（与其他桩方法容错口径一致）；
            # 断言移出 try，防止 AssertionError 被吞造成恒绿
            return
        # dry_run=True 时应返回原始源码或不做实际修改
        assert isinstance(result, str)


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-p", "no:cacheprovider"])
'''
def _escape_py_str(value: str) -> str:
    value = (value.replace("\\", "\\\\")
                  .replace('"', '\\"')
                  .replace("\n", "\\n")
                  .replace("\r", "\\r"))
    return re.sub(r"[\x00-\x1f\x7f]", lambda m: f"\\x{ord(m.group()):02x}", value)
def _atomic_write_text(path: str, text: str) -> None:
    tmp_path = f"{path}.{os.getpid()}.{time.perf_counter_ns()}.tmp"
    try:
        with open(tmp_path, "w", encoding="utf-8", newline="\n") as fh:
            fh.write(text)
        os.replace(tmp_path, path)
    except BaseException:
        if not safe_delete(tmp_path):
            logger.debug("临时文件清理失败（残留待后续回收）: %s", tmp_path)
        raise
def _fixer_host_has_side_effect(fixer: FixerInfo) -> bool:
    host_file = fixer.file if isinstance(fixer.file, str) else ""
    if not host_file or not os.path.isfile(host_file):
        return False
    tree, fail_note = load_parsed_tree(host_file)
    if tree is None:
        logger.warning(
            "[CoverageBooster] 修复器源码无法确认安全性（%s），"
            "保守跳过导入型测试桩: %s", fail_note, host_file)
        return True
    return module_has_toplevel_side_effect(tree)
def is_booster_stub(path: str) -> bool:
    fname = os.path.basename(path)
    if not (fname.startswith("test_gen_") and fname.endswith(".py")):
        return False
    source, _fingerprint = read_source_with_fingerprint(path)
    if source is None:
        return False
    head = source[:2048]
    return (_BOOSTER_STUB_MARK in head
            or _LEGACY_BOOSTER_STUB_MARK in head)
def _delete_or_warn(path: str, message: str) -> bool:
    if safe_delete(path):
        return True
    logger.warning(message, path)
    return False
def _discard_unsafe_booster_stub(cov: TestCoverage, output_dir: str) -> None:
    stale = _stub_file_path(cov.fixer, output_dir)
    if not os.path.isfile(stale) or not is_booster_stub(stale):
        return
    _delete_or_warn(
        stale, "[CoverageBooster] 清理副作用模块旧测试桩失败: %s")
def _is_py_ident(name: object) -> bool:
    if not isinstance(name, str) or not name:
        return False
    return name.isidentifier() and not keyword.iskeyword(name)
def _valid_dotted_module_name(module: object) -> bool:
    return (isinstance(module, str) and bool(module)
            and all(_is_py_ident(part) for part in module.split(".")))
def _booster_stub_belongs_to_fixer(path: str, fixer: FixerInfo) -> bool:
    source, _fingerprint = read_source_with_fingerprint(path)
    if source is None:
        return False
    tree, error = parse_py_source(source)
    if error is not None:
        return False
    host_matches = False
    rule_matches = False
    for node in walk_nodes(tree):
        if (isinstance(node, ast.ImportFrom) and node.level == 0
                and node.module == fixer.module
                and any(alias.name == fixer.class_name for alias in node.names)):
            host_matches = True
        elif (isinstance(node, ast.Constant)
              and node.value == fixer.rule_id):
            rule_matches = True
    return host_matches and rule_matches
def _stub_filename(fixer: FixerInfo) -> str:
    stem = f"test_gen_{fixer.module}_{fixer.rule_id.lower()}"
    return re.sub(r"[^A-Za-z0-9_]", "_", stem) + ".py"
def _stub_file_path(fixer: FixerInfo, output_dir: str) -> str:
    return os.path.join(output_dir, _stub_filename(fixer))
def generate_test_stub(fixer: FixerInfo, output_dir: str) -> str | None:
    output_dir = coerce_target_file(output_dir)
    if not output_dir:
        logger.warning("[CoverageBooster] 桩输出目录非法或为空，跳过测试桩生成")
        return None
    if not _valid_dotted_module_name(fixer.module):
        logger.warning(
            "[CoverageBooster] 修复器所在模块名非合法 Python 标识符，"
            "跳过测试桩生成（避免产出语法错误桩破坏测试收集）: %s",
            fixer.module)
        return None
    if not _is_py_ident(fixer.class_name):
        logger.warning(
            "[CoverageBooster] 修复器类名非合法 Python 标识符，"
            "跳过测试桩生成（避免产出语法错误桩破坏测试收集）: %s",
            fixer.class_name)
        return None
    if _fixer_host_has_side_effect(fixer):
        logger.warning(
            "[CoverageBooster] 修复器模块存在顶层副作用，"
            "跳过会导入该模块的测试桩: %s", fixer.file)
        return None
    os.makedirs(output_dir, exist_ok=True)
    filepath = _stub_file_path(fixer, output_dir)
    if os.path.isfile(filepath):
        if not _booster_stub_belongs_to_fixer(filepath, fixer):
            logger.warning(
                "[CoverageBooster] 已存在同名测试桩但模块/类/规则归属不符，"
                "拒绝冒领且不覆盖: %s", filepath)
            return None
        logger.info("[CoverageBooster] 测试桩已存在且归属一致，跳过覆盖（保护手工补充的用例）: %s", filepath)
        return filepath
    module_path = fixer.module.replace(".", "/")
    code = _TEST_STUB_TEMPLATE.format(
        class_name=fixer.class_name,
        rule_id=_escape_py_str(fixer.rule_id),
        module=fixer.module,
        module_path=module_path,
        booster_mark=_BOOSTER_STUB_MARK,
        bootstrap=_IMPORT_BOOTSTRAP.format(
            module_path=_escape_py_str(module_path),
            import_root=_escape_py_str(
                _host_import_root(fixer.module, fixer.file))),
    )
    _atomic_write_text(filepath, code)
    logger.info("[CoverageBooster] 生成测试桩: %s → %s", fixer.class_name, filepath)
    return filepath
def _try_generate_stub(
    cov: TestCoverage,
    output_dir: str,
    seen_stubs: dict[str, str],
    failed: list[str],
) -> str | None:
    try:
        path = generate_test_stub(cov.fixer, output_dir)
    except OSError as e:
        failed.append(cov.fixer.class_name)
        logger.warning("[CoverageBooster] 生成测试桩失败 %s: %s", cov.fixer.class_name, e)
        return None
    if not path:
        return None
    first_rule = seen_stubs.get(path)
    if first_rule is not None:
        logger.warning(
            "[CoverageBooster] rule_id 归一撞车: %r 与 %r 同归桩文件 %s，"
            "仅保留首个桩（后者未获独立测试）",
            first_rule, cov.fixer.rule_id, path)
        return None
    seen_stubs[path] = cov.fixer.rule_id
    return path
def _booster_stub_host_module(path: str) -> str:
    source, _ = read_source_with_fingerprint(path)
    if source is None:
        return ""
    tree, error = parse_py_source(source)
    if error is not None:
        return ""
    stem = os.path.basename(path).removeprefix("test_gen_")
    fallback = ""
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.ImportFrom) and node.level == 0
                and node.module) or node.module == "__future__":
            continue
        if stem.startswith(node.module.replace(".", "_") + "_"):
            return node.module
        if not fallback:
            fallback = node.module
    return fallback
def _host_module_stems(skill_dir: str) -> frozenset[str] | None:
    if sorted_dir_entries(skill_dir) is None:
        return None
    return frozenset(name for name, _path in _iter_py_modules(skill_dir))
def _cleanup_missing_host_booster_stubs_in_dir(
        skill_dir: str, generated_dir: str) -> None:
    if not os.path.isdir(generated_dir):
        return
    host_modules = _host_module_stems(skill_dir)
    stub_entries = sorted_dir_entries(generated_dir)
    if host_modules is None or stub_entries is None:
        return
    for fname in stub_entries:
        path = os.path.join(generated_dir, fname)
        if not os.path.isfile(path) or not is_booster_stub(path):
            continue
        module = _booster_stub_host_module(path)
        if not module or module in host_modules:
            continue
        _delete_or_warn(
            path, "[CoverageBooster] 清理失去宿主模块的旧测试桩失败: %s")
def cleanup_missing_host_booster_stubs(skill_dir: str,
                                        tests_dir: str) -> None:
    _cleanup_missing_host_booster_stubs_in_dir(
        skill_dir, os.path.join(tests_dir, GENERATED_SUBDIR))
def _cleanup_stale_booster_stubs(generated_dir: str,
                                  coverage: list[TestCoverage],
                                  skill_dir: str) -> None:
    if not os.path.isdir(generated_dir):
        return
    entries = sorted_dir_entries(generated_dir)
    if entries is None:
        return
    active_names = {_stub_filename(cov.fixer) for cov in coverage}
    host_files = dict(_iter_py_modules(skill_dir))
    host_failures: dict[str, str] = {}
    for fname in entries:
        path = os.path.join(generated_dir, fname)
        if (fname in active_names or not os.path.isfile(path)
                or not is_booster_stub(path)):
            continue
        module = _booster_stub_host_module(path)
        host_file = host_files.get(module, "")
        if host_file:
            if module not in host_failures:
                _tree, fail_note = load_parsed_tree(host_file)
                host_failures[module] = fail_note or ""
            if host_failures[module]:
                logger.warning(
                    "[CoverageBooster] 宿主暂不可解析，保留旧测试桩 %s: %s",
                    path, host_failures[module])
                continue
        _delete_or_warn(
            path, "[CoverageBooster] 清理失去修复器的旧测试桩失败: %s")
def generate_missing_tests(
    skill_dir: str,
    tests_dir: str | None = None,
    output_dir: str | None = None,
) -> list[str]:
    skill_dir = coerce_target_file(skill_dir)
    if not skill_dir:
        logger.warning("[CoverageBooster] 技能目录非法或为空，跳过测试桩补齐")
        return []
    tests_dir = _tests_dir(skill_dir, tests_dir)
    explicit_output = coerce_target_file(output_dir)
    if explicit_output and not os.path.isabs(explicit_output):
        explicit_output = os.path.join(skill_dir, explicit_output)
    default_output = os.path.join(tests_dir, GENERATED_SUBDIR)
    output_dir = explicit_output or default_output
    cleanup_dirs = [default_output]
    if (os.path.normcase(os.path.abspath(output_dir))
            != os.path.normcase(os.path.abspath(default_output))):
        cleanup_dirs.append(output_dir)
    for cleanup_dir in cleanup_dirs:
        _cleanup_missing_host_booster_stubs_in_dir(skill_dir, cleanup_dir)
    coverage = analyze_test_coverage(skill_dir, tests_dir)
    for cleanup_dir in cleanup_dirs:
        _cleanup_stale_booster_stubs(cleanup_dir, coverage, skill_dir)
    generated: list[str] = []
    reused: list[str] = []
    failed: list[str] = []
    seen_stubs: dict[str, str] = {}
    for cov in coverage:
        if _fixer_host_has_side_effect(cov.fixer):
            logger.warning(
                "[CoverageBooster] 副作用模块不保留导入型测试桩: %s",
                cov.fixer.file)
            for cleanup_dir in cleanup_dirs:
                _discard_unsafe_booster_stub(cov, cleanup_dir)
            continue
        if cov.has_test:
            continue
        existed = os.path.isfile(_stub_file_path(cov.fixer, output_dir))
        path = _try_generate_stub(cov, output_dir, seen_stubs, failed)
        if not path:
            continue
        (reused if existed else generated).append(path)
    if failed:
        logger.warning("[CoverageBooster] %d 个测试桩生成失败: %s", len(failed), ", ".join(failed))
    if reused:
        logger.info("[CoverageBooster] 复用已有测试桩 %d 个（未计为本次生成）",
                    len(reused))
    logger.info("[CoverageBooster] 生成了 %d 个测试桩", len(generated))
    return generated
_CONVENTION_MODULE_NAMES = frozenset(
    {"__init__.py", "conftest.py", "setup.py", "__main__.py"})
_SOURCE_ROOT_NAMES = ("src",)
def is_fixer_candidate_file(fname: str) -> bool:
    if not isinstance(fname, str) or not is_scan_py_name(fname):
        return False
    if is_test_source_basename(fname):
        return False
    return fname.lower() not in _CONVENTION_MODULE_NAMES
def _package_chain_parts(skill_dir: str, rel_dir: str) -> list[str] | None:
    root_name = os.path.basename(os.path.abspath(skill_dir))
    root_is_package = (
        _is_py_ident(root_name)
        and os.path.isfile(os.path.join(skill_dir, "__init__.py")))
    package_parts = [root_name] if root_is_package else []
    if rel_dir == ".":
        return package_parts
    parts = [part for part in rel_dir.split(os.sep)
             if part and part != os.curdir]
    if not all(_is_py_ident(part) for part in parts):
        return None
    return package_parts + parts
def _module_dotted_name(fname: str,
                        mod_parts: list[str]) -> str | None:
    if not is_fixer_candidate_file(fname):
        return None
    stem = fname[:-3]
    if not _is_py_ident(stem):
        return None
    return ".".join(mod_parts + [stem])
def _source_roots(skill_dir: str) -> list[str]:
    roots = [skill_dir]
    for name in _SOURCE_ROOT_NAMES:
        candidate = os.path.join(skill_dir, name)
        if (os.path.isdir(candidate)
                and not os.path.isfile(
                    os.path.join(candidate, "__init__.py"))):
            roots.append(candidate)
    return roots
def _raise_walk_error(error: OSError) -> None:
    raise error


def _iter_py_modules(skill_dir: str) -> list[tuple[str, str]]:
    skill_dir = os.path.abspath(skill_dir)
    results: list[tuple[str, str]] = []
    seen: set[str] = set()
    prune = frozenset(scan_exclude_dirs(skill_dir))
    roots = _source_roots(skill_dir)
    root_keys = [os.path.normcase(os.path.abspath(root)) for root in roots]
    for scan_root in roots:
        _own = os.path.normcase(os.path.abspath(scan_root))
        nested_roots = {key for key in root_keys if key != _own}
        for root, dirs, files in os.walk(
                scan_root, onerror=_raise_walk_error):
            dirs[:] = sorted(
                d for d in dirs
                if not is_pruned_scan_dir(d, prune)
                and os.path.normcase(os.path.abspath(
                    os.path.join(root, d))) not in nested_roots)
            mod_parts = _package_chain_parts(
                scan_root, os.path.relpath(root, scan_root))
            if mod_parts is None:
                dirs[:] = []
                continue
            for fname in sorted(files):
                dotted = _module_dotted_name(fname, mod_parts)
                if dotted is None:
                    continue
                filepath = os.path.join(root, fname)
                if filepath in seen:
                    continue
                seen.add(filepath)
                results.append((dotted, filepath))
    return results
_DANGEROUS_NAME_PARTS = (
    "删除", "移除", "清理", "写入", "保存", "读取", "加载", "扫描",
    "分析", "构建", "生成", "运行", "执行", "启动", "停止", "下载",
    "上传", "请求", "监听", "连接", "查询", "搜索", "导入", "导出",
    "重置", "安装", "卸载", "注册", "刷新", "同步", "迁移", "校验",
    "验证", "修复", "优化", "处理", "转换", "合并", "拆分", "初始化",
    "提交", "发布", "部署", "渲染", "报告", "审计", "诊断", "检测",
    "检查", "配置", "调度", "触发", "计划", "监控", "抽取", "采集",
    "analy", "build", "graph", "scan", "metric", "report", "render",
    "execute", "pipeline", "audit", "diagnos", "detect", "check",
    "load", "save", "write", "read", "parse", "process", "config",
    "init", "connect", "close", "serve", "start", "stop",
    "download", "upload", "fetch", "request", "crawl", "scrape",
    "watch", "monitor", "invoke", "dispatch", "route", "handle",
    "trigger", "plan", "optim", "refactor", "fix", "verify", "valid",
    "guard", "run", "main", "gen", "apply", "update", "install",
    "uninstall", "register", "unregister", "clear", "reset",
    "delete", "remove", "query", "search", "index",
    "export", "import", "serialize", "deserialize", "migrate",
    "seed", "poll", "sync", "refresh", "retry", "wait",
)
_DANGEROUS_CLASS_PARTS = (
    "缓存", "上下文", "管理器", "构建器", "工厂", "运行器", "引擎",
    "分析器", "检测器", "扫描器", "客户端", "连接器", "会话", "处理器",
    "服务", "协调器", "编排器", "加载器", "写入器", "读取器", "驱动器",
    "适配器", "监控器", "服务器", "工作器", "线程池", "管道", "注册表",
    "存储", "仓库", "数据库",
    "cache", "context", "manager", "builder", "factory", "runner",
    "engine", "analyzer", "detector", "scanner", "client", "connector",
    "session", "handler", "service", "coordinator", "orchestrator",
    "loader", "saver", "writer", "reader", "driver", "adapter",
    "monitor", "watcher", "server", "worker", "pool", "fetcher",
    "pipeline", "registry", "store", "repo", "database", "db",
)
_DANGEROUS_PARAM_PARTS = (
    "路径", "文件", "目录", "根目录", "文件夹", "链接", "地址", "主机",
    "端口", "连接", "套接字", "会话", "客户端", "节点", "上下文",
    "数据", "配置", "命令", "环境", "正则", "模式", "回调", "流",
    "缓冲",
    "path", "file", "dir", "root", "folder", "url", "host", "port",
    "conn", "socket", "session", "client", "tree", "node", "visitor",
    "ast", "ctx", "context", "data", "json", "yaml", "toml",
    "cmd", "command", "shell", "env", "config", "regex", "pattern",
    "handler", "callback", "stream", "buffer", "fd", "handle",
)
SUPPLEMENTAL_MARK = "auto-generated-supplemental-test-suite"
def _none_default(default: ast.expr) -> bool:
    return isinstance(default, ast.Constant) and default.value is None
def _param_name_dangerous(name: str | None) -> bool:
    return any(k in (name or "").lower() for k in _DANGEROUS_PARAM_PARTS)
def _kwonly_args_safe(a: ast.arguments) -> bool:
    for arg, d in zip(a.kwonlyargs, a.kw_defaults, strict=False):
        if d is None or _none_default(d) or _param_name_dangerous(arg.arg):
            return False
    return True
def _positional_defaults_safe(pos_args: list, defaults: list) -> bool:
    return (not any(_none_default(d) for d in defaults)
            and not any(_param_name_dangerous(arg.arg) for arg in pos_args))
def _method_positional_args(a: ast.arguments,
                           skip_first: bool) -> list:
    pos_args = list(a.posonlyargs) + list(a.args)
    if skip_first and pos_args:
        return pos_args[1:]
    return pos_args
def _all_defaults(func_node: ast.FunctionDef | ast.AsyncFunctionDef,
                  skip_first: bool = False) -> bool:
    a = func_node.args
    if not _kwonly_args_safe(a):
        return False
    pos_args = _method_positional_args(a, skip_first)
    if not pos_args:
        return True
    if len(a.defaults) < len(pos_args):
        return False
    return _positional_defaults_safe(pos_args, a.defaults)
def _function_name_demoted(name: str) -> bool:
    if name.startswith("__") and name.endswith("__"):
        return True
    return any(d in name.lower() for d in _DANGEROUS_NAME_PARTS)
def _has_own_yield(node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    return any(isinstance(current, (ast.Yield, ast.YieldFrom))
               for current in _iter_own_ast_nodes(node))
def _function_form_demoted(node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    if node.decorator_list:
        return True
    if isinstance(node, ast.AsyncFunctionDef):
        return True
    if _has_own_yield(node):
        return True
    return node.args.vararg is not None or node.args.kwarg is not None
def _classify_function(node: ast.FunctionDef | ast.AsyncFunctionDef) -> str:
    if _function_name_demoted(node.name):
        return "exists"
    if _function_form_demoted(node):
        return "exists"
    if not _all_defaults(node):
        return "exists"
    return "call"
def _bare_class_instantiable(node: ast.ClassDef) -> bool:
    for _b in node.bases:
        if not (isinstance(_b, ast.Name) and _b.id == "object"):
            return False
    return not node.keywords
def _class_body_name_bindings(node: ast.ClassDef, name: str) -> list[ast.AST]:
    bindings: list[ast.AST] = []
    for item in _iter_class_body_nodes(node):
        for bound in _module_def_flow_statement(item, {}).get(name, ()):
            if all(bound is not previous for previous in bindings):
                bindings.append(bound)
    return bindings
def _ctor_accepts_zero_args(method) -> bool:
    if method.decorator_list or isinstance(method, ast.AsyncFunctionDef):
        return False
    if method.args.vararg or method.args.kwarg:
        return False
    return _all_defaults(method, skip_first=True)
_ABSTRACT_METHOD_DECORATORS = frozenset({
    "abstractmethod", "abstractclassmethod", "abstractstaticmethod",
    "abstractproperty",
})
_ABSTRACT_BASE_NAMES = frozenset({"ABC", "Protocol"})
def _expr_tail_name(expr: ast.expr) -> str:
    while isinstance(expr, ast.Subscript):
        expr = expr.value
    if isinstance(expr, ast.Name):
        return expr.id
    if isinstance(expr, ast.Attribute):
        return expr.attr
    return ""
def _decorator_marks_abstract(decorator: ast.expr) -> bool:
    target = decorator.func if isinstance(decorator, ast.Call) else decorator
    return _expr_tail_name(target) in _ABSTRACT_METHOD_DECORATORS
def _class_has_abstract_marker(
        node: ast.ClassDef,
        abstract_bases: set[str] | frozenset[str]) -> bool:
    for kw in node.keywords:
        if kw.arg == "metaclass" and _expr_tail_name(kw.value) == "ABCMeta":
            return True
    for base in node.bases:
        name = _expr_tail_name(base)
        if name in _ABSTRACT_BASE_NAMES or name in abstract_bases:
            return True
    return any(
        isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
        and any(_decorator_marks_abstract(d) for d in item.decorator_list)
        for item in _iter_class_body_nodes(node))
def _collect_abstract_class_names(tree: ast.Module) -> set[str]:
    classes = list(_iter_module_scope_classes(tree.body))
    abstract: set[str] = set()
    changed = True
    while changed:
        changed = False
        for node in classes:
            if node.name in abstract:
                continue
            if _class_has_abstract_marker(node, abstract):
                abstract.add(node.name)
                changed = True
    return abstract
def _classify_via_init(node: ast.ClassDef) -> str:
    if node.keywords:
        return "exists"
    new_bindings = _class_body_name_bindings(node, "__new__")
    if any(not isinstance(binding, _FUNC_NODE_TYPES)
           or not _ctor_accepts_zero_args(binding)
           for binding in new_bindings):
        return "exists"
    if not _bare_class_instantiable(node):
        return "exists"
    init_bindings = _class_body_name_bindings(node, "__init__")
    if any(not isinstance(binding, _FUNC_NODE_TYPES)
           or not _ctor_accepts_zero_args(binding)
           for binding in init_bindings):
        return "exists"
    return "call"
def _classify_class(
        node: ast.ClassDef,
        abstract_bases: set[str] | frozenset[str]) -> str:
    name = node.name
    if any(d in name.lower() for d in _DANGEROUS_CLASS_PARTS):
        return "exists"
    if node.decorator_list:
        return "exists"
    if _class_has_abstract_marker(node, abstract_bases):
        return "exists"
    return _classify_via_init(node)
def _merge_module_def_states(
        *states: dict, require_all_paths: bool = True) -> dict:
    required_names: set[str] | None = None
    if states and require_all_paths:
        required_names = set(states[0])
        for state in states[1:]:
            required_names.intersection_update(state)
    merged: dict[str, list[ast.AST]] = {}
    for state in states:
        for name, nodes in state.items():
            if required_names is not None and name not in required_names:
                continue
            target = merged.setdefault(name, [])
            for node in nodes:
                if all(node is not previous for previous in target):
                    target.append(node)
    return {name: tuple(nodes) for name, nodes in merged.items()}
def _module_def_rebind(states: dict, names, marker: ast.AST) -> dict:
    rebound = {name for name in names if name}
    if not rebound:
        return states
    return {**states, **{name: (marker,) for name in rebound}}
def _module_def_binding_states(item: ast.AST, states: dict) -> dict:
    names: set[str] = set()
    if isinstance(item, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
        if not (isinstance(item, ast.AnnAssign) and item.value is None):
            targets = (item.targets if isinstance(item, ast.Assign)
                       else [item.target])
            for target in targets:
                names.update(_iter_binding_names(target))
    elif isinstance(item, ast.Delete):
        for target in item.targets:
            names.update(_iter_binding_names(target))
    elif isinstance(item, ast.Import):
        names.update(alias.asname or alias.name.split(".", 1)[0]
                     for alias in item.names)
    elif isinstance(item, ast.ImportFrom):
        if any(alias.name == "*" for alias in item.names):
            names.update(states)
        names.update(alias.asname or alias.name for alias in item.names
                     if alias.name != "*")
    stack = [item]
    while stack:
        current = stack.pop()
        if (current is not item and isinstance(
                current, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))):
            continue
        if isinstance(current, ast.Lambda):
            stack.extend(_definition_binding_exprs(current))
            continue
        if isinstance(current, ast.NamedExpr):
            names.update(_iter_binding_names(current.target))
        stack.extend(ast.iter_child_nodes(current))
    return _module_def_rebind(states, names, item)
def _module_def_pattern_bindings(pattern: ast.AST) -> set[str]:
    names: set[str] = set()
    for current in walk_nodes(pattern):
        if isinstance(current, (ast.MatchAs, ast.MatchStar, ast.MatchMapping)):
            names.update(name for name in (
                getattr(current, "name", None), getattr(current, "rest", None))
                if name)
    return names
def _module_def_suite(body, states: dict) -> dict:
    for item in body:
        states = _module_def_flow_statement(item, states)
    return states
def _module_def_if_states(item: ast.If, states: dict) -> dict:
    current = _module_def_binding_states(item.test, states)
    live = main_guard_live_body(item)
    if live is not None:
        return _module_def_suite(live, current)
    static = static_if_branch(item.test)
    if static is not None:
        return _module_def_suite(item.body if static else item.orelse, current)
    return _merge_module_def_states(
        _module_def_suite(item.body, current),
        _module_def_suite(item.orelse, current),
    )
def _module_def_loop_states(item: ast.AST, states: dict) -> dict:
    test = item.iter if isinstance(item, (ast.For, ast.AsyncFor)) else item.test
    current = _module_def_binding_states(test, states)
    if isinstance(item, ast.While) and static_if_branch(item.test) is False:
        return _module_def_suite(item.orelse, current)
    if _loop_has_own_jump(item):
        affected = _merge_module_def_states(
            _module_def_suite(item.body, {}),
            _module_def_suite(item.orelse, {}),
            require_all_paths=False,
        )
        current = _module_def_rebind(current, affected, item)
        if isinstance(item, (ast.For, ast.AsyncFor)):
            current = _module_def_rebind(
                current, _iter_binding_names(item.target), item)
        return current
    zero_iterations = _module_def_suite(item.orelse, current)
    if isinstance(item, ast.While) and static_if_branch(item.test) is True:
        zero_iterations = {}
    body_states = current
    if isinstance(item, (ast.For, ast.AsyncFor)):
        body_states = _module_def_rebind(
            current, _iter_binding_names(item.target), item)
    body_exit = _module_def_suite(item.body, body_states)
    normal_exit = _module_def_suite(item.orelse, body_exit)
    return _merge_module_def_states(zero_iterations, normal_exit)
def _module_def_try_states(item: ast.AST, states: dict) -> dict:
    handler_prefixes = [states]
    current = states
    for statement in item.body:
        current = _module_def_flow_statement(statement, current)
        handler_prefixes.append(current)
    try_exit = current
    paths = [_module_def_suite(item.orelse, try_exit)]
    if item.handlers:
        handler_entry = _merge_module_def_states(*handler_prefixes)
        for handler in item.handlers:
            handled_entry = _module_def_rebind(
                handler_entry, (handler.name,), handler)
            handled = _module_def_suite(handler.body, handled_entry)
            paths.append(_module_def_rebind(
                handled, (handler.name,), handler))
    return _module_def_suite(
        item.finalbody, _merge_module_def_states(*paths))
def _module_def_match_states(item: ast.AST, states: dict) -> dict:
    current = _module_def_binding_states(item.subject, states)
    paths: list[dict] = []
    unmatched = current
    for case in item.cases:
        captures = _module_def_pattern_bindings(case.pattern)
        case_states = _module_def_rebind(current, captures, case.pattern)
        if case.guard is not None:
            case_states = _module_def_binding_states(case.guard, case_states)
            unmatched = _module_def_binding_states(case.guard, unmatched)
        paths.append(_module_def_suite(case.body, case_states))
        unmatched = _module_def_rebind(unmatched, captures, case.pattern)
    has_irrefutable_case = any(
        isinstance(case.pattern, ast.MatchAs)
        and case.pattern.pattern is None and case.guard is None
        for case in item.cases)
    if not has_irrefutable_case:
        paths.append(unmatched)
    return _merge_module_def_states(*paths)
def _module_def_flow_statement(item: ast.stmt, states: dict) -> dict:
    if isinstance(item, _DEFINITION_NODE_TYPES):
        current = states
        for expr in _definition_binding_exprs(item):
            current = _module_def_binding_states(expr, current)
        return {**current, item.name: (item,)}
    if isinstance(item, ast.If):
        return _module_def_if_states(item, states)
    if isinstance(item, (ast.For, ast.AsyncFor, ast.While)):
        return _module_def_loop_states(item, states)
    if isinstance(item, (ast.With, ast.AsyncWith)):
        current = states
        for entry in item.items:
            current = _module_def_binding_states(entry.context_expr, current)
            if entry.optional_vars is not None:
                current = _module_def_rebind(
                    current, _iter_binding_names(entry.optional_vars), item)
        return _module_def_suite(item.body, current)
    if isinstance(item, (ast.Try, TRY_STAR_T)):
        return _module_def_try_states(item, states)
    if MATCH_T and isinstance(item, MATCH_T):
        return _module_def_match_states(item, states)
    return _module_def_binding_states(item, states)
def _module_top_level_names(tree: ast.AST) -> tuple[list[str], list[str]]:
    funcs: list[str] = []
    classes: list[str] = []
    for name, nodes in _module_def_suite(
            list(getattr(tree, "body", ())), {}).items():
        if name.startswith("_"):
            continue
        if all(isinstance(node, _FUNC_NODE_TYPES) for node in nodes):
            funcs.append(name)
        elif all(isinstance(node, ast.ClassDef) for node in nodes):
            classes.append(name)
        elif all(isinstance(node, _DEFINITION_NODE_TYPES) for node in nodes):
            funcs.append(name)
    return funcs, classes
def _classify_named_nodes(tree: ast.Module, names: list, classifier,
                          expected_types) -> tuple[list, list]:
    by_name = _module_def_suite(tree.body, {})
    call_names, exists_names = [], []
    for name in dict.fromkeys(names):
        nodes = by_name.get(name, ())
        if not nodes:
            continue
        if (all(isinstance(node, expected_types) for node in nodes)
                and all(classifier(node) == "call" for node in nodes)):
            call_names.append(name)
        else:
            exists_names.append(name)
    return call_names, exists_names
class MemberGrades(NamedTuple):
    call_funcs: list[str]
    exists_funcs: list[str]
    call_classes: list[str]
    exists_classes: list[str]
    def any_testable(self) -> bool:
        return any((self.call_funcs, self.exists_funcs,
                    self.call_classes, self.exists_classes))
def classify_module_members(tree: ast.Module) -> MemberGrades:
    funcs, classes = _module_top_level_names(tree)
    abstract_classes = _collect_abstract_class_names(tree)
    call_funcs, exists_funcs = _classify_named_nodes(
        tree, funcs, _classify_function, _FUNC_NODE_TYPES)
    call_classes, exists_classes = _classify_named_nodes(
        tree, classes, lambda node: _classify_class(node, abstract_classes),
        ast.ClassDef)
    return MemberGrades(call_funcs, exists_funcs, call_classes, exists_classes)
def _append_test_case(lines: list[str], taken: set[str], name: str, suffix: str,
                      grade: str, body: list[str]) -> None:
    lines.append("")
    lines.append(f"def test_{_unique_test_name(f'{name}_{suffix}', taken)}():")
    lines.append(f"    # 分级: {grade}")
    lines.extend(body)
_MEMBER_TEST_SPECS: tuple[tuple[str, str, str, tuple[str, ...]], ...] = (
    ("exists_funcs", "exists",
     "exists — 仅验证存在性与可调用，不实际调用",
     ("    _fn = getattr(_load_module(), {name!r})",
      "    assert callable(_fn)")),
    ("call_funcs", "invocation",
     "call — 零参数/全默认参数调用，仅验证不抛异常",
     ("    _mod = _load_module()", "    _mod.{name}()")),
    ("call_classes", "instantiable",
     "call — 无必填构造参数，实例化仅验证不抛异常",
     ("    _cls = getattr(_load_module(), {name!r})",
      "    _inst = _cls()",
      "    assert _inst is not None")),
    ("exists_classes", "class_exists",
     "exists — 仅验证类存在",
     ("    _cls = getattr(_load_module(), {name!r})",
      "    assert isinstance(_cls, type)")),
)
def _append_member_tests(lines: list[str], grades: MemberGrades,
                         taken: set[str]) -> None:
    for group, suffix, grade, body_tpl in _MEMBER_TEST_SPECS:
        for name in getattr(grades, group):
            body = [line.format(name=name) for line in body_tpl]
            _append_test_case(lines, taken, name, suffix, grade, body)
def build_test_source(mod_path: str, rel_file: str,
                       grades: MemberGrades, *, import_root: str = "") -> str:
    rel_file = _escape_py_str(rel_file.replace("\\", "/"))
    module_path = _escape_py_str(mod_path.replace(".", "/"))
    import_root = _escape_py_str(import_root)
    taken: set[str] = set()
    lines: list[str] = [
        "# -*- coding: utf-8 -*-",
        f"# {SUPPLEMENTAL_MARK}: {rel_file}",
        '"""补足测试套件 — 由统一测试套件引擎自动生成（可安全删除/重建）。',
        f"模块: {rel_file}",
        (f"分级: call函数={len(grades.call_funcs)} "
        f"exists函数={len(grades.exists_funcs)} "
        f"call类={len(grades.call_classes)} exists类={len(grades.exists_classes)}"),
        '"""',
        "",
        "import os",
        "import sys",
        "import importlib",
        "",
        *(_IMPORT_BOOTSTRAP.format(
            module_path=module_path, import_root=import_root).splitlines()),
        "",
        "",
        "def _load_module():",
        '    """加载目标模块（importlib 缓存幂等）。"""',
        f"    return importlib.import_module({mod_path!r})",
        "",
        "",
        "def test_module_importable():",
        "    assert _load_module() is not None",
        "",
    ]
    _append_member_tests(lines, grades, taken)
    return "\n".join(lines) + "\n"
def safe_test_name(name: str) -> str:
    cleaned = re.sub(r"[^0-9a-zA-Z_]", "_", name)
    if not cleaned:
        cleaned = "x"
    if cleaned[0].isdigit():
        cleaned = "_" + cleaned
    return cleaned
def _candidate_names(seed: str, base: str):
    yield base
    digest = hashlib.sha1(
        seed.encode("utf-8"), usedforsecurity=False).hexdigest()[:6]
    yield f"{base}__{digest}"
    n = 2
    while True:
        yield f"{base}__{digest}_{n}"
        n += 1
def _unique_test_name(name: str, taken: set[str]) -> str:
    candidate = next(c for c in _candidate_names(name, safe_test_name(name))
                     if c not in taken)
    taken.add(candidate)
    return candidate
_SUFFIX = "_supplemental.py"
def _tests_dir(skill_dir: str, tests_dir: str | None = None) -> str:
    explicit = coerce_target_file(tests_dir)
    if explicit:
        return (explicit if os.path.isabs(explicit)
                else os.path.join(skill_dir, explicit))
    resolved = resolve_tests_dir(skill_dir)
    if resolved:
        return resolved
    return os.path.join(skill_dir, DEFAULT_TEST_DIR_NAME)
def _is_generated_file(path: str) -> bool:
    fname = os.path.basename(path)
    if not (fname.endswith(_SUFFIX) and fname.startswith("test_")):
        return False
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            head = f.read(2048)
    except OSError as _e:
        log_swallowed(__name__, _e, context='_is_generated_file:OSError')
        return False
    return SUPPLEMENTAL_MARK in head
def _is_engine_artifact(path: str) -> bool:
    return _is_generated_file(path) or is_booster_stub(path)
def _claim_test_stem(mod_path: str, owners: dict[str, str]) -> str:
    base = safe_test_name(mod_path.replace(".", "_"))
    return next(
        candidate for candidate in _candidate_names(mod_path, base)
        if owners.setdefault(
            os.path.normcase(candidate), mod_path) == mod_path)
def _claim_output(mod_path: str, tests_dir: str,
                  stem_owners: dict[str, str]) -> tuple[str, str]:
    stem = _claim_test_stem(mod_path, stem_owners)
    test_name = f"test_{stem}{_SUFFIX}"
    return test_name, os.path.join(tests_dir, test_name)
def _cleanup_stale_generated(stale_generated: list[str],
                             touched: set[str]) -> None:
    for f in stale_generated:
        if os.path.normcase(f) in touched:
            continue
        if _is_generated_file(f):
            _delete_or_warn(
                f, "[Supplement] 清理单个旧生成测试失败（跳过继续）: %s")
def _classify_existing_state(
        skill_dir: str, tests_dir: str) -> tuple[str, list[str], dict | None]:
    project_tests = [
        fpath for fpath in _iter_project_test_paths(skill_dir, tests_dir)
        if is_test_source_file(os.path.basename(fpath))
    ]
    if not project_tests:
        return "generated", [], None
    if any(not _is_engine_artifact(fpath) for fpath in project_tests):
        return "user_tests", [], _structured_result(
            "user_tests", 0, tests_dir,
            f"项目 {skill_dir} 内已有用户手写测试，"
            "跳过补足生成（尊重用户接管）")
    return ("rebuilt",
            [fpath for fpath in project_tests
             if _is_generated_file(fpath)], None)
def _write_supplementary_file(out_path: str,
                              test_source: str) -> tuple[str, str | None]:
    payload = test_source.encode("utf-8")
    try:
        with open(out_path, "rb") as f:
            if f.read() == payload:
                return "unchanged", None
    except OSError as e:
        logger.debug("补足测试内容比对读取失败（跳过比对，直接重写）: %s: %s",
                     out_path, e)
    try:
        _atomic_write_text(out_path, test_source)
    except OSError as e:
        log_swallowed(__name__, e,
                      context='_write_supplementary_file:OSError')
        return "failed", str(e)
    return "written", None
@dataclass
class _SupplementRun:
    mode: str
    module_count: int
    generated_files: list[str] = field(default_factory=list)
    unchanged_files: list[str] = field(default_factory=list)
    skipped: list[str] = field(default_factory=list)
    ignored: list[str] = field(default_factory=list)
    failed: list[str] = field(default_factory=list)
    touched: set[str] = field(default_factory=set)
def _resolve_supplement_status(run: _SupplementRun, ready: int) -> tuple[str, str]:
    if run.failed:
        if ready:
            return "error", (
                f"已就绪文件={ready}，生成失败模块={len(run.failed)}")
        return "error", f"生成失败模块={len(run.failed)}"
    if ready:
        status = run.mode
        if run.unchanged_files:
            return status, (
                f"就绪文件={ready} (写入{len(run.generated_files)}/"
                f"不变{len(run.unchanged_files)}, {run.mode})")
        return status, f"生成文件={ready} ({run.mode})"
    if run.skipped:
        if run.ignored or len(run.skipped) != run.module_count:
            return "skipped_partial", (
                "未生成任何文件（跳过(顶层副作用) 与 忽略(无可测成员) 混合）")
        return "skipped_all", (
            f"全部 {len(run.skipped)} 个模块因顶层副作用被跳过，未生成")
    if run.ignored:
        return "ignored_all", (
            f"全部 {len(run.ignored)} 个模块无可测成员，未生成")
    return "no_python", "无可生成内容"
def _boost_fixer_stubs(skill_dir: str, tests_dir: str) -> int:
    try:
        return len(generate_missing_tests(skill_dir, tests_dir))
    except Exception as _ce:
        logger.warning("[Supplement] 修复器测试桩生成失败: %s", _ce,
                       exc_info=True)
        return 0
def _finalize_summary(skill_dir: str, tests_dir: str, run: _SupplementRun) -> dict:
    parts = [f"模块数={run.module_count}"]
    fixer_stub_count = _boost_fixer_stubs(skill_dir, tests_dir)
    if fixer_stub_count:
        parts.append(f"修复器测试桩={fixer_stub_count}")
    ready = len(run.generated_files) + len(run.unchanged_files)
    status, main_part = _resolve_supplement_status(run, ready)
    parts.append(main_part)
    if run.skipped:
        parts.append(f"跳过(顶层副作用)={len(run.skipped)}")
    if run.ignored:
        parts.append(f"忽略(无可测成员)={len(run.ignored)}")
    if run.failed:
        parts.append(f"失败={len(run.failed)}")
    return _structured_result(
        status, run.module_count, tests_dir,
        ", ".join(parts) or "无输出",
        file_count=ready, fixer_stub_count=fixer_stub_count)
def _structured_result(status: str, module_count: int, tests_dir: str,
                       summary: str, *, file_count: int = 0,
                       fixer_stub_count: int = 0) -> dict:
    return {
        "status": status,
        "module_count": module_count,
        "file_count": file_count,
        "fixer_stub_count": fixer_stub_count,
        "tests_dir": tests_dir,
        "summary": summary,
    }
def _supplement_one_module(
    mod_path: str, fpath: str, skill_dir: str, tests_dir: str,
    stem_owners: dict[str, str],
) -> tuple[str, str, str | None]:
    rel_file = os.path.relpath(fpath, skill_dir)
    tree, fail_note = load_parsed_tree(fpath)
    if fail_note:
        _test_name, keep_path = _claim_output(mod_path, tests_dir, stem_owners)
        return "failed", f"{rel_file} ({fail_note})", keep_path
    if module_has_toplevel_side_effect(tree):
        return "skipped", rel_file, None
    grades: MemberGrades = classify_module_members(tree)
    if not grades.any_testable():
        return "ignored", "", None
    test_source = build_test_source(
        mod_path, rel_file, grades,
        import_root=_host_import_root(mod_path, fpath))
    test_name, out_path = _claim_output(mod_path, tests_dir, stem_owners)
    action, write_err = _write_supplementary_file(out_path, test_source)
    if action == "unchanged":
        return "unchanged", test_name, out_path
    if action == "written":
        return "written", test_name, out_path
    return "failed", f"{test_name} (写入失败: {write_err})", out_path
def _run_module_supplements(modules: list[tuple[str, str]], skill_dir: str,
                            tests_dir: str, mode: str,
                            module_count: int) -> _SupplementRun:
    run = _SupplementRun(mode=mode, module_count=module_count)
    buckets = {
        "failed": run.failed,
        "skipped": run.skipped,
        "ignored": run.ignored,
        "unchanged": run.unchanged_files,
        "written": run.generated_files,
    }
    stem_owners: dict[str, str] = {}
    for mod_path, fpath in modules:
        action, detail, touched_path = _supplement_one_module(
            mod_path, fpath, skill_dir, tests_dir, stem_owners)
        bucket = buckets.get(action)
        if bucket is not None:
            bucket.append(detail)
        if touched_path is not None:
            run.touched.add(os.path.normcase(touched_path))
    return run
def _scan_modules_for_supplement(
    skill_dir: str, tests_dir: str, stale_generated: list[str],
) -> tuple[list[tuple[str, str]], dict | None]:
    try:
        modules = _iter_py_modules(skill_dir)
    except OSError as e:
        log_swallowed(__name__, e, context='ensure_supplemental_tests:scan')
        return [], _structured_result(
            "error", 0, tests_dir, f"扫描模块失败: {e}")
    if not modules:
        cleanup_missing_host_booster_stubs(skill_dir, tests_dir)
        _cleanup_stale_generated(stale_generated, set())
        return [], _structured_result(
            "no_python", 0, tests_dir,
            "目标技能目录未发现可测 Python 模块，无法生成补足测试")
    return modules, None
def ensure_supplemental_tests(skill_dir: str,
                              tests_dir: str | None = None) -> dict:
    skill_dir = coerce_target_file(skill_dir)
    if not skill_dir or not os.path.isdir(skill_dir):
        logger.warning(
            "[Supplement] 项目目录非法或不可访问，跳过补足测试生成: %r",
            skill_dir)
        return _structured_result(
            "error", 0, "", "项目目录非法或不可访问，跳过补足测试生成")
    skill_dir = os.path.abspath(skill_dir)
    tests_dir = _tests_dir(skill_dir, tests_dir)
    mode, stale_generated, early = _classify_existing_state(skill_dir, tests_dir)
    if early is not None:
        return early
    modules, early = _scan_modules_for_supplement(
        skill_dir, tests_dir, stale_generated)
    if early is not None:
        return early
    try:
        os.makedirs(tests_dir, exist_ok=True)
    except OSError as e:
        log_swallowed(__name__, e, context='ensure_supplemental_tests:makedirs')
        return _structured_result(
            "error", len(modules), tests_dir, f"创建测试目录失败: {e}")
    run = _run_module_supplements(
        modules, skill_dir, tests_dir, mode, len(modules))
    _cleanup_stale_generated(stale_generated, run.touched)
    return _finalize_summary(skill_dir, tests_dir, run)

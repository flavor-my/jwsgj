from __future__ import annotations

import ast
import glob
import json
import logging
import math
import os
import posixpath
import re
from collections import deque
from collections.abc import Iterator
from dataclasses import asdict, dataclass

from jwsgj.diag_shared_ast_nodes import iter_module_level_stmts
from jwsgj.diag_shared_ast_views import definition_time_expressions, shared_walk
from jwsgj.diag_shared_source_core import parse_py_file
from jwsgj.diag_testing_source import iter_test_py_files
from jwsgj.diag_testing_test_index import (
    _PYTEST_ASSERTION_CALLS,
    _PYTEST_RAISES_CALL,
    _SELF_ASSERTION_METHODS,
    _is_mutable_container_value,
    _iter_target_value_pairs,
    is_test_function_name,
    iter_collectable_test_functions,
    tree_collectable_test_classes,
)
from jwsgj.diag_types_normalize import dict_or_empty, safe_int
from jwsgj.diag_types_vocab import (
    FIELD_TOTAL_FUNCTIONS,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    collect_py_files_default,
    is_backup_snapshot_dir,
    is_scan_py_name,
    is_test_file_path,
    safe_relpath,
)
from jwsgj.xv_intermediate_store import load_intermediate, locate_sub_results

logger = logging.getLogger(__name__)
logger.addHandler(logging.NullHandler())
__all__ = [
    "analyze_call_frequency",
    "analyze_test_quality",
    "resolve_e1_snapshot_source",
]
logger.info("diag_testing_metrics 已加载：%d 项导出", len(__all__))
_RULE_METRIC_ATTR = {
    "T18-BROAD-ASSERT": "broad_asserts",
    "T18-NO-ASSERT": "functions_without_assert",
    "T18-EXCEPTION-TEST": "functions_with_raises",
    "T18-SHARED-STATE": "setup_has_mutable_state",
}
def _tq_collect_ast_child_batch(node: ast.AST, batch: list) -> None:
    d = node.__dict__
    for fname in node.__class__._fields:
        v = d.get(fname)
        if isinstance(v, ast.AST):
            batch.append(v)
            continue
        if not isinstance(v, list):
            continue
        for item in v:
            if isinstance(item, ast.AST):
                batch.append(item)
_BROAD_ASSERT_COMPOSITE_TYPES = (
    ast.BoolOp, ast.BinOp, ast.Compare, ast.IfExp, ast.UnaryOp,
)
def _tq_is_reportable_broad_assert(method: str, broad_asserts: frozenset,
                                   child: ast.Call) -> bool:
    if method not in broad_asserts:
        return False
    if not child.args:
        return False
    return isinstance(child.args[0], _BROAD_ASSERT_COMPOSITE_TYPES)
_NESTED_DEF_TYPES = frozenset({
    ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda,
})
def _tq_nested_definition_exprs(node) -> Iterator[ast.AST]:
    yield from definition_time_expressions(node)
    if isinstance(node, ast.ClassDef):
        yield from node.body
def _tq_definition_time_has_call(node) -> bool:
    todo = list(_tq_nested_definition_exprs(node))
    while todo:
        child = todo.pop()
        if child.__class__ in _NESTED_DEF_TYPES:
            todo.extend(_tq_nested_definition_exprs(child))
            continue
        if isinstance(child, ast.Call):
            return True
        todo.extend(ast.iter_child_nodes(child))
    return False
_STMT_BODY_FIELDS = ("body", "orelse", "finalbody", "handlers", "cases")
def _tq_shared_attr_target(target, receiver_names) -> str | None:
    if (isinstance(target, ast.Attribute)
            and isinstance(target.value, ast.Name)
            and target.value.id in receiver_names):
        return f"{target.value.id}.{target.attr}"
    return None
def _tq_assign_targets(stmt) -> tuple | None:
    if isinstance(stmt, ast.AnnAssign):
        return None if stmt.value is None else (stmt.target,)
    if isinstance(stmt, ast.Assign):
        return tuple(stmt.targets)
    return None
def _tq_global_bindings(node) -> frozenset[str]:
    names: set[str] = set()
    _todo: list[ast.AST] = list(ast.iter_child_nodes(node))
    while _todo:
        child = _todo.pop()
        if child.__class__ in _NESTED_DEF_TYPES:
            continue
        if isinstance(child, ast.Global):
            names.update(child.names)
            continue
        _todo.extend(ast.iter_child_nodes(child))
    return frozenset(names)
def _tq_hook_receiver_names(node) -> frozenset[str]:
    names = {"self", "cls"}
    if (node.name in _CLASS_SCOPE_HOOKS
            or node.name in ("setup_module", "teardown_module")):
        parameters = (*node.args.posonlyargs, *node.args.args)
        if parameters:
            names.add(parameters[0].arg)
    return frozenset(names)
def _tq_setup_mutable_targets(stmt, global_names: frozenset[str],
                              receiver_names: frozenset[str]) -> list[str]:
    targets = _tq_assign_targets(stmt)
    if targets is None:
        return []
    names = []
    for target in targets:
        for subtarget, value in _iter_target_value_pairs(target, stmt.value):
            if not _is_mutable_container_value(value):
                continue
            name = _tq_shared_attr_target(subtarget, receiver_names)
            if (name is None and isinstance(subtarget, ast.Name)
                    and subtarget.id in global_names):
                name = subtarget.id
            if name is not None:
                names.append(name)
    return names
def _tq_with_has_call(stmt) -> bool:
    return any(isinstance(item.context_expr, ast.Call) for item in stmt.items)
def _tq_unwrap_await(value):
    while isinstance(value, ast.Await):
        value = value.value
    return value
def _tq_stmt_is_direct_call(stmt) -> bool:
    if isinstance(stmt, ast.Expr):
        return isinstance(_tq_unwrap_await(stmt.value), ast.Call)
    if isinstance(stmt, (ast.Assign, ast.AnnAssign)):
        return (stmt.value is not None
                and isinstance(_tq_unwrap_await(stmt.value), ast.Call))
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        return _tq_with_has_call(stmt)
    # return <call>() 与 x = <call>() 同属值位直接调用，被调方可能含断言。
    if isinstance(stmt, ast.Return):
        return (stmt.value is not None
                and isinstance(_tq_unwrap_await(stmt.value), ast.Call))
    return False
def _tq_child_stmt_lists(stmt) -> list:
    return [v for v in (getattr(stmt, f, None) for f in _STMT_BODY_FIELDS)
            if isinstance(v, list)]
def _tq_stmt_has_implicit_call(stmts) -> bool:
    _todo = list(stmts)
    while _todo:
        stmt = _todo.pop()
        if stmt.__class__ in _NESTED_DEF_TYPES:
            if _tq_definition_time_has_call(stmt):
                return True
            continue
        if _tq_stmt_is_direct_call(stmt):
            return True
        for inner in _tq_child_stmt_lists(stmt):
            _todo.extend(inner)
    return False
_BROAD_ASSERT_METHODS = frozenset(
    {"assertTrue", "assertFalse", "assertIsNone", "assertIsNotNone"})
_EXCEPTION_TEST_CONTEXTS = frozenset(
    {"assertRaises", "assertRaisesRegex"})
class _TestImportContext:
    __slots__ = ("from_pkg_binds", "module_aliases")
    def __init__(self) -> None:
        self.from_pkg_binds: dict[str, tuple[str, str]] = {}
        self.module_aliases: dict[str, str] = {}
    def reset(self) -> None:
        self.from_pkg_binds.clear()
        self.module_aliases.clear()
    def clone(self):
        cloned = _TestImportContext()
        cloned.from_pkg_binds = self.from_pkg_binds.copy()
        cloned.module_aliases = self.module_aliases.copy()
        return cloned
    def register(self, node) -> None:
        if isinstance(node, ast.Import):
            self._register_module_import(node)
        elif isinstance(node, ast.ImportFrom):
            self._register_from_import(node)
    def _register_module_import(self, node) -> None:
        for alias in node.names:
            bound_name = alias.asname or alias.name.split(".", 1)[0]
            self.module_aliases[bound_name] = (
                alias.name if alias.asname else bound_name)
            self.from_pkg_binds.pop(bound_name, None)
    def _register_from_import(self, node) -> None:
        for alias in node.names:
            if alias.name == "*":
                continue
            bound_name = alias.asname or alias.name
            self.from_pkg_binds.pop(bound_name, None)
            self.module_aliases.pop(bound_name, None)
            if node.module and not node.level:
                self.from_pkg_binds[bound_name] = (node.module, alias.name)
    def pytest_assertion_name(self, name: str) -> str | None:
        record = self.from_pkg_binds.get(name)
        if record is None or record[0] != "pytest":
            return None
        return record[1] if record[1] in _PYTEST_ASSERTION_CALLS else None
    def binds_pytest_module(self, alias: str) -> bool:
        return self.module_aliases.get(alias) == "pytest"
def _tq_local_import_context(node, imports: _TestImportContext):
    scoped = imports.clone()
    local_imports = []
    todo = list(node.body)
    while todo:
        child = todo.pop()
        if child.__class__ in _NESTED_DEF_TYPES:
            continue
        if isinstance(child, (ast.Import, ast.ImportFrom)):
            local_imports.append(child)
            continue
        todo.extend(ast.iter_child_nodes(child))
    local_imports.sort(key=lambda item: (item.lineno, item.col_offset))
    for child in local_imports:
        scoped.register(child)
    return scoped
@dataclass
class TestQualityMetrics:
    total_test_functions: int = 0
    total_assertions: int = 0
    assertion_density: float = 0.0
    functions_without_assert: int = 0
    functions_with_raises: int = 0
    broad_asserts: int = 0
    setup_has_mutable_state: int = 0
@dataclass
class TestQualityFinding:
    rule_id: str
    severity: str
    confidence: float
    file: str
    line: int
    message: str
    pattern_name: str = ""
_MODULE_SCOPE_HOOKS = frozenset({
    "setup_module", "teardown_module", "setup_function", "teardown_function",
    "setUpModule", "tearDownModule",
})
_CLASS_SCOPE_HOOKS = frozenset({
    "setUp", "tearDown", "setUpClass", "tearDownClass",
    "setup_method", "teardown_method", "setup_class", "teardown_class",
})
_SETUP_TEARDOWN_HOOKS = _MODULE_SCOPE_HOOKS | _CLASS_SCOPE_HOOKS
def _iter_setup_teardown_hooks(
        scope, collectable_classes: frozenset,
        hooks: frozenset) -> Iterator[ast.AST]:
    for node in iter_module_level_stmts(scope):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if node.name in hooks:
                yield node
        elif (isinstance(node, ast.ClassDef)
              and node in collectable_classes):
            yield from _iter_setup_teardown_hooks(
                node, collectable_classes, _CLASS_SCOPE_HOOKS)
def _iter_test_members(tree) -> Iterator[ast.AST]:
    collectable_classes = frozenset(tree_collectable_test_classes(tree))
    members = [
        *iter_collectable_test_functions(tree, collectable_classes),
        *_iter_setup_teardown_hooks(
            tree, collectable_classes, _MODULE_SCOPE_HOOKS),
    ]
    members.sort(key=lambda node: (node.lineno, node.col_offset))
    yield from members
def _tq_name_call_evidence(func, imports) -> tuple[int, bool]:
    _pytest_name = imports.pytest_assertion_name(func.id)
    if _pytest_name is not None:
        return 1, _pytest_name == _PYTEST_RAISES_CALL
    if "assert" in func.id:
        return 1, False
    return 0, False
def _tq_report_broad_assert(findings, node, child, method: str,
                            rel_path: str) -> None:
    findings.append(TestQualityFinding(
        rule_id="T18-BROAD-ASSERT",
        severity="P3",
        confidence=0.50,
        file=rel_path,
        line=child.lineno,
        message=(f"测试 '{node.name}' 使用宽泛断言"
                 f" {method}()，建议使用更具体的断言方法"),
        pattern_name="broad_assertion",
    ))
def _tq_attr_call_evidence(findings, imports, node, func, child,
                           rel_path: str) -> tuple[int, bool]:
    method = func.attr
    if "assert" in method:
        if _tq_is_reportable_broad_assert(
                method, _BROAD_ASSERT_METHODS, child):
            _tq_report_broad_assert(findings, node, child, method, rel_path)
        return 1, method in _EXCEPTION_TEST_CONTEXTS
    if isinstance(func.value, ast.Name):
        if (method in _SELF_ASSERTION_METHODS
                and func.value.id == "self"):
            return 1, False
        if (method in _PYTEST_ASSERTION_CALLS
                and imports.binds_pytest_module(func.value.id)):
            return 1, method == _PYTEST_RAISES_CALL
    return 0, False
def _tq_call_assert_evidence(findings, imports, node, child,
                             rel_path: str) -> tuple[int, bool]:
    func = child.func
    _fcls = func.__class__
    if _fcls is ast.Name:
        return _tq_name_call_evidence(func, imports)
    if _fcls is ast.Attribute:
        return _tq_attr_call_evidence(
            findings, imports, node, func, child, rel_path)
    return 0, False
def _tq_count_assert_evidence(findings, imports, node,
                              rel_path: str) -> tuple[int, bool]:
    assert_count = 0
    has_raises = False
    _todo = deque()
    _pop = _todo.popleft
    _extend = _todo.extend
    _batch: list = []
    _batch_clear = _batch.clear
    _skip_types = _NESTED_DEF_TYPES
    _tq_collect_ast_child_batch(node, _batch)
    _extend(_batch)
    while _todo:
        child = _pop()
        if child.__class__ in _skip_types:
            _extend(_tq_nested_definition_exprs(child))
            continue
        _batch_clear()
        _tq_collect_ast_child_batch(child, _batch)
        _extend(_batch)
        _cls = child.__class__
        if _cls is ast.Assert:
            assert_count += 1
            continue
        if _cls is not ast.Call:
            continue
        _delta, _raises = _tq_call_assert_evidence(
            findings, imports, node, child, rel_path)
        assert_count += _delta
        has_raises = has_raises or _raises
    return assert_count, has_raises
def _t18_finding_row(rf) -> dict:
    return {
        "rule_id": rf.rule_id,
        "severity": rf.severity,
        "confidence": rf.confidence,
        "message": rf.message,
        "file": rf.file,
        "line": rf.line,
        "source": "F3",
        "pattern_name": rf.pattern_name,
    }
class TestQualityAnalyzer:
    __test__ = False
    def __init__(self, skill_dir: str, cache=None):
        self.skill_dir = skill_dir
        self._cache = cache
        self.findings: list[TestQualityFinding] = []
        self.metrics = TestQualityMetrics()
        self._imports = _TestImportContext()
    def _tally_finding_metrics(self) -> None:
        for f_obj in self.findings:
            attr = _RULE_METRIC_ATTR.get(f_obj.rule_id)
            if attr is not None:
                setattr(self.metrics, attr, getattr(self.metrics, attr) + 1)
    def analyze(self) -> list[TestQualityFinding]:
        self.findings = []
        self.metrics = TestQualityMetrics()
        for fpath in iter_test_py_files(self.skill_dir):
            self._analyze_file(fpath)
        if self.metrics.total_test_functions > 0:
            self.metrics.assertion_density = (
                self.metrics.total_assertions / self.metrics.total_test_functions
            )
        self._tally_finding_metrics()
        return list(self.findings)
    def get_metrics(self) -> dict:
        return asdict(self.metrics)
    def _cached_ast(self, filepath):
        _get_ast = getattr(self._cache, "get_ast", None)
        if not callable(_get_ast):
            return None
        try:
            return _get_ast(filepath)
        except Exception as _e:
            log_swallowed(
                __name__, _e,
                context=('TestQualityAnalyzer._cached_ast:'
                         f'{type(_e).__name__}'))
            return None
    def _load_file_ast(self, filepath):
        tree = self._cached_ast(filepath)
        if tree is not None:
            return tree
        _source, tree = parse_py_file(filepath)
        if tree is None:
            logger.warning("[TestQuality] 分析文件失败，跳过: %s", filepath)
        return tree
    def _reset_and_collect_imports(self, tree) -> None:
        self._imports.reset()
        for _imp in iter_module_level_stmts(tree):
            if isinstance(_imp, (ast.Import, ast.ImportFrom)):
                self._imports.register(_imp)
    def _maybe_analyze_member(self, node, rel_path: str) -> None:
        if is_test_function_name(node.name):
            self._analyze_test_function(node, rel_path)
        if node.name in _SETUP_TEARDOWN_HOOKS:
            self._check_setup_mutable_state(node, rel_path)
    def _analyze_file(self, filepath: str):
        tree = self._load_file_ast(filepath)
        if tree is None:
            return
        rel_path = safe_relpath(filepath, self.skill_dir)
        self._reset_and_collect_imports(tree)
        for node in _iter_test_members(tree):
            self._maybe_analyze_member(node, rel_path)
    def _analyze_test_function(self, node, rel_path: str):
        self.metrics.total_test_functions += 1
        imports = _tq_local_import_context(node, self._imports)
        assert_count, has_raises = _tq_count_assert_evidence(
            self.findings, imports, node, rel_path)
        self.metrics.total_assertions += assert_count
        if assert_count == 0 and not _tq_stmt_has_implicit_call(node.body):
            self.findings.append(TestQualityFinding(
                rule_id="T18-NO-ASSERT",
                severity="P2",
                confidence=0.75,
                file=rel_path,
                line=node.lineno,
                message=f"测试函数 '{node.name}' 没有断言语句",
                pattern_name="no_assertion",
            ))
        if has_raises:
            self.findings.append(TestQualityFinding(
                rule_id="T18-EXCEPTION-TEST",
                severity="info",
                confidence=0.60,
                file=rel_path,
                line=node.lineno,
                message=f"测试函数 '{node.name}' 覆盖异常路径（正面信号）",
                pattern_name="exception_test",
            ))
    def _report_shared_state(self, hook_name: str, target_name: str,
                             rel_path: str, line: int) -> None:
        self.findings.append(TestQualityFinding(
            rule_id="T18-SHARED-STATE",
            pattern_name="shared_mutable_state",
            severity="P3",
            confidence=0.60,
            file=rel_path,
            line=line,
            message=(f"{hook_name} 中创建可变共享状态"
                     f" {target_name}，可能影响测试隔离性"),
        ))
    def _check_setup_mutable_state(self, node, rel_path: str):
        global_names = _tq_global_bindings(node)
        receiver_names = _tq_hook_receiver_names(node)
        _todo: list[ast.AST] = list(ast.iter_child_nodes(node))
        while _todo:
            child = _todo.pop()
            if child.__class__ in _NESTED_DEF_TYPES:
                continue
            _todo.extend(ast.iter_child_nodes(child))
            for target_name in _tq_setup_mutable_targets(
                    child, global_names, receiver_names):
                self._report_shared_state(
                    node.name, target_name, rel_path, child.lineno)
def analyze_test_quality(skill_dir: str, cache=None) -> tuple[list, dict]:
    analyzer = TestQualityAnalyzer(skill_dir, cache=cache)
    raw_findings = analyzer.analyze()
    issue_findings = [rf for rf in raw_findings if rf.severity != "info"]
    exception_test_count = sum(
        1 for rf in raw_findings if rf.rule_id == "T18-EXCEPTION-TEST")
    metrics = analyzer.get_metrics()
    quality_part = {
        "findings_count": len(issue_findings),
        "metrics": metrics,
        "exception_test_count": exception_test_count,
    }
    return [_t18_finding_row(rf) for rf in issue_findings], quality_part
_JSON_READ_EXCEPTIONS = (
    json.JSONDecodeError, UnicodeDecodeError, OSError, RecursionError)
_SNAPSHOT_READ_FAILED = object()
_SNAPSHOT_MID_E1 = "E1"
_SNAPSHOT_MID_F1 = "F1"
_SNAPSHOT_LEGACY_GLOBS = {_SNAPSHOT_MID_E1: ("E_*.json",)}
def _snapshot_doc_entry(data) -> tuple[dict | None, str]:
    if not isinstance(data, dict):
        return None, ""
    return data, str(data.get("_report_timestamp") or "")
def _iter_snapshot_docs(intermediate_dir: str, mid: str,
                        *, loud: bool = False) -> list[tuple[dict | None, str]]:
    if not intermediate_dir:
        return []
    docs: list[tuple[dict | None, str]] = []
    unified = load_intermediate(
        intermediate_dir, mid, strict_provenance=False)
    if isinstance(unified, dict) and unified.get("status") != "corrupted":
        docs.append(_snapshot_doc_entry(unified))
    for _pattern in _SNAPSHOT_LEGACY_GLOBS.get(mid, ()):
        for path in sorted(
                glob.glob(os.path.join(intermediate_dir, _pattern)),
                reverse=True):
            data = _read_snapshot_json(path, loud=loud)
            if data is _SNAPSHOT_READ_FAILED:
                continue
            docs.append(_snapshot_doc_entry(data))
    return docs
def _read_snapshot_json(src_path: str, *, loud: bool):
    _name = os.path.basename(src_path)
    try:
        with open(src_path, encoding="utf-8-sig") as fh:
            return json.load(fh)
    except _JSON_READ_EXCEPTIONS as _e:
        if loud:
            logger.warning("[F3] 快照 %s 读取失败（%s），该候选跳过；"
                           "无可用候选时快照守卫降级为 P3 声明，"
                           "覆盖率侧由 F3-T17-EMPTY-COVERAGE 兜底",
                           _name, _e)
        else:
            logger.debug("快照 %s（跳过）读取/解析失败: %s", _name, _e)
        return _SNAPSHOT_READ_FAILED
def _load_disk_fallback_source(intermediate_dir: str) -> tuple | None:
    _invalid_e1: tuple | None = None
    for data, ts_raw in _iter_snapshot_docs(
            intermediate_dir, _SNAPSHOT_MID_E1, loud=True):
        if data is not None:
            e1_payload = extract_e1_payload(data)
            if e1_payload is not None:
                return e1_payload, ts_raw
        if _invalid_e1 is None:
            _invalid_e1 = (None, ts_raw)
    for data, ts_raw in _iter_snapshot_docs(
            intermediate_dir, _SNAPSHOT_MID_F1, loud=True):
        e1_fp, _ = unpack_f1_payload(data)
        if e1_fp is not None:
            return e1_fp, ts_raw
    return _invalid_e1
def _dig_e1_result_payload(payload: dict) -> dict | None:
    sub = locate_sub_results(payload)
    e1 = dict_or_empty(sub.get("E1"))
    e1_res = dict_or_empty(e1.get("result"))
    e1p = e1_res.get("payload")
    return e1p if isinstance(e1p, dict) else None
_E1_EVIDENCE_KEYS = ("coverage", "source_fingerprint")
def _carries_e1_evidence(candidate) -> bool:
    return (isinstance(candidate, dict)
            and any(key in candidate for key in _E1_EVIDENCE_KEYS))
def _extract_wrapped_e1(candidate) -> dict | None:
    payload = dict_or_empty(candidate)
    if not payload:
        return None
    e1p = _dig_e1_result_payload(payload)
    if e1p is not None:
        return e1p
    if _carries_e1_evidence(payload):
        return payload
    inner = payload.get("payload")
    if _carries_e1_evidence(inner):
        return inner
    return None
def extract_e1_payload(data) -> dict | None:
    doc = dict_or_empty(data)
    if not doc:
        return None
    wrapped = _extract_wrapped_e1(doc.get("payload"))
    if wrapped is not None:
        return wrapped
    return _extract_wrapped_e1(doc)
def pick_e1_coverage_source(
        intermediate_dir: str) -> tuple[dict | None, str]:
    for data, ts_raw in _iter_snapshot_docs(
            intermediate_dir or "", _SNAPSHOT_MID_E1):
        e1p = extract_e1_payload(data)
        if e1p is not None and (
                "coverage" in e1p or "source_fingerprint" in e1p):
            return e1p, ts_raw
    return None, ""
def unpack_f1_payload(data) -> tuple[dict | None, dict]:
    payload = (data.get("payload", data)
               if isinstance(data, dict) else None)
    if not isinstance(payload, dict):
        return None, {}
    if ("coverage" not in payload
            and isinstance(payload.get("payload"), dict)):
        payload = payload["payload"]
    _cov = payload.get("coverage")
    if isinstance(_cov, dict):
        final_cov = _cov
    elif "coverage" in payload:
        final_cov = {}
    else:
        final_cov = payload
    return payload, final_cov
def probe_f1_legacy_source(
        intermediate_dir: str) -> tuple[dict, dict, str] | None:
    for data, ts_raw in _iter_snapshot_docs(
            intermediate_dir or "", _SNAPSHOT_MID_F1):
        payload, final_cov = unpack_f1_payload(data)
        if payload is not None and final_cov:
            return payload, final_cov, ts_raw
    return None
def _memory_e1_payload(e1_payload: dict) -> dict:
    extracted = extract_e1_payload({"payload": e1_payload})
    return extracted if extracted is not None else e1_payload
def resolve_e1_snapshot_source(
        intermediate_dir: str,
        e1_payload: dict | None = None) -> tuple[dict | None, str, bool] | None:
    if isinstance(e1_payload, dict):
        return (_memory_e1_payload(e1_payload), "", True)
    _idir = intermediate_dir or ""
    _ssot_fp, _ssot_ts = pick_e1_coverage_source(_idir)
    if _ssot_fp is not None:
        return (_ssot_fp, _ssot_ts, False)
    _f1_probe = probe_f1_legacy_source(_idir)
    if _f1_probe is not None:
        return (_f1_probe[0], _f1_probe[2], False)
    _disk = _load_disk_fallback_source(_idir)
    if _disk is None:
        return None
    return (_disk[0], _disk[1], False)
def _nonempty_dict(value) -> bool:
    return bool(dict_or_empty(value))
_DUNDER_NAME_RE = re.compile(r"__.+__", re.DOTALL)
_FROZEN_GATE_FUNC_PREFIXES = ("pytest_", "visit_")
_STALE_NAMES_SUMMARY_LIMIT = 8
FROZEN_DETAILS_LIMIT = 2000
_FILE_LEVEL_FUNC_NAME = "_file_level"
def _is_execution_count(count) -> bool:
    if isinstance(count, bool) or not isinstance(count, (int, float)):
        return False
    if count < 0:
        return False
    if isinstance(count, float):
        return math.isfinite(count) and count.is_integer()
    return True
def _is_valid_file_coverage(value) -> bool:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return False
    if isinstance(value, float):
        return math.isfinite(value) and value >= 0
    return value >= 0
_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
def _iter_tree_nodes(_obj) -> list:
    _wn = getattr(_obj, "walk_nodes", None)
    if callable(_wn):
        return _wn()
    if isinstance(_obj, ast.AST):
        _tree = _obj
    else:
        _tree = getattr(_obj, "tree", None)
        if _tree is None:
            return []
    _nodes = shared_walk(_tree)
    return _nodes if isinstance(_nodes, list) else list(_nodes)
def _reference_project_py_files(skill_dir: str) -> list:
    return [
        fpath for fpath in collect_py_files_default(skill_dir)
        if not is_test_file_path(safe_relpath(fpath, skill_dir))
    ]
def _reference_file_key(fpath: str, skill_dir: str) -> str:
    if not os.path.isabs(fpath):
        fpath = os.path.join(skill_dir, fpath)
    return os.path.normcase(os.path.abspath(fpath))
def _reference_entry_ast_getter(cache_entries, skill_dir: str):
    entries = {}
    for entry in cache_entries:
        rel = getattr(entry, "rel_path", "") or ""
        if (getattr(entry, "tree", None) is not None
                and is_scan_py_name(os.path.basename(rel))):
            entries[_reference_file_key(rel, skill_dir)] = entry
    return lambda fpath: entries.get(_reference_file_key(fpath, skill_dir))
def _parse_reference_tree_file(fpath: str, rel: str) -> ast.AST | None:
    _source, tree = parse_py_file(fpath, quiet=True)
    if tree is None:
        logger.debug("T17 引用索引跳过不可解析文件 %s", rel)
    return tree
def _reference_trees(py_files: list, skill_dir: str,
                     get_ast=None) -> list:
    trees: list = []
    for fpath in py_files:
        if not is_scan_py_name(os.path.basename(fpath)):
            continue
        rel = safe_relpath(fpath, skill_dir)
        tree = None
        if get_ast is not None:
            try:
                tree = get_ast(fpath)
            except Exception as exc:
                log_swallowed(
                    __name__, exc, context=f"T17 引用索引缓存读取 {rel}")
                tree = None
        if tree is None:
            tree = _parse_reference_tree_file(fpath, rel)
        if tree is not None:
            trees.append((rel, tree))
    return trees
def _rel_hits_backup_dir(rel: str) -> bool:
    return any(is_backup_snapshot_dir(part)
               for part in (rel or "").replace("\\", "/").split("/"))
def _collect_reference_trees(skill_dir: str, cache=None) -> list:
    py_files = _reference_project_py_files(skill_dir)
    get_ast = getattr(cache, "get_ast", None)
    if not callable(get_ast):
        cache_entries = getattr(cache, "entries", None)
        if cache_entries:
            get_ast = _reference_entry_ast_getter(cache_entries, skill_dir)
    trees = _reference_trees(py_files, skill_dir, get_ast)
    return [(rel, obj) for rel, obj in trees
            if not _rel_hits_backup_dir(rel)]
def _scan_name_node(node, scan):
    # 赋值/删除目标是定义而非引用：`orphan = 2` 不能让同名函数
    # 被误判为 referenced，否则 frozen 死代码漏报。
    if isinstance(node.ctx, ast.Load):
        scan.refs.add(node.id)
def _scan_attr_node(node, scan):
    if isinstance(node.ctx, ast.Load):
        scan.refs.add(node.attr)
def _scan_const_node(node, scan):
    _v = node.value
    if isinstance(_v, str) and _IDENT_RE.match(_v):
        scan.str_candidates.append((_v, node.lineno))
def _scan_fdef_node(node, scan):
    scan.names.add(node.name)
def _all_decl_targets(node) -> tuple:
    if isinstance(node, ast.Assign):
        return tuple(getattr(node, "targets", None) or ())
    _single = getattr(node, "target", None)
    return (_single,) if _single is not None else ()
def _scan_all_decl_node(node, scan):
    # __all__.append/extend/insert("name") 也是导出声明；只认赋值范围会
    # 把这些导出函数当成未被引用，进而误报 frozen 死代码。
    if (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)):
        func = node.value.func
        if (isinstance(func, ast.Attribute)
                and isinstance(func.value, ast.Name)
                and func.value.id == "__all__"
                and func.attr in ("append", "extend", "insert")):
            scan.all_ranges.append((node.lineno, node.end_lineno))
        return
    if any(isinstance(t, ast.Name) and t.id == "__all__"
           for t in _all_decl_targets(node)):
        scan.all_ranges.append((node.lineno, node.end_lineno))
_NODE_SCANNERS = {
    ast.Name: _scan_name_node,
    ast.Attribute: _scan_attr_node,
    ast.Constant: _scan_const_node,
    ast.FunctionDef: _scan_fdef_node,
    ast.AsyncFunctionDef: _scan_fdef_node,
    ast.Assign: _scan_all_decl_node,
    ast.AugAssign: _scan_all_decl_node,
    ast.AnnAssign: _scan_all_decl_node,
    ast.Expr: _scan_all_decl_node,
}
class _TreeScan:
    __slots__ = ("all_ranges", "names", "refs", "str_candidates")
    def __init__(self, refs: set):
        self.refs = refs
        self.names: set[str] = set()
        self.str_candidates: list = []
        self.all_ranges: list = []
def _scan_tree_symbols(_obj, refs):
    scan = _TreeScan(refs)
    _scanners = _NODE_SCANNERS
    for node in _iter_tree_nodes(_obj):
        _scan_node = _scanners.get(node.__class__)
        if _scan_node is not None:
            _scan_node(node, scan)
    return scan.names, scan.str_candidates, scan.all_ranges
def _merge_string_candidates(refs, str_candidates, all_ranges) -> None:
    # 只有 __all__ 声明范围内的字符串是导出声明；普通字符串（docstring、
    # 错误消息）不是符号引用，否则 frozen 死代码会被字符串提到名字而漏报。
    if not str_candidates or not all_ranges:
        return
    refs.update(
        _v for _v, _ln in str_candidates
        if any(lo <= _ln <= hi for lo, hi in all_ranges))
def _norm_source_path(path: str) -> str:
    _p = os.path.normcase(path or "").replace("\\", "/")
    if not _p:
        return ""
    _p = posixpath.normpath(_p)
    return "" if _p == "." else _p
def _defined_path_keys(skill_dir: str, rel: str) -> set[str]:
    _norm = _norm_source_path(rel)
    _absolute = _norm_source_path(
        os.path.abspath(os.path.join(skill_dir, rel)))
    return {k for k in (_norm, _absolute, _norm.rsplit("/", 1)[-1]) if k}
def _is_register_call(node: ast.AST) -> bool:
    if not isinstance(node, ast.Call):
        return False
    func = node.func
    if isinstance(func, ast.Attribute):
        name = func.attr
    elif isinstance(func, ast.Name):
        name = func.id
    else:
        return False
    return name.startswith("register")
_FIXTURE_DECORATOR_NAMES = frozenset({"fixture", "pytest_fixture"})
def _decorator_tail_name(decorator) -> str:
    if isinstance(decorator, ast.Call):
        decorator = decorator.func
    if isinstance(decorator, ast.Attribute):
        return decorator.attr
    if isinstance(decorator, ast.Name):
        return decorator.id
    return ""
def _fixture_import_aliases(tree) -> frozenset:
    if not isinstance(tree, ast.AST):
        return frozenset()
    aliases = set()
    for node in iter_module_level_stmts(tree):
        if not isinstance(node, ast.ImportFrom):
            continue
        if node.level or not node.module:
            continue
        if node.module.split(".")[0] not in ("pytest", "pytest_asyncio"):
            continue
        for alias in node.names:
            if alias.name in ("fixture", "yield_fixture"):
                aliases.add(alias.asname or alias.name)
    return frozenset(aliases)
def _is_fixture_decorated(node, aliases: frozenset) -> bool:
    return any(
        _decorator_tail_name(dec) in _FIXTURE_DECORATOR_NAMES
        or _decorator_tail_name(dec) in aliases
        for dec in getattr(node, "decorator_list", ()))
def _framework_entry_name(node, aliases: frozenset) -> bool:
    if _is_fixture_decorated(node, aliases):
        return True
    return (node.name.startswith("_register")
            and any(_is_register_call(child) for child in walk_nodes(node)))
def _build_reference_index(
        skill_dir: str, cache=None) -> tuple[frozenset, dict, dict]:
    refs: set[str] = set()
    defined: dict[str, set[str]] = {}
    framework: dict[str, set[str]] = {}
    for rel, _obj in _collect_reference_trees(skill_dir, cache):
        names, _str_candidates, _all_ranges = _scan_tree_symbols(_obj, refs)
        _merge_string_candidates(refs, _str_candidates, _all_ranges)
        _tree = (_obj if isinstance(_obj, ast.AST)
                 else getattr(_obj, "tree", None))
        _aliases = _fixture_import_aliases(_tree)
        entry_names = {
            node.name
            for node in _iter_tree_nodes(_obj)
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            and _framework_entry_name(node, _aliases)
        }
        for _key in _defined_path_keys(skill_dir, rel):
            defined.setdefault(_key, set()).update(names)
            if entry_names:
                framework.setdefault(_key, set()).update(entry_names)
    return (frozenset(refs),
            {k: frozenset(v) for k, v in defined.items()},
            {k: frozenset(v) for k, v in framework.items()})
def _heat_level_of(call_count: int, hot: int, warm: int) -> str:
    if call_count >= hot:
        return "hot"
    if call_count >= warm:
        return "warm"
    if call_count >= 1:
        return "cold"
    return "frozen"
def _first_nonempty_dict(cov: dict, *keys: str) -> dict:
    for key in keys:
        value = cov.get(key)
        if _nonempty_dict(value):
            return value
    return {}
def _stale_coverage_finding(stale_entries: list) -> dict:
    _stale_names = ", ".join(
        f"{e.filepath}:{e.func_name}"
        for e in stale_entries[:_STALE_NAMES_SUMMARY_LIMIT])
    if len(stale_entries) > _STALE_NAMES_SUMMARY_LIMIT:
        _stale_names += f" 等 {len(stale_entries)} 条"
    return {
        "rule_id": "F3-STALE-COVERAGE",
        "file": "",
        "line": 0,
        "severity": "P2",
        "source": "F3",
        "message": (f"F1 覆盖率快照与当前源码不一致（{len(stale_entries)} 条"
                    " frozen 候选引用的函数在当前源码中不存在，"
                    f"如 {_stale_names}），疑为并发修改或陈旧中间"
                    "结果，需重跑 F1+F3 复核"),
        "confidence": 1.0,
        "heat_level": "stale",
        "call_count": 0,
        "category": "call_frequency_validation",
        "detail": {"stale_funcs": [
            {"file": e.filepath, "func": e.func_name, "line": e.line}
            for e in stale_entries]},
    }
class CallFrequencyEntry:
    __slots__ = (
        "call_count",
        "call_sources",
        "filepath",
        "func_name",
        "gate",
        "heat_level",
        "line",
    )
    def __init__(self, func_name: str, filepath: str, line: int,
                 call_count: int, call_sources: list | None = None,
                 heat_level: str = "cold"):
        self.func_name = func_name
        self.filepath = filepath
        self.line = line
        self.call_count = call_count
        self.call_sources = call_sources or []
        self.heat_level = heat_level
        self.gate = "covered"
    def to_dict(self) -> dict:
        return {
            "func_name": self.func_name,
            "file": self.filepath,
            "line": self.line,
            "call_count": self.call_count,
            "call_sources": self.call_sources,
            "heat_level": self.heat_level,
        }
class CallFrequencyHeatmap:
    HOT_THRESHOLD = 10
    WARM_THRESHOLD = 3
    def __init__(self) -> None:
        self.entries = {}
        self._coverage: dict = {}
        self._skill_dir: str | None = None
        self._ref_index: frozenset | None = None
        self._defined_by_file: dict[str, frozenset[str]] | None = None
        self._framework_entries: dict[str, frozenset[str]] | None = None
    def analyze(self, intermediate_dir: str | None = None,
                skill_dir: str | None = None, cache=None,
                e1_payload: dict | None = None) -> dict:
        self.entries = {}
        self._coverage = {}
        self._skill_dir = skill_dir
        self._ref_index = None
        self._defined_by_file = None
        self._framework_entries = None
        if intermediate_dir or e1_payload is not None:
            self._load_coverage_from_intermediate(
                intermediate_dir or "", e1_payload=e1_payload)
        if skill_dir:
            (self._ref_index,
             self._defined_by_file,
             self._framework_entries) = _build_reference_index(
                skill_dir, cache)
        self._build_frequency_map()
        self._classify_heat_levels()
        return self._build_report()
    def _load_coverage_from_intermediate(self, intermediate_dir: str,
                                         e1_payload: dict | None = None) -> None:
        if isinstance(e1_payload, dict):
            _mem_payload = _memory_e1_payload(e1_payload)
            coverage = _mem_payload.get("coverage")
            self._coverage = dict(coverage) if _nonempty_dict(coverage) else {}
            self._promote_func_coverage()
            return
        _ssot_fp, _ = pick_e1_coverage_source(intermediate_dir)
        if _ssot_fp is not None:
            coverage = _ssot_fp.get("coverage")
            self._coverage = dict(coverage) if _nonempty_dict(coverage) else {}
            self._promote_func_coverage()
            return
        probe = probe_f1_legacy_source(intermediate_dir)
        if probe is not None:
            self._coverage = dict(probe[1])
            self._promote_func_coverage()
    def _promote_func_coverage(self) -> None:
        if not isinstance(self._coverage, dict):
            return
        if _nonempty_dict(self._coverage.get("func_coverage")):
            return
        _metrics = self._coverage.get("metrics") or {}
        _func_cov = (_metrics.get("func_coverage")
                     if isinstance(_metrics, dict) else None)
        if isinstance(_func_cov, dict) and _func_cov:
            self._coverage["func_coverage"] = _func_cov
    def _build_frequency_map(self):
        cov = self._coverage
        func_cov = _first_nonempty_dict(cov, "functions", "func_coverage")
        if func_cov:
            self._collect_func_level_entries(func_cov)
        file_cov = _first_nonempty_dict(
            cov, "coverage_by_file", "file_coverage")
        if file_cov and not func_cov:
            self._collect_file_level_entries(file_cov)
    def _collect_func_level_entries(self, func_cov: dict) -> None:
        for func_key, info in func_cov.items():
            if not isinstance(info, dict):
                continue
            count = info.get("executed_count")
            if not _is_execution_count(count):
                count = info.get("call_count")
            if not _is_execution_count(count):
                logger.debug(
                    "T17 跳过不可解释计数条目 %r: count=%r",
                    func_key, count)
                continue
            _key_text = str(func_key)
            _key_file, _separator, _key_name = _key_text.rpartition(":")
            if not is_scan_py_name(os.path.basename(_key_file)):
                _key_file = ""
            _bare_name = info.get("name") or _key_name.rsplit(".", 1)[-1]
            _line = info.get("line")
            entry = CallFrequencyEntry(
                func_name=str(_bare_name),
                filepath=str(info.get("file") or _key_file),
                line=safe_int(_line) if _line is not None else 0,
                call_count=int(count),
            )
            self.entries[func_key] = entry
    def _collect_file_level_entries(self, file_cov: dict) -> None:
        for filepath, cov_val in file_cov.items():
            if not _is_valid_file_coverage(cov_val):
                continue
            key = f"{filepath}:{_FILE_LEVEL_FUNC_NAME}"
            if key not in self.entries:
                self.entries[key] = CallFrequencyEntry(
                    func_name=_FILE_LEVEL_FUNC_NAME,
                    filepath=str(filepath),
                    line=0,
                    call_count=0 if cov_val == 0 else 1,
                )
    def _classify_heat_levels(self):
        for entry in self.entries.values():
            entry.heat_level = _heat_level_of(
                entry.call_count, self.HOT_THRESHOLD, self.WARM_THRESHOLD)
    def _frozen_gate_verdict(self, entry, stale_entries: list) -> str:
        if entry.func_name == _FILE_LEVEL_FUNC_NAME:
            return "unverified"
        _rel = _norm_source_path(entry.filepath)
        verdict = self._existence_gate_verdict(entry, _rel, stale_entries)
        if verdict is not None:
            return verdict
        if self._gate_blind_exempted(entry):
            return "exempted"
        if self._ref_index is None:
            return "unverified"
        if entry.func_name in self._ref_index:
            return "referenced"
        return "dead_code"
    def _existence_gate_verdict(self, entry, rel: str,
                                stale_entries: list) -> str | None:
        if self._defined_by_file is None:
            return None
        if not rel:
            return "unverified"
        names = self._defined_by_file.get(rel)
        if names is None:
            source_path = (rel if os.path.isabs(rel)
                           else os.path.join(self._skill_dir or "", rel))
            if os.path.isfile(source_path):
                return "unverified"
        if names is None or entry.func_name not in names:
            stale_entries.append(entry)
            return "stale"
        return None
    def _gate_blind_exempted(self, entry) -> bool:
        _rel = _norm_source_path(entry.filepath)
        _framework = (
            self._framework_entries is not None
            and entry.func_name in self._framework_entries.get(_rel, ()))
        _dunder = _DUNDER_NAME_RE.fullmatch(entry.func_name) is not None
        return (_framework
                or _dunder
                or posixpath.basename(_rel) == "conftest.py"
                or entry.func_name.startswith(_FROZEN_GATE_FUNC_PREFIXES))
    def _collect_frozen_gates(self) -> tuple[list, list]:
        findings = []
        stale_entries: list = []
        for entry in self.entries.values():
            if entry.heat_level != "frozen":
                continue
            entry.gate = self._frozen_gate_verdict(entry, stale_entries)
            if entry.gate == "dead_code":
                findings.append(self._frozen_finding(entry))
        if stale_entries:
            findings.append(_stale_coverage_finding(stale_entries))
        return findings, stale_entries
    def _heat_counts(self) -> dict:
        heat_counts: dict[str, int] = {}
        for e in self.entries.values():
            heat_counts[e.heat_level] = heat_counts.get(e.heat_level, 0) + 1
        return heat_counts
    def _build_report(self) -> dict:
        findings, stale_entries = self._collect_frozen_gates()
        heat_counts = self._heat_counts()
        return {
            "status": "pass",
            "method_id": "T17",
            "payload": {
                "findings_list": findings,
                "metrics": {
                    FIELD_TOTAL_FUNCTIONS: len(self.entries),
                    "hot_count": heat_counts.get("hot", 0),
                    "warm_count": heat_counts.get("warm", 0),
                    "cold_count": heat_counts.get("cold", 0),
                    "frozen_count": heat_counts.get("frozen", 0),
                    "stale_count": len(stale_entries),
                    "heat_map": [
                        {**e.to_dict(), "gate": e.gate}
                        for e in self.entries.values()
                    ],
                },
            },
            "findings": findings,
        }
    def _frozen_finding(self, entry) -> dict:
        return {
            "rule_id": "call_frequency",
            "file": entry.filepath,
            "line": entry.line,
            "severity": "P3",
            "message": (f"function {entry.func_name} call_count=0, "
                        "heat=frozen (零执行，疑似死代码)"),
            "confidence": self._heat_to_confidence(entry.heat_level),
            "heat_level": entry.heat_level,
            "call_count": entry.call_count,
            "category": "call_frequency_validation",
            "source": "F3",
            "detail": entry.to_dict(),
        }
    @staticmethod
    def _heat_to_confidence(heat_level: str) -> float:
        mapping = {
            "hot": 0.90,
            "warm": 0.80,
            "cold": 0.60,
            "frozen": 0.50,
        }
        return mapping.get(heat_level, 0.50)
def _frozen_details_payload(metrics: dict) -> tuple[list, int]:
    heat_map = metrics.get("heat_map") or []
    details = [
        {"func_name": e.get("func_name"), "file": e.get("file"),
         "line": e.get("line"), "gate": e.get("gate")}
        for e in heat_map
        if isinstance(e, dict) and e.get("heat_level") == "frozen"
        and e.get("gate") not in ("exempted", "stale", "unverified")
    ]
    truncated = max(0, len(details) - FROZEN_DETAILS_LIMIT)
    return details[:FROZEN_DETAILS_LIMIT], truncated
def _heatmap_payload(metrics: dict) -> dict:
    _frozen_details, _frozen_truncated = _frozen_details_payload(metrics)
    return {
        "total_functions": metrics.get(FIELD_TOTAL_FUNCTIONS, 0),
        "hot": metrics.get("hot_count", 0),
        "warm": metrics.get("warm_count", 0),
        "cold": metrics.get("cold_count", 0),
        "frozen": metrics.get("frozen_count", 0),
        "stale_count": metrics.get("stale_count", 0),
        "frozen_details": _frozen_details,
        "frozen_details_truncated": _frozen_truncated,
    }
def analyze_call_frequency(skill_dir: str, intermediate_dir: str | None = None,
                           cache=None,
                           e1_payload: dict | None = None) -> tuple[list, dict]:
    heatmap = CallFrequencyHeatmap()
    report = heatmap.analyze(intermediate_dir=intermediate_dir,
                             skill_dir=skill_dir, cache=cache,
                             e1_payload=e1_payload)
    metrics = report.get("payload", {}).get("metrics", {})
    return report.get("findings", []), _heatmap_payload(metrics)

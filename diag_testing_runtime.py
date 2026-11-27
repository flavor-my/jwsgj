from __future__ import annotations

import ast
import configparser
import importlib
import importlib.util
import json
import logging
import os
import subprocess as _sp
import sys
import time
import unittest
from collections import Counter, defaultdict, deque
from concurrent.futures import ThreadPoolExecutor
from contextlib import ExitStack
from dataclasses import dataclass

from jwsgj.build_text_frontmatter import skill_md_verdict
from jwsgj.diag_self_check import current_process_rss_mb, ensure_deps
from jwsgj.diag_testing_import_audit import (
    analyze_import_topology,
    annotate_structure_metrics,
    broken_cross_call_findings,
    collect_cross_module_calls,
    collect_import_side_effects,
    package_identity,
    package_module_dotted,
    resolve_broken_cross_calls,
    root_init_entry,
    scan_entry_import_findings,
)
from jwsgj.diag_testing_source import (
    FileCache,
    FileEntry,
    entry_rel_path,
    get_internal_modules,
    iter_module_binding_nodes,
    iter_test_py_files,
    nodes_where,
    own_scope_loaded_names,
    resolve_file_cache,
    skill_has_nested_sources,
)
from jwsgj.diag_testing_test_index import (
    PytestSummaryResult,
    QualityRun,
    TestQualityVisitor,
    collect_test_entries,
    collect_test_findings,
    detect_test_smells,
    finalize_test_quality,
    parse_pytest_summary,
)
from jwsgj.diag_types_defs import TestMethodResult, scan_issue
from jwsgj.log_config import log_swallowed, timed_log
from jwsgj.runtime_paths import subprocess_noartifact_env
from jwsgj.runtime_scope import (
    DIAG_OUT_OF_SCOPE_DIRS,
    SCAN_IGNORE_DIRS,
    is_backup_snapshot_dir,
    is_test_file_path,
    is_test_source_basename,
    isolated_import_scope,
    parse_timeout_env,
)
from jwsgj.skill_profile import LAYOUT_SCRIPTS, detect_layout

logger = logging.getLogger(__name__)
__all__ = [
    'config_syntax_valid',
    'run_e2e_tests',
    'run_integration_tests',
    'run_unit_tests',
]
_E2E_FAIL_PENALTY = 30
_REACHABILITY_UNREACHABLE_RATIO = 0.3
def _coerce_skill_dir(skill_dir) -> str | None:
    try:
        decoded = os.fsdecode(skill_dir)
    except (TypeError, ValueError) as exc:
        logger.debug("技能目录不可归一 %r: %s", skill_dir, exc)
        return None
    if not decoded.strip():
        logger.debug("技能目录为空，不按进程 cwd 推断测试目标")
        return None
    return decoded
_WORKFLOW_TEST_KEYS = (
    ('import', 'full_import'),
    ('entry_access', 'entry_functions'),
    ('version', 'version_accessible'),
    ('api_consistency', 'all_consistency'),
    ('config', 'config_files'),
    ('call_chain', 'call_chain_integrity'),
    ('data_flow', 'data_flow_integrity'),
    ('error_handling', 'error_propagation'),
    ('reachability', 'reachability'),
    ('module_parse', 'all_modules_parse'),
)
def _workflow_categories(e2e_results: list) -> dict:
    test_names = {item.get('test') for item in e2e_results
                  if isinstance(item, dict)
                  and isinstance(item.get('test'), str)}
    return {category: test_key in test_names
            for category, test_key in _WORKFLOW_TEST_KEYS}
def _stmt_is_recovery(stmt) -> bool:
    if isinstance(stmt, (ast.Pass, ast.Raise)):
        return False
    return not (isinstance(stmt, ast.Expr)
                and isinstance(getattr(stmt, 'value', None), ast.Constant))
def _handler_is_recovery(handler) -> bool:
    body = list(getattr(handler, 'body', ()) or ())
    if body and isinstance(body[-1], ast.Raise):
        return False
    return any(_stmt_is_recovery(stmt) for stmt in body)
def _error_recovery_stats(cache) -> tuple:
    has_fallback = 0
    total_except_blocks = 0
    for entry in cache.valid_entries:
        if is_test_file_path(entry_rel_path(entry)):
            continue
        for node in nodes_where(entry, (ast.ExceptHandler,)):
            total_except_blocks += 1
            has_fallback += _handler_is_recovery(node)
    return has_fallback, total_except_blocks
def _e2e_finding_message(item: dict) -> str:
    msg = item.get('message') or ''
    if msg:
        return msg
    extra = [f"{k}={v}" for k, v in item.items()
             if k not in ('test', 'status') and v not in (None, '', 0)]
    return '; '.join(extra[:4]) or str(item.get('test') or '')
def _e2e_finding_record(item: dict) -> dict:
    test = item.get('test') or 'e2e_test'
    line = item.get('line')
    if not isinstance(line, int) or isinstance(line, bool):
        line = 0
    return scan_issue(
        item.get('file') or item.get('module') or '?',
        line,
        test,
        'P1' if item.get('status') == 'fail' else 'P2',
        _e2e_finding_message(item),
        rule_family='e2e_test',
        rule_id=item.get('test') or 'e2e_unknown',
        category='e2e_test',
    )
def _normalize_e2e_findings(e2e_results: list) -> list:
    normalized_findings = []
    for item in e2e_results:
        if not isinstance(item, dict):
            normalized_findings.append(item)
            continue
        if item.get('status') not in ('fail', 'warn'):
            continue
        normalized_findings.append(_e2e_finding_record(item))
    return normalized_findings
def _finalize_e2e_results(result, e2e_results, cache, start):
    status_counts = Counter(
        item.get("status") for item in e2e_results
        if isinstance(item, dict) and isinstance(item.get("status"), str))
    passed = status_counts["pass"]
    warned = status_counts["warn"]
    failed = status_counts["fail"]
    total = len(e2e_results)
    skipped = max(0, total - passed - warned - failed)
    workflow_categories = _workflow_categories(e2e_results)
    workflow_completeness = (
        sum(workflow_categories.values()) / max(len(workflow_categories), 1) * 100
    )
    has_fallback, total_except_blocks = _error_recovery_stats(cache)
    recovery_rate = has_fallback / max(total_except_blocks, 1) * 100
    result.metrics = {
        "total_tests": total,
        "passed": passed,
        "warned": warned,
        "failed": failed,
        "skipped": skipped,
        "workflow_completeness_pct": round(workflow_completeness, 1),
        "error_recovery_rate": round(recovery_rate, 1),
        "total_except_blocks": total_except_blocks,
        "fallback_handlers": has_fallback,
    }
    result.findings = _normalize_e2e_findings(e2e_results)
    result.status, result.score, result.summary = _score_e2e_outcome(
        passed, warned, failed, total)
    return result.finish(start)
def _score_e2e_outcome(passed: int, warned: int, failed: int,
                       total: int) -> tuple[str, int, str]:
    if total <= 0:
        return "skip", 0, "端到端测试无可评估项"
    skipped = max(0, total - passed - warned - failed)
    _skip_tail = f", {skipped} 项跳过" if skipped else ""
    if failed == 0 and warned == 0:
        if passed == 0:
            return "skip", 0, f"端到端测试无可评估项{_skip_tail}"
        if skipped:
            return "pass", 100, f"端到端测试 {passed} 项通过{_skip_tail}"
        return "pass", 100, f"端到端测试全部通过 ({passed}/{total})"
    if failed == 0:
        return "pass", 80, f"端到端测试 {passed} 通过, {warned} 警告{_skip_tail}"
    return "warn", max(0, 100 - failed * _E2E_FAIL_PENALTY), (
        f"端到端测试 {passed} 通过, {failed} 失败{_skip_tail}")
def _import_chain_failure_record(test: str, detail: str) -> dict:
    detail = detail[:300]
    return {"test": test, "status": "fail", "error": detail,
            "file": "__init__.py", "message": detail}
def _append_import_chain_failure(e2e_results: list, exc: BaseException) -> None:
    passed_import = any(
        isinstance(r, dict) and r.get("test") == "full_import"
        and r.get("status") == "pass" for r in e2e_results)
    test = "post_import_checks" if passed_import else "full_import"
    e2e_results.append(_import_chain_failure_record(test, str(exc)))
_MODULE_ATTR_MISSING = object()
def _module_attr(mod, name: str):
    try:
        return getattr(mod, name)
    except Exception as _exc:  # noqa: BLE001
        logger.debug("模块属性不可读 %s.%s: %s",
                     getattr(mod, '__name__', '?'), name, _exc)
        return _MODULE_ATTR_MISSING
def _module_dir(mod) -> list[str]:
    try:
        return dir(mod)
    except Exception as _exc:  # noqa: BLE001
        logger.debug("模块目录不可读 %s: %s",
                     getattr(mod, '__name__', '?'), _exc)
        return []
def _entry_function_surface(mod, *, defer: bool) -> dict:
    entry_funcs = [name for name in _module_dir(mod)
                   if not name.startswith('_')
                   and callable(_module_attr(mod, name))]
    if entry_funcs:
        return {"test": "entry_functions", "status": "pass",
                "count": len(entry_funcs)}
    if defer:
        return {"test": "entry_functions", "status": "skip",
                "message": "非根包布局：入口由具体脚本/模块检查"}
    return {"test": "entry_functions", "status": "warn",
            "message": "无公开入口函数"}
def _version_surface(mod, *, defer: bool) -> dict:
    version = _module_attr(mod, '__version__')
    if (version is not _MODULE_ATTR_MISSING and version is not None
            and str(version).strip()):
        return {"test": "version_accessible", "status": "pass",
                "version": str(version)}
    if defer:
        return {"test": "version_accessible", "status": "skip",
                "message": "非根包布局：版本由 SKILL.md/frontmatter 承载"}
    return {"test": "version_accessible", "status": "warn",
            "message": "无 __version__"}
def _export_surface(mod) -> dict:
    exports = _module_attr(mod, '__all__')
    if exports is _MODULE_ATTR_MISSING:
        return {"test": "all_consistency", "status": "skip",
                "message": "无 __all__"}
    if isinstance(exports, (str, bytes, bytearray)):
        return {"test": "all_consistency", "status": "fail",
                "message": "__all__ 必须是字符串名称序列，不能是单个字符串"}
    try:
        export_items = tuple(exports)
    except Exception as exc:  # noqa: BLE001
        logger.debug("__all__ 不可迭代: %s", exc)
        return {"test": "all_consistency", "status": "fail",
                "message": "__all__ 不是可迭代名称序列"}
    if any(not isinstance(name, str) for name in export_items):
        return {"test": "all_consistency", "status": "fail",
                "message": "__all__ 必须只包含字符串名称"}
    missing = sorted({name for name in export_items
                      if _module_attr(mod, name) is _MODULE_ATTR_MISSING})
    if missing:
        return {"test": "all_consistency", "status": "fail",
                "message": f"__all__ 引用不存在的名称: {missing}"}
    return {"test": "all_consistency", "status": "pass"}
def _check_module_attribute_surface(mod, *, defer: bool) -> list:
    return [_entry_function_surface(mod, defer=defer),
            _version_surface(mod, defer=defer), _export_surface(mod)]
def _e2e_test_import_chain(skill_dir: str, skill_name: str) -> list:
    e2e_results = []
    defer_root_surface = skill_has_nested_sources(skill_dir)
    with isolated_import_scope(skill_dir, skill_name=skill_name):
        try:
            init_path = os.path.join(skill_dir, "__init__.py")
            if os.path.isfile(init_path):
                spec = importlib.util.spec_from_file_location(skill_name, init_path)
                if spec and spec.loader:
                    mod = importlib.util.module_from_spec(spec)
                    sys.modules[skill_name] = mod
                    spec.loader.exec_module(mod)
                    e2e_results.append({"test": "full_import", "status": "pass"})
                    e2e_results.extend(_check_module_attribute_surface(
                        mod, defer=defer_root_surface))
                else:
                    e2e_results.append({
                        "test": "full_import", "status": "skip",
                        "file": "__init__.py",
                        "message": "无法构建模块导入规格，导入链未执行",
                    })
            elif defer_root_surface:
                e2e_results.append({
                    "test": "full_import", "status": "skip",
                    "file": "__init__.py",
                    "message": "脚本/src/命名空间布局无需根包导入，改查具体模块",
                })
            else:
                e2e_results.append(_import_chain_failure_record(
                    "full_import", "缺少 __init__.py"))
        except (ImportError, AttributeError, SyntaxError, TypeError, ValueError, OSError, RuntimeError) as e:
            logger.debug("suppressed Exception: %s", e)
            _append_import_chain_failure(e2e_results, e)
        except SystemExit as e:
            logger.warning("e2e import chain: 被测包模块级退出: %s", e)
            _append_import_chain_failure(
                e2e_results,
                RuntimeError(f"模块导入中调用退出: SystemExit({e.code})"))
        except Exception as e:  # noqa: BLE001
            logger.warning("e2e import chain: 被测包模块级异常: %s", e)
            _append_import_chain_failure(e2e_results, e)
    return e2e_results
def _e2e_test_skill_md(skill_dir: str) -> list:
    e2e_results = []
    skill_md = os.path.join(skill_dir, "SKILL.md")
    try:
        if not os.path.isfile(skill_md):
            e2e_results.append({"test": "skill_md_valid", "status": "skip", "message": "无 SKILL.md"})
            return e2e_results
        with open(skill_md, encoding='utf-8') as f:
            content = f.read()
        status, message = skill_md_verdict(content)
        e2e_results.append({"test": "skill_md_valid", "status": status,
                            "message": message})
    except (OSError, UnicodeDecodeError) as e:
        logger.debug("suppressed OSError/UnicodeDecodeError: %s", e)
        e2e_results.append({"test": "skill_md_valid", "status": "fail", "error": str(e)})
    return e2e_results
def _e2e_test_module_parse(cache: FileCache) -> list:
    e2e_results = []
    parsed = 0
    failed = 0
    for entry in cache.entries:
        if entry.is_init and entry.rel_path.replace('\\', '/') == '__init__.py':
            continue
        if entry.tree is None:
            failed += 1
        else:
            parsed += 1
    if failed == 0:
        e2e_results.append({"test": "all_modules_parse", "status": "pass",
                            "count": parsed})
    else:
        e2e_results.append({"test": "all_modules_parse", "status": "fail",
                            "failed": failed})
    return e2e_results
def _e2e_test_call_chain(cache: FileCache) -> list:
    findings = broken_cross_call_findings(cache)
    if not findings:
        return [{"test": "call_chain_integrity", "status": "pass"}]
    details = [str(item.get('symbol') or item.get('message') or '')
               for item in findings]
    return [{"test": "call_chain_integrity", "status": "warn",
             "broken": len(findings), "details": details[:5]}]
_PLACEHOLDER_RAISE_NAMES = frozenset({'NotImplementedError', 'NotImplemented'})
def _raise_target_name(stmt: ast.Raise) -> str | None:
    exc = stmt.exc
    if isinstance(exc, ast.Call):
        exc = exc.func
    if isinstance(exc, ast.Name):
        return exc.id
    if isinstance(exc, ast.Attribute):
        return exc.attr
    return None
def _is_placeholder_stmt(stmt) -> bool:
    if isinstance(stmt, ast.Pass):
        return True
    if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant):
        return stmt.value.value is Ellipsis
    if isinstance(stmt, ast.Raise):
        return _raise_target_name(stmt) in _PLACEHOLDER_RAISE_NAMES
    return False
def _is_abstract_body(node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    body = list(node.body)
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) \
            and isinstance(body[0].value.value, str):
        body = body[1:]
    if not body:
        return True
    return all(_is_placeholder_stmt(stmt) for stmt in body)
def _func_def_record(node, entry) -> tuple:
    params = [arg.arg for arg in
              (*node.args.posonlyargs, *node.args.args, node.args.vararg,
               *node.args.kwonlyargs, node.args.kwarg)
              if arg is not None and arg.arg and arg.arg not in ('self', 'cls')]
    return node, params, own_scope_loaded_names(node), entry
def _data_flow_scope_key(entry) -> str:
    return entry_rel_path(entry).replace('\\', '/')
def _collect_func_defs_and_arg_calls(cache) -> tuple:
    func_defs = []
    called_with_args: set = set()
    _def_types = (ast.FunctionDef, ast.AsyncFunctionDef)
    for entry in cache.valid_entries:
        if is_test_file_path(entry_rel_path(entry)):
            continue
        _scope_key = _data_flow_scope_key(entry)
        for node in nodes_where(entry, _def_types + (ast.Call,)):
            if isinstance(node, _def_types):
                func_defs.append(_func_def_record(node, entry))
            elif (isinstance(node.func, ast.Name)
                  and (node.args or node.keywords)):
                called_with_args.add((_scope_key, node.func.id))
    return func_defs, called_with_args
_COMPAT_DOC_MARKERS = ("兼容", "compat", "deprecated", "别名", " alias")
def _documented_compat_param(node, name: str) -> bool:
    doc = ast.get_docstring(node) or ""
    if not doc or name not in doc:
        return False
    lowered = doc.lower()
    return any(marker in lowered for marker in _COMPAT_DOC_MARKERS)
def _data_flow_broken(node, params, used, called_with_args,
                      scope_key: str) -> bool:
    non_ud = [name for name in params if not name.startswith('_')]
    if not non_ud or any(p in used for p in non_ud):
        return False
    if all(_documented_compat_param(node, p) for p in non_ud):
        return False
    if (scope_key, node.name) not in called_with_args:
        return False
    return not _is_abstract_body(node)
def _e2e_test_data_flow(cache: FileCache) -> list:
    e2e_results = []
    func_defs, called_with_args = _collect_func_defs_and_arg_calls(cache)
    data_flow_issues = 0
    issue_details: list = []
    for node, params, used, entry in func_defs:
        if not _data_flow_broken(
                node, params, used, called_with_args,
                _data_flow_scope_key(entry)):
            continue
        non_ud = [name for name in params if not name.startswith('_')]
        data_flow_issues += 1
        issue_details.append(
            f"{entry_rel_path(entry)}:{node.lineno} {node.name}"
            f"({', '.join(non_ud)})"
        )
    if data_flow_issues == 0:
        e2e_results.append({"test": "data_flow_integrity", "status": "pass"})
    else:
        e2e_results.append({"test": "data_flow_integrity", "status": "warn",
                            "broken_data_flow_functions": data_flow_issues,
                            "details": issue_details[:10]})
    return e2e_results
def _e2e_test_error_propagation(cache: FileCache) -> list:
    e2e_results = []
    raise_count = 0
    except_count = 0
    for entry in cache.valid_entries:
        if is_test_file_path(entry_rel_path(entry)):
            continue
        for node in nodes_where(entry, (ast.Raise, ast.ExceptHandler)):
            raise_count += isinstance(node, ast.Raise)
            except_count += isinstance(node, ast.ExceptHandler)
    if except_count == 0 and raise_count > 5:
        e2e_results.append({"test": "error_propagation", "status": "warn",
                            "message": f"{raise_count} 个 raise 但 0 个 except 处理器"})
    else:
        e2e_results.append({"test": "error_propagation", "status": "pass",
                            "raises": raise_count, "excepts": except_count})
    return e2e_results
def _e2e_test_reachability(cache: FileCache) -> list:
    e2e_results = []
    package_root = package_identity(
        getattr(cache, 'skill_dir', '') or '')[0]
    init_entry = root_init_entry(cache, package_root)
    init_tree = init_entry.tree if init_entry else None
    if init_tree is None:
        e2e_results.append({"test": "reachability", "status": "skip", "message": "无 __init__.py"})
        return e2e_results
    if not cache.internal_mods:
        e2e_results.append({"test": "reachability", "status": "skip", "message": "无内部模块"})
        return e2e_results
    reach_mods = _core_reach_mods(cache)
    if not reach_mods:
        e2e_results.append({"test": "reachability", "status": "skip",
                            "message": "无生产模块（仅测试模块，可达性不适用）"})
        return e2e_results
    graph = _build_reach_graph(cache, reach_mods)
    lazy_registered = _lazy_registered_mods(cache, reach_mods)
    visited = _bfs_reachable(graph, {'__init__'} | lazy_registered)
    total = len(reach_mods)
    unreachable = reach_mods - visited
    if len(unreachable) / max(total, 1) <= _REACHABILITY_UNREACHABLE_RATIO:
        e2e_results.append({"test": "reachability", "status": "pass",
                            "reachable": total - len(unreachable), "total": total})
    else:
        sample = sorted(unreachable)[:5]
        e2e_results.append({"test": "reachability", "status": "warn",
                            "message": f"{len(unreachable)}/{total} 内部模块无法从 __init__ 可达 "
                                       f"(示例: {', '.join(sample)})"})
    return e2e_results
def _bfs_reachable(graph: dict, seeds: set) -> set:
    visited = set(seeds)
    queue = deque(visited)
    while queue:
        for neighbor in graph.get(queue.popleft(), ()):
            if neighbor not in visited:
                visited.add(neighbor)
                queue.append(neighbor)
    return visited
def _core_reach_mods(cache) -> set:
    core_stems: set = set()
    tests_stems: set = set()
    for e in cache.valid_entries:
        if not e.mod_stem:
            continue
        if is_test_file_path(entry_rel_path(e)):
            tests_stems.add(e.mod_stem)
        else:
            core_stems.add(e.mod_stem)
    return cache.internal_mods - (tests_stems - core_stems)
def _import_edge_target(imp, reach_mods: set) -> str | None:
    module = imp.get('module') or ''
    name = imp.get('name') or ''
    module_stem = module.split('.')[-1] if module else ''
    name_stem = name.split('.')[-1] if name else ''
    stem = module_stem or name_stem
    if stem in reach_mods:
        return stem
    if module and '.' not in module and name_stem in reach_mods:
        return name_stem
    return None
def _entry_reach_targets(entry, reach_mods: set) -> set:
    src = entry.mod_stem or '__init__'
    targets: set = set()
    for imp in entry.imports:
        target = _import_edge_target(imp, reach_mods)
        if target is not None and target != src:
            targets.add(target)
    return targets
def _build_reach_graph(cache, reach_mods: set) -> dict:
    graph: dict[str, set] = {}
    for entry in cache.valid_entries:
        if not entry.mod_stem and not entry.is_init:
            continue
        if is_test_file_path(entry_rel_path(entry)):
            continue
        targets = _entry_reach_targets(entry, reach_mods)
        if targets:
            graph.setdefault(entry.mod_stem or '__init__', set()).update(targets)
    return graph
def _is_lazy_module_reference(name: str, reference: str) -> bool:
    module_path = reference.split(':', 1)[0].strip()
    normalized = module_path.lstrip('.')
    if (not normalized
            or any(not part.isidentifier() for part in normalized.split('.'))):
        return False
    return module_path == name or module_path.endswith(f'.{name}')
def _lazy_surface_modules(tree) -> set[str]:
    modules: set[str] = set()
    for node in iter_module_binding_nodes(tree):
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        value = node.value
        if not isinstance(value, ast.Dict):
            continue
        modules.update(
            key.value.rsplit(".", 1)[-1]
            for key, item in zip(value.keys, value.values, strict=False)
            if (isinstance(key, ast.Constant) and isinstance(key.value, str)
                and isinstance(item, ast.Constant)
                and isinstance(item.value, str)
                and _is_lazy_module_reference(key.value, item.value))
        )
    return modules
def _lazy_registered_mods(cache, reach_mods: set) -> set:
    registered: set[str] = set()
    for entry in cache.valid_entries:
        if is_test_file_path(entry_rel_path(entry)):
            continue
        registered |= _lazy_surface_modules(entry.tree)
    return registered & reach_mods
_JSON_SYNTAX_ERRORS = (ValueError, RecursionError)
def _reject_json_constant(constant: str):
    raise ValueError(f"非标准 JSON 数值常量: {constant}")
def _json_loads_strict(content: str):
    return json.loads(content, parse_constant=_reject_json_constant)
def _json_syntax_valid(content: str) -> bool:
    try:
        _json_loads_strict(content)
        return True
    except _JSON_SYNTAX_ERRORS as e:
        logger.debug("json config degraded: %s", e)
        return False
# JSONL 仅以换行符分隔；不可用 str.splitlines()：它还会在 U+0085/U+2028/U+2029
# 处断行，而这些是 JSON 字符串内允许裸写的字符，会把合法 JSONL 误判为语法非法。
def _jsonl_syntax_valid(content: str) -> bool:
    normalized = content.replace("\r\n", "\n").replace("\r", "\n")
    lines = [ln for ln in normalized.split("\n") if ln.strip()]
    if not lines:
        return True
    try:
        for ln in lines:
            _json_loads_strict(ln)
        return True
    except _JSON_SYNTAX_ERRORS as e:
        logger.debug("jsonl config degraded: %s", e)
        return False
def _load_toml_module():
    try:
        import tomllib  # lazy-by-design
    except ImportError:
        try:
            import tomli as tomllib  # lazy-by-design
        except ImportError:
            return None
    return tomllib
def _toml_syntax_valid(content: str) -> bool:
    toml_module = _load_toml_module()
    if toml_module is None:
        logger.warning("toml 配置解析器不可用，无法证明语法有效")
        return False
    try:
        toml_module.loads(content)
        return True
    except (ValueError, RecursionError) as e:
        logger.debug("toml config degraded: %s", e)
        return False
def _ini_syntax_valid(content: str) -> bool:
    parser = configparser.ConfigParser(interpolation=None, strict=False)
    try:
        parser.read_string(content)
        return True
    except (configparser.Error, ValueError, RecursionError) as e:
        logger.debug("ini config degraded: %s", e)
        return False
def _yaml_syntax_valid(content: str) -> bool:
    try:
        import yaml  # lazy-by-design
    except ImportError as _swallowed_exc:  # pragma: no cover
        logger.warning("yaml 配置解析器不可用，无法证明语法有效: %s",
                       _swallowed_exc)
        return False
    try:
        deque(yaml.compose_all(content), maxlen=0)
        return True
    except (yaml.YAMLError, RecursionError) as e:
        logger.debug("yaml config degraded: %s", e)
        return False
def config_syntax_valid(config_path: str, content: str) -> bool:
    content = content.removeprefix("\ufeff")
    lowered = config_path.lower()
    if lowered.endswith('.json'):
        return _json_syntax_valid(content)
    if lowered.endswith('.jsonl'):
        return _jsonl_syntax_valid(content)
    if lowered.endswith('.toml'):
        return _toml_syntax_valid(content)
    if lowered.endswith('.ini'):
        return _ini_syntax_valid(content)
    if lowered.endswith(('.yaml', '.yml')):
        return _yaml_syntax_valid(content)
    return True
def _check_config_file(cf: str) -> bool:
    try:
        with open(cf, encoding='utf-8') as f:
            content = f.read()
    except (OSError, UnicodeDecodeError) as e:
        logger.debug("config file read degraded: %s", e)
        return False
    return config_syntax_valid(cf, content)
_CONFIG_SKIP_DIRS_LOWER = frozenset(
    d.lower() for d in (DIAG_OUT_OF_SCOPE_DIRS | SCAN_IGNORE_DIRS)) | {
        'logs',
    }
def _collect_config_files(skill_dir: str) -> list:
    config_files = []
    config_exts = ('.yaml', '.yml', '.json', '.jsonl', '.ini', '.toml')
    for root, dirs, files in os.walk(skill_dir):
        dirs[:] = [d for d in dirs
                   if not d.startswith('.')
                   and d.lower() not in _CONFIG_SKIP_DIRS_LOWER
                   and not is_backup_snapshot_dir(d)]
        for f in files:
            if f.lower().endswith(config_exts):
                config_files.append(os.path.join(root, f))
    return config_files
def _e2e_test_config_files(skill_dir: str) -> list:
    config_files = _collect_config_files(skill_dir)
    if not config_files:
        return [{"test": "config_files", "status": "skip", "message": "无配置文件"}]
    invalid = sum(not _check_config_file(cf) for cf in config_files)
    if invalid == 0:
        return [{"test": "config_files", "status": "pass",
                 "count": len(config_files)}]
    return [{"test": "config_files", "status": "warn", "failed": invalid}]
def run_e2e_tests(skill_dir: str, **kwargs) -> TestMethodResult:
    start = time.perf_counter()
    result = TestMethodResult(
        method_name="端到端测试",
        method_id="e2e_test",
    )
    _raw_dir = skill_dir
    skill_dir = _coerce_skill_dir(skill_dir)
    if skill_dir is None:
        return TestMethodResult.invalid_input(
            _raw_dir, "端到端测试", "e2e_test", "测试", start)
    cache: FileCache = kwargs.get('_cache')
    if cache is not None:
        skill_dir = getattr(cache, "skill_dir", "") or skill_dir
    skill_dir = os.path.abspath(skill_dir)
    if not os.path.isdir(skill_dir):
        return TestMethodResult.invalid_input(
            skill_dir, "端到端测试", "e2e_test", "测试", start)
    if cache is None:
        cache = FileCache(skill_dir)
        cache.load()
    skill_name = package_identity(skill_dir)[1]
    e2e_results = []
    e2e_results.extend(_e2e_test_import_chain(skill_dir, skill_name))
    e2e_results.extend(_e2e_test_skill_md(skill_dir))
    e2e_results.extend(_e2e_test_module_parse(cache))
    e2e_results.extend(_e2e_test_call_chain(cache))
    e2e_results.extend(_e2e_test_data_flow(cache))
    e2e_results.extend(_e2e_test_error_propagation(cache))
    e2e_results.extend(_e2e_test_reachability(cache))
    e2e_results.extend(_e2e_test_config_files(skill_dir))
    return _finalize_e2e_results(result, e2e_results, cache, start)
@dataclass(frozen=True)
class _IntegrationRunStats:
    cycles: list
    import_failures: list
    import_success: int
    total: int
    side_effects: list
def _grade_integration_result(result, stats: _IntegrationRunStats):
    cycles = stats.cycles
    import_failures = stats.import_failures
    import_success = stats.import_success
    total = stats.total
    side_effects = stats.side_effects
    if total == 0:
        status, score = "warn", 0
        summary = ("无可测模块（total=0：技能目录无 .py、"
                   "路径不可达或全部条目不可导入），"
                   "集成域无评估对象")
    elif not import_failures and not cycles:
        status, score = "pass", 100 if not side_effects else 90
        summary = f"所有 {total} 个模块导入成功, {len(cycles)} 循环依赖"
    elif not import_failures:
        status, score = "warn", 70
        summary = f"{import_success}/{total} 导入成功, {len(cycles)} 循环依赖"
    elif len(import_failures) <= 2:
        status, score = "warn", 60
        summary = f"{import_success}/{total} 模块导入成功, {len(import_failures)} 失败, {len(cycles)} 循环"
    else:
        status, score = "warn", 25
        summary = (f"{import_success}/{total} 模块导入成功, {len(import_failures)} 失败, {len(cycles)} 循环")
    result.status = status
    result.score = score
    result.summary = summary
def _import_failure_item(rel_path: str, mod_stem: str, error_type: str,
                         message: str, error) -> dict:
    return {
        "file": rel_path, "module": mod_stem,
        "type": "import_failure", "severity": "medium",
        "message": message,
        "error_type": error_type,
        "error": str(error)[:300],
    }
def _import_failure_from_exc(rel_path: str, mod_stem: str, error) -> dict:
    if isinstance(error, ImportError):
        return _import_failure_item(
            rel_path, mod_stem, "ImportError",
            f"模块 {mod_stem} 导入失败: {str(error)[:120]}", error)
    if isinstance(error, SyntaxError):
        return _import_failure_item(
            rel_path, mod_stem, "SyntaxError",
            f"模块 {mod_stem} 语法错误导致导入失败", error)
    if isinstance(error, SystemExit):
        return _import_failure_item(
            rel_path, mod_stem, "SystemExit",
            f"模块 {mod_stem} 导入中调用退出: SystemExit({error.code})", error)
    error_type = type(error).__name__
    return _import_failure_item(
        rel_path, mod_stem, error_type,
        f"模块 {mod_stem} 导入失败: {error_type}", error)
def _import_module_classified(modname: str, rel_path: str,
                              mod_stem: str) -> dict | None:
    try:
        importlib.import_module(modname)  # lazy-by-design
        return None
    except (SystemExit, Exception) as error:  # noqa: BLE001
        logger.debug("suppressed %s: %s", type(error).__name__, error)
        return _import_failure_from_exc(rel_path, mod_stem, error)
_IMPORT_READY = 'import'
_IMPORT_SKIP_ROOT_INIT = 'root_init'
_IMPORT_SKIP_STALE = 'stale'
_IMPORT_SKIP_TEST = 'test'
_IMPORT_SKIP_OUTSIDE = 'outside_package'
def _import_entry_disposition(entry, package_root: str) -> str:
    if (entry.is_init
            and package_module_dotted(entry, package_root) == ''):
        return _IMPORT_SKIP_ROOT_INIT
    if not os.path.isfile(entry.path):
        return _IMPORT_SKIP_STALE
    if is_test_file_path(entry_rel_path(entry)):
        return _IMPORT_SKIP_TEST
    if package_module_dotted(entry, package_root) is None:
        return _IMPORT_SKIP_OUTSIDE
    return _IMPORT_READY
def _import_entry_modname(entry, package_name: str,
                          package_root: str) -> str:
    dotted = package_module_dotted(entry, package_root)
    if dotted is None:
        raise ValueError(f"包外条目没有导入名: {entry_rel_path(entry)}")
    return '.'.join(part for part in (package_name, dotted) if part)
def _import_entry(entry, package_name, package_root,
                  internal_mods) -> tuple:
    _modname = _import_entry_modname(entry, package_name, package_root)
    return (_modname,
            collect_cross_module_calls(entry, internal_mods),
            _import_module_classified(
                _modname, entry_rel_path(entry), _modname))
def _try_import_modules(cache, skill_dir, internal_mods):
    import_success = 0
    import_failures = []
    cross_module_calls: dict[str, set[str]] = defaultdict(set)
    package_root, package_name = package_identity(skill_dir)
    layout = detect_layout(skill_dir)
    script_layout = layout.kind == LAYOUT_SCRIPTS
    def _path_key(path) -> str:
        return os.path.normcase(os.path.abspath(path))
    declared_scripts = {
        _path_key(path if os.path.isabs(path) else os.path.join(skill_dir, path))
        for path in layout.scripts
    }
    _dispositions = [
        (entry, _import_entry_disposition(entry, package_root))
        for entry in cache.entries]
    script_entry_paths = (
        {_path_key(entry.path) for entry, _disposition in _dispositions
         if _path_key(entry.path) in declared_scripts}
        if script_layout else set())
    _entries = [e for e, disposition in _dispositions
                if disposition == _IMPORT_READY
                or (disposition == _IMPORT_SKIP_OUTSIDE
                    and _path_key(e.path) in script_entry_paths)]
    if not _entries:
        _entries = [e for e, disposition in _dispositions
                    if disposition == _IMPORT_SKIP_ROOT_INIT]
    side_effects = collect_import_side_effects(
        [e for e, disposition in _dispositions
         if e.tree is not None
         and disposition in (_IMPORT_READY, _IMPORT_SKIP_ROOT_INIT,
                             _IMPORT_SKIP_OUTSIDE)])
    def _remove_script_root() -> None:
        try:
            sys.path.remove(skill_dir)
        except ValueError:
            logger.debug("脚本导入根已被被测代码移除: %s", skill_dir)
    with ExitStack() as stack:
        if script_entry_paths:
            sys.path.insert(0, skill_dir)
            stack.callback(_remove_script_root)
        if not script_layout or layout.package_name:
            stack.enter_context(isolated_import_scope(
                package_root, with_search_path=True,
                skill_name=package_name))
        script_roots = sorted({
            _import_entry_modname(entry, "", skill_dir).split(".", 1)[0]
            for entry in _entries
            if _path_key(entry.path) in script_entry_paths
        })
        for root_name in script_roots:
            stack.enter_context(isolated_import_scope(
                skill_dir, skill_name=root_name))
        for entry in _entries:
            is_script = _path_key(entry.path) in script_entry_paths
            entry_root = skill_dir if is_script else package_root
            entry_package = "" if is_script else package_name
            _modname, _calls, _fail_item = _import_entry(
                entry, entry_package, entry_root, internal_mods)
            cross_module_calls[_modname].update(_calls)
            if _fail_item is None:
                import_success += 1
            else:
                import_failures.append(_fail_item)
    return import_success, import_failures, side_effects, cross_module_calls
def _resolve_run_context(skill_dir: str, cache) -> tuple:
    if cache is None:
        skill_dir = os.path.abspath(skill_dir)
        cache = FileCache(skill_dir)
        cache.load()
    else:
        skill_dir = getattr(cache, "skill_dir", "") or os.path.abspath(skill_dir)
    internal_mods = (getattr(cache, "internal_mods", None)
                     or get_internal_modules(skill_dir))
    return cache, skill_dir, internal_mods
def _extend_run_findings(result, stats: _IntegrationRunStats,
                         lazy_imports, conditional_imports) -> None:
    for cycle in stats.cycles[:5]:
        result.findings.append({
            "type": "circular_dependency",
            "severity": "high",
            "modules": cycle,
            "message": f"循环依赖: {' → '.join(cycle)} → {cycle[0]}",
        })
    result.findings.extend(stats.import_failures[:20])
    result.findings.extend(stats.side_effects[:10])
    result.findings.extend(lazy_imports[:10])
    result.findings.extend(conditional_imports[:10])
def run_integration_tests(skill_dir: str, **kwargs) -> TestMethodResult:
    start = time.perf_counter()
    _raw_dir = skill_dir
    skill_dir = _coerce_skill_dir(skill_dir)
    if skill_dir is None:
        return TestMethodResult.invalid_input(
            _raw_dir, "集成测试", "integration_test", "测试", start)
    cache, skill_dir, internal_mods = _resolve_run_context(
        skill_dir, kwargs.get('_cache'))
    if not os.path.isdir(skill_dir):
        return TestMethodResult.invalid_input(
            skill_dir, "集成测试", "integration_test", "测试", start)
    result = TestMethodResult(
        method_name="集成测试",
        method_id="integration_test",
    )
    topology = analyze_import_topology(cache, internal_mods)
    lazy_imports, conditional_imports = scan_entry_import_findings(
        cache, internal_mods)
    import_success, import_failures, side_effects, cross_module_calls = \
        _try_import_modules(cache, skill_dir, internal_mods)
    error_types = Counter(f["error_type"] for f in import_failures)
    total = import_success + len(import_failures)
    stats = _IntegrationRunStats(
        cycles=topology.cycles, import_failures=import_failures,
        import_success=import_success, total=total,
        side_effects=side_effects)
    result.metrics = {
        "total_modules": total,
        "imported_successfully": import_success,
        "import_failures": len(import_failures),
        "success_rate": round(import_success / total * 100, 1) if total > 0 else 0,
        "circular_dependencies": len(topology.cycles),
        "cross_module_calls": sum(len(v) for v in cross_module_calls.values()),
        "module_level_side_effects": len(side_effects),
        "error_types": dict(error_types),
        "lazy_imports": len(lazy_imports),
        "conditional_imports": len(conditional_imports),
        "topo_sort_valid": topology.topo_valid,
        "topo_order_length": len(topology.topo_order),
    }
    _extend_run_findings(result, stats, lazy_imports, conditional_imports)
    result.metrics['broken_cross_calls'] = resolve_broken_cross_calls(
        cache, result, internal_mods)
    annotate_structure_metrics(result, topology)
    _grade_integration_result(result, stats)
    return result.finish(start)
_DEFAULT_PYTEST_TIMEOUT_S = 1800
_DEFAULT_TEST_RSS_LIMIT_MB = 2048
_PYTEST_SUBPROCESS_TIMEOUT_S = parse_timeout_env(
    os.environ.get('JWSGJ_PYTEST_TIMEOUT_S', str(_DEFAULT_PYTEST_TIMEOUT_S)),
    _DEFAULT_PYTEST_TIMEOUT_S)
_TEST_RSS_LIMIT_MB = parse_timeout_env(
    os.environ.get('JWSGJ_TEST_RSS_LIMIT_MB',
                   str(_DEFAULT_TEST_RSS_LIMIT_MB)),
    _DEFAULT_TEST_RSS_LIMIT_MB)
_PYTEST_FUTURE_GRACE_S = 60
class _DegradedPytestResult:
    def __init__(self, why: str):
        self.testsRun = 0
        self.failures: list = []
        self.errors: list = []
        self.skipped: list = []
        self.degraded_reason = why
def _degraded_pytest_result(reason: str):
    logger.warning("测试执行未产生完整结果，按 AST 静态口径降级: %s", reason)
    return _DegradedPytestResult(reason)
def _module_spec_available(name: str) -> bool:
    try:
        return importlib.util.find_spec(name) is not None
    except (ImportError, ValueError, AttributeError) as _exc:
        logger.debug("模块规格不可解析 %s: %s", name, _exc)
        return False
def _ensure_pytest_available() -> bool:
    if _module_spec_available('pytest'):
        return True
    ensure_deps(['pytest'])
    return _module_spec_available('pytest')
_PYTEST_CMD_SAFE_LEN = 24000
_PYTEST_CMD_PREFIX = ('-m', 'pytest', '-p', 'no:cacheprovider',
                      '-o', 'addopts=')
_PYTEST_CMD_SUFFIX = ('-q', '--tb=short', '--no-header')
_RUNTIME_XDIST_WORKERS = 4
def _pytest_xdist_args() -> list:
    if (os.environ.get('JWSGJ_PYTEST_XDIST', '1') != '0'
            and _module_spec_available('xdist')):
        return ['-n', str(min(os.cpu_count() or 1,
                              _RUNTIME_XDIST_WORKERS))]
    return []
def _pytest_fixed_cmd_len(xdist_args: list) -> int:
    return (len(sys.executable)
            + sum(len(arg) + 1
                  for arg in (*_PYTEST_CMD_PREFIX, *xdist_args,
                              *_PYTEST_CMD_SUFFIX)))
def _pytest_files_batches(test_files: list, xdist_args: list) -> list[list]:
    _fixed = _pytest_fixed_cmd_len(xdist_args)
    batches: list[list] = []
    cur: list = []
    cur_len = _fixed
    for p in test_files:
        _need = len(p) + 1
        if cur and cur_len + _need > _PYTEST_CMD_SAFE_LEN:
            batches.append(cur)
            cur, cur_len = [], _fixed
        cur.append(p)
        cur_len += _need
    if cur:
        batches.append(cur)
    return batches
def _merge_pytest_batches(batches: list, run_one_batch) -> tuple:
    merged = PytestSummaryResult(0, 0)
    merged_passed = 0
    total = len(batches)
    for index, batch in enumerate(batches):
        try:
            proc = run_one_batch(batch)
        except (_sp.TimeoutExpired, OSError) as exc:
            logger.warning("pytest 批 %d/%d 执行失败: %s", index + 1, total, exc)
            cause = ('timeout' if isinstance(exc, _sp.TimeoutExpired)
                     else 'failed')
            merged.degraded_reason = _batch_degraded_reason(index, total, cause)
            return merged, merged_passed
        parsed = parse_pytest_summary(proc.stdout + proc.stderr)
        if parsed is None:
            logger.warning("pytest 批 %d/%d 输出解析失败", index + 1, total)
            merged.degraded_reason = _batch_degraded_reason(
                index, total, 'parse_failed')
            return merged, merged_passed
        part, part_passed = parsed
        executed_files = getattr(merged, 'executed_files', None)
        if executed_files is None:
            executed_files = set()
            merged.executed_files = executed_files
        executed_files.update(batch)
        merged.testsRun += part.testsRun
        merged_passed += part_passed
        merged.failures.extend(part.failures)
        merged.errors.extend(part.errors)
        merged.collection_errors.extend(part.collection_errors)
        merged.skipped = [None] * (len(merged.skipped) + len(part.skipped))
    return merged, merged_passed
def _batch_degraded_reason(index: int, total: int, cause: str) -> str:
    return f"pytest_batch_{index + 1}_of_{total}_{cause}"
def _start_pytest_future(skill_dir: str, test_files: list):
    _xdist_args = _pytest_xdist_args()
    _batches = _pytest_files_batches(test_files, _xdist_args)
    _future_timeout = (
        _PYTEST_SUBPROCESS_TIMEOUT_S * len(_batches) + _PYTEST_FUTURE_GRACE_S)
    _run_env = subprocess_noartifact_env()
    _package_root, _ = package_identity(skill_dir)
    _import_root = os.path.dirname(os.path.abspath(_package_root))
    _existing_pythonpath = _run_env.get("PYTHONPATH", "")
    _run_env["PYTHONPATH"] = (
        _import_root if not _existing_pythonpath
        else os.pathsep.join((_import_root, _existing_pythonpath))
    )
    def _run_one_batch(batch: list):
        return _sp.run(  # jwsgj:suppress SYM-TAINT
            [sys.executable, *_PYTEST_CMD_PREFIX, *batch, *_xdist_args,
             *_PYTEST_CMD_SUFFIX],
            capture_output=True, text=True, encoding='utf-8', errors='replace',
            timeout=_PYTEST_SUBPROCESS_TIMEOUT_S, cwd=skill_dir, check=False,
            env=_run_env,
        )
    def _run_pytest_subprocess():
        if len(_batches) <= 1:
            return _run_one_batch(list(test_files))
        return _merge_pytest_batches(_batches, _run_one_batch)
    executor = ThreadPoolExecutor(max_workers=1)
    return executor, executor.submit(_run_pytest_subprocess), _future_timeout
def _collect_pytest_result(future, timeout: float):
    try:
        proc = future.result(timeout=timeout)
        if isinstance(proc, tuple):
            return proc
        parsed = parse_pytest_summary(proc.stdout + proc.stderr)
        if parsed is None:
            return _degraded_pytest_result("pytest_output_parse_failed"), 0
        return parsed
    except Exception as exc:  # noqa: BLE001
        logger.warning("pytest 子进程失败: %s", exc)
        return _degraded_pytest_result(f"pytest_subprocess_failed: {exc}"), 0
class _DiscardStream:
    __slots__ = ()
    def write(self, text: str) -> int:
        return len(text)
    def flush(self) -> None:
        pass
def _abort_inprocess_unittest(reason: str):
    logger.warning("进程内 unittest 执行跳过: %s", reason)
    return _degraded_pytest_result(f"inprocess_aborted: {reason}"), 0
def _unittest_entry(test, tb, skill_dir: str) -> tuple:
    test = getattr(test, 'test_case', test)
    _method = getattr(test, getattr(test, '_testMethodName', ''), None)
    _code = getattr(getattr(_method, '__func__', None), '__code__', None)
    _file = getattr(_code, 'co_filename', '') or ''
    if _file and skill_dir:
        try:
            _rel = os.path.relpath(_file, skill_dir)
        except ValueError:
            _rel = ''
        if _rel and not _rel.startswith('..'):
            _file = _rel.replace('\\', '/')
    _qual = f"{type(test).__qualname__}.{getattr(test, '_testMethodName', '')}"
    _label = f"FAILED {_file}::{_qual}" if _file else f"FAILED {_qual}"
    return (_label, str(tb)[:500])
def _normalize_unittest_entries(test_result, unexpected,
                                skill_dir: str) -> None:
    test_result.failures = [
        _unittest_entry(_t, _tb, skill_dir) for _t, _tb in test_result.failures]
    test_result.errors = [
        _unittest_entry(_t, _tb, skill_dir) for _t, _tb in test_result.errors]
    test_result.failures.extend(
        _unittest_entry(_t, 'Unexpected success', skill_dir)
        for _t in unexpected)
class _SubTestTrackingTextResult(unittest.TextTestResult):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.successful_subtest_tests: set[int] = set()
    def addSubTest(self, test, subtest, outcome) -> None:
        if outcome is None:
            self.successful_subtest_tests.add(id(test))
        super().addSubTest(test, subtest, outcome)
def _run_inprocess_unittest(suite, skill_dir: str):
    _rss_mb = current_process_rss_mb()
    if _rss_mb > _TEST_RSS_LIMIT_MB:
        return _abort_inprocess_unittest(
            f"RSS {_rss_mb:.0f}MB 超过阈值 {_TEST_RSS_LIMIT_MB}MB")
    try:
        runner = unittest.TextTestRunner(
            stream=_DiscardStream(), verbosity=0,
            resultclass=_SubTestTrackingTextResult)
        test_result = runner.run(suite)
        _unexpected = list(
            getattr(test_result, 'unexpectedSuccesses', None) or ())
        _failed_test_ids = {
            id(getattr(test, 'test_case', test))
            for test, _detail in test_result.failures
        }
        _error_test_ids = {
            id(getattr(test, 'test_case', test))
            for test, _detail in test_result.errors
        }
        _unexpected_test_ids = {
            id(getattr(test, 'test_case', test)) for test in _unexpected
        }
        _failed_test_ids.update(_unexpected_test_ids)
        test_result.failed_method_count = len(_failed_test_ids)
        test_result.error_method_count = len(_error_test_ids)
        test_result.failed_or_error_method_count = len(
            _failed_test_ids | _error_test_ids)
        _skipped_test_ids = {
            id(getattr(test, 'test_case', test))
            for test, _detail in test_result.skipped
        }
        _partial_skipped_test_ids = (
            _skipped_test_ids
            & getattr(test_result, 'successful_subtest_tests', set()))
        _expected_test_ids = {
            id(getattr(test, 'test_case', test))
            for test, _detail in (
                getattr(test_result, 'expectedFailures', None) or [])
        }
        _wholly_skipped_test_ids = (
            _skipped_test_ids - _failed_test_ids - _error_test_ids
            - _expected_test_ids - _partial_skipped_test_ids)
        test_result.skipped_method_count = len(_wholly_skipped_test_ids)
        test_result.partial_subtest_skips = len(_partial_skipped_test_ids)
        _non_passed = (_failed_test_ids | _error_test_ids
                       | _expected_test_ids | _wholly_skipped_test_ids)
        passed = max(0, test_result.testsRun - len(_non_passed))
        _normalize_unittest_entries(test_result, _unexpected, skill_dir)
        return test_result, passed
    except (SystemExit, Exception) as exc:  # noqa: BLE001
        log_swallowed(__name__, exc, context='_run_inprocess_unittest:Exc')
        return _abort_inprocess_unittest(str(exc))
def _disambiguate_test_mod_name(te, used_mod_names: set) -> str:
    mod_name = os.path.splitext(os.path.basename(te.path))[0]
    if mod_name in used_mod_names:
        _dir_part = (os.path.dirname(te.rel_path)
                     .replace('\\', '/').replace('/', '_')) or 'root'
        _base = f"{mod_name}__{_dir_part}"
        mod_name = _base
        _seq = 2
        while mod_name in used_mod_names:
            mod_name = f"{_base}{_seq}"
            _seq += 1
    return mod_name
def _restore_inprocess_modules(module_hosts: dict) -> None:
    for mod_name, (host_present, host_mod) in module_hosts.items():
        if host_present:
            sys.modules[mod_name] = host_mod
        else:
            sys.modules.pop(mod_name, None)
def _load_test_module_inprocess(te, mod_name, loader, suite,
                                module_hosts=None) -> bool:
    _host_mod = sys.modules.get(mod_name)
    _host_present = mod_name in sys.modules
    try:
        spec = importlib.util.spec_from_file_location(mod_name, te.path)
        if spec and spec.loader:
            mod = importlib.util.module_from_spec(spec)
            sys.modules[mod_name] = mod
            spec.loader.exec_module(mod)
            suite.addTests(loader.loadTestsFromModule(mod))
            if module_hosts is not None:
                module_hosts[mod_name] = (_host_present, _host_mod)
            return True
    except (SystemExit, Exception) as exc:  # noqa: BLE001
        logger.warning("加载测试模块失败: %s", exc)
    finally:
        if module_hosts is None or mod_name not in module_hosts:
            if _host_present:
                sys.modules[mod_name] = _host_mod
            else:
                sys.modules.pop(mod_name, None)
    return False
def _file_stat_entry(te, vis, loaded: bool) -> dict:
    return {
        "file": te.rel_path,
        "test_classes": vis.test_classes,
        "test_functions": vis.test_functions,
        "assertions": vis.assertions,
        "has_assertion_evidence": vis.has_assertion_evidence,
        "loaded": loaded,
    }
def _report_path_key(raw_path, skill_dir: str = '') -> str:
    text = str(raw_path or '').strip().replace('\\', '/')
    if not text:
        return ''
    if not os.path.isabs(text):
        text = os.path.join(skill_dir, text)
    return os.path.normcase(os.path.normpath(text))
def _pytest_unloaded_rel_paths(test_result, test_entries,
                                skill_dir: str) -> set:
    reported = [str(p) for p in
                (getattr(test_result, 'collection_errors', None) or ())
                if str(p).strip()]
    if not reported:
        return set()
    by_key: dict = {}
    by_base: dict = {}
    for te in test_entries:
        rel_path = str(te.rel_path)
        for raw in (te.path, te.rel_path):
            key = _report_path_key(raw, skill_dir)
            if key:
                by_key.setdefault(key, rel_path)
        by_base.setdefault(os.path.basename(rel_path).lower(), []).append(
            rel_path)
    unloaded: set = set()
    for raw in reported:
        rel_path = by_key.get(_report_path_key(raw, skill_dir))
        if rel_path is None and not os.path.isabs(str(raw)):
            candidates = by_base.get(os.path.basename(raw).lower(), [])
            if len(candidates) == 1:
                rel_path = candidates[0]
        if rel_path is not None:
            unloaded.add(rel_path)
    return unloaded
def _pytest_file_stats(test_entries, visitor_results, test_result,
                       skill_dir: str) -> tuple:
    unloaded = _pytest_unloaded_rel_paths(test_result, test_entries, skill_dir)
    executed = getattr(test_result, 'executed_files', None)
    if executed is None:
        if getattr(test_result, 'degraded_reason', ''):
            return ([_file_stat_entry(te, visitor_results[te.rel_path], False)
                     for te in test_entries], 0)
        stats = [_file_stat_entry(te, visitor_results[te.rel_path],
                                  str(te.rel_path) not in unloaded)
                 for te in test_entries]
        return stats, len(test_entries) - len(unloaded)
    executed_keys = {_report_path_key(path, skill_dir) for path in executed}
    stats = []
    for te in test_entries:
        loaded = (_report_path_key(te.path, skill_dir) in executed_keys
                  and str(te.rel_path) not in unloaded)
        stats.append(_file_stat_entry(
            te, visitor_results[te.rel_path], loaded))
    return stats, sum(1 for stat in stats if stat["loaded"])
def _build_per_file_stats(test_entries, visitor_results, loader, suite,
                          module_hosts=None) -> tuple:
    per_file_stats: list[dict] = []
    loaded_count = 0
    _used_mod_names: set[str] = set()
    _prev_dwb = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        for te in test_entries:
            mod_name = _disambiguate_test_mod_name(te, _used_mod_names)
            _used_mod_names.add(mod_name)
            vis = visitor_results[te.rel_path]
            loaded = _load_test_module_inprocess(
                te, mod_name, loader, suite, module_hosts)
            if loaded:
                loaded_count += 1
            per_file_stats.append(_file_stat_entry(te, vis, loaded))
    finally:
        sys.dont_write_bytecode = _prev_dwb
    return per_file_stats, loaded_count
def _collect_unparseable_test_files(cache) -> list[str]:
    broken: list[str] = []
    _seen: set[str] = set()
    for e in cache.test_dir_entries:
        if e.tree is None:
            _append_unparseable(broken, _seen, e.rel_path)
    return broken
def _append_unparseable(broken: list, seen: set, rel_path: str) -> None:
    if rel_path not in seen:
        seen.add(rel_path)
        broken.append(rel_path)
def _discover_additional_test_entries(cache) -> list:
    skill_dir = getattr(cache, 'skill_dir', '') or ''
    if not skill_dir:
        return []
    seen = {
        _report_path_key(entry.path)
        for entry in [*cache.entries, *cache.test_dir_entries]
    }
    additional = []
    for path in iter_test_py_files(skill_dir):
        if not is_test_source_basename(os.path.basename(path)):
            continue
        key = _report_path_key(path)
        if key in seen:
            continue
        seen.add(key)
        additional.append(FileEntry(path, skill_dir))
    return additional
def _finalize_empty_suite_result(result, broken_test_files: list,
                                 start: float):
    if broken_test_files:
        result.status = "error"
        result.score = 0
        result.summary = (
            f"发现 {len(broken_test_files)} 个测试文件但全部解析失败"
            f"（{', '.join(broken_test_files[:3])}"
            + (" 等" if len(broken_test_files) > 3 else "")
            + "）：无法执行任何测试，须先修复解析错误")
        result.findings.append(_unparseable_finding(broken_test_files))
    else:
        result.status = "skip"
        result.score = 0
        result.summary = "未发现测试文件 (test_*.py / *_test.py)"
    result.metrics = {
        "test_files": len(broken_test_files), "loaded_files": 0,
        "tests_run": 0, "passed": 0, "failed": 0, "errors": 0, "skipped": 0,
        "assertion_density": 0, "total_assertions": 0, "test_smells": 0,
        "unparseable_test_files": len(broken_test_files),
        "pytest_status": (
            "test_files_unparseable" if broken_test_files
            else "no_test_files"),
    }
    return result.finish(start)
def _gather_pytest_file_scope(cache, test_entries) -> list:
    test_files_in_dir = [e.path for e in cache.test_dir_entries]
    _tests_scope = {_report_path_key(p) for p in test_files_in_dir}
    return [
        e.path for e in test_entries
        if _report_path_key(e.path) not in _tests_scope
    ] + test_files_in_dir
def _append_degraded_findings(result, test_result, test_entries) -> None:
    _degrade_reason = getattr(test_result, "degraded_reason", None)
    if getattr(test_result, "testsRun", 0) == 0 and test_entries:
        result.findings.append({
            "type": "test_execution_degraded",
            "severity": "high",
            "message": (
                f"单元测试通道未执行任何用例（原因: "
                f"{_degrade_reason or 'no_tests_collected'}，发现 "
                f"{len(test_entries)} 个测试文件）：测试结果不可作为证据，"
                "须在源码稳定窗口复跑确认"),
        })
    elif _degrade_reason and test_entries:
        result.findings.append({
            "type": "test_execution_partial_degraded",
            "severity": "high",
            "message": (
                f"pytest 分批执行部分降级（原因: {_degrade_reason}）："
                f"已完成批次的 {test_result.testsRun} 个用例结果有效，"
                "失败批次及未执行批次的用例状态未知，测试结果不完整，"
                "须在源码稳定窗口复跑确认"),
        })
def _unparseable_finding(broken_test_files: list) -> dict:
    return {
        "type": "test_files_unparseable",
        "severity": "high",
        "message": (
            f"{len(broken_test_files)} 个测试文件解析失败（语法/编码错误）"
            f"未被执行：{', '.join(broken_test_files[:10])}"
            + (" …" if len(broken_test_files) > 10 else "")),
    }
def _append_unparseable_finding(result, broken_test_files: list) -> None:
    if not broken_test_files:
        return
    result.findings.append(_unparseable_finding(broken_test_files))
def _decide_pytest_channel(cache, test_entries) -> tuple:
    use_pytest = _ensure_pytest_available()
    test_files_in_dir = (_gather_pytest_file_scope(cache, test_entries)
                         if use_pytest else [])
    return bool(test_files_in_dir), test_files_in_dir
@dataclass
class _UnitRun:
    visitor_results: dict
    per_file_stats: list
    loaded_count: int
    test_result: object
    passed: int
    elapsed_s: float
def _execute_unit_tests(skill_dir, test_entries, use_pytest,
                        test_files_in_dir) -> _UnitRun:
    run_start = time.perf_counter()
    executor = future = None
    future_timeout = None
    if use_pytest:
        executor, future, future_timeout = _start_pytest_future(
            skill_dir, test_files_in_dir)
    try:
        visitor_results = _visit_test_entries(test_entries)
        if future is not None:
            test_result, passed = _collect_pytest_result(
                future, timeout=future_timeout)
            per_file_stats, loaded_count = _pytest_file_stats(
                test_entries, visitor_results, test_result, skill_dir)
        else:
            module_hosts = {}
            try:
                loader = unittest.TestLoader()
                suite = unittest.TestSuite()
                per_file_stats, loaded_count = _build_per_file_stats(
                    test_entries, visitor_results, loader, suite, module_hosts)
                test_result, passed = _run_inprocess_unittest(suite, skill_dir)
            finally:
                _restore_inprocess_modules(module_hosts)
    finally:
        if executor is not None:
            executor.shutdown(wait=False)
    return _UnitRun(
        visitor_results=visitor_results, per_file_stats=per_file_stats,
        loaded_count=loaded_count, test_result=test_result, passed=passed,
        elapsed_s=time.perf_counter() - run_start)
def _visit_test_entries(test_entries) -> dict:
    visitor_results = {}
    for te in test_entries:
        vis = TestQualityVisitor(te.rel_path)
        vis.visit(te.tree)
        visitor_results[te.rel_path] = vis
    return visitor_results


_NON_TEST_MODULE_BASENAMES = frozenset({"conftest.py"})


def _is_test_module_entry(entry) -> bool:
    """包标记（__init__.py）与 pytest 插件文件（conftest.py）不是测试模块。

    它们位于测试目录下会被 ``is_test`` 归为测试文件，若计入测试条目会虚增
    test_files，并按「空测试文件」误报标准 tests 包布局。
    """
    basename = os.path.basename(str(entry.path).replace("\\", "/")).lower()
    return basename != "__init__.py" and basename not in _NON_TEST_MODULE_BASENAMES


@timed_log()
def run_unit_tests(skill_dir: str, **kwargs) -> TestMethodResult:
    start = time.perf_counter()
    result = TestMethodResult(
        method_name="单元测试",
        method_id="unit_test",
    )
    cache = resolve_file_cache(skill_dir, kwargs)
    if cache is None:
        logger.warning("[UnitTest] 单元测试中止: 技能目录无效 %r", skill_dir)
        return TestMethodResult.invalid_input(
            skill_dir, "单元测试", "unit_test", "测试", start)
    skill_dir = getattr(cache, "skill_dir", "") or skill_dir
    test_entries = [entry for entry in collect_test_entries(cache)
                    if _is_test_module_entry(entry)]
    broken_test_files = _collect_unparseable_test_files(cache)
    broken_seen = set(broken_test_files)
    for entry in _discover_additional_test_entries(cache):
        if entry.tree is None:
            _append_unparseable(
                broken_test_files, broken_seen, entry.rel_path)
        elif entry.is_test and _is_test_module_entry(entry):
            test_entries.append(entry)
    if not test_entries:
        return _finalize_empty_suite_result(result, broken_test_files, start)
    use_pytest, test_files_in_dir = _decide_pytest_channel(
        cache, test_entries)
    outcome = _execute_unit_tests(
        skill_dir, test_entries, use_pytest, test_files_in_dir)
    if not use_pytest and broken_test_files:
        collection_errors = list(
            getattr(outcome.test_result, "collection_errors", None) or ())
        for rel_path in broken_test_files:
            if rel_path not in collection_errors:
                collection_errors.append(rel_path)
        outcome.test_result.collection_errors = collection_errors
    total_assertions = sum(f["assertions"] for f in outcome.per_file_stats)
    executed_assertions = sum(f["assertions"] for f in outcome.per_file_stats
                              if f["loaded"])
    tests_run = outcome.test_result.testsRun
    assertion_density = (
        executed_assertions / tests_run if tests_run > 0 else 0)
    test_smells = detect_test_smells(outcome.per_file_stats, skill_dir)
    result.metrics = {
        "test_files": len(test_entries) + len(broken_test_files),
        "loaded_files": outcome.loaded_count,
        "tests_run": tests_run,
        "passed": outcome.passed,
        "failed": getattr(
            outcome.test_result, 'failed_method_count',
            len(outcome.test_result.failures)),
        "errors": getattr(
            outcome.test_result, 'error_method_count',
            len(outcome.test_result.errors)),
        "skipped": getattr(
            outcome.test_result, 'skipped_method_count',
            len(outcome.test_result.skipped)),
        "assertion_density": round(assertion_density, 2),
        "total_assertions": total_assertions,
        "test_execution_ms": round(outcome.elapsed_s * 1000, 2),
        "pytest_status": getattr(outcome.test_result, "degraded_reason", "ok"),
        "test_smells": len(test_smells),
        "unparseable_test_files": len(broken_test_files),
    }
    collect_test_findings(result, outcome.test_result, test_smells)
    _append_unparseable_finding(result, broken_test_files)
    _append_degraded_findings(result, outcome.test_result, test_entries)
    finalize_test_quality(QualityRun(
        result=result, visitor_results=outcome.visitor_results,
        test_entries=test_entries, cache=cache,
        per_file_stats=outcome.per_file_stats,
        test_result=outcome.test_result, test_smells=test_smells,
        assertion_density=assertion_density, passed=outcome.passed,
        started_at=start,
    ))
    return result

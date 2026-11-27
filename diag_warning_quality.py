from __future__ import annotations

import ast
import bisect
import json
import logging
import os
import re
import time
from typing import Any

from jwsgj.diag_guard_io import (
    guarded_open,
)
from jwsgj.diag_shared_source_core import (
    read_source_via_channel,
    scan_line_quote_state,
)
from jwsgj.diag_shared_source_scan import (
    comment_only_spans,
)
from jwsgj.diag_types_normalize import (
    append_judgment,
    append_recommendation_once,
    as_count,
    as_dict,
    as_number,
    dict_or_empty,
    judgment_dicts,
    judgment_str_fields,
    strict_iterable_list,
)
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    CAT_DYNAMIC_DISPATCH,
    FIELD_FALSE_NEGATIVE_RISK,
    FIELD_RECOMMENDATIONS,
    FMT_DATETIME,
    RULE_HIGH_COMPLEXITY,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import (
    warning_history_path,
)
from jwsgj.runtime_scope import (
    collect_py_files_default,
)

__all__ = [
    'build_root_cause_chain',
    'census_dynamic_features',
    'compute_false_negative_risk',
    'detect_warning_cascades',
    'heuristic_semantic_review',
    'run_warning_quality_analysis',
    'scan_files_for_satd',
    'track_warning_lifecycle',
]
logger = logging.getLogger(__name__)
logger.info("diag_warning_quality 告警质量与报告级判定域已加载: %d 项导出", len(__all__))
def _report_skill_dir(report: dict) -> str:
    skill_dir = report.get("skill_dir", "")
    if isinstance(skill_dir, (str, bytes, os.PathLike)):
        try:
            return os.fsdecode(os.fspath(skill_dir))
        except TypeError:
            return ""
    return ""
def _normalize_status(value: Any) -> str:
    return value.strip().lower() if isinstance(value, str) else ""
_CENSUS_INTROSPECTION_CALLS = frozenset(
    {"getattr", "hasattr", "setattr", "delattr", "type", "isinstance"})
_CENSUS_CODE_GEN_CALLS = frozenset({"eval", "exec", "compile"})
_CENSUS_LIB_LOADING_CALLS = frozenset({"__import__"})
_CENSUS_NAME_CATEGORIES = {
    name: category
    for category, names in (
        ("introspection", _CENSUS_INTROSPECTION_CALLS),
        ("code_generation", _CENSUS_CODE_GEN_CALLS),
        ("library_loading", _CENSUS_LIB_LOADING_CALLS),
    )
    for name in names
}
_DYNAMIC_CATEGORY_KEYS = (
    "introspection", "object_changes", "code_generation", "library_loading",
)
def _census_file_tree(fp: str, diag_ctx=None):
    if isinstance(fp, (bytes, os.PathLike)):
        fp = os.fsdecode(fp)
    source = read_source_via_channel(fp, diag_ctx, "动态特性普查")
    if source is None:
        return None
    if diag_ctx is not None:
        try:
            tree = diag_ctx.get_ast(fp)
        except Exception as e:  # noqa: BLE001 — 既有隔离降级路径，异常已留痕
            logger.debug("动态特性普查: ctx.get_ast 失败，回退直解析 %s: %s", fp, e)
            tree = None
        if tree is not None:
            return tree
    try:
        return ast.parse(source, filename=fp)
    except (SyntaxError, ValueError, RecursionError, MemoryError):
        logger.debug("动态特性普查: 跳过无法解析的文件 %s", fp, exc_info=True)
        return None
def _census_classify_name(name: str, categories: dict,
                          count_import_module: bool) -> None:
    category = _CENSUS_NAME_CATEGORIES.get(name)
    if category is not None:
        categories[category] += 1
        return
    if count_import_module and name == "import_module":
        categories["library_loading"] += 1
def _census_classify_call(func_ref: ast.AST, categories: dict) -> None:
    if isinstance(func_ref, ast.Name):
        _census_classify_name(func_ref.id, categories, count_import_module=True)
        return
    if not isinstance(func_ref, ast.Attribute):
        return
    attr = func_ref.attr
    if (isinstance(func_ref.value, ast.Name)
            and func_ref.value.id == "builtins"):
        _census_classify_name(attr, categories, count_import_module=False)
        return
    if attr == "import_module":
        categories["library_loading"] += 1
_CENSUS_DICT_MUTATING_METHODS = frozenset(
    {"update", "setdefault", "pop", "popitem", "clear"})
def _census_is_object_change(node) -> bool:
    if isinstance(node, ast.Attribute):
        return (node.attr == "__dict__"
                and isinstance(node.ctx, (ast.Store, ast.Del)))
    if isinstance(node, ast.Subscript):
        value = node.value
        return (isinstance(value, ast.Attribute) and value.attr == "__dict__"
                and isinstance(node.ctx, (ast.Store, ast.Del)))
    if isinstance(node, ast.Call):
        func = node.func
        return (isinstance(func, ast.Attribute)
                and func.attr in _CENSUS_DICT_MUTATING_METHODS
                and isinstance(func.value, ast.Attribute)
                and func.value.attr == "__dict__")
    return False
def _census_walk_tree(tree, categories: dict) -> None:
    for node in walk_nodes(tree):
        if isinstance(node, ast.Call):
            _census_classify_call(node.func, categories)
        if _census_is_object_change(node):
            categories["object_changes"] += 1
def _collect_dynamic_categories(skill_dir: str,
                               diag_ctx=None) -> tuple[dict, int]:
    categories = dict.fromkeys(_DYNAMIC_CATEGORY_KEYS, 0)
    if diag_ctx is not None:
        py_files = {fp for fp in (getattr(diag_ctx, "py_files", ()) or ())
                    if isinstance(fp, (str, bytes, os.PathLike))}
    else:
        py_files = collect_py_files_default(skill_dir)
    scanned = 0
    for fp in py_files:
        tree = _census_file_tree(fp, diag_ctx)
        if tree is None:
            continue
        scanned += 1
        _census_walk_tree(tree, categories)
    if scanned == 0:
        logger.debug("动态特性普查: 未解析到任何源码文件（skill_dir=%s），"
                     "本次普查不作风险判定证据", skill_dir)
    return categories, scanned
def _dynamic_fn_risk_adjustment(categories: dict, total: int,
                                scanned: int) -> int:
    if scanned <= 0:
        return 0
    adjustment = 0
    if categories["code_generation"] > 0:
        adjustment += 2
    if categories["introspection"] > 20:
        adjustment += 1
    if categories["library_loading"] > 3:
        adjustment += 1
    if total == 0:
        adjustment = -1
    return adjustment
def census_dynamic_features(report: dict, diag_ctx=None) -> dict:
    report = dict_or_empty(report)
    skill_dir = _report_skill_dir(report)
    if not skill_dir:
        return {"total": 0,
                "categories": dict.fromkeys(_DYNAMIC_CATEGORY_KEYS, 0),
                "fn_risk_adjustment": 0}
    categories, scanned = _collect_dynamic_categories(skill_dir, diag_ctx)
    total = sum(categories.values())
    return {
        "total": total,
        "categories": categories,
        "fn_risk_adjustment": _dynamic_fn_risk_adjustment(
            categories, total, scanned),
    }
def _chain_orphan_functions(report: dict, coupling: dict) -> dict | None:
    _call_chain = report.get("call_chain")
    orphans = as_count(_call_chain.get("orphans")) if isinstance(_call_chain, dict) else 0
    if orphans <= 0:
        return None
    edges = as_count(coupling.get("import_edges"))
    isolated_mods = as_count(coupling.get("isolated_modules"))
    if isolated_mods > 0:
        return {
            "symptom": f"{orphans} orphan functions",
            "cause": f"{isolated_mods} isolated modules with only {edges} import edges",
            "fix": "Add explicit imports between isolated modules to establish call chains",
            "confidence": 85
        }
    return {
        "symptom": f"{orphans} orphan functions",
        "cause": "Functions defined but never called internally (library API pattern)",
        "fix": "Verify external consumers exist, or mark as @deprecated",
        "confidence": 70
    }
def _chain_circular_deps(coupling: dict) -> dict | None:
    cycles = as_count(coupling.get("cycles"))
    if cycles <= 0:
        return None
    return {
        "symptom": f"{cycles} circular dependency cycles",
        "cause": "Tight coupling between modules, likely bidirectional imports",
        "fix": "Extract shared interfaces into a separate base module",
        "confidence": 90
    }
def _chain_confirmed_dead(report: dict) -> dict | None:
    confirmed = _confirmed_dead_count(report)
    if confirmed <= 0:
        return None
    return {
        "symptom": f"{confirmed} confirmed dead code entries",
        "cause": "Functions/modules with no internal or external callers",
        "fix": "Remove dead code or document as public API",
        "confidence": 95
    }
def build_root_cause_chain(report: dict) -> dict:
    report = dict_or_empty(report)
    _materialize_report_entry_iterators(report)
    coupling = report.get("module_coupling")
    if not isinstance(coupling, dict):
        coupling = {}
    chains = [
        chain for chain in (
            _chain_orphan_functions(report, coupling),
            _chain_circular_deps(coupling),
            _chain_confirmed_dead(report),
        ) if chain is not None
    ]
    return {
        "chains": len(chains),
        "top_chains": sorted(chains, key=lambda c: c["confidence"], reverse=True)
    }
def _runtime_metrics(report: dict) -> dict:
    runtime = report.get("runtime_metrics")
    return runtime if isinstance(runtime, dict) else {}
def _runtime_blindspot_metrics(report: dict) -> dict:
    metrics = _runtime_metrics(report).get("blindspot_metrics")
    return metrics if isinstance(metrics, dict) else {}
def _runtime_candidate_count(report: dict) -> int:
    metrics = _runtime_blindspot_metrics(report)
    counts = []
    for key in ("cross_validation_full", "cross_validation"):
        cv = metrics.get(key)
        if not isinstance(cv, dict):
            continue
        if "dynamic_binding_candidates" in cv:
            counts.append(len(strict_iterable_list(
                cv.get("dynamic_binding_candidates"))))
    return max(counts, default=0)
def _fn_risk_dynamic_dispatch(report: dict) -> tuple[str | None, dict, int]:
    cv = report.get(CAT_CROSS_VALIDATION) or {}
    dyn_candidates = 0
    if isinstance(cv, dict):
        _cands = cv.get("dynamic_binding_candidates")
        dyn_candidates = len(strict_iterable_list(_cands))
    dyn_candidates = max(dyn_candidates, _runtime_candidate_count(report))
    if dyn_candidates > 10:
        return CAT_DYNAMIC_DISPATCH, {"level": "high", "count": dyn_candidates}, 3
    if dyn_candidates > 3:
        return CAT_DYNAMIC_DISPATCH, {"level": "medium", "count": dyn_candidates}, 2
    if dyn_candidates > 0:
        return CAT_DYNAMIC_DISPATCH, {"level": "low", "count": dyn_candidates}, 1
    return None, {}, 0
def _fn_risk_exception_flow(report: dict) -> tuple[str | None, dict, int]:
    exc_flow = report.get("exception_type_flow") or {}
    swallowed = as_count(exc_flow.get("swallowed_exceptions")) if isinstance(exc_flow, dict) else 0
    if not swallowed:
        _exc_prop = _runtime_blindspot_metrics(report).get(
            "exception_propagation")
        if isinstance(_exc_prop, dict):
            swallowed = as_count(_exc_prop.get("total_swallowed"))
    em_data = report.get("exception_miner_patterns") or {}
    if not isinstance(em_data, dict) or not em_data:
        _exc_metrics = report.get("exception_metrics")
        em_data = (_exc_metrics.get("exception_miner")
                   if isinstance(_exc_metrics, dict) else {}) or {}
    em_total = as_count(em_data.get("total")) if isinstance(em_data, dict) else 0
    exc_complexity = swallowed + em_total
    if exc_complexity > 10:
        return "exception_flow_complexity", {"level": "high", "count": exc_complexity}, 3
    if exc_complexity > 3:
        return "exception_flow_complexity", {"level": "medium", "count": exc_complexity}, 2
    return None, {}, 0
def _fn_risk_bayesian_model(report: dict) -> tuple[str | None, dict, int]:
    bayesian = report.get("bayesian_model") or {}
    if isinstance(bayesian, dict):
        verdict = _normalize_status(
            bayesian.get("model_verdict", "reliable"))
        posterior = as_number(bayesian.get("posterior"), 0)
        if verdict == "unreliable":
            return "bayesian_unreliable", {"level": "high", "posterior": posterior}, 3
        if verdict == "uncertain":
            return "bayesian_uncertain", {"level": "medium", "posterior": posterior}, 1
    return None, {}, 0
def _fn_risk_simulation_failure(report: dict) -> tuple[str | None, dict, int]:
    sim = report.get("simulation") or {}
    if not isinstance(sim, dict) or not sim:
        sim = _runtime_metrics(report).get("simulation") or {}
    sim_executed = as_count(sim.get("executed")) if isinstance(sim, dict) else 0
    if sim_executed > 0:
        fail_rate = as_count(sim.get("failed")) / sim_executed
        if fail_rate > 0.5:
            return "simulation_failure", {"level": "high", "fail_rate": round(fail_rate, 2)}, 3
        if fail_rate > 0.2:
            return "simulation_failure", {"level": "medium", "fail_rate": round(fail_rate, 2)}, 2
    return None, {}, 0
def _fn_risk_pattern_collapse(report: dict) -> tuple[str | None, dict, int]:
    _clustering = _runtime_blindspot_metrics(report).get("clustering")
    collapse = (_clustering.get("pattern_collapse")
                if isinstance(_clustering, dict) else {})
    if not isinstance(collapse, dict) or not collapse:
        bs_data = report.get("blindspots")
        bs_data = bs_data if isinstance(bs_data, dict) else {}
        collapse = bs_data.get("pattern_collapse") or {}
        if not isinstance(collapse, dict) or not collapse:
            _summary = bs_data.get("summary")
            collapse = (_summary.get("pattern_collapse")
                        if isinstance(_summary, dict) else {})
    collapsed_groups = (as_count(collapse.get("collapsed_groups"))
                        if isinstance(collapse, dict) else 0)
    if collapsed_groups > 0:
        return "pattern_collapse", {
            "level": "medium",
            "groups": collapsed_groups,
            "affected": as_count(collapse.get("affected_entries")),
        }, 2
    return None, {}, 0
def _fn_risk_dynamic_census(report: dict) -> tuple[str | None, dict, int]:
    census = report.get("dynamic_feature_census") or {}
    if not isinstance(census, dict):
        return None, {}, 0
    adjustment = int(as_number(census.get("fn_risk_adjustment"), 0))
    if adjustment <= 0:
        return None, {}, adjustment
    return "dynamic_feature_density", {
        "level": "high" if adjustment >= 3 else "medium",
        "adjustment": adjustment,
        "total": as_count(census.get("total")),
    }, adjustment
_FN_RISK_FACTORS = (
    _fn_risk_dynamic_dispatch,
    _fn_risk_exception_flow,
    _fn_risk_bayesian_model,
    _fn_risk_simulation_failure,
    _fn_risk_pattern_collapse,
    _fn_risk_dynamic_census,
)
def _score_risk_factors(report: dict) -> tuple[dict, int]:
    risk_factors: dict = {}
    risk_score = 0
    for factor in _FN_RISK_FACTORS:
        key, info, delta = factor(report)
        if key and delta > 0:
            risk_factors[key] = info
        risk_score += delta
    return risk_factors, max(0, risk_score)
def _risk_level_of(risk_score: int) -> str:
    if risk_score >= 8:
        return "high"
    if risk_score >= 4:
        return "medium"
    return "low"
def _fn_risk_recommendations(risk_factors: dict) -> list[str]:
    recommendations = []
    if CAT_DYNAMIC_DISPATCH in risk_factors:
        recommendations.append(
            f"动态分发风险({risk_factors[CAT_DYNAMIC_DISPATCH]['count']}处): "
            "建议运行 RuntimeBindingScanner 深度扫描"
        )
    if "exception_flow_complexity" in risk_factors:
        recommendations.append(
            f"异常流复杂({risk_factors['exception_flow_complexity']['count']}处): "
            "建议审查异常吞没和嵌套处理"
        )
    if "bayesian_unreliable" in risk_factors:
        recommendations.append(
            "贝叶斯模型不可靠: 部分盲区可能为假阴性，建议人工复核"
        )
    if "simulation_failure" in risk_factors:
        recommendations.append(
            f"模拟执行失败率{risk_factors['simulation_failure'].get('fail_rate', 0):.0%}: "
            "建议先修复模拟环境与执行前置, 否则模拟结论不可作为判定依据"
        )
    if "pattern_collapse" in risk_factors:
        recommendations.append(
            f"模式坍缩({risk_factors['pattern_collapse']['groups']} 组, 影响 "
            f"{risk_factors['pattern_collapse'].get('affected', 0)} 条): "
            "建议收窄过宽的模式匹配, 避免多条缺陷被合并成一条"
        )
    if "bayesian_uncertain" in risk_factors:
        recommendations.append(
            "贝叶斯模型不确定(后验未达可靠阈值): 关键结论建议人工抽样复核"
        )
    _dyn = risk_factors.get("dynamic_feature_density") or {}
    if _dyn.get("adjustment", 0) > 0:
        recommendations.append(
            f"动态特性密集({_dyn.get('total', 0)}处, "
            "含反射/代码生成): 静态结论易漏判，建议运行时绑定扫描复核"
        )
    return recommendations
def compute_false_negative_risk(report: dict) -> dict:
    report = dict_or_empty(report)
    _materialize_report_entry_iterators(report)
    risk_factors, risk_score = _score_risk_factors(report)
    return {
        "risk_level": _risk_level_of(risk_score),
        "risk_score": risk_score,
        "risk_factors": risk_factors,
        FIELD_RECOMMENDATIONS: _fn_risk_recommendations(risk_factors),
    }
def detect_warning_cascades(report: dict) -> dict:
    report = dict_or_empty(report)
    _materialize_report_entry_iterators(report)
    judgments = judgment_dicts(report.get("judgments"))
    if len(judgments) < 2:
        return {"cascade_groups": 0, "root_warnings": 0, "cascaded_warnings": 0, "details": []}
    groups = {}
    for j in judgments:
        key, label, status = judgment_str_fields(j)
        if _normalize_status(status) == "pass":
            continue
        source = _cascade_source_of(key, label)
        if source:
            groups.setdefault(source, []).append(j)
    cascade_groups, root_warnings, cascaded_warnings = _assemble_cascade_groups(groups)
    return {
        "cascade_groups": len(cascade_groups),
        "root_warnings": root_warnings,
        "cascaded_warnings": cascaded_warnings,
        "details": cascade_groups[:20],
    }
_SEVERITY_ORDER = {"fail": 3, "critical": 3, "warn": 2, "info": 1, "pass": 0}
_CASCADE_FILE_PAT = re.compile(
    r'(?<!\w)((?:[A-Za-z]:)?[\\/]*(?:[\w.-]+[\\/])*'
    r'[\w][\w.-]*\.py)')
_CASCADE_MODULE_PAT = re.compile(
    r'(?<!\w)(?:module|file|path|模块|文件|路径)[:\s]+([\w][\w.]*)',
    re.IGNORECASE)
def _cascade_anchors(label: str) -> tuple[str | None, str | None]:
    file_match = _CASCADE_FILE_PAT.search(label)
    module_match = _CASCADE_MODULE_PAT.search(label)
    file_name = file_match.group(1) if file_match else None
    if file_name:
        file_name = file_name.replace("\\", "/").removeprefix("./")
    return (file_name, module_match.group(1) if module_match else None)
_CASCADE_TOKEN_SOURCES = (
    ("circular", "circular_dependency"),
    ("syntax", "syntax_error"),
    ("breakpoint", "broken_chain"),
)
def _cascade_source_of(key: str, label: str) -> str | None:
    file_name, module_name = _cascade_anchors(label)
    key_lower = key.lower()
    label_lower = label.lower()
    anchor = file_name or module_name
    for token, source in _CASCADE_TOKEN_SOURCES:
        if _mentions(key_lower, label_lower, token):
            return _anchored_source(source, anchor)
    if "broken" in label_lower:
        return _anchored_source("broken_chain", anchor)
    if "import" in key_lower:
        return _anchored_source("import_issue", anchor) if anchor else None
    if file_name:
        return "file:" + file_name
    if module_name:
        return "module:" + module_name
    return None
def _mentions(key_lower: str, label_lower: str, token: str) -> bool:
    return token in key_lower or token in label_lower
def _anchored_source(prefix: str, anchor: str | None) -> str | None:
    return f"{prefix}:{anchor}" if anchor else prefix
def _assemble_cascade_groups(groups: dict) -> tuple:
    cascade_groups = []
    root_warnings = 0
    cascaded_warnings = 0
    for source, members in groups.items():
        if len(members) < 2:
            continue
        sorted_members = sorted(
            members,
            key=lambda m: _SEVERITY_ORDER.get(
                _normalize_status(judgment_str_fields(m)[2]) or "info", 1),
            reverse=True
        )
        root = sorted_members[0]
        cascaded = sorted_members[1:]
        root_warnings += 1
        cascaded_warnings += len(cascaded)
        _root_key, _root_label, _ = judgment_str_fields(root)
        cascade_groups.append({
            "source": source,
            "root": {"key": _root_key, "label": _root_label},
            "cascaded": [
                {"key": _k, "label": _l, "status": _s}
                for _k, _l, _s in map(judgment_str_fields, cascaded)
            ],
            "total": len(members),
        })
    return cascade_groups, root_warnings, cascaded_warnings
def _legacy_warning_fingerprint(key: str, label: str) -> str:
    return key if key else "|" + label[:40].strip()
def _warning_file_anchor(file_name: str, skill_dir: str = "") -> str:
    anchor = os.path.normpath(file_name)
    if skill_dir:
        root = os.path.abspath(skill_dir)
        full = os.path.abspath(
            anchor if os.path.isabs(anchor) else os.path.join(root, anchor))
        try:
            rel = os.path.relpath(full, root)
        except ValueError:
            rel = None
        if rel is not None and rel != os.pardir and not rel.startswith(
                os.pardir + os.sep):
            anchor = rel
        else:
            anchor = full
    return os.path.normcase(anchor)
def _warning_fingerprint(key: str, label: str,
                         skill_dir: str = "") -> str:
    fingerprint = _legacy_warning_fingerprint(key, label)
    file_name, module_name = _cascade_anchors(label)
    anchor = file_name or module_name
    if not anchor:
        return fingerprint
    if file_name:
        anchor = _warning_file_anchor(file_name, skill_dir)
    return f"{fingerprint}@{anchor}"
def _current_warning_fingerprints(report: dict) -> list[dict]:
    current_warnings = []
    for j in judgment_dicts(report.get("judgments")):
        key, label, status = judgment_str_fields(j)
        status = _normalize_status(status)
        if status == "pass":
            continue
        fp = _warning_fingerprint(
            key, label, _report_skill_dir(report))
        current_warnings.append({
            "fingerprint": fp,
            "key": key,
            "status": status,
            "label": label,
        })
    return current_warnings
def _load_warning_history(warning_history_path: str) -> set:
    previous_fps: set = set()
    try:
        if os.path.isfile(warning_history_path):
            with open(warning_history_path, encoding='utf-8-sig') as f:
                history = json.loads(f.read())
            if not isinstance(history, dict):
                history = {}
            _fps = history.get("fingerprints", [])
            previous_fps = ({fp for fp in _fps if isinstance(fp, str) and fp}
                            if isinstance(_fps, list) else set())
    except (OSError, ValueError, RecursionError, TypeError, KeyError,
            AttributeError) as _e:
        log_swallowed(__name__, _e, context='_load_warning_history:read')
    return previous_fps
def _save_warning_history(data_dir: str, warning_history_path: str,
                          current_fps: set) -> None:
    try:
        if data_dir:
            os.makedirs(data_dir, exist_ok=True)
            with guarded_open(warning_history_path, 'w', encoding='utf-8') as f:
                json.dump({
                    "fingerprints": sorted(current_fps),
                    "timestamp": time.strftime(FMT_DATETIME),
                    "count": len(current_fps),
                }, f, ensure_ascii=False, indent=2, default=str)
    except (OSError, TypeError, ValueError) as _e:
        log_swallowed(__name__, _e, context='_save_warning_history:write')
def _classify_lifecycle(current_warnings: list[dict],
                        persistent_fps: set) -> tuple[list[dict], int]:
    classified = []
    for w in current_warnings:
        if w["fingerprint"] in persistent_fps:
            w["lifecycle"] = "persistent"
        else:
            w["lifecycle"] = "newly_introduced"
        classified.append(w)
    return classified, len(persistent_fps)
_WARNING_HISTORY_FILENAME = "warning_history.json"
def _warning_data_dir(skill_dir: str, data_dir: str) -> str:
    if isinstance(skill_dir, (bytes, os.PathLike)):
        skill_dir = os.fsdecode(os.fspath(skill_dir))
    if isinstance(data_dir, (str, bytes, os.PathLike)):
        explicit = os.fsdecode(os.fspath(data_dir)).strip()
        if explicit:
            return explicit
    if skill_dir and os.path.isdir(skill_dir):
        try:
            return os.path.dirname(warning_history_path(skill_dir))
        except (OSError, ValueError, RuntimeError) as _e:
            log_swallowed(__name__, _e,
                          context='_warning_data_dir:warning_history_path')
    logger.debug("警告历史基线目录不可用（skill_dir 非真实目录，按无历史处理）")
    return ""
def _warning_history_location(skill_dir: str,
                              data_dir: str = "") -> tuple[str, str]:
    resolved = _warning_data_dir(skill_dir, data_dir)
    if not resolved:
        return "", ""
    return resolved, os.path.join(resolved, _WARNING_HISTORY_FILENAME)
def track_warning_lifecycle(report: dict, *, persist: bool = True,
                            data_dir: str = "") -> dict:
    report = dict_or_empty(report)
    _materialize_report_entry_iterators(report)
    skill_dir = _report_skill_dir(report)
    if not skill_dir:
        return {"persistent": 0, "newly_introduced": 0, "removed": 0,
                "total_current": 0, "total_previous": 0, "details": [],
                "fingerprint_lifecycle": {}}
    current_warnings = _current_warning_fingerprints(report)
    current_fps = {w["fingerprint"] for w in current_warnings}
    history_dir, warning_history_path = _warning_history_location(
        skill_dir, data_dir)
    previous_fps = _load_warning_history(warning_history_path)
    persistent_fps = current_fps & previous_fps
    matched_previous_fps = set(persistent_fps)
    for warning in current_warnings:
        fingerprint = warning["fingerprint"]
        if fingerprint in persistent_fps:
            continue
        legacy_fingerprints = (
            _warning_fingerprint(warning["key"], warning["label"]),
            _legacy_warning_fingerprint(warning["key"], warning["label"]),
        )
        for legacy_fingerprint in legacy_fingerprints:
            if legacy_fingerprint in previous_fps:
                persistent_fps.add(fingerprint)
                matched_previous_fps.add(legacy_fingerprint)
    removed_fps = previous_fps - matched_previous_fps
    classified, persistent_count = _classify_lifecycle(
        current_warnings, persistent_fps)
    newly_count = len(current_fps) - persistent_count
    if persist:
        _save_warning_history(history_dir, warning_history_path, current_fps)
    return {
        "persistent": persistent_count,
        "newly_introduced": newly_count,
        "removed": len(removed_fps),
        "total_current": len(current_fps),
        "total_previous": len(previous_fps),
        "details": classified[:50],
        "fingerprint_lifecycle": {
            w["fingerprint"]: w["lifecycle"] for w in classified},
    }
def _commit_warning_lifecycle(report: dict, data_dir: str) -> None:
    skill_dir = _report_skill_dir(report)
    if not skill_dir:
        return
    lifecycle = report.get("warning_lifecycle")
    fingerprint_lifecycle = (lifecycle.get("fingerprint_lifecycle")
                             if isinstance(lifecycle, dict) else None)
    if not isinstance(fingerprint_lifecycle, dict):
        logger.debug("告警生命周期缺少分类指纹快照，跳过历史提交")
        return
    history_dir, warning_history_path = _warning_history_location(
        skill_dir, data_dir)
    current_fps = {fp for fp in fingerprint_lifecycle
                   if isinstance(fp, str) and fp}
    _save_warning_history(history_dir, warning_history_path, current_fps)
_ACTIONABILITY_BUCKETS = ((3.0, "actionable"), (1.0, "informational"))
def _classify_warning_actionability(report: dict) -> dict:
    bayesian = as_dict(report.get("bayesian_model"))
    bayesian_verdict = _normalize_status(
        bayesian.get("model_verdict", "reliable"))
    bayesian_posterior = as_number(bayesian.get("posterior"), 0.5)
    fn_level = _normalize_status(
        as_dict(report.get(FIELD_FALSE_NEGATIVE_RISK)).get(
            "risk_level", "low"))
    classified = {"actionable": [], "informational": [], "noise": []}
    for j in judgment_dicts(report.get("judgments")):
        key, label, status = judgment_str_fields(j)
        status = _normalize_status(status)
        if status == "pass":
            continue
        action_score = _score_actionability(
            key, label, status or "info",
            bayesian_verdict, bayesian_posterior, fn_level)
        bucket = next((name for threshold, name in _ACTIONABILITY_BUCKETS
                       if action_score >= threshold), "noise")
        classified[bucket].append(j)
    return {
        "actionable_count": len(classified["actionable"]),
        "informational_count": len(classified["informational"]),
        "noise_count": len(classified["noise"]),
        "actionable_keys": [str(j.get("key") or "?") for j in classified["actionable"]],
        "summary": (
            f"{len(classified['actionable'])} actionable, "
            f"{len(classified['informational'])} informational, "
            f"{len(classified['noise'])} noise"
        ),
    }
_STATUS_BASE_SCORE = {
    status: float(rank) for status, rank in _SEVERITY_ORDER.items() if rank > 0}
def _bayesian_score_adjustment(bayesian_verdict: str,
                               bayesian_posterior: float) -> float:
    adjustment = 0.0
    if bayesian_verdict == "unreliable":
        adjustment -= 1.0
    elif bayesian_verdict == "uncertain":
        adjustment -= 0.5
    if bayesian_posterior > 0.7:
        adjustment += 0.5
    return adjustment
def _contains_any(text: str, keywords: tuple[str, ...]) -> bool:
    return any(keyword in text for keyword in keywords)
def _label_score_adjustment(label: str) -> float:
    if label and _contains_any(label.lower(), ("critical", "broken", "fail")):
        return 0.5
    return 0.0
def _fn_risk_score_adjustment(status: str, fn_level: str) -> float:
    if fn_level == "high" and status == "info":
        return 1.0
    return 0.0
def _key_score_adjustment(key: str) -> float:
    key_lower = key.lower()
    adjustment = 0.0
    if _contains_any(key_lower, ("critical", "dead_code", "circular",
                                 "syntax", "broken", "swallowed")):
        adjustment += 1.0
    if _contains_any(key_lower, ("bayesian_correction", "baseline_trend",
                                 "skill_type")):
        adjustment -= 1.0
    return adjustment
def _score_actionability(key: str, label: str, status: str,
                         bayesian_verdict: str, bayesian_posterior: float,
                         fn_level: str) -> float:
    return (_STATUS_BASE_SCORE.get(status, 0.0)
            + _bayesian_score_adjustment(bayesian_verdict, bayesian_posterior)
            + _label_score_adjustment(label)
            + _fn_risk_score_adjustment(status, fn_level)
            + _key_score_adjustment(key))
def _extract_warning_context(report: dict) -> dict:
    judgments = report.get("judgments") or []
    if not judgments:
        return {"context_count": 0, "high_risk_contexts": 0, "details": []}
    context_results = []
    high_risk = 0
    fn_high = _normalize_status(
        as_dict(report.get(FIELD_FALSE_NEGATIVE_RISK)).get("risk_level")) == "high"
    model_unreliable = _normalize_status(
        as_dict(report.get("bayesian_model")).get("model_verdict")) == "unreliable"
    for j in judgment_dicts(judgments):
        key, label, status = judgment_str_fields(j)
        status = _normalize_status(status)
        tags, risk_factors = _context_tags_and_risk(label, status, fn_high, model_unreliable)
        if risk_factors >= 2:
            tags.append("high_risk_context")
            high_risk += 1
        context_results.append({
            "judgment_key": key,
            "status": status,
            "context_tags": tags,
            "risk_factors": risk_factors,
        })
    return {
        "context_count": len(context_results),
        "high_risk_contexts": high_risk,
        "details": context_results,
    }
_CONTEXT_STATUS_LABEL = {"fail": "critical_severity", "critical": "critical_severity",
                         "warn": "warning_severity", "info": "info_severity",
                         "pass": "passed"}
_CONTEXT_KEYWORD_TAGS = (
    (("circular", "cycle", "loop"), ("circular_dependency",)),
    (("syntax", "parse error"), ("syntax_error",)),
    (("orphan", "isolated", "dead code", "unreachable"), ("dead_code", "no_callers")),
    (("breakpoint", "unresolved", "broken"), ("broken_chain",)),
    (("swallow", "bare except", "exception"), ("within_except",)),
    (("complex", "nested", "deep"), (RULE_HIGH_COMPLEXITY,)),
    (("false positive", "fp", "potential"), ("likely_noise",)),
    (("actionable", "critical", "must fix"), ("actionable",)),
)
_CONTEXT_RISK_FACTOR_SET = (RULE_HIGH_COMPLEXITY, "dead_code", "no_callers",
                            "within_except", "high_fn_risk")
def _context_tags_and_risk(label: str, status: str, fn_high: bool,
                           model_unreliable: bool) -> tuple:
    tags = []
    _t = _CONTEXT_STATUS_LABEL.get(status)
    if _t:
        tags.append(_t)
    label_lower = label.lower()
    for kw_group, tag_group in _CONTEXT_KEYWORD_TAGS:
        if _contains_any(label_lower, kw_group):
            tags.extend(tag_group)
    if fn_high:
        tags.append("high_fn_risk")
    if model_unreliable:
        tags.append("unreliable_model")
    risk_factors = sum(1 for t in tags if t in _CONTEXT_RISK_FACTOR_SET)
    return tags, risk_factors
_SUPPRESSION_KEYWORDS = (
    "bare_except", "swallowed", "broad_except",
    "noqa", "pylint_disable", "type_ignore",
    "filter_warning", "no_type_check", "suppress",
)
_SUPPRESSION_HIGH_RISK_KEYWORDS = ("bare_except", "swallowed")
_SUPPRESSION_FILE_THRESHOLD = 3
def _suppression_findings(judgments: list) -> list[dict]:
    findings = []
    for j in judgment_dicts(judgments):
        key, label, status = judgment_str_fields(j)
        status = _normalize_status(status)
        if status == "pass":
            continue
        haystack = f"{label.lower()} {key.lower()}"
        if not _contains_any(haystack, _SUPPRESSION_KEYWORDS):
            continue
        findings.append({
            "judgment_key": key,
            "status": status,
            "label": label,
            "file": _cascade_anchors(f"{label} {key}")[0],
            "suppression_category": _classify_suppression(haystack),
            "risk": ("high" if _contains_any(haystack, _SUPPRESSION_HIGH_RISK_KEYWORDS)
                     else "medium"),
        })
    return findings
_SEVERE_STATUSES = tuple(
    status for status, rank in _SEVERITY_ORDER.items() if rank >= 2)
def _masked_risk_count(judgments: list, suppression_findings: list) -> int:
    high_risk = [f for f in suppression_findings if f["risk"] == "high"]
    if not high_risk:
        return 0
    high_risk_rows = {
        (f.get("judgment_key", ""), f.get("label", ""),
         _normalize_status(f.get("status")), f.get("file"))
        for f in high_risk
    }
    high_risk_files = {f.get("file") for f in high_risk if f.get("file")}
    masked = 0
    for j in judgment_dicts(judgments):
        key, label, status = judgment_str_fields(j)
        status = _normalize_status(status)
        file_name = _cascade_anchors(f"{label} {key}")[0]
        if status not in _SEVERE_STATUSES:
            continue
        if (key, label, status, file_name) in high_risk_rows:
            continue
        if file_name in high_risk_files:
            masked += 1
    return masked
def _high_suppression_entries(findings: list[dict]) -> list[dict]:
    by_file: dict[str | None, int] = {}
    for finding in findings:
        file_name = finding.get("file")
        by_file[file_name] = by_file.get(file_name, 0) + 1
    entries = [
        {"file": file_name, "suppression_count": count, "risk": "high",
         "note": "Multiple suppression patterns detected - may mask real issues"}
        for file_name, count in sorted(by_file.items(),
                                       key=lambda kv: (-kv[1], kv[0] or ""))
        if file_name and count >= _SUPPRESSION_FILE_THRESHOLD
    ]
    if entries or len(findings) < _SUPPRESSION_FILE_THRESHOLD:
        return entries
    return [{"file": None, "suppression_count": len(findings), "risk": "high",
             "note": "Multiple suppression patterns detected - may mask real issues"}]
def _detect_suppression_patterns(report: dict) -> dict:
    report = dict_or_empty(report)
    judgments = report.get("judgments") or []
    suppression_findings = _suppression_findings(judgments)
    high_suppression_files = _high_suppression_entries(suppression_findings)
    return {
        "total_suppressions": len(suppression_findings),
        "high_suppression_files": high_suppression_files,
        "masked_risk_count": _masked_risk_count(judgments, suppression_findings),
        "details": suppression_findings,
    }
_SUPPRESSION_CATEGORIES = (
    (("noqa", "pylint"), "comment_directive"),
    (("type_ignore", "no_type_check"), "type_suppression"),
    (("bare_except", "broad_except", "swallowed"), "exception_swallowing"),
    (("filter_warning",), "warning_filter"),
)
def _classify_suppression(btype: str) -> str:
    btype_lower = btype.lower()
    return next((category for keywords, category in _SUPPRESSION_CATEGORIES
                 if _contains_any(btype_lower, keywords)), "other")
def _rank_judgments_priority(report: dict) -> None:
    judgments = report.get("judgments")
    materialized = strict_iterable_list(judgments)
    if not materialized:
        return
    if not isinstance(judgments, (list, tuple)):
        report["judgments"] = materialized
        judgments = materialized
    ranked = _sort_judgments(report, judgments)
    top_issues = _top_issue_rows(ranked)
    report["priority_ranking"] = {
        "algorithm": "severity(40%) + impact(25%) + difficulty(20%) + persistence(15%)",
        "top_issues": top_issues,
    }
    if top_issues:
        logger.info("  [Priority] Top issue: %s - %s",
                    top_issues[0]["key"], top_issues[0]["label"][:80])
def _sort_judgments(report: dict, judgments) -> list:
    persistence = _persistence_scores(report)
    skill_dir = _report_skill_dir(report)
    ranked = sorted(strict_iterable_list(judgments),
                    key=lambda j: _rank_score(j, persistence, skill_dir),
                    reverse=True)
    report["judgments"] = ranked
    return ranked
def _top_issue_rows(ranked) -> list[dict]:
    severe = [j for j in judgment_dicts(ranked)
              if _normalize_status(j.get("status")) in _SEVERE_STATUSES][:5]
    return [{"rank": i + 1, "key": key or "?", "label": label}
            for i, (key, label, _status) in enumerate(
                map(judgment_str_fields, severe))]
_RANK_WEIGHT = {3: 100, 2: 60, 1: 30, 0: 0}
_STATUS_WEIGHT = {status: _RANK_WEIGHT[rank]
                  for status, rank in _SEVERITY_ORDER.items()}
_FIX_WEIGHT = {"circular_deps": 35, "blindspots_critical": 30,
               "cv_dead_code": 28, "fragmentation": 25,
               "call_depth": 22, "blindspots_high": 20,
               "except_anti_patterns": 18, "public_coverage": 15}
_IMPACT_TIERS = ((100, 35), (10, 28))
_IMPACT_DEFAULT = 22
def _impact_of(label: str) -> int:
    nums = [float(n) for n in re.findall(r'(\d+\.?\d*)', label)]
    if not nums:
        return 25
    max_num = max(nums)
    return next((score for limit, score in _IMPACT_TIERS
                 if max_num > limit), _IMPACT_DEFAULT)
_PERSISTENCE_WEIGHT = {"persistent": 15.0, "newly_introduced": 5.0}
_DEFAULT_PERSISTENCE = _PERSISTENCE_WEIGHT["persistent"]
def _persistence_weight(name: Any) -> float | None:
    return _PERSISTENCE_WEIGHT.get(name) if isinstance(name, str) else None
def _persistence_scores(report: dict) -> dict[str, float]:
    lifecycle = report.get("warning_lifecycle")
    if not isinstance(lifecycle, dict):
        return {}
    mapping = lifecycle.get("fingerprint_lifecycle")
    if isinstance(mapping, dict):
        return {fp: weight
                for fp, name in mapping.items()
                for weight in (_persistence_weight(name),)
                if isinstance(fp, str) and weight is not None}
    details = lifecycle.get("details")
    if not isinstance(details, list):
        return {}
    scores: dict[str, float] = {}
    for detail in details:
        if not isinstance(detail, dict):
            continue
        fp = detail.get("fingerprint")
        weight = _persistence_weight(detail.get("lifecycle"))
        if isinstance(fp, str) and weight is not None:
            scores[fp] = weight
    return scores
def _rank_score(j, persistence: dict[str, float] | None = None,
                skill_dir: str = "") -> float:
    if not isinstance(j, dict):
        return -1.0
    key, label, status = judgment_str_fields(j)
    sw = _STATUS_WEIGHT.get(_normalize_status(status) or "info", 30)
    impact = _impact_of(label)
    fw = _FIX_WEIGHT.get(key or "", 20)
    hist = _DEFAULT_PERSISTENCE
    if persistence:
        hist = persistence.get(
            _warning_fingerprint(key, label, skill_dir), hist)
    return sw * 0.4 + impact * 0.25 + fw * 0.2 + hist * 0.15
def _guard_step(report: dict, step: str, excs: tuple, fn) -> None:
    try:
        fn()
    except excs as e:
        logger.debug("suppressed [%s] (%s): %s", step,
                     ", ".join(c.__name__ for c in excs), e)
        errors = report.get("errors")
        if not isinstance(errors, list):
            errors = []
            report["errors"] = errors
        errors.append({"step": step, "error": str(e)})
_SATD_MARKER_JUDGMENTS = (
    ("bug", "satd_bug_markers", "fail",
     "SATD: {0} BUG markers found — known bugs in dead code"),
    ("xxx", "satd_xxx_markers", "warn",
     "SATD: {0} XXX markers found — dangerous/attention-required code"),
    ("hack", "satd_hack_markers", "info",
     "SATD: {0} HACK markers found — temporary workarounds"),
)
def _step_semantic_review(report: dict, ctx=None) -> None:
    semantic_review = heuristic_semantic_review(report, diag_ctx=ctx)
    report["semantic_review"] = semantic_review
    if semantic_review.get("hints", 0) > 0:
        _mc = semantic_review.get("marker_counts") or {}
        for marker, key, status, template in _SATD_MARKER_JUDGMENTS:
            count = _mc.get(marker, 0)
            if count > 0:
                append_judgment(report, key, status, template.format(count))
        logger.info(
            f"  [SATD] 语义审查: {semantic_review.get('hints', 0)} hints "
            f"(safe:{semantic_review.get('safe_to_remove', 0)} "
            f"review:{semantic_review.get('needs_review', 0)} "
            f"future:{semantic_review.get('keep_for_future', 0)})")
def _step_dynamic_census(report: dict, ctx=None) -> None:
    dynamic_census = census_dynamic_features(report, diag_ctx=ctx)
    report["dynamic_feature_census"] = dynamic_census
    if dynamic_census["total"] > 0:
        logger.info(
            f"  [DynCensus] {dynamic_census['total']} dynamic features "
            f"(introspection:{dynamic_census['categories']['introspection']} "
            f"code_gen:{dynamic_census['categories']['code_generation']} "
            f"lib_loading:{dynamic_census['categories']['library_loading']})")
def _step_fn_risk(report: dict) -> None:
    fn_risk = compute_false_negative_risk(report)
    report[FIELD_FALSE_NEGATIVE_RISK] = fn_risk
    if fn_risk["risk_level"] == "high":
        append_judgment(
            report, FIELD_FALSE_NEGATIVE_RISK, "warn",
            f"False negative risk: HIGH (score={fn_risk['risk_score']})"
            " — real issues may be masked")
        for rec in fn_risk.get(FIELD_RECOMMENDATIONS, []):
            append_recommendation_once(report, f"[FN-Risk] {rec}")
    elif fn_risk["risk_level"] == "medium":
        append_judgment(
            report, FIELD_FALSE_NEGATIVE_RISK, "info",
            f"False negative risk: MEDIUM (score={fn_risk['risk_score']})")
    logger.info(
        f"  [FN-Risk] Level={fn_risk['risk_level']} "
        f"Score={fn_risk['risk_score']} "
        f"Factors={list(fn_risk['risk_factors'].keys())}")
def _step_actionability(report: dict) -> None:
    actionability = _classify_warning_actionability(report)
    report["warning_actionability"] = actionability
    logger.info(f"  [Actionability] {actionability['summary']}")
def _step_context(report: dict) -> None:
    context_analysis = _extract_warning_context(report)
    report["warning_context"] = context_analysis
    if context_analysis["high_risk_contexts"] > 0:
        logger.info(
            f"  [Context] {context_analysis['context_count']} 个盲点已标注上下文, "
            f"{context_analysis['high_risk_contexts']} 个高风险上下文")
def _step_suppression(report: dict) -> None:
    suppression_analysis = _detect_suppression_patterns(report)
    report["suppression_patterns"] = suppression_analysis
    if suppression_analysis["total_suppressions"] > 0:
        logger.info(
            f"  [Suppression] 检测到 {suppression_analysis['total_suppressions']} 个抑制模式, "
            f"{suppression_analysis['masked_risk_count']} 个可能掩盖的真实问题")
        if suppression_analysis["high_suppression_files"]:
            for hf in suppression_analysis["high_suppression_files"]:
                _target = hf.get("file") or "全局"
                append_recommendation_once(
                    report,
                    f"[Suppression] {_target} 检测到 "
                    f"{hf['suppression_count']} 个抑制模式 — {hf['note']}",
                )
def _step_lifecycle(report: dict, data_dir: str) -> None:
    lifecycle = track_warning_lifecycle(
        report, persist=False, data_dir=data_dir)
    report["warning_lifecycle"] = lifecycle
    if lifecycle["persistent"] > 0 or lifecycle["newly_introduced"] > 0:
        logger.info(
            f"  [Lifecycle] {lifecycle['persistent']} persistent, "
            f"{lifecycle['newly_introduced']} newly-introduced, "
            f"{lifecycle['removed']} removed warnings")
        if lifecycle["newly_introduced"] > 0:
            append_judgment(
                report, "warning_lifecycle", "info",
                f"Warning lifecycle: {lifecycle['persistent']} persistent, "
                f"{lifecycle['newly_introduced']} newly-introduced")
def _step_cascades(report: dict) -> None:
    cascades = detect_warning_cascades(report)
    report["warning_cascades"] = cascades
    if cascades["cascade_groups"] > 0:
        logger.info(
            f"  [Cascade] {cascades['cascade_groups']} cascade groups, "
            f"{cascades['cascaded_warnings']} cascaded warnings "
            f"from {cascades['root_warnings']} root causes")
def _step_root_cause(report: dict) -> None:
    root_causes = build_root_cause_chain(report)
    report["root_cause_analysis"] = root_causes
    if root_causes.get("chains", 0) > 0:
        top_rc = root_causes["top_chains"][0]
        append_judgment(
            report, "root_cause_chain", "warn",
            f"Root cause: {top_rc['symptom']} → {top_rc['cause']}"
            f" ({top_rc['confidence']}% confidence)")
        if top_rc.get("fix"):
            append_recommendation_once(report, f"[RootCause] {top_rc['fix']}")
        logger.info(
            f"  [RootCause] {root_causes['chains']} 条根因链, 最高置信 {top_rc['confidence']}%: "
            f"{top_rc['symptom']} → {top_rc['cause']}"
        )
_STEP_EXCS = (KeyError, TypeError, AttributeError)
_STEP_EXCS_IO = _STEP_EXCS + (OSError,)
_STEP_EXCS_INDEX = _STEP_EXCS + (IndexError,)
_WARNING_QUALITY_STEPS = (
    ("semantic_review", _STEP_EXCS_IO, _step_semantic_review),
    ("dynamic_feature_census", _STEP_EXCS_IO, _step_dynamic_census),
    (FIELD_FALSE_NEGATIVE_RISK, _STEP_EXCS, _step_fn_risk),
    ("root_cause_chain", _STEP_EXCS_INDEX, _step_root_cause),
    ("warning_actionability", _STEP_EXCS, _step_actionability),
    ("warning_context", _STEP_EXCS, _step_context),
    ("suppression_patterns", _STEP_EXCS, _step_suppression),
    ("warning_lifecycle", _STEP_EXCS, _step_lifecycle),
    ("warning_cascades", _STEP_EXCS, _step_cascades),
    ("priority_ranking", _STEP_EXCS, _rank_judgments_priority),
)
_CTX_AWARE_STEPS = frozenset({_step_semantic_review, _step_dynamic_census})
_DATA_DIR_AWARE_STEPS = frozenset({_step_lifecycle})
def _run_warning_quality_analyses(report: dict, ctx,
                                  data_dir: str) -> None:
    for step, excs, fn in _WARNING_QUALITY_STEPS:
        if fn in _CTX_AWARE_STEPS:
            _guard_step(report, step, excs, lambda fn=fn: fn(report, ctx))
        elif fn in _DATA_DIR_AWARE_STEPS:
            _guard_step(report, step, excs,
                        lambda fn=fn: fn(report, data_dir))
        else:
            _guard_step(report, step, excs, lambda fn=fn: fn(report))
def _rollback_appended(report: dict, baseline: dict) -> None:
    for _name, keep in baseline.items():
        values = report.get(_name)
        if isinstance(values, list) and len(values) > keep:
            del values[keep:]
def run_warning_quality_analysis(report: dict, ctx: Any = None,
                                data_dir: str = "") -> dict:
    if not isinstance(report, dict):
        raise TypeError(
            f"run_warning_quality_analysis 需要 dict 报告，收到 {type(report).__name__}")
    if report.get("_warning_quality_applied"):
        return report
    for _field in ("findings", "errors", "judgments", FIELD_RECOMMENDATIONS):
        if not isinstance(report.get(_field), list):
            report[_field] = strict_iterable_list(report.get(_field))
    if not isinstance(report.get("blindspots"), dict):
        report["blindspots"] = strict_iterable_list(report.get("blindspots"))
    _materialize_report_entry_iterators(report)
    baseline = {field: len(report[field])
                for field in ("errors", "judgments", FIELD_RECOMMENDATIONS)}
    judgments_order = list(report["judgments"])
    report["_warning_quality_applied"] = True
    try:
        errors_before = len(report["errors"])
        _run_warning_quality_analyses(report, ctx, data_dir)
        lifecycle_failed = any(
            isinstance(error, dict) and error.get("step") == "warning_lifecycle"
            for error in report["errors"][errors_before:])
        if not lifecycle_failed:
            _commit_warning_lifecycle(report, data_dir)
    except BaseException as _e:
        _rollback_appended(report, baseline)
        report["judgments"] = judgments_order[:baseline["judgments"]]
        report.pop("_warning_quality_applied", None)
        logger.debug("告警质量分析中断, 幂等标记与追加项已回滚以允许重跑: %s", _e)
        raise
    return report
_LINE_BOUNDARY = re.compile(r'\r\n|\r|\n')
def _line_offsets(source: str) -> list[int]:
    return [0] + [m.end() for m in _LINE_BOUNDARY.finditer(source)]
_SATD_BUG_RE = r"\bBUG\b"
_SATD_HACK_RE = r"\bHACK\b"
_SATD_XXX_RE = r"\bXXX\b"
_SATD_TEMP_RE = r"\btemp(?:orary)?\b"
_SATD_TEMP_SOLUTION_RE = _SATD_TEMP_RE + r"[ \t]+solution\b"
_MARKER_PATTERNS = (
    ("bug", _SATD_BUG_RE),
    ("hack", _SATD_HACK_RE),
    ("xxx", _SATD_XXX_RE),
)
_SATD_PATTERNS = {
    "safe_to_remove": [
        (r"\bdebug\b", "debug code"),
        ((r"(?<![A-Za-z0-9_])临时(?![^，。；\n]{0,3}方案)"
          r"(?![A-Za-z0-9_])"), "temporary code"),
        (_SATD_TEMP_RE + r"(?![ \t]+solution\b)", "temporary code"),
        (r"\bdeprecated\b", "deprecated"),
        (r"(?<![A-Za-z0-9_])废弃(?![A-Za-z0-9_])", "deprecated"),
        (r"(?<![A-Za-z0-9_])不再使用(?![A-Za-z0-9_])", "no longer used"),
        (r"\b(?-i:TEST)\b", "test-only code"),
        (r"(?<![A-Za-z0-9_])试验(?![A-Za-z0-9_])", "experimental code"),
    ],
    "needs_review": [
        (r"\bTODO\b", "todo marker"),
        (r"\bFIXME\b", "fixme marker"),
        (_SATD_HACK_RE, "hack/temporary workaround"),
        (_SATD_XXX_RE, "dangerous/attention required"),
        (_SATD_BUG_RE, "known bug marker"),
        (r"(?<![A-Za-z0-9_])待实现(?![A-Za-z0-9_])", "pending implementation"),
        (r"(?<![A-Za-z0-9_])待修复(?![A-Za-z0-9_])", "pending fix"),
        (_SATD_TEMP_SOLUTION_RE, "temporary solution"),
        ((r"(?<![A-Za-z0-9_])临时(?:解决|处置|处理|应对)?方案"
          r"(?![A-Za-z0-9_])"), "temporary solution"),
        (r"\bfault\b", "known fault marker"),
        (r"\bdefect\b", "known defect marker"),
        (r"\bfailure\b", "known failure marker"),
        (r"\bbroken\b", "broken code marker"),
        (r"\bcrash\b", "crash risk marker"),
    ],
    "keep_for_future": [
        (r"\bfuture\b", "future use"),
        (r"(?<![A-Za-z0-9_])预留(?![A-Za-z0-9_])", "reserved"),
        (r"(?<![A-Za-z0-9_])扩展(?![A-Za-z0-9_])", "extension point"),
        (r"\bWORKAROUND\b", "intentional workaround"),
        (r"\bOPTIMIZE\b", "optimization pending"),
        (r"(?<![A-Za-z0-9_])优化(?![A-Za-z0-9_])", "optimization pending"),
        (r"(?<![A-Za-z0-9_])兼容(?![A-Za-z0-9_])", "compatibility code"),
        (r"\brefactor\b", "refactoring pending"),
        (r"\barchitecture\b", "architecture concern"),
        (r"\bclean[- ]?up\b", "cleanup pending"),
        (r"\bsmell\b", "code smell marker"),
        (r"\banti[- ]?pattern\b", "anti-pattern marker"),
    ],
    "documentation_debt": [
        (r"\bdocument(?:ation)?\b", "documentation pending"),
        (r"\bdocs?\b", "docs pending"),
        (r"\bexplain\b", "needs explanation"),
        (r"\bdescribe\b", "needs description"),
        (r"(?<![A-Za-z0-9_])待文档(?![A-Za-z0-9_])", "documentation pending"),
        (r"(?<![A-Za-z0-9_])待说明(?![A-Za-z0-9_])", "explanation pending"),
    ],
    "test_debt": [
        (r"\buntested\b", "untested code"),
        (r"\bno test\b", "missing tests"),
        (r"\bcoverage\b", "coverage concern"),
        (r"(?<![A-Za-z0-9_])待测试(?![A-Za-z0-9_])", "test pending"),
        (r"\bneed test\b", "test needed"),
        (r"\bskip test\b", "test skipped"),
    ],
}
_SATD_NEGATION_PHRASES = [
    r"not\s+a\s+(?:TODO|FIXME|HACK|BUG|XXX)",
    r"不是.{0,4}(?:待办|修复|临时|错误)",
    r"this\s+is\s+not\s+(?:a\s+)?(?:todo|hack|bug|workaround)",
    r"no\s+longer\s+(?:a\s+)?(?:todo|hack|bug)",
]
def _satd_line_text(source: str, line_offsets: list[int],
                    start: int, end: int) -> tuple[int, str]:
    line_idx = bisect.bisect_right(line_offsets, start) - 1
    line_start = line_offsets[line_idx]
    boundary = _LINE_BOUNDARY.search(source, end)
    line_end = boundary.start() if boundary else len(source)
    return line_idx + 1, source[line_start:line_end]
def _satd_entry(source: str, rel: str, category: str, pattern: str, desc: str,
                match, line_offsets: list[int], negation_phrases: list) -> dict | None:
    line_no, line_text = _satd_line_text(
        source, line_offsets, match.start(), match.end())
    line_start = line_offsets[line_no - 1]
    marker_start = match.start() - line_start
    marker_end = match.end() - line_start
    if any(neg_match.start() <= marker_start and marker_end <= neg_match.end()
           for neg_pat in negation_phrases
           for neg_match in re.finditer(neg_pat, line_text, re.IGNORECASE)):
        return None
    context_window = source[max(0, match.start()-30):match.end()+30]
    context = context_window.replace('\n', ' ').strip()
    return {
        "file": rel, "line": line_no,
        "category": category, "pattern": desc,
        "regex": pattern, "context": context[:80]
    }
def _comment_spans_by_row(source: str) -> dict[int, list[tuple[int, int]]]:
    spans = comment_only_spans(source)
    if spans is not None:
        return spans
    fallback: dict[int, list[tuple[int, int]]] = {}
    in_str = ""
    for row, line_text in enumerate(_LINE_BOUNDARY.split(source), 1):
        start, in_str = scan_line_quote_state(line_text, in_str)
        if start >= 0:
            fallback[row] = [(start, len(line_text))]
    return fallback
def _satd_match_in_comment(spans: dict, line_offsets: list[int],
                           start: int, end: int) -> bool:
    row = bisect.bisect_right(line_offsets, start)
    line_base = line_offsets[row - 1]
    col_start, col_end = start - line_base, end - line_base
    return any(col_start >= span_start and col_end <= span_end
               for span_start, span_end in spans.get(row, ()))
def _scan_source_for_satd(source: str, rel: str, patterns: dict,
                          negation_phrases: list) -> tuple[list, dict]:
    findings = []
    counts: dict = {}
    line_offsets = _line_offsets(source)
    comment_spans = _comment_spans_by_row(source)
    for category, rules in patterns.items():
        for pattern, desc in rules:
            for match in re.finditer(pattern, source, re.IGNORECASE):
                if not _satd_match_in_comment(
                        comment_spans, line_offsets,
                        match.start(), match.end()):
                    continue
                entry = _satd_entry(source, rel, category, pattern, desc, match,
                                    line_offsets, negation_phrases)
                if entry is None:
                    continue
                findings.append(entry)
                counts[category] = counts.get(category, 0) + 1
    return findings, counts
def _satd_relpath(fp: str, skill_dir: str) -> str:
    try:
        return os.path.relpath(fp, skill_dir).replace('\\', '/')
    except (ValueError, TypeError) as _e:
        log_swallowed(__name__, _e, context='_satd_relpath:fallback')
        return fp.replace('\\', '/')
def scan_files_for_satd(py_files: set, patterns: dict, negation_phrases: list, diag_ctx, skill_dir: str):
    py_files = strict_iterable_list(py_files)
    if not isinstance(patterns, dict):
        patterns = {}
    negation_phrases = strict_iterable_list(negation_phrases)
    findings = []
    counts = {"safe_to_remove": 0, "needs_review": 0, "keep_for_future": 0,
              "documentation_debt": 0, "test_debt": 0}
    for raw_fp in sorted(py_files, key=str):
        if not isinstance(raw_fp, (str, bytes, os.PathLike)):
            logger.debug("SATD 扫描: 跳过非路径条目 %r", raw_fp)
            continue
        fp = os.fsdecode(os.fspath(raw_fp))
        source = read_source_via_channel(fp, diag_ctx, "SATD 扫描")
        if source is None:
            continue
        rel = _satd_relpath(fp, skill_dir)
        file_findings, file_counts = _scan_source_for_satd(
            source, rel, patterns, negation_phrases)
        findings.extend(file_findings)
        for category, hits in file_counts.items():
            counts[category] = counts.get(category, 0) + hits
    return findings, counts
def _empty_review_result() -> dict:
    return {"hints": 0, "safe_to_remove": 0, "needs_review": 0,
            "keep_for_future": 0, "documentation_debt": 0, "test_debt": 0,
            "marker_counts": {"bug": 0, "hack": 0, "xxx": 0},
            "findings": []}
_CONFIRMED_DEAD_ENTRY_SOURCES = ("dead_code", "confirmed_dead")
_CONFIRMED_DEAD_SOURCES = ("blindspots", *_CONFIRMED_DEAD_ENTRY_SOURCES)
def _entry_sequence(value: Any) -> list:
    if isinstance(value, dict):
        for key in ("entries", "items"):
            nested = value.get(key)
            if nested is None:
                continue
            sequence = _entry_sequence(nested)
            if sequence:
                return sequence
        return []
    return strict_iterable_list(value)
def _materialize_one_shot_entries(value):
    if isinstance(value, dict):
        for key in ("entries", "items"):
            if key in value:
                value[key] = _materialize_one_shot_entries(value[key])
        return value
    try:
        if iter(value) is not value:
            return value
    except TypeError:
        return value
    return strict_iterable_list(value)
def _materialize_report_entry_iterators(report: dict) -> None:
    for key in ("judgments", *_CONFIRMED_DEAD_SOURCES):
        if key in report:
            report[key] = _materialize_one_shot_entries(report[key])
    channels = [report.get(CAT_CROSS_VALIDATION)]
    metrics = _runtime_blindspot_metrics(report)
    channels.extend(metrics.get(key) for key in
                    ("cross_validation_full", "cross_validation"))
    for channel in channels:
        if isinstance(channel, dict) and "dynamic_binding_candidates" in channel:
            key = "dynamic_binding_candidates"
            channel[key] = _materialize_one_shot_entries(channel[key])
def _confirmed_count(dp: dict) -> int:
    if not isinstance(dp, dict):
        return 0
    value = dp.get("confirmed")
    count = as_count(value)
    if count:
        return count
    if isinstance(value, str):
        text = value.strip()
        if text.isdigit():
            return int(text)
    return 0
def _confirmed_dead_count(report: dict) -> int:
    dp = report.get("dead_code_phases")
    count = _confirmed_count(dp if isinstance(dp, dict) else {})
    if count:
        return count
    return max((len(_entry_sequence(report.get(key)))
                for key in _CONFIRMED_DEAD_ENTRY_SOURCES), default=0)
def _has_confirmed_dead_evidence(report: dict) -> bool:
    return _confirmed_dead_count(report) > 0 or any(
        _entry_sequence(report.get(key)) for key in _CONFIRMED_DEAD_SOURCES)
def _confirmed_entry_file(entry: Any, skill_dir: str) -> str | None:
    if isinstance(entry, dict):
        fp = entry.get("filepath") or entry.get("file", "")
    else:
        fp = getattr(entry, "filepath", "") or getattr(entry, "file", "")
    if not fp or not isinstance(fp, (str, bytes, os.PathLike)):
        return None
    fp = os.fsdecode(os.fspath(fp))
    root = os.path.abspath(skill_dir)
    resolved_root = os.path.realpath(root)
    full = os.path.abspath(
        fp if os.path.isabs(fp) else os.path.join(root, fp))
    resolved = os.path.realpath(full)
    try:
        rel = os.path.relpath(resolved, resolved_root)
    except ValueError as _e:
        log_swallowed(__name__, _e, context='_confirmed_entry_file:relpath')
        return None
    if rel == os.pardir or rel.startswith(os.pardir + os.sep):
        return None
    return full if os.path.isfile(resolved) else None
def _semantic_review_targets(report: dict, diag_ctx, skill_dir: str) -> set:
    py_files = set()
    has_entries = False
    for bs_key in _CONFIRMED_DEAD_SOURCES:
        entries = _entry_sequence(report.get(bs_key))
        if entries:
            has_entries = True
        for entry in entries:
            full = _confirmed_entry_file(entry, skill_dir)
            if full is not None:
                py_files.add(full)
    if not py_files and not has_entries:
        if diag_ctx is not None:
            py_files.update(diag_ctx.py_files)
        else:
            py_files.update(collect_py_files_default(skill_dir))
    elif not py_files:
        logger.debug("语义审查: 死代码条目均无可读文件路径，跳过全文件回退扫描")
    return py_files
def _marker_counts(findings: list[dict]) -> dict[str, int]:
    return {
        marker: sum(1 for f in findings if f.get("regex") == pattern)
        for marker, pattern in _MARKER_PATTERNS
    }
def heuristic_semantic_review(report: dict, diag_ctx=None) -> dict:
    report = dict_or_empty(report)
    skill_dir = _report_skill_dir(report)
    if not skill_dir:
        return _empty_review_result()
    _materialize_report_entry_iterators(report)
    if not _has_confirmed_dead_evidence(report):
        return _empty_review_result()
    py_files = _semantic_review_targets(report, diag_ctx, skill_dir)
    findings, counts = scan_files_for_satd(
        py_files, _SATD_PATTERNS, _SATD_NEGATION_PHRASES, diag_ctx, skill_dir
    )
    marker_counts = _marker_counts(findings)
    return {
        "hints": sum(counts.values()),
        "safe_to_remove": counts.get("safe_to_remove", 0),
        "needs_review": counts.get("needs_review", 0),
        "keep_for_future": counts.get("keep_for_future", 0),
        "documentation_debt": counts.get("documentation_debt", 0),
        "test_debt": counts.get("test_debt", 0),
        "marker_counts": marker_counts,
        "findings": findings[:20],
    }

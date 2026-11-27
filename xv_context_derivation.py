from __future__ import annotations

import itertools
import logging
import math
import os
import re
import threading
from collections import Counter
from dataclasses import (
    dataclass,
    field,
)
from types import SimpleNamespace
from typing import (
    Any,
    NamedTuple,
)

from jwsgj.diag_guard_io import (
    check_path_traversal,
)
from jwsgj.diag_types_normalize import (
    coerce_line,
    dict_or_empty,
    finding_file_key,
    finding_file_path,
    finite_float_or_none,
    identifier_text,
    is_finite_num,
    is_number,
    is_real_number,
    method_status_detail,
    parse_locator_file,
    safe_float,
    safe_int,
    str_or,
    timestamp_ms,
)
from jwsgj.diag_types_vocab import (
    CONF_CAP,
    CONF_MEDIUM,
    CV_RULES,
    FIELD_ADJUSTED_CONFIDENCE,
    LEGACY_TO_SUB,
    PERCENT_FACTOR,
    RULE_FAMILY_MAP,
    SUB_ENGINE_META,
    UNTESTED_COVERAGE_BLINDSPOT_TYPES,
)
from jwsgj.fix_guide_rule_identity import (
    RULE_FAMILY_SETS,
    lookup_rule_family,
)
from jwsgj.log_config import (
    log_swallowed,
)
from jwsgj.runtime_paths import (
    resolve_skill_dir,
)
from jwsgj.xv_intermediate_store import (
    get_round_start_ts,
    load_intermediate_fused,
    locate_sub_results,
)

logger = logging.getLogger(__name__)
__all__ = [
    'COMPLEXITY_BOOST',
    'COVERAGE_BOOST',
    'COVERAGE_CRITICAL',
    'COVERAGE_SUFFICIENT',
    'DEGRADED_STATUSES',
    'HIGH_COMPLEXITY_CC',
    'HOTSPOT_BOOST',
    'METHOD_EVIDENCE_TYPES',
    'METHOD_REGISTRY',
    'PHASES',
    'TERMINAL_STATUSES',
    'TREATMENT_PHASE',
    'UNCOVERED_THRESHOLD_PCT',
    'AnalysisContext',
    'ContextKey',
    'CrossValidationEnricher',
    'MethodConfig',
    'PhaseConfig',
    'all_method_ids',
    'analyze_degradation_impact',
    'available_evidence_methods',
    'build_context_from_intermediates',
    'business_payload',
    'check_coverage',
    'check_method_registry_reachability',
    'coverage_mapping',
    'derive_skill_dir_and_graph',
    'finding_producing_methods',
    'func_executed_count',
    'generate_missing_placeholders',
    'get_rule_required_methods',
    'inject_quadrant_findings',
    'iter_func_coverage',
    'lookup_method_phase',
    'metric_only_methods',
    'normalize_method_status',
    'normalized_independent_results',
    'sub_engine_payload',
    'sub_result',
    'verify_full_participation',
]
def _as_source_ids(value):
    if isinstance(value, (str, bytes)):
        return (value,) if value else ()
    return value or ()
def _skill_root_arg(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    try:
        raw = os.fspath(value)
    except TypeError:
        raise TypeError(
            f"skill_dir 须为 str 或 PathLike，实际为 {type(value).__name__}: "
            f"{value!r}") from None
    return raw if isinstance(raw, str) else os.fsdecode(raw)
TERMINAL_STATUSES: tuple[str, ...] = ("pass", "warn", "fail", "timeout")
_PRESENT_STATUSES = frozenset({"pass", "warn", "fail"})
@dataclass(frozen=True)
class MethodConfig:
    id: str
    name: str
    domain: str
    produces_findings: bool
    cv_rules: list[str] = field(default_factory=list)
    depends_on: list[str] = field(default_factory=list)
    needs_cache: bool = True
@dataclass(frozen=True)
class PhaseConfig:
    name: str
    methods: list[str]
    quick_skip: bool = False
PHASES: list[PhaseConfig] = [
    PhaseConfig("阶段A: 文件级扫描+健康评估+文档质量", ["A"]),
    PhaseConfig("阶段B: AST核心+历史模式",           ["B"]),
    PhaseConfig("阶段C: 运行时分析",                 ["C"]),
    PhaseConfig("阶段D: 安全深入分析",               ["D"]),
    PhaseConfig("阶段E: 测试执行",                   ["E"], quick_skip=True),
]
TREATMENT_PHASE = PhaseConfig("阶段F: 治疗执行", ["F"])
def _derive_cv_rules(method_id: str, declared=None) -> list[str]:
    rules = list(_as_source_ids(declared))
    for rule_id, desc in CV_RULES.items():
        if method_id in desc.source_methods and rule_id not in rules:
            rules.append(rule_id)
    return rules
def _make_method_registry():
    def _mk(method_id, name, domain, findings, cv=None, dep=None):
        return MethodConfig(
            id=method_id, name=name, domain=domain, produces_findings=findings,
            cv_rules=_derive_cv_rules(method_id, cv), depends_on=list(dep or []))
    _entries = [
        ("A", "主引擎A: 五维文件分析+健康评估+静默降级+文档质量",
              "diagnosis", True,
              ["规则52","规则53","规则54","规则27","规则51"], []),
        ("B", "主引擎B: AST核心检测+历史模式",
              "analysis", True,
              ["规则2","规则3","规则4","规则6","规则7","规则8","规则9","规则10",
               "规则12","规则13","规则42","规则49","规则28","规则30","规则35"], []),
        ("C", "主引擎C: 运行时分析（调用图+沙箱+资源泄漏）",
              "diagnosis", True,
              ["规则1","规则8","规则10","规则11","规则21","规则43"], []),
        ("D", "主引擎D: 安全深入分析（统一安全+符号执行）",
              "analysis", True,
              ["规则2","规则12","规则47","规则22"], []),
        ("E", "主引擎E: 测试执行（统一测试+定向突变+后处理）",
              "test", True,
              ["规则4","规则5","规则8","规则29","规则33","规则45"], []),
        # F 产出的是 actions[].findings 形式的真实缺陷（治疗链汇总前序发现），
        # 标记为 False 会让 available_evidence_methods / 证据强度上限 / CV 规则
        # 派生三条链路同时漏掉 F 的产出。
        ("F", "主引擎F: 治疗链（修复清单+安全操作+门禁+等价性+重构+清理）",
              "treatment", True, ["规则18","规则23"], ["B"]),
    ]
    return {
        mid: _mk(mid, name, domain, findings, cv, dep)
        for mid, name, domain, findings, cv, dep in _entries
    }
METHOD_REGISTRY: dict[str, MethodConfig] = _make_method_registry()
def lookup_method_phase(mid: str) -> str:
    try:
        for phase in PHASES:
            if mid in phase.methods:
                return phase.name
        if mid in TREATMENT_PHASE.methods:
            return TREATMENT_PHASE.name
    except Exception as e:  # noqa: BLE001
        logger.warning("lookup_method_phase(%s) failed: %s", mid, e)
    return ""
METHOD_EVIDENCE_TYPES: dict[str, set[str]] = {
    "A": {"ast", "metric", "manual", "static_text", "config"},
    "B": {"ast", "static_text", "cohesion", "history"},
    "C": {"call_graph", "dynamic", "resource"},
    "D": {"ast", "static_text", "resource", "dynamic"},
    "E": {"runtime", "coverage", "dynamic", "test_quality"},
    # F 的证据来自治疗链子引擎（门禁/等价性/重构/清理），缺登记会让
    # 证据类型聚合与置信度上限计算把 F 当成无证据方法。
    "F": {"ast", "static_text", "resource", "test_quality"},
}
COVERAGE_CRITICAL: float = 0.30
COVERAGE_SUFFICIENT: float = 0.70
DEGRADED_STATUSES: tuple = ("missing", "corrupted", "skip", "error", "timeout")
_MISSING_STATUSES: frozenset[str] = frozenset(DEGRADED_STATUSES) & {
    "missing", "corrupted"}
_SKIPPED_STATUSES: frozenset[str] = frozenset(DEGRADED_STATUSES) & {"skip"}
_STATUS_BUCKET_PRESENT = "present"
_STATUS_BUCKET_MISSING = "missing"
_STATUS_BUCKET_SKIPPED = "skipped"
_STATUS_BUCKET_DEGRADED = "degraded"
_STATUS_BUCKET_ORDER: tuple[str, ...] = (
    _STATUS_BUCKET_PRESENT,
    _STATUS_BUCKET_MISSING,
    _STATUS_BUCKET_SKIPPED,
    _STATUS_BUCKET_DEGRADED,
)
def normalize_method_status(raw: object) -> str:
    if isinstance(raw, str):
        status = raw.strip().casefold()
        if status:
            detail = method_status_detail(status)
            if detail == "corrupted" and status not in {"corrupted", "corrupt"}:
                return status
            return detail
    return "missing"
def generate_missing_placeholders(cv) -> None:
    results = getattr(cv, "independent_results", None)
    if not isinstance(results, dict):
        results = {}
        cv.independent_results = results
    for mid, cfg in METHOD_REGISTRY.items():
        if mid not in results:
            results[mid] = {
                "method_id": mid, "method_name": cfg.name,
                "domain": cfg.domain, "status": "missing",
                "payload": {}, "error": "中间结果文件缺失",
                "_missing": True,
                "findings_list": [],
                "rule_families_produced": [],
                "partial": True,
                "quality_flags": ["missing_placeholder"],
                "evidence_types": [],
                "execution_mode": "missing",
                "degradation_context": {
                    "affected_rules": list(cfg.cv_rules),
                    "reason": "missing",
                },
                "timestamp": timestamp_ms(),
                "duration_ms": 0,
                "phase": lookup_method_phase(mid),
            }
def _entry_status(entry) -> str:
    if not isinstance(entry, dict) or entry.get("_missing"):
        return "missing"
    return normalize_method_status(entry.get("status"))
def _method_status_bucket(entry) -> str:
    status = _entry_status(entry)
    if status in _PRESENT_STATUSES:
        return _STATUS_BUCKET_PRESENT
    if status in _MISSING_STATUSES:
        return _STATUS_BUCKET_MISSING
    if status in _SKIPPED_STATUSES:
        return _STATUS_BUCKET_SKIPPED
    return _STATUS_BUCKET_DEGRADED
def _method_status_index(cv) -> tuple[dict[str, list[str]], dict[str, int]]:
    buckets: dict[str, list[str]] = {name: [] for name in _STATUS_BUCKET_ORDER}
    status_counts: dict[str, int] = {}
    results = normalized_independent_results(cv)
    for mid in METHOD_REGISTRY:
        entry = results.get(mid)
        buckets[_method_status_bucket(entry)].append(mid)
        status = _entry_status(entry)
        status_counts[status] = status_counts.get(status, 0) + 1
    return buckets, status_counts
def check_coverage(cv) -> dict:
    total_registered = len(METHOD_REGISTRY)
    buckets, _status_counts = _method_status_index(cv)
    present_methods = buckets[_STATUS_BUCKET_PRESENT]
    missing_methods = buckets[_STATUS_BUCKET_MISSING]
    skipped_methods = buckets[_STATUS_BUCKET_SKIPPED]
    degraded_methods = buckets[_STATUS_BUCKET_DEGRADED]
    real_count = len(present_methods)
    placeholder_count = (len(missing_methods) + len(skipped_methods)
                         + len(degraded_methods))
    coverage_rate = real_count / max(total_registered, 1)
    sufficient = coverage_rate >= COVERAGE_SUFFICIENT
    critical = coverage_rate < COVERAGE_CRITICAL
    report = {
        "total_registered": total_registered,
        "real_method_count": real_count,
        "placeholder_count": placeholder_count,
        "coverage_rate": round(coverage_rate, 4),
        "missing_methods": missing_methods,
        "skipped_methods": skipped_methods,
        "degraded_methods": degraded_methods,
        "sufficient": sufficient,
        "critical": critical,
    }
    if not sufficient:
        logger.warning("[CV-Coverage] Method coverage insufficient: "
                      "%.1f%% (%d/%d real, %d missing, %d skipped, %d degraded)",
                      coverage_rate * PERCENT_FACTOR, real_count,
                      total_registered, len(missing_methods),
                      len(skipped_methods), len(degraded_methods))
    if critical:
        logger.error("[CV-Coverage] CRITICAL: coverage < %.0f%%, "
                     "CV results will be unreliable",
                     COVERAGE_CRITICAL * PERCENT_FACTOR)
    return report
def verify_full_participation(cv2) -> dict:
    total = len(METHOD_REGISTRY)
    buckets, status_counts = _method_status_index(cv2)
    present = buckets[_STATUS_BUCKET_PRESENT]
    missing = buckets[_STATUS_BUCKET_MISSING]
    skipped = buckets[_STATUS_BUCKET_SKIPPED]
    degraded = buckets[_STATUS_BUCKET_DEGRADED]
    participation_rate = (
        round(len(present) / total * PERCENT_FACTOR, 1) if total > 0 else 0.0)
    absent = len(missing) + len(skipped) + len(degraded)
    return {
        "total_methods": total,
        "present": len(present),
        "missing": missing,
        "skipped": skipped,
        "degraded": degraded,
        "participation_rate": participation_rate,
        "status_breakdown": status_counts,
        "all_participated": absent == 0,
        "summary": (
            f"{len(present)}/{total} 方法参与 ({participation_rate}%)"
            + (f"; 缺失: {len(missing)}, 跳过: {len(skipped)}, "
               f"降级: {len(degraded)}"
               if absent else "")
        ),
    }
def _method_registry_ids(predicate, label: str) -> list[str]:
    try:
        return [mid for mid, cfg in METHOD_REGISTRY.items() if predicate(cfg)]
    except Exception as e:  # noqa: BLE001
        logger.warning("[XV] %s 获取失败: %s", label, e)
        return []
def all_method_ids(quick_mode: bool = False) -> list[str]:
    """按相位顺序返回全部诊断方法 ID（含 F 组治疗执行）。

    F 组挂在 TREATMENT_PHASE 而非 PHASES 上，只遍历 PHASES 会把 F 排除在
    ``get_diagnosis_progress().next_method`` 之外——而 ``next_method`` 正是批量
    诊断的推进入口，结果是 F 引擎（死代码检测）在完整管线中永远不可达。
    """
    try:
        ids = []
        for phase in (*PHASES, TREATMENT_PHASE):
            if quick_mode and phase.quick_skip:
                continue
            ids.extend(phase.methods)
        return ids
    except Exception as e:  # noqa: BLE001
        logger.warning("[XV] 方法ID列表获取失败 in all_method_ids(): %s", e)
        return []
def check_method_registry_reachability() -> dict:
    """方法注册表可达性：METHOD_REGISTRY 与 all_method_ids() 必须双向一致。

    历史缺陷：F 组挂在 TREATMENT_PHASE 上，而 all_method_ids 只遍历 PHASES，
    结果 F 注册齐备却永不进入 ``next_method``——完整管线静默跳过死代码检测，
    归零门禁反而因为「没有发现」而放行。本守卫把四个维度都变成硬错误：
    注册但不可达、可枚举但未注册、方法 ID 重复、缺证据类型登记。

    返回 ``{"ok": bool, "issues": [...], "actions_required": [...]}``；
    守卫自身异常一律按未通过返回（不得当作放行信号）。
    """
    try:
        enumerated = all_method_ids()
        registered = list(METHOD_REGISTRY)
        unreachable = [mid for mid in registered if mid not in enumerated]
        unregistered = [mid for mid in enumerated if mid not in METHOD_REGISTRY]
        duplicates = sorted(
            mid for mid, count in Counter(enumerated).items() if count > 1)
        missing_evidence = sorted(
            mid for mid in enumerated if mid not in METHOD_EVIDENCE_TYPES)
        issues: list[str] = []
        actions: list[str] = []
        if unreachable:
            issues.append(f"注册但不可达（永不执行）: {unreachable}")
            actions.append("把未枚举的方法 ID 补入 PHASES/TREATMENT_PHASE")
        if unregistered:
            issues.append(f"可枚举但未注册（执行即报错）: {unregistered}")
            actions.append("在 METHOD_REGISTRY 补齐方法配置")
        if duplicates:
            issues.append(f"方法 ID 重复枚举: {duplicates}")
            actions.append("去重相位定义，每个方法 ID 只能出现一次")
        if missing_evidence:
            issues.append(f"缺证据类型登记: {missing_evidence}")
            actions.append("在 METHOD_EVIDENCE_TYPES 补齐证据类型")
        return {"ok": not issues, "methods": enumerated,
                "registered": registered, "issues": issues,
                "actions_required": actions}
    except Exception as exc:  # 门禁异常保守阻塞
        logger.exception("[XV] 方法注册表可达性校验异常，保守阻塞")
        return {"ok": False, "methods": [], "registered": [],
                "issues": [f"守卫执行异常: {type(exc).__name__}: {exc}"],
                "actions_required": ["修复方法注册表后重跑"]}
def finding_producing_methods() -> list[str]:
    return _method_registry_ids(
        lambda cfg: cfg.produces_findings, "findings方法列表")
def metric_only_methods() -> list[str]:
    return _method_registry_ids(
        lambda cfg: not cfg.produces_findings, "指标方法列表")
UNCOVERED_THRESHOLD_PCT = 40
HIGH_COMPLEXITY_CC = 15
COVERAGE_BOOST = 0.15
COMPLEXITY_BOOST = 0.10
HOTSPOT_BOOST = 0.10
def _top100_by_complexity(entries: list[dict], cc_key: str) -> list[dict]:
    return sorted(entries,
                  key=lambda e: safe_float(e.get(cc_key), 0.0),
                  reverse=True)[:100]
def _same_file_name(left, right) -> bool:
    left_key = finding_file_key(left)
    right_key = finding_file_key(right)
    if not left_key or not right_key or left_key == right_key:
        return bool(left_key and left_key == right_key)
    left_parts = tuple(part for part in left_key.split("/") if part)
    right_parts = tuple(part for part in right_key.split("/") if part)
    if not left_parts or not right_parts or left_parts[-1] != right_parts[-1]:
        return False
    left_is_absolute = (left_key.startswith("/")
                        or (len(left_key) > 2 and left_key[1:3] == ":/"))
    right_is_absolute = (right_key.startswith("/")
                         or (len(right_key) > 2 and right_key[1:3] == ":/"))
    if left_is_absolute != right_is_absolute:
        if left_is_absolute:
            absolute_parts, relative_parts = left_parts, right_parts
        else:
            absolute_parts, relative_parts = right_parts, left_parts
        return (len(relative_parts) <= len(absolute_parts)
                and absolute_parts[-len(relative_parts):] == relative_parts)
    if left_is_absolute:
        return False
    return "/" not in left_key or "/" not in right_key
def _select_file_candidates(candidates: list[tuple], file_key: str) -> list[tuple]:
    target = finding_file_key(file_key)
    exact = [item for item in candidates
             if target and finding_file_key(item[0]) == target]
    if exact:
        return exact
    basename = [item for item in candidates
                if _same_file_name(item[0], file_key)]
    identities = {finding_file_key(item[0]) for item in basename}
    return basename if len(identities) == 1 else []
def _iter_same_file(entries, file_key: str):
    if not isinstance(entries, list):
        return
    candidates = [(finding_file_path(entry), entry)
                  for entry in entries if isinstance(entry, dict)]
    for _path, entry in _select_file_candidates(candidates, file_key):
        yield entry
class ContextKey:
    CALL_GRAPH = "call_graph"
    ORPHAN_FUNCTIONS = "orphan_functions"
    BLINDSPOTS = "blindspots"
    COVERAGE_BY_FILE = "coverage_by_file"
    COVERAGE_OVERALL = "coverage_overall"
    UNCOVERED_FILES = "uncovered_files"
    COMPLEXITY_BY_FILE = "complexity_by_file"
    HIGH_COMPLEXITY_FUNCS = "high_complexity_funcs"
    PERFORMANCE_HOTSPOTS = "performance_hotspots"
def _collect_degraded_methods(cv) -> list[dict]:
    degraded_methods = []
    results = normalized_independent_results(cv)
    for mid, cfg in METHOD_REGISTRY.items():
        entry = results.get(mid)
        bucket = _method_status_bucket(entry)
        if bucket == _STATUS_BUCKET_PRESENT:
            continue
        degraded_methods.append({
            "mid": mid, "name": cfg.name,
            "status": _entry_status(entry), "bucket": bucket,
            "partial": dict_or_empty(entry).get("partial", False),
            "affected_rules": list(cfg.cv_rules),
        })
    return degraded_methods
def _available_method_count(required: list, cv) -> int:
    results = normalized_independent_results(cv)
    return sum(
        1 for m in required
        if _method_status_bucket(results.get(m)) == _STATUS_BUCKET_PRESENT)
def _availability_level(avail: int, total: int) -> str:
    if total == 0 or avail == total:
        return "full"
    return "none" if avail == 0 else "partial"
def _classify_rule_availability(cv) -> tuple[list, list, list]:
    buckets = {"full": [], "partial": [], "none": []}
    for rule_id in CV_RULES:
        required = get_rule_required_methods(rule_id)
        level = _availability_level(_available_method_count(required, cv),
                                    len(required))
        buckets[level].append(rule_id)
    return buckets["full"], buckets["partial"], buckets["none"]
def _degradation_summary(degraded_methods: list[dict],
                         fully_degraded: list, partially_degraded: list) -> str:
    total_d = len(degraded_methods)
    if total_d == 0:
        return f"全部{len(METHOD_REGISTRY)}个方法正常参与交叉验证，无降级影响"
    missing_names = [d["mid"] for d in degraded_methods
                     if d["bucket"] == _STATUS_BUCKET_MISSING]
    skipped_names = [d["mid"] for d in degraded_methods
                     if d["bucket"] == _STATUS_BUCKET_SKIPPED]
    degraded_names = [d["mid"] for d in degraded_methods
                      if d["bucket"] == _STATUS_BUCKET_DEGRADED]
    summary = f"{total_d}个方法异常"
    if missing_names:
        summary += f"(缺失: {','.join(missing_names)})"
    if skipped_names:
        summary += f"(跳过: {','.join(skipped_names)})"
    if degraded_names:
        summary += f"(降级: {','.join(degraded_names)})"
    summary += (f"，影响{len(fully_degraded)}条规则完全降级、"
                f"{len(partially_degraded)}条规则部分降级")
    return summary
def analyze_degradation_impact(cv) -> dict:
    degraded_methods = _collect_degraded_methods(cv)
    fully_available, partially_degraded, fully_degraded = (
        _classify_rule_availability(cv))
    _apply_platform_conservative_mode(cv, len(degraded_methods),
                                       len(METHOD_REGISTRY))
    return {
        "degraded_methods": degraded_methods,
        "fully_available_rules": sorted(fully_available),
        "partially_degraded_rules": sorted(partially_degraded),
        "fully_degraded_rules": sorted(fully_degraded),
        "summary": _degradation_summary(
            degraded_methods, fully_degraded, partially_degraded),
    }
_THRESHOLD_KEYS: tuple = ("AUTO_CONFIRM_THRESHOLD", "AUTO_STRENGTH_THRESHOLD")
_DEGRADATION_RATIO_HIGH: float = 0.25
def _platform_threshold_pair(cv) -> tuple[float, float] | None:
    confirm = finite_float_or_none(
        getattr(cv, "AUTO_CONFIRM_THRESHOLD", None))
    strength = finite_float_or_none(
        getattr(cv, "AUTO_STRENGTH_THRESHOLD", None))
    if confirm is not None and strength is not None:
        return confirm, strength
    return None
def _class_threshold(cv, key: str, fallback: float) -> float:
    value = finite_float_or_none(getattr(type(cv), key, None))
    return value if value is not None else fallback
def _snapshot_platform_thresholds(cv) -> None:
    snapshot = _platform_threshold_pair(cv)
    if snapshot is None:
        return
    cv._platform_threshold_snapshot = snapshot
    own_attrs = getattr(cv, "__dict__", {})
    cv._platform_had_override = {
        _key: _key in own_attrs for _key in _THRESHOLD_KEYS}
def _enter_platform_conservative_mode(cv, degraded_count: int,
                                      total_registered: int,
                                      ratio: float) -> None:
    current = _platform_threshold_pair(cv)
    if current is None:
        logger.info("[CV-P3] 平台降级保守模式跳过：%s 未声明数值阈值属性",
                    type(cv).__name__)
        return
    current_confirm, current_strength = current
    base_snapshot = (getattr(cv, "_platform_threshold_snapshot", None)
                     if getattr(cv, "_platform_degraded", False) else None)
    if not _platform_snapshot_ok(base_snapshot):
        base_snapshot = current
    base_confirm = _class_threshold(
        cv, "AUTO_CONFIRM_THRESHOLD", base_snapshot[0])
    base_strength = _class_threshold(
        cv, "AUTO_STRENGTH_THRESHOLD", base_snapshot[1])
    new_confirm = max(current_confirm,
                      min(max(base_confirm * 1.10, 0.80), 0.90))
    new_strength = max(current_strength,
                       min(max(base_strength * 1.10, CONF_MEDIUM), CONF_CAP))
    try:
        if not getattr(cv, "_platform_degraded", False):
            _snapshot_platform_thresholds(cv)
        cv.AUTO_CONFIRM_THRESHOLD = new_confirm
        cv.AUTO_STRENGTH_THRESHOLD = new_strength
        cv._platform_degraded = True
    except AttributeError as exc:
        snapshot = getattr(cv, "_platform_threshold_snapshot", None)
        if _platform_snapshot_ok(snapshot):
            try:
                _restore_platform_thresholds(cv)
            except AttributeError as rollback_exc:
                logger.warning("[CV-P3] 阈值写入失败后的回滚未完成: %s",
                               rollback_exc)
        logger.info("[CV-P3] 平台降级保守模式跳过：%s 阈值载体不可写 (%s)",
                    type(cv).__name__, type(exc).__name__)
        return
    logger.info("[CV-P3] 平台降级保守模式(阈值上调): "
                "confirm=%.3f strength=%.3f (%d/%d 方法降级 %.0f%%)",
                cv.AUTO_CONFIRM_THRESHOLD, cv.AUTO_STRENGTH_THRESHOLD,
                degraded_count, total_registered, ratio * PERCENT_FACTOR)
def _platform_snapshot_ok(snapshot) -> bool:
    return (isinstance(snapshot, tuple) and len(snapshot) == 2
            and all(is_real_number(_v) and math.isfinite(_v)
                    for _v in snapshot))
def _restore_platform_thresholds(cv) -> None:
    snapshot = getattr(cv, "_platform_threshold_snapshot", None)
    _had = getattr(cv, "_platform_had_override", None)
    own_attrs = getattr(cv, "__dict__", None)
    _snapshot_ok = _platform_snapshot_ok(snapshot)
    for _key, _snap_v in zip(
            _THRESHOLD_KEYS,
            snapshot if _snapshot_ok else (None, None),
            strict=True):
        had_override = (isinstance(_had, dict)
                        and _had.get(_key) is True)
        restore_value = (
            _snapshot_ok
            and (not isinstance(own_attrs, dict) or had_override))
        if restore_value:
            if getattr(cv, _key, None) != _snap_v:
                setattr(cv, _key, _snap_v)
        elif isinstance(own_attrs, dict):
            own_attrs.pop(_key, None)
    cv._platform_degraded = False
def _apply_platform_conservative_mode(cv, degraded_count: int,
                                      total_registered: int) -> None:
    ratio = degraded_count / max(total_registered, 1)
    if ratio > _DEGRADATION_RATIO_HIGH:
        _enter_platform_conservative_mode(
            cv, degraded_count, total_registered, ratio)
        return
    if getattr(cv, "_platform_degraded", False):
        _restore_platform_thresholds(cv)
def get_rule_required_methods(rule_id: str) -> list[str]:
    desc = CV_RULES.get(rule_id)
    if desc is not None:
        return list(desc.source_methods)
    return []
class AnalysisContext:
    def __init__(self):
        self._data: dict[str, Any] = {}
        self._lock = threading.RLock()
        self._providers: set[str] = set()
    def set(self, key: str, value: Any, provider: str = ""):
        with self._lock:
            self._data[key] = value
            if provider:
                self._providers.add(provider)
        logger.debug("[Context] SET %s by %s (type=%s)",
                     key, provider, type(value).__name__)
    def get(self, key: str, default: Any = None) -> Any:
        with self._lock:
            return self._data.get(key, default)
    def has(self, key: str) -> bool:
        with self._lock:
            return key in self._data
    def get_all(self) -> dict[str, Any]:
        with self._lock:
            return dict(self._data)
    @property
    def available_keys(self) -> list[str]:
        with self._lock:
            return sorted(self._data.keys())
    @property
    def provider_count(self) -> int:
        with self._lock:
            return len(self._providers)
class CrossValidationEnricher:
    def __init__(self, context: AnalysisContext):
        self.context = context
    def enrich_finding(self, finding: dict) -> dict:
        if not isinstance(finding, dict):
            return finding
        enrichment = {
            "coverage_context": None,
            "complexity_context": None,
            "hotspot_context": None,
            "priority_boost": 0.0,
        }
        file_key = finding_file_path(finding)
        if not file_key:
            locator = finding.get("locator") or ""
            file_key = parse_locator_file(locator)
        if not file_key or file_key == "unknown":
            return self._merge(finding, enrichment)
        self._enrich_coverage(file_key, enrichment)
        self._enrich_complexity(finding, file_key, enrichment)
        self._enrich_hotspot(finding, file_key, enrichment)
        return self._merge(finding, enrichment)
    def _context_mapping(self, key: str) -> dict | None:
        value = self.context.get(key)
        return value if isinstance(value, dict) and value else None
    def _enrich_coverage(self, file_key: str, enrichment: dict) -> None:
        cov_by_file = self._context_mapping(ContextKey.COVERAGE_BY_FILE)
        if cov_by_file is None:
            return
        cov = finite_float_or_none(self._find_file_in_dict(cov_by_file, file_key))
        if cov is None:
            return
        is_uncovered = cov < UNCOVERED_THRESHOLD_PCT
        enrichment["coverage_context"] = {
            "file_coverage": cov,
            "is_uncovered": is_uncovered,
        }
        if is_uncovered:
            enrichment["priority_boost"] += COVERAGE_BOOST
            enrichment["coverage_context"]["risk"] = "未覆盖代码路径，问题可能被隐藏"
    def _enrich_complexity(self, finding: dict, file_key: str,
                           enrichment: dict) -> None:
        fn_cc = self._function_complexity(finding, file_key)
        if fn_cc is not None:
            is_high = fn_cc > HIGH_COMPLEXITY_CC
            enrichment["complexity_context"] = self._complexity_context(
                fn_cc, "function",
                risk="高复杂度函数，维护风险高" if is_high else "")
            if is_high:
                enrichment["priority_boost"] += COMPLEXITY_BOOST
            return
        cc = self._file_complexity(file_key)
        if cc is not None:
            enrichment["complexity_context"] = self._complexity_context(
                cc, "file")
    def _file_complexity(self, file_key: str) -> float | None:
        complexity_by_file = self._context_mapping(ContextKey.COMPLEXITY_BY_FILE)
        if complexity_by_file is None:
            return None
        return finite_float_or_none(
            self._find_file_in_dict(complexity_by_file, file_key))
    @staticmethod
    def _complexity_context(cc: float, granularity: str,
                            risk: str = "") -> dict:
        payload = {
            "max_complexity": cc,
            "complexity_granularity": granularity,
            "is_high_complexity": cc > HIGH_COMPLEXITY_CC,
        }
        if risk:
            payload["risk"] = risk
        return payload
    def _file_hotspots(self, file_key: str) -> list[dict]:
        return list(_iter_same_file(
            self.context.get(ContextKey.PERFORMANCE_HOTSPOTS), file_key))
    @staticmethod
    def _build_hotspot_context(entries: list[dict], granularity: str) -> dict:
        return {
            "hotspot_count": len(entries),
            "functions": [str(h.get("function") or "")
                          for h in entries[:5]],
            "hotspot_granularity": granularity,
        }
    def _enrich_hotspot(self, finding: dict, file_key: str,
                        enrichment: dict) -> None:
        matching = self._file_hotspots(file_key)
        if not matching:
            return
        fname = str(finding.get("function")
                    or finding.get("func_name") or "")
        fn_matching = ([h for h in matching
                        if str(h.get("function") or "") == fname]
                       if fname else [])
        if fn_matching:
            enrichment["hotspot_context"] = self._build_hotspot_context(
                fn_matching, "function")
            enrichment["priority_boost"] += HOTSPOT_BOOST
            return
        enrichment["hotspot_context"] = self._build_hotspot_context(
            matching, "file")
    def _iter_file_complexity_entries(self, file_key: str):
        hcf_list = self.context.get(ContextKey.HIGH_COMPLEXITY_FUNCS)
        for h in _iter_same_file(hcf_list, file_key):
            h_cc = finite_float_or_none(h.get("complexity"))
            if h_cc is None:
                continue
            yield h_cc, h
    def _match_complexity_by_name(self, file_key: str, fname: str) -> float | None:
        matched = None
        for h_cc, h in self._iter_file_complexity_entries(file_key):
            h_name = str(h.get("name") or h.get("function") or "")
            if h_name != fname:
                continue
            if matched is not None:
                return None
            matched = h_cc
        return matched
    def _match_complexity_by_line(self, file_key: str, fline) -> float | None:
        if not fline:
            return None
        f_n = safe_float(fline, None)
        for h_cc, h in self._iter_file_complexity_entries(file_key):
            h_line = h.get("line")
            if f_n is None:
                if fline == h_line:
                    return h_cc
            elif f_n == safe_float(h_line, None):
                return h_cc
        return None
    def _function_complexity(self, finding: dict, file_key: str) -> float | None:
        fline = finding.get("line") or finding.get("lineno") or 0
        line_cc = self._match_complexity_by_line(file_key, fline)
        if line_cc is not None:
            return line_cc
        fname = str(finding.get("function") or finding.get("func_name") or "")
        if fname:
            return self._match_complexity_by_name(file_key, fname)
        return None
    def enrich_findings(self, findings: list[dict]) -> list[dict]:
        if findings is None or isinstance(findings, (str, bytes)):
            return []
        try:
            items = list(findings)
        except TypeError as _e:
            log_swallowed(__name__, _e,
                          context=f'CrossValidationEnricher.enrich_findings:{type(_e).__name__}')
            return []
        enriched = []
        for f in items:
            try:
                enriched.append(self.enrich_finding(f))
            except Exception as _e:  # noqa: BLE001
                log_swallowed(
                    __name__, _e,
                    context=f'CrossValidationEnricher.enrich_findings:{type(_e).__name__}')
                enriched.append(f)
        return enriched
    def get_context_summary(self) -> dict:
        orphan_count = self._count_payload(
            self.context.get(ContextKey.ORPHAN_FUNCTIONS))
        blindspot_count = self._count_payload(
            self.context.get(ContextKey.BLINDSPOTS))
        return {
            "available_keys": self.context.available_keys,
            "provider_count": self.context.provider_count,
            "coverage_available": self.context.has(ContextKey.COVERAGE_BY_FILE),
            "complexity_available": self.context.has(ContextKey.COMPLEXITY_BY_FILE),
            "hotspots_available": self.context.has(ContextKey.PERFORMANCE_HOTSPOTS),
            "call_graph_available": self.context.has(ContextKey.CALL_GRAPH),
            "orphan_count": orphan_count,
            "blindspot_count": blindspot_count,
            "uncovered_file_count": self._count_payload(
                self.context.get(ContextKey.UNCOVERED_FILES)),
            "high_complexity_count": self._count_high_complexity(
                self.context.get(ContextKey.HIGH_COMPLEXITY_FUNCS)),
        }
    @staticmethod
    def _count_payload(value) -> int:
        if isinstance(value, (list, dict)):
            return len(value)
        if is_finite_num(value):
            return max(0, int(value))
        return 0
    @staticmethod
    def _count_high_complexity(entries) -> int:
        if not isinstance(entries, list):
            return 0
        count = 0
        for entry in entries:
            cc = finite_float_or_none(dict_or_empty(entry).get("complexity"))
            if cc is not None and cc > HIGH_COMPLEXITY_CC:
                count += 1
        return count
    @staticmethod
    def _find_file_in_dict(data: dict, file_key: str) -> Any | None:
        if file_key in data:
            return data[file_key]
        matches = _select_file_candidates(list(data.items()), file_key)
        return matches[0][1] if matches else None
    def _merge(self, finding: dict, enrichment: dict) -> dict:
        result = dict(finding)
        result["context_enrichment"] = enrichment
        boost = finite_float_or_none(enrichment.get("priority_boost", 0))
        if boost is None or boost <= 0:
            return result
        target = next(
            (field for field in (FIELD_ADJUSTED_CONFIDENCE, "confidence")
             if field in result), "")
        old_conf = safe_float(result.get(target), None) if target else None
        if old_conf is None and target == FIELD_ADJUSTED_CONFIDENCE:
            old_conf = safe_float(result.get("confidence"), None)
        if old_conf is None:
            return result
        result[target] = max(0.0, min(1.0, old_conf + boost))
        result["_context_boost"] = round(boost, 2)
        return result
def business_payload(result: dict) -> dict:
    try:
        p = result.get("payload") if isinstance(result, dict) else None
        if not isinstance(p, dict):
            return {}
        inner = p.get("payload")
        if isinstance(inner, dict) and inner:
            return inner
        return p
    except Exception as e:  # noqa: BLE001
        logger.warning("business_payload: %s", e)
        return {}
def _resolve_sub_id(method_id: str) -> str:
    if not method_id:
        return ""
    sub_id = LEGACY_TO_SUB.get(method_id, "")
    if not sub_id and method_id in SUB_ENGINE_META:
        sub_id = method_id
    return sub_id
def _sub_payload_from_view(p: dict, sub_id: str) -> dict | None:
    subs = locate_sub_results(p)
    if sub_id not in subs:
        return None
    entry = subs[sub_id]
    if not isinstance(entry, dict):
        return {}
    result = entry.get("result")
    if not isinstance(result, dict):
        return {}
    payload = result.get("payload")
    return payload if isinstance(payload, dict) else {}
def sub_engine_payload(result: dict, method_id: str = "") -> dict:
    try:
        if not isinstance(result, dict):
            return {}
        sub_id = _resolve_sub_id(method_id)
        if sub_id:
            p = result.get("payload")
            if isinstance(p, dict):
                hit = _sub_payload_from_view(p, sub_id)
                if hit is not None:
                    return hit
        return business_payload(result)
    except Exception as e:  # noqa: BLE001
        logger.warning("sub_engine_payload: %s", e)
        return {}
def sub_result(payload: dict, sub_id: str) -> dict | None:
    entry = dict_or_empty(locate_sub_results(payload).get(sub_id))
    result = entry.get("result")
    return result if isinstance(result, dict) else None
def _load_raw_intermediate(intermediate_dir: str, mid: str,
                           freshness_cutoff: str):
    if not isinstance(intermediate_dir, str) or not intermediate_dir:
        return None
    try:
        data = load_intermediate_fused(intermediate_dir, mid,
                                       freshness_cutoff=freshness_cutoff)
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e,
                      context=f'_load_raw_intermediate:{type(e).__name__}')
        return None
    if isinstance(data, dict) and data.get("status") == "corrupted":
        return None
    return data if isinstance(data, dict) else None
def _f1_findings(data) -> list:
    _p = dict_or_empty(dict_or_empty(data).get("payload"))
    for _cand in (data, _p, sub_result(_p, "E1")):
        if not isinstance(_cand, dict):
            continue
        _f = _cand.get("findings")
        if isinstance(_f, list) and _f:
            return _f
    return []
def iter_func_coverage(func_cov: Any) -> Any:
    if not isinstance(func_cov, dict):
        return
    for key, info in func_cov.items():
        if isinstance(info, dict):
            yield key, info
def func_executed_count(info: dict) -> int:
    return max(0, safe_int(dict_or_empty(info).get("executed_count", 0)))
def _func_cov_entry_file(key, info) -> str:
    return (str_or(dict_or_empty(info).get("file"))
            or _func_cov_key_file(key))
def _aggregate_func_coverage(func_cov: dict) -> dict[str, float]:
    per_file: dict[str, dict[str, int]] = {}
    for _key, info in iter_func_coverage(func_cov):
        fp = _func_cov_entry_file(_key, info)
        if not fp:
            continue
        stat = per_file.setdefault(fp, {"total": 0, "tested": 0})
        stat["total"] += 1
        if func_executed_count(info) > 0:
            stat["tested"] += 1
    return {
        fp: round(s["tested"] / s["total"] * 100, 1)
        for fp, s in per_file.items()
    }
def _aggregate_module_coverage(module_cov) -> dict[str, float]:
    per_file: dict[str, dict[str, int]] = {}
    if not isinstance(module_cov, list):
        return {}
    for entry in module_cov:
        if not isinstance(entry, dict):
            continue
        fp = str_or(entry.get("file")) or str_or(entry.get("path"))
        total = max(0, safe_int(entry.get("functions", 0)))
        if not fp or total <= 0:
            continue
        tested = min(max(0, safe_int(entry.get("tested_functions", 0))), total)
        stat = per_file.setdefault(fp, {"total": 0, "tested": 0})
        stat["total"] += total
        stat["tested"] += tested
    return {
        fp: round(s["tested"] / s["total"] * 100, 1)
        for fp, s in per_file.items() if s["total"] > 0
    }
def _coverage_by_file(coverage: dict) -> dict[str, float]:
    func_cov = coverage.get("func_coverage")
    per_file = (_aggregate_func_coverage(func_cov)
                if isinstance(func_cov, dict) and func_cov else {})
    if per_file:
        return per_file
    return _aggregate_module_coverage(
        coverage.get("module_coverage") or coverage.get("modules"))
def _low_coverage_files(coverage_by_file: dict[str, float]) -> list[str]:
    return [fp for fp, coverage in coverage_by_file.items()
            if coverage < UNCOVERED_THRESHOLD_PCT]
def _set_overall_coverage(ctx: AnalysisContext, metrics: dict) -> None:
    overall = finite_float_or_none(metrics.get("overall_coverage_pct"))
    if overall is None:
        return
    ctx.set(ContextKey.COVERAGE_OVERALL, overall, provider="F1")
def _set_file_coverage(ctx: AnalysisContext, coverage: dict) -> None:
    coverage_by_file = _coverage_by_file(coverage)
    if not coverage_by_file:
        return
    ctx.set(ContextKey.COVERAGE_BY_FILE, coverage_by_file, provider="F1")
    uncovered = _low_coverage_files(coverage_by_file)
    if uncovered:
        ctx.set(ContextKey.UNCOVERED_FILES, uncovered, provider="F1")
def coverage_mapping(host) -> dict | None:
    value = dict_or_empty(host).get("coverage")
    return value if isinstance(value, dict) and value else None
def _extract_coverage_ctx(ctx: AnalysisContext, payload: dict) -> None:
    coverage_metrics = coverage_mapping(payload)
    if coverage_metrics is None:
        return
    _set_overall_coverage(ctx, coverage_metrics)
    _set_file_coverage(ctx, coverage_metrics)
def _parse_hotspot_entry(f) -> dict | None:
    if not isinstance(f, dict):
        return None
    if not (f.get("function")
            and isinstance(f.get("file"), str)
            and f.get("file")):
        return None
    cc_val = finite_float_or_none(f.get("cc"))
    if cc_val is None:
        return None
    return {
        "function": f.get("function"),
        "file": f.get("file"),
        "line": coerce_line(f.get("line", 0)),
        "cc": round(cc_val, 2),
    }
def _collect_hotspot_entries(findings) -> tuple[list[dict], dict[str, float]]:
    hotspots: list[dict] = []
    complexity_by_file: dict[str, float] = {}
    if not isinstance(findings, list):
        return hotspots, complexity_by_file
    for f in findings:
        entry = _parse_hotspot_entry(f)
        if entry is None:
            continue
        hotspots.append(entry)
        fp = entry["file"]
        cc = entry["cc"]
        if fp not in complexity_by_file or cc > complexity_by_file[fp]:
            complexity_by_file[fp] = cc
    return hotspots, complexity_by_file
def _as_complexity_entry(hotspot: dict) -> dict:
    return {
        "name": hotspot["function"],
        "file": hotspot["file"],
        "line": hotspot["line"],
        "complexity": hotspot["cc"],
    }
def _extract_complexity_ctx(ctx: AnalysisContext, payload: dict,
                            findings: list | None = None) -> None:
    _src = (findings if isinstance(findings, list) and findings
            else payload.get("findings") or [])
    hotspots, complexity_by_file = _collect_hotspot_entries(_src)
    if hotspots:
        ctx.set(ContextKey.PERFORMANCE_HOTSPOTS, hotspots, provider="F1")
        ctx.set(ContextKey.HIGH_COMPLEXITY_FUNCS, [
            _as_complexity_entry(h)
            for h in _top100_by_complexity(hotspots, "cc")
        ], provider="F1")
    if complexity_by_file:
        ctx.set(ContextKey.COMPLEXITY_BY_FILE, complexity_by_file, provider="F1")
def _extract_callgraph_ctx(ctx: AnalysisContext, intermediate_dir: str,
                           freshness_cutoff: str) -> None:
    d1_payload = sub_engine_payload(
        _load_raw_intermediate(intermediate_dir, "D1", freshness_cutoff), "D1")
    cg_meta = d1_payload.get("callgraph")
    if isinstance(cg_meta, dict) and not cg_meta.get("error"):
        if any(is_number(cg_meta.get(k)) for k in ("functions", "edges")):
            graph = {
                "functions": max(0, safe_int(cg_meta.get("functions"))),
                "edges": max(0, safe_int(cg_meta.get("edges"))),
            }
            if "coverage_pct" in cg_meta:
                graph["coverage_pct"] = safe_float(cg_meta.get("coverage_pct"))
            ctx.set(ContextKey.CALL_GRAPH, graph, provider="D1")
        if is_number(cg_meta.get("orphans")):
            ctx.set(ContextKey.ORPHAN_FUNCTIONS,
                    max(0, safe_int(cg_meta.get("orphans"))), provider="D1")
        if is_number(cg_meta.get("blindspots")):
            ctx.set(ContextKey.BLINDSPOTS,
                    max(0, safe_int(cg_meta.get("blindspots"))), provider="D1")
def _resolve_round_skill_dir(skill_dir, intermediate_dir) -> str:
    return _skill_root_arg(skill_dir) or resolve_skill_dir(intermediate_dir)
def build_context_from_intermediates(intermediate_dir: str,
                                     skill_dir: str = "") -> AnalysisContext | None:
    resolved_skill_dir = _resolve_round_skill_dir(skill_dir, intermediate_dir)
    cutoff = (get_round_start_ts(resolved_skill_dir)
              if resolved_skill_dir else "")
    f1_data = _load_raw_intermediate(intermediate_dir, "F1", cutoff)
    payload = sub_engine_payload(f1_data, "F1")
    ctx = AnalysisContext()
    _extract_coverage_ctx(ctx, payload)
    _extract_complexity_ctx(ctx, payload, _f1_findings(f1_data))
    _extract_callgraph_ctx(ctx, intermediate_dir, cutoff)
    if ctx.provider_count == 0:
        logger.info("[Context] F1 载荷无可提取上下文（覆盖率/热点数据均缺失），跳过富化")
        return None
    logger.info("[Context] 磁盘上下文构建完成: keys=%s (providers=%d)",
                ctx.available_keys, ctx.provider_count)
    return ctx
def _coerce_index_dict(cg_meta: dict, key: str, skip_label: str) -> dict:
    index = cg_meta.get(key)
    if not isinstance(index, dict):
        if index:
            logger.warning('[pre_validate] %s 形态非法,已跳过%s: %r',
                           key, skip_label, type(index).__name__)
        index = {}
    return index
def _functions_from_index(functions_index: dict) -> dict:
    functions = {}
    for fname, info in functions_index.items():
        if not isinstance(info, dict):
            continue
        _filepath = info.get('filepath', '')
        functions[fname] = SimpleNamespace(
            name=fname,
            filepath=_filepath if isinstance(_filepath, str) else '',
            start_line=safe_int(info.get('start_line', 0)),
            end_line=safe_int(info.get('end_line', 0)),
        )
    return functions
def _callers_and_calls_from_index(callers_index: dict) -> tuple[dict, list]:
    callers = {}
    calls = []
    for callee, caller_list in callers_index.items():
        if not isinstance(caller_list, (list, tuple, set)):
            logger.warning('[pre_validate] callers_index 值形态非法,已跳过该边组: %r', callee)
            continue
        caller_set = {c for c in caller_list if isinstance(c, str) and c}
        callers[callee] = caller_set
        calls.extend(SimpleNamespace(caller_func=caller, callee_func=callee)
                     for caller in sorted(caller_set))
    return callers, calls
def _rebuild_call_graph_from_index(cg_meta):
    if not isinstance(cg_meta, dict):
        logger.warning('[pre_validate] callgraph 摘要形态非法,已跳过重建: %r',
                       type(cg_meta).__name__)
        return None
    functions = _functions_from_index(
        _coerce_index_dict(cg_meta, 'functions_index', '函数面'))
    if not functions:
        return None
    callers, calls = _callers_and_calls_from_index(
        _coerce_index_dict(cg_meta, 'callers_index', '边组'))
    return SimpleNamespace(functions=functions, callers=callers, calls=calls)
def normalized_independent_results(cv) -> dict:
    _ind_results = getattr(cv, 'independent_results', None)
    return _ind_results if isinstance(_ind_results, dict) else {}
def _call_graph_from_results(ind_results: dict):
    for method_id in ('C', 'D1'):
        result = ind_results.get(method_id)
        if not isinstance(result, dict) or not result:
            continue
        payload = sub_engine_payload(result, "D1")
        cg = payload.get('callgraph') if isinstance(payload, dict) else None
        if isinstance(cg, dict) and cg.get('functions_index'):
            graph = _rebuild_call_graph_from_index(cg)
            if graph is not None:
                return graph
    return None
def derive_skill_dir_and_graph(cv):
    ind_results = normalized_independent_results(cv)
    graph = _call_graph_from_results(ind_results)
    skill_dir = _skill_root_arg(getattr(cv, 'skill_dir', '') or '')
    intermediate_dir = _skill_root_arg(getattr(cv, '_intermediate_dir', '') or '')
    if not skill_dir and intermediate_dir:
        skill_dir = _project_root_of(intermediate_dir)
    return skill_dir, graph
_PROJECT_ROOT_MARKERS: tuple[str, ...] = (
    "SKILL.md", "pyproject.toml", "setup.py", "setup.cfg",
    "requirements.txt", "requirements.in", "Pipfile", "Pipfile.lock",
    "poetry.lock", "uv.lock", "pdm.lock", "environment.yml", "tox.ini",
    ".git", ".hg", ".svn", ".bzr",
)
def _project_root_of(intermediate_dir: str) -> str:
    if not resolve_skill_dir(intermediate_dir):
        return ""
    current = os.path.abspath(intermediate_dir)
    while True:
        if any(os.path.exists(os.path.join(current, marker))
               for marker in _PROJECT_ROOT_MARKERS):
            return current
        parent = os.path.dirname(current)
        if parent == current:
            return ""
        current = parent
def _func_cov_key_file(key) -> str:
    key = str_or(key)
    if ":" not in key:
        return key
    head, _, tail = key.rpartition(":")
    if not head:
        return ""
    if len(head) == 1 and head.isalpha() and tail[:1] in ("\\", "/"):
        return key
    return head
def _coverage_sections(f1_payload: Any) -> tuple[dict, ...]:
    inner = dict_or_empty(dict_or_empty(f1_payload).get("payload"))
    return tuple(
        cov for cov in (
            coverage_mapping(f1_payload),
            coverage_mapping(inner),
        )
        if cov is not None
    )
def _collect_low_coverage_files(f1_payload: Any) -> set[str]:
    low: set[str] = set()
    for cov in _coverage_sections(f1_payload):
        low |= {os.path.normpath(fp)
                for fp in _low_coverage_files(_coverage_by_file(cov))}
    return low
_DEAD_FAMILY = "dead_code"
_KIND_DEAD = "quadrant_dead"
_KIND_UNDERTESTED = "quadrant_undertested"
_KIND_DYNAMIC = "quadrant_dynamic"
_NON_DEAD_FILE_RULES: frozenset[str] = UNTESTED_COVERAGE_BLINDSPOT_TYPES | frozenset({
    "dynamic_binding", "dead_code_increase", "orphan_increase",
    _KIND_DYNAMIC, _KIND_UNDERTESTED,
})
_DEAD_CODE_RULE_IDS: frozenset[str] = (
    frozenset(RULE_FAMILY_SETS.get(_DEAD_FAMILY, frozenset()))
    | frozenset(_rid for _rid, _fam in RULE_FAMILY_MAP.items()
               if _fam == _DEAD_FAMILY)
) - _NON_DEAD_FILE_RULES
_DEAD_CODE_KEYWORDS: tuple[str, ...] = (
    "\u6b7b\u4ee3\u7801", "dead_code", "dead code", "deadcode", "unused",
    "\u672a\u4f7f\u7528", "\u96f6\u6d88\u8d39", "zero_consumer", "\u5b64\u513f", "orphan",
)
_DEAD_DELTA_MARKERS: tuple[str, ...] = (
    "increase", "decrease", "delta", "trend", "growth")
_DEAD_ENTITY_WORDS: frozenset[str] = frozenset({
    "code", "func", "funcs", "function", "functions", "method", "methods",
    "member", "members", "class", "classes", "var", "vars", "variable",
    "variables", "symbol", "symbols", "module", "modules", "import",
    "imports", "branch", "branches", "loop", "loops", "stub", "stubs",
    "shell", "shells", "field", "fields", "property", "properties",
    "parameter", "parameters", "param", "params", "local", "locals",
    "constant", "constants", "assignment", "assignments", "handler",
    "handlers", "route", "routes",
})
_WORD_SEPARATOR_PATTERN = re.compile(r"[^0-9A-Za-z]+")
_CAMEL_BOUNDARY_PATTERN = re.compile(r"(?<=[a-z0-9])(?=[A-Z])")
def _matches_dead_family_text(text: str, *,
                              exclude_delta: bool) -> bool:
    lowered = text.strip().lower()
    if not lowered:
        return False
    if exclude_delta and any(marker in lowered
                             for marker in _DEAD_DELTA_MARKERS):
        return False
    if any(keyword in lowered for keyword in _DEAD_CODE_KEYWORDS):
        return True
    spaced = _CAMEL_BOUNDARY_PATTERN.sub("_", text.strip())
    tokens = [tok for tok in _WORD_SEPARATOR_PATTERN.split(spaced.lower()) if tok]
    return any(left == "dead" and right in _DEAD_ENTITY_WORDS
               for left, right in itertools.pairwise(tokens))
def _is_dead_code_rule(rule_id: str) -> bool:
    if not rule_id or rule_id in _NON_DEAD_FILE_RULES:
        return False
    if rule_id in _DEAD_CODE_RULE_IDS:
        return True
    if lookup_rule_family(rule_id) == _DEAD_FAMILY:
        return True
    return _matches_dead_family_text(rule_id, exclude_delta=True)
def _dead_finding_file(f: dict) -> str:
    if not _is_dead_code_finding(f):
        return ""
    return finding_file_path(f) or str_or(f.get("path"))
def _b1_findings(b1_data: Any, b1_payload: Any) -> list:
    if isinstance(b1_payload, dict):
        findings = b1_payload.get("findings")
        if not (isinstance(findings, list) and findings):
            findings = business_payload(b1_payload).get("findings")
        if isinstance(findings, list) and findings:
            return findings
    if isinstance(b1_data, dict):
        fallback = b1_data.get("findings_list")
        if isinstance(fallback, list):
            return fallback
    return []
def _collect_dead_code_files(b1_data: Any, b1_payload: Any) -> set[str]:
    dead: set[str] = set()
    b1_findings = _b1_findings(b1_data, b1_payload)
    if not isinstance(b1_findings, list):
        return dead
    for f in b1_findings:
        if not isinstance(f, dict):
            continue
        fp = _dead_finding_file(f)
        if fp:
            dead.add(os.path.normpath(fp))
    return dead
def _extract_group_result(data, sub_id: str) -> dict:
    group_payload = dict_or_empty(dict_or_empty(data).get("payload"))
    if not group_payload:
        return {}
    found = sub_result(group_payload, sub_id)
    return group_payload if found is None else found
@dataclass(frozen=True)
class _QuadrantSpec:
    label: str
    confidence: float
    source: str
    severity: str = "P2"
_QUADRANT_SPECS: dict[str, _QuadrantSpec] = {
    _KIND_DEAD: _QuadrantSpec("死代码", 0.75, "B"),
    _KIND_UNDERTESTED: _QuadrantSpec("低覆盖", 0.65, "E"),
}
_DYNAMIC_CONFIDENCE: float = 0.85
_DYNAMIC_SPEC = _QuadrantSpec("动态风险", _DYNAMIC_CONFIDENCE, "B", "P1")
def _mk_finding(rule_id: str, fp: str, spec: _QuadrantSpec,
                source: str) -> dict:
    return {
        "rule_id": rule_id,
        "file": fp,
        "line": 0,
        "severity": spec.severity,
        "confidence": spec.confidence,
        "message": f"{spec.label}象限: {os.path.basename(fp)}",
        "_source_method": source,
        "rule_family": rule_id,
    }
def _existing_under_skill_root(fp: str, skill_dir: str) -> bool:
    fp = str_or(fp)
    if not fp:
        return False
    if not skill_dir:
        return False
    _p = fp if os.path.isabs(fp) else os.path.join(skill_dir, fp)
    path_safe, _ = check_path_traversal(skill_dir, _p)
    return path_safe and os.path.isfile(_p)
def _norm_path_key(p: str, skill_dir: str) -> str:
    raw = str_or(p)
    if not raw:
        return ""
    anchored = (raw if os.path.isabs(raw) or not skill_dir
                else os.path.join(skill_dir, raw))
    return finding_file_key(anchored)
@dataclass(frozen=True)
class _QuadrantIndex:
    low_files: frozenset[str]
    dead_files: frozenset[str]
    low_base: frozenset[str]
    dead_base: frozenset[str]
    low_keys: frozenset[str]
    dead_keys: frozenset[str]
    skill_dir: str
    @classmethod
    def build(cls, low_files: set[str], dead_files: set[str],
              skill_dir: str) -> _QuadrantIndex:
        return cls(
            low_files=frozenset(low_files),
            dead_files=frozenset(dead_files),
            low_base=frozenset(os.path.basename(f) for f in low_files),
            dead_base=frozenset(os.path.basename(f) for f in dead_files),
            low_keys=frozenset(_norm_path_key(x, skill_dir) for x in low_files),
            dead_keys=frozenset(_norm_path_key(x, skill_dir) for x in dead_files),
            skill_dir=skill_dir,
        )
    @staticmethod
    def _hit(fp: str, files: frozenset[str], bases: frozenset[str]) -> bool:
        return fp in files or os.path.basename(fp) in bases
    def _is_dual_source(self, fp: str) -> bool:
        key = _norm_path_key(fp, self.skill_dir)
        return key in self.low_keys and key in self.dead_keys
    def _kind(self, fp: str) -> str:
        if self._is_dual_source(fp):
            return _KIND_DYNAMIC
        key = _norm_path_key(fp, self.skill_dir)
        if key in self.low_keys:
            return _KIND_UNDERTESTED
        if key in self.dead_keys:
            return _KIND_DEAD
        in_low = self._hit(fp, self.low_files, self.low_base)
        in_dead = self._hit(fp, self.dead_files, self.dead_base)
        if in_low and not in_dead:
            return _KIND_UNDERTESTED
        if in_dead and not in_low:
            return _KIND_DEAD
        return self._kind_when_both(fp)
    def _kind_when_both(self, fp: str) -> str:
        if self._is_dual_source(fp):
            return _KIND_DYNAMIC
        return _KIND_DEAD if fp in self.dead_files else _KIND_UNDERTESTED
    def classify(self, fp: str) -> list:
        kind = self._kind(fp)
        if kind == _KIND_DYNAMIC:
            return [_mk_finding(_KIND_DYNAMIC, fp, _DYNAMIC_SPEC, _src)
                    for _src in ("B", "E")]
        spec = _QUADRANT_SPECS[kind]
        return [_mk_finding(kind, fp, spec, spec.source)]
def _classify_quadrant_files(all_files: set, index: _QuadrantIndex) -> list:
    quadrant_findings = []
    for fp in sorted(all_files):
        quadrant_findings.extend(index.classify(fp))
    return quadrant_findings
def _quadrant_finding_key(finding: dict, skill_dir: str) -> tuple:
    return (finding.get("rule_id"),
            _norm_path_key(finding.get("file", ""), skill_dir),
            finding.get("_source_method", ""))
def _dedup_quadrant_findings(quadrant_findings: list, skill_dir: str) -> list:
    _seen = set()
    _dedup = []
    for _qf in quadrant_findings:
        if not isinstance(_qf, dict):
            continue
        _key = _quadrant_finding_key(_qf, skill_dir)
        if _key not in _seen:
            _seen.add(_key)
            _dedup.append(_qf)
    return _dedup
def _quadrant_cutoff(cv2) -> str | None:
    try:
        _sd = _resolve_round_skill_dir(
            getattr(cv2, "skill_dir", None),
            getattr(cv2, "_intermediate_dir", ""))
        return get_round_start_ts(_sd) if _sd else ""
    except Exception as _cut_e:  # noqa: BLE001
        logger.warning("[Quadrant] round_start_ts 获取失败，跳过象限注入: %s",
                       _cut_e)
        return None
class _QuadrantSources(NamedTuple):
    e1: dict
    b1: dict
    @property
    def is_empty(self) -> bool:
        return not self.e1 and not self.b1
def _load_quadrant_sources(
        intermediate_dir: str, cutoff: str) -> _QuadrantSources | None:
    try:
        return _QuadrantSources(
            _load_raw_intermediate(intermediate_dir, "F1", cutoff),
            _load_raw_intermediate(intermediate_dir, "B1", cutoff))
    except Exception as _e:  # noqa: BLE001
        logger.warning("[Quadrant] E1/B1 load failed: %s", _e)
        return None
def _quadrant_findings_from(e1_data, b1_data, skill_dir: str) -> list:
    skill_dir = _skill_root_arg(skill_dir)
    if not str_or(skill_dir):
        logger.info("[Quadrant] skill_dir 未知，无法核验文件存在性，跳过象限注入")
        return []
    low_files = _collect_low_coverage_files(_extract_group_result(e1_data, "E1"))
    dead_files = _collect_dead_code_files(
        b1_data, _extract_group_result(b1_data, "B1"))
    all_files = {f for f in (low_files | dead_files)
                 if _existing_under_skill_root(f, skill_dir)}
    index = _QuadrantIndex.build(low_files, dead_files, skill_dir)
    return _dedup_quadrant_findings(
        _classify_quadrant_files(all_files, index), skill_dir)
def inject_quadrant_findings(cv2, intermediate_dir: str) -> None:
    cutoff = _quadrant_cutoff(cv2)
    if cutoff is None:
        return
    sources = _load_quadrant_sources(intermediate_dir, cutoff)
    if sources is None:
        return
    if sources.is_empty:
        logger.debug("[Quadrant] E1+B1 empty, skip")
        return
    _inject_sources(cv2, sources)
def _quadrant_skill_dir(cv2) -> str:
    declared = _skill_root_arg(getattr(cv2, "skill_dir", None))
    if declared:
        return declared
    return derive_skill_dir_and_graph(cv2)[0]
def _inject_sources(cv2, sources: _QuadrantSources) -> None:
    try:
        skill_dir = _quadrant_skill_dir(cv2)
        findings = _quadrant_findings_from(sources.e1, sources.b1, skill_dir)
        existing = {_quadrant_finding_key(item, skill_dir)
                    for item in cv2.all_findings if isinstance(item, dict)}
        fresh = [item for item in findings
                 if _quadrant_finding_key(item, skill_dir) not in existing]
        if fresh:
            cv2.all_findings.extend(fresh)
            logger.info("[Quadrant] 注入 %d 个象限 finding", len(fresh))
    except Exception as _qe:  # pragma: no cover  # noqa: BLE001
        logger.warning("[Quadrant] quadrant parse failed (skip injection): %s", _qe)
def _evidence_quality_flags_allow(result: dict) -> bool:
    flags = result.get("quality_flags")
    if flags is None:
        return True
    if isinstance(flags, str):
        return "empty_scan" not in flags
    if not isinstance(flags, (list, tuple, set, frozenset)):
        return False
    return "empty_scan" not in flags
def available_evidence_methods(results: dict) -> set[str]:
    return {
        mid for mid, r in dict_or_empty(results).items()
        if mid in METHOD_REGISTRY
        and METHOD_REGISTRY[mid].produces_findings
        and _method_status_bucket(r) == _STATUS_BUCKET_PRESENT
        and _evidence_quality_flags_allow(dict_or_empty(r))
    }
_DEAD_CODE_RULE_ID_FIELDS: tuple[str, ...] = (
    "rule_id", "category", "rule_family", "check_id")
def _is_dead_code_finding(finding) -> bool:
    if not isinstance(finding, dict):
        return False
    identifiers = tuple(
        identifier_text(finding.get(key))
        for key in _DEAD_CODE_RULE_ID_FIELDS)
    if any(identifier in _NON_DEAD_FILE_RULES for identifier in identifiers):
        return False
    text = " ".join(
        str(finding.get(k, "")) for k in
        ("rule_id", "description", "category", "rule_family",
         "check_id", "message")
    )
    if any(marker in text.lower() for marker in _DEAD_DELTA_MARKERS):
        return False
    if any(_is_dead_code_rule(identifier) for identifier in identifiers):
        return True
    return _matches_dead_family_text(text, exclude_delta=True)
logger.info("xv_context_derivation 已加载: %d 项导出", len(__all__))

from __future__ import annotations

import hashlib
import logging
import math
import os
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from concurrent.futures import TimeoutError as _FutTimeoutError
from typing import Any

from jwsgj.diag_types_defs import (
    dict_findings,
    severity_breakdown_of,
)
from jwsgj.diag_types_normalize import (
    clamp_unit,
    clean_source_ids,
    coerce_line,
    count_findings_in_payload,
    degrade_factor_of,
    derive_rule_id,
    env_number,
    extract_finding_line,
    finding_file_key,
    findings_container,
    identifier_text,
    integral_count,
    is_real_number,
    iter_payload_finding_items,
    normalize_sources,
    parse_locator_file,
    safe_float,
    safe_int,
    signal_bool,
    str_or,
    strict_iterable_list,
)
from jwsgj.diag_types_vocab import (
    ALL_FAMILY_KEYS,
    CONCLUSION_V2_MAP,
    CONF_HIGH,
    CONF_VERY_HIGH,
    DEFAULT_CONFIDENCE_FALLBACK,
    FIELD_ADJUSTED_CONFIDENCE,
    FIELD_BASE_CONFIDENCE,
    FIELD_FINDINGS_SUPPRESSED,
    MESSAGE_TRUNCATE_LEN,
    RULE_FAMILY_MAP,
    SEVERITY_RANK,
    SIGNAL_DEGRADE_FACTOR,
    SIGNAL_PARTIAL_SOURCES,
    SOURCE_SEQUENCE_TYPES,
)
from jwsgj.fix_guide_rule_identity import (
    lookup_rule_family,
)
from jwsgj.fp_rules_judge import (
    DEFAULT_SEVERITY,
)
from jwsgj.xv_intermediate_store import (
    canonical_cv_path,
)

logger = logging.getLogger(__name__)
_EMPTY_TEXT_DEFAULT = ""
__all__ = [
    'aggregate_by_function',
    'apply_rule_stats',
    'build_data_lineage',
    'build_findings_index',
    'collect_all_findings',
    'collected_sources_before_gate',
    'compute_p0p1_protection_log',
    'compute_statistics',
    'finding_file_of',
    'fuse_regression_into_xv',
    'inner_finding_count',
    'normalize_finding_input',
    'normalized_confidence',
    'propagate_finding_metadata',
    'source_method_counts',
    'summarize_findings',
]
def _source_key(raw: object) -> str:
    return str_or(raw).strip()
def _normalize_severity(raw: object) -> str:
    return str_or(raw).strip().upper() or DEFAULT_SEVERITY
def _valid_source_ids(sources: object) -> set[str]:
    if not isinstance(sources, SOURCE_SEQUENCE_TYPES):
        return set()
    return {
        source.strip()
        for source in sources
        if isinstance(source, str) and source.strip()
    }
_RAW_STAT_BUCKETS: dict[str, tuple[str, str]] = {
    "confirmed": ("confirmed", "findings_confirmed"),
    "suppressed": ("suppressed", FIELD_FINDINGS_SUPPRESSED),
    "investigated": ("investigated", "findings_investigated"),
    "review": ("review_c", "findings_review"),
    "reviewed": ("review_c", "findings_review"),
}
_EFFECTIVE_STAT_BUCKETS: dict[str, tuple[str, str]] = {
    "likely": ("likely_c", "findings_likely"),
    "uncertain": ("uncertain_c", "findings_uncertain"),
}
_RAW_CONCL_RULE_BUCKETS: dict[str, str] = {
    conclusion: stat_key.removesuffix("_c")
    for conclusion, (stat_key, _findings_key) in _RAW_STAT_BUCKETS.items()
}
_EFFECTIVE_CONCL_RULE_BUCKETS: dict[str, str] = {
    conclusion: stat_key.removesuffix("_c")
    for conclusion, (stat_key, _findings_key) in _EFFECTIVE_STAT_BUCKETS.items()
}
def apply_rule_stats(cv: Any, xv_findings: list) -> None:
    for f in xv_findings or ():
        if not isinstance(f, dict):
            logger.warning("[Stats] 规则统计跳过非 dict 载荷(%s)", type(f).__name__)
            continue
        rule_key = str_or(f.get("rule_applied"))
        rule = cv.rules_applied.get(rule_key)
        if not rule:
            continue
        rule["triggered"] = True
        fc = len(findings_container(f)) or 1
        rule["findings_count"] += fc
        _bucket = _RAW_CONCL_RULE_BUCKETS.get(_safe_conclusion(f))
        if _bucket is not None:
            rule[_bucket] += fc
        _bucket_v2 = _EFFECTIVE_CONCL_RULE_BUCKETS.get(
            _effective_conclusion(f) or "uncertain")
        if _bucket_v2 is not None:
            rule[_bucket_v2] += fc
_P0P1_PROTECTION_REASONS = (
    ("_known_fp_family_high_sev", "known_fp_family_high_sev"),
    ("_low_confidence_high_severity", "low_confidence_high_severity"),
    ("_single_group_new_finding", "single_group_new_finding"),
)
def compute_p0p1_protection_log(xv_findings: list) -> list:
    p0p1_protection_log = []
    for f in xv_findings or ():
        if not isinstance(f, dict):
            logger.warning("[Stats] P0/P1 保护日志跳过非 dict 载荷(%s)",
                           type(f).__name__)
            continue
        reasons = [reason for field, reason in _P0P1_PROTECTION_REASONS
                   if f.get(field)]
        if reasons:
            p0p1_protection_log.append({
                "locator": f.get("locator", ""),
                "severity": f.get("severity", ""),
                "reasons": reasons,
            })
    return p0p1_protection_log
def _effective_conclusion(f: dict) -> str:
    candidate = str_or(f.get("conclusion_v2")).strip().lower()
    if candidate:
        mapped = CONCLUSION_V2_MAP.get(candidate)
        if mapped is not None:
            return mapped
    raw = str_or(f.get("conclusion")).strip().lower()
    return CONCLUSION_V2_MAP.get(raw, raw)
def _safe_conclusion(f: dict) -> str:
    return str_or(f.get("conclusion")).strip().lower() or "uncertain"
def inner_finding_count(f: dict) -> int:
    return len(findings_container(f))
_CONFIDENCE_FIELDS = (
    FIELD_ADJUSTED_CONFIDENCE, FIELD_BASE_CONFIDENCE, "confidence")
def _finite_number(value):
    if not is_real_number(value):
        return None
    return safe_float(value, None)
def _numeric_confidence(xvf: dict):
    for field in _CONFIDENCE_FIELDS:
        value = _finite_number(xvf.get(field))
        if value is not None:
            return clamp_unit(value)
    if all(field not in xvf for field in _CONFIDENCE_FIELDS):
        return DEFAULT_CONFIDENCE_FALLBACK
    return None
def _empty_stat_buckets() -> dict:
    stats = {"xv_finding_count": 0}
    for stat_key, findings_key in (*_RAW_STAT_BUCKETS.values(),
                                   *_EFFECTIVE_STAT_BUCKETS.values()):
        stats[stat_key] = 0
        stats[findings_key] = 0
    return stats
def compute_statistics(findings_list: list) -> dict:
    stats = _empty_stat_buckets()
    for f in findings_list or ():
        if not isinstance(f, dict):
            logger.warning("[Stats] 统计跳过非 dict 载荷(%s)", type(f).__name__)
            continue
        inner = inner_finding_count(f) or 1
        stats["xv_finding_count"] += inner
        bucket = (_RAW_STAT_BUCKETS.get(_safe_conclusion(f))
                  if f.get("conclusion") is not None else None)
        if bucket is not None:
            stats[bucket[0]] += 1
            stats[bucket[1]] += inner
        eff = _effective_conclusion(f) or "uncertain"
        bucket = _EFFECTIVE_STAT_BUCKETS.get(eff)
        if bucket is not None:
            stats[bucket[0]] += 1
            stats[bucket[1]] += inner
    return stats
def finding_file_of(f: dict) -> str:
    if not isinstance(f, dict):
        return ""
    filepath = str_or(
        f.get("file") or f.get("file_path") or f.get("filepath")).strip()
    if filepath:
        return filepath
    locator = str_or(f.get("locator"))
    return (parse_locator_file(locator) if locator else "").strip()
def _file_key(xvf: dict) -> str:
    return finding_file_key(finding_file_of(xvf)) or "unknown"
def aggregate_by_function(xv_findings: list) -> list:
    if not xv_findings:
        return []
    file_groups: dict[str, list] = {}
    file_labels: dict[str, str] = {}
    for xvf in xv_findings:
        if not isinstance(xvf, dict):
            continue
        file_key = _file_key(xvf)
        file_groups.setdefault(file_key, []).append(xvf)
        file_labels.setdefault(file_key, finding_file_of(xvf) or "unknown")
    aggregations = [
        _summarize_file_group(file_labels[filepath], group)
        for filepath, group in file_groups.items()
    ]
    aggregations.sort(
        key=lambda a: SEVERITY_RANK.get(
            a["max_severity"], _UNKNOWN_SEVERITY_RANK))
    return aggregations
_CONCLUSION_PRIORITY: dict[str, int] = {
    "confirmed": 0, "likely": 1,
    "uncertain": 2, "investigated": 2, "review": 2, "reviewed": 2,
    "suppressed": 3, "contradictory": 4,
}
_UNKNOWN_SEVERITY_RANK = max(SEVERITY_RANK.values()) + 1
def _group_max_severity(group: list) -> str:
    rows = []
    for xvf in group:
        rows.append(xvf)
        rows.extend(dict_findings(findings_container(xvf)))
    return _worst_severity_of(rows)
def _conclusion_distribution(group: list) -> dict:
    dist: dict = {}
    for xvf in group:
        c = _safe_conclusion(xvf)
        dist[c] = dist.get(c, 0) + 1
    return dist
def _dominant_conclusion(dist: dict) -> str:
    if not dist:
        return "uncertain"
    return min(
        dist.items(),
        key=lambda x: (-x[1], _CONCLUSION_PRIORITY.get(x[0], 5), x[0]),
    )[0]
def _group_avg_confidence(group: list) -> float:
    confs = [
        v for xvf in group
        if (v := _numeric_confidence(xvf)) is not None
    ]
    return round(sum(confs) / len(confs), 3) if confs else 0.0
def _add_rule_family(families: set, finding: dict) -> None:
    rf = str_or(finding.get("rule_family")).strip()
    if rf:
        families.add(rf)
def _group_rule_families(group: list) -> list:
    families: set = set()
    for xvf in group:
        _add_rule_family(families, xvf)
        for f in dict_findings(findings_container(xvf)):
            _add_rule_family(families, f)
    return sorted(families)
def _group_source_methods(group: list) -> list:
    all_sources: set[str] = set()
    for xvf in dict_findings(group):
        all_sources.update(_valid_source_ids(xvf.get("sources")))
        for f in dict_findings(findings_container(xvf)):
            _method = _source_key(f.get("_source_method"))
            if _method:
                all_sources.add(_method)
    return sorted(all_sources)
def _summarize_file_group(filepath: str, group: list) -> dict:
    concl_dist = _conclusion_distribution(group)
    total_findings = sum(inner_finding_count(f) or 1 for f in group)
    return {
        "file": filepath,
        "total_findings": total_findings,
        "max_severity": _group_max_severity(group),
        "conclusion_distribution": concl_dist,
        "dominant_conclusion": _dominant_conclusion(concl_dist),
        "avg_confidence": _group_avg_confidence(group),
        "rule_families": _group_rule_families(group),
        "source_methods": _group_source_methods(group),
        "is_multi_issue_file": total_findings >= 3,
    }
def _count_confirmed_source(_confirmed: Counter, finding: dict) -> None:
    inner = finding.get("findings") or []
    inner_counted = False
    if isinstance(inner, (list, tuple)):
        for ef in inner:
            if not isinstance(ef, dict):
                continue
            source = _source_key(ef.get("_source_method"))
            if source:
                _confirmed[source] += 1
                inner_counted = True
    if inner_counted:
        return
    source = _source_key(finding.get("_source_method"))
    if source:
        _confirmed[source] += 1
def _confirmed_method_counts(xv_findings: list) -> Counter:
    _confirmed = Counter()
    for f in xv_findings or ():
        if not (isinstance(f, dict) and _safe_conclusion(f) == "confirmed"):
            continue
        _count_confirmed_source(_confirmed, f)
    return _confirmed
def source_method_counts(findings: list) -> Counter:
    counts: Counter = Counter()
    for finding in findings or ():
        if (not isinstance(finding, dict)
                or finding.get("_is_statistical") is True):
            continue
        source = _source_key(finding.get("_source_method"))
        if source:
            counts[source] += 1
    return counts
def collected_sources_before_gate(cv) -> list:
    sources = set()
    for finding in (getattr(cv, "all_findings", None) or []):
        if (not isinstance(finding, dict)
                or finding.get("_is_statistical") is True):
            continue
        source = _source_key(finding.get("_source_method"))
        if source:
            sources.add(source)
    return sorted(sources)
_COLLECT_RATE_ALERT = 0.5
def _lineage_row(produced: int, collected: int, confirmed: int,
                 filtered: int) -> dict:
    return {
        "produced": produced, "collected": collected, "confirmed": confirmed,
        "filtered": filtered,
        "collect_rate": round(collected / produced, 3) if produced else 0.0,
    }
def _lineage_count(mapping, mid) -> int:
    if not isinstance(mapping, dict):
        return 0
    return max(0, integral_count(mapping.get(mid, 0)) or 0)
def build_data_lineage(cv, xv_findings: list) -> dict:
    _filtered = source_method_counts(getattr(cv, "all_findings", None) or [])
    _collected = getattr(cv, "_collected_before_filter", None)
    if not isinstance(_collected, dict):
        _collected = _filtered
    _confirmed = _confirmed_method_counts(xv_findings)
    lineage = {}
    results = getattr(cv, "independent_results", None)
    for mid, result in (results.items() if isinstance(results, dict) else ()):
        if not isinstance(result, dict):
            logger.warning("[DataLineage] %s 独立结果非 dict(%s)，跳过",
                           mid, type(result).__name__)
            continue
        produced = _produced_finding_count(result)
        row = _lineage_row(produced, _lineage_count(_collected, mid),
                           _lineage_count(_confirmed, mid),
                           _lineage_count(_filtered, mid))
        lineage[mid] = row
        if produced and row["collect_rate"] < _COLLECT_RATE_ALERT:
            logger.error("[DataLineage] %s 收集率<50%% (%d/%d): 结果可能被静默丢失",
                         mid, row["collected"], produced)
    return lineage
_PARALLEL_THRESHOLD = 10
_METHOD_DOMAIN_FAMILY: dict[str, str] = {
    "A": "diag_general", "B": "type_check", "C": "call_graph",
    "D": "danger_pattern", "E": "test_smell", "F": "diag_general",
}
def _method_domain_family(mid: str) -> str:
    return _METHOD_DOMAIN_FAMILY.get(str_or(mid).strip()[:1], "diag_general")
def _str_fallback(value, default: str = _EMPTY_TEXT_DEFAULT) -> str:
    if value is None:
        return default
    if isinstance(value, str):
        return value
    if isinstance(value, (list, tuple)):
        value = _first_hashable(value)
        if value is None:
            return default
    if isinstance(value, bool):
        return default
    if isinstance(value, float) and not math.isfinite(value):
        return default
    return str(value)
def _first_present(f: dict, keys: tuple[str, ...], normalize=None):
    for key in keys:
        value = f.get(key)
        if normalize is not None:
            value = normalize(value)
        if value:
            return value
    return ""
def _fallback_normalize(cv2, current: list, candidates) -> list:
    if current:
        return current
    if isinstance(candidates, (list, tuple)) and candidates:
        return _normalize_finding_items(cv2, candidates)
    return current
def _payload_candidates(result: dict) -> list[dict]:
    if not isinstance(result, dict):
        return []
    mr = result.get("method_result")
    candidates = [result.get("payload")]
    if isinstance(mr, dict):
        candidates.append(mr.get("payload"))
    return [c for c in candidates if isinstance(c, dict)]
def _fallback_finding_lists(result: dict) -> list:
    if not isinstance(result, dict):
        return []
    mr = result.get("method_result")
    candidates = []
    if isinstance(mr, dict):
        candidates.append(mr.get("findings_list"))
    candidates.append(result.get("findings_list"))
    candidates.append(result.get("findings"))
    return [c for c in candidates if isinstance(c, (list, tuple))]
def _result_status(result: dict) -> str:
    if not isinstance(result, dict):
        return "unknown"
    status = str_or(result.get("status")).strip().lower()
    if status:
        return status
    method_result = result.get("method_result")
    if isinstance(method_result, dict):
        status = str_or(method_result.get("status")).strip().lower()
    return status or "unknown"
def _extract_payload_findings(cv2, result: dict) -> tuple[list[dict], str]:
    status = _result_status(result)
    findings = []
    for payload in _payload_candidates(result):
        findings = _normalize_finding_items(
            cv2, iter_payload_finding_items(payload))
        if findings:
            break
    for candidates in _fallback_finding_lists(result):
        findings = _fallback_normalize(cv2, findings, candidates)
        if findings:
            break
    return findings, status
def _norm_source_method(f: dict, mid: str) -> None:
    _sm = f.get("_source_method")
    _sm_text = _sm.strip() if isinstance(_sm, str) else ""
    if not _sm_text or _sm_text.lower() == "unknown":
        _sm_text = str_or(mid).strip() or "unknown"
    f["_source_method"] = _sm_text
def _mark_partial_degrade(f: dict, status: str) -> None:
    # 只有真正的执行失败才降级证据；verdict=fail（发现 P0）的方法已完整产出，
    # 不能把它的 findings 当成「部分结果」打折。
    if status in ("fail", "failed"):
        return
    status_partial = status in ("timeout", "error", "partial")
    partial = signal_bool(f.get("_partial_degrade")) or status_partial
    f["_partial_degrade"] = partial
    if not partial:
        return
    if SIGNAL_DEGRADE_FACTOR not in f:
        f[SIGNAL_DEGRADE_FACTOR] = (
            CONF_VERY_HIGH if status == "partial" else CONF_HIGH)
    if "_partial_reason" not in f:
        f["_partial_reason"] = status if status_partial else "partial"
def _norm_file_field(f: dict) -> None:
    _raw_file = f.get("file")
    _file_text = identifier_text(_raw_file) if _raw_file else ""
    if _file_text:
        f["file"] = _file_text
        return
    f["file"] = _first_present(
        f, _FILE_FALLBACK_KEYS, normalize=identifier_text)
    if not f["file"]:
        f["file"] = finding_file_of(f)
_MESSAGE_FALLBACK_KEYS = ("suggestion", "desc", "msg", "detail", "details")
_FILE_FALLBACK_KEYS = (
    "file_path", "filepath", "path", "filename", "source_file", "rel_path")
def _norm_message_severity(f: dict) -> None:
    _msg = _str_fallback(f.get("message")) if f.get("message") else ""
    if not _msg:
        _msg = _str_fallback(_first_present(f, _MESSAGE_FALLBACK_KEYS))
    f["message"] = _msg
    _sev = identifier_text(f.get("severity")).strip().upper()
    if not _sev:
        _sev = (identifier_text(f.get("level")).strip().upper()
                or DEFAULT_SEVERITY)
    f["severity"] = _sev
_LINE_FALLBACK_KEYS = ("line_no", "lineno", "start_line", "begin_line")
def _finding_line_of(f: dict) -> int:
    line = _first_present(
        f, ("line", "line_number", *_LINE_FALLBACK_KEYS),
        normalize=coerce_line)
    return line or extract_finding_line(f)
def _identity_digest(f: dict) -> str:
    return hashlib.sha1(
        str(f.get("message", "")).encode("utf-8", "replace"),
        usedforsecurity=False).hexdigest()[:12]
def _norm_line_identity(f: dict) -> None:
    f["line"] = _finding_line_of(f)
    if not f.get("finding_id"):
        _fid_file = f.get("file", "")
        _fid = (f"{f.get('_source_method', 'unknown')}:{_fid_file}:"
                f"{f.get('line', 0)}:{f.get('rule_id', '')}")
        f["finding_id"] = f"{_fid}:{_identity_digest(f)}"
    if not f.get("description"):
        f["description"] = f.get("message", "")
def _normalize_finding_fields(f: dict, mid: str, status: str) -> None:
    _norm_source_method(f, mid)
    _mark_partial_degrade(f, status)
    _norm_file_field(f)
    f["rule_id"] = derive_rule_id(f)
    _norm_message_severity(f)
    _norm_line_identity(f)
def _family_candidate(f: dict) -> str:
    _rid_cand = identifier_text(f.get("rule_id"))
    if _rid_cand and _rid_cand != "unknown":
        return _rid_cand
    return _first_present(
        f, ("quadrant", "type", "blindspot_type", "category"),
        normalize=identifier_text)
def _remap_existing_family(f: dict) -> None:
    _existing_rf = f.get("rule_family", "")
    if _existing_rf:
        try:
            _mapped_rf = RULE_FAMILY_MAP.get(_existing_rf)
            if _mapped_rf and _mapped_rf != _existing_rf:
                f["_original_rule_family"] = _existing_rf
                f["rule_family"] = _mapped_rf
        except (KeyError, TypeError) as e:
            logger.warning("rule_family重映射失败: %s", e)
def _infer_rule_family(f: dict, mid: str) -> None:
    _rf_raw = f.get("rule_family")
    if isinstance(_rf_raw, str):
        _rf_raw = _rf_raw.strip()
    else:
        _rf_raw = identifier_text(_rf_raw)
    if _rf_raw:
        f["rule_family"] = _rf_raw
    else:
        f.pop("rule_family", None)
    if not f.get("rule_family"):
        _rf_candidate = _family_candidate(f)
        if _rf_candidate and _rf_candidate != "NONE":
            try:
                f["rule_family"] = lookup_rule_family(_rf_candidate)
            except Exception as e:  # noqa: BLE001
                logger.warning("_infer_rule_family: %s", e)
                f["rule_family"] = _rf_candidate
        else:
            f["rule_family"] = _method_domain_family(mid)
    _remap_existing_family(f)
def _dedup_key_text(value) -> str:
    v = _first_hashable(value)
    return v if isinstance(v, str) else str(v or "")
def _dedup_key(f: dict) -> tuple:
    return (
        _dedup_key_text(f.get("_source_method", "")),
        _dedup_key_text(f.get("file", "")),
        coerce_line(f.get("line", 0)),
        _dedup_key_text(f.get("rule_id", "")),
        _identity_digest(f),
    )
def _assign_placeholder_locator(f: dict) -> None:
    _ph = hashlib.sha1(
        (f"{f.get('_source_method','')}|{f.get('rule_id','')}|"
         f"{f.get('line',0)}|{_identity_digest(f)}").encode(
             "utf-8", "replace"),
        usedforsecurity=False).hexdigest()[:12]
    f["file"] = f"__no_location__#{_ph}"
def _dedup_and_validate(f: dict, seen_keys: set) -> bool:
    _k = _dedup_key(f)
    if _k in seen_keys:
        return False
    seen_keys.add(_k)
    _fpath = f.get("file", "")
    if not _fpath or not str(_fpath).strip():
        _assign_placeholder_locator(f)
    _sev_raw = f.get("severity")
    if not isinstance(_sev_raw, str) or not _sev_raw.strip():
        f["severity"] = DEFAULT_SEVERITY
    return True
def _extract_one_safe(cv2, mid, result) -> tuple:
    try:
        findings, status = _extract_payload_findings(cv2, result)
        normalized = []
        for f in findings:
            try:
                _normalize_finding_fields(f, mid, status)
                _apply_feedback_multiplier(cv2, f, mid)
                _infer_rule_family(f, mid)
            except Exception as e:  # noqa: BLE001
                logger.warning(
                    "[Collect] 方法 %s 单条 finding 归一失败，已跳过: %s", mid, e)
                continue
            normalized.append(f)
        return mid, normalized, status
    except Exception as e:  # noqa: BLE001
        logger.warning("[Collect] 方法 %s 提取异常，降级为空结果: %s", mid, e)
        return mid, [], "error"
def _await_completed(futures: dict) -> list:
    try:
        return list(as_completed(futures, timeout=60))
    except (TimeoutError, _FutTimeoutError):
        logger.warning("[Collect] 整体提取超时(60s)，降级处理已完成的方法")
        return [f for f in futures if f.done()]
def _harvest_future(future, futures: dict, results: dict) -> None:
    mid = futures[future]
    try:
        mid_val, findings, status = future.result(timeout=15)
        results[mid_val] = (findings, status)
    except (TimeoutError, _FutTimeoutError):
        logger.warning("[Collect] 方法 %s 提取超时，降级为空结果", mid)
        results[mid] = ([], "timeout")
    except Exception as e:  # noqa: BLE001
        logger.warning("[Collect] 方法 %s 提取异常，降级为空结果: %s", mid, e)
        results[mid] = ([], "error")
def _extract_parallel(cv2, items: list) -> dict:
    results: dict = {}
    executor = ThreadPoolExecutor(max_workers=min(4, os.cpu_count() or 1))
    try:
        futures = {executor.submit(_extract_one_safe, cv2, mid, result): mid
                   for mid, result in items}
        for future in _await_completed(futures):
            _harvest_future(future, futures, results)
    finally:
        executor.shutdown(wait=False, cancel_futures=True)
    return results
def _extract_sequential(cv2, items: list) -> dict:
    results: dict = {}
    for mid, result in items:
        mid_val, findings, status = _extract_one_safe(cv2, mid, result)
        results[mid_val] = (findings, status)
    return results
def _extract_and_normalize_all(cv2, items: list) -> dict:
    if len(items) > _PARALLEL_THRESHOLD:
        return _extract_parallel(cv2, items)
    return _extract_sequential(cv2, items)
def _gap_reported_count(raw: dict) -> int:
    fc = raw.get("findings_count")
    if isinstance(fc, (int, float)):
        return integral_count(fc) or 0
    if not isinstance(fc, str):
        return 0
    return safe_int(fc)
def _produced_finding_count(result: dict) -> int:
    if not isinstance(result, dict):
        return 0
    counts = [_gap_reported_count(result)]
    for payload in _payload_candidates(result):
        declared = count_findings_in_payload(payload)
        actual = sum(1 for _ in iter_payload_finding_items(payload))
        counts.append(declared)
        if actual:
            counts.append(actual)
    for candidates in _fallback_finding_lists(result):
        if candidates:
            counts.append(len(candidates))
            break
    return max([0, *counts])
def _mk_gap_stat_finding(mid, fc, actual, gap, summary) -> dict:
    return {
        "_source_method": str_or(mid).strip() or "unknown",
        "rule_id": f"stat_gap_{mid}",
        "rule_family": _method_domain_family(mid),
        "file": f"__statistical__{mid}",
        "line": 0,
        "severity": DEFAULT_SEVERITY,
        "message": f"[GAP] {mid} reported {fc} findings but only {actual} collected (gap={gap}): {summary}",
        "_partial_degrade": True,
        "_partial_reason": "statistical_gap",
        SIGNAL_DEGRADE_FACTOR: 0.50,
        "_is_statistical": True,
    }
def _collect_gap_findings(cv2, _results_map: dict) -> list:
    gap_findings = []
    for mid, result in _independent_results(cv2).items():
        if not isinstance(result, dict):
            continue
        stat = _stat_gap_finding(cv2, mid, result, _results_map)
        if stat is not None:
            gap_findings.append(stat)
    return gap_findings
_GAP_COUNTED_STATUSES = (
    "pass", "passed", "ok", "success", "completed", "warn", "fail", "failed",
    "partial", "error", "timeout",
)
def _stat_gap_finding(cv2, mid: str, result: dict, _results_map: dict):
    fc = _produced_finding_count(result)
    _extracted, _ = _results_map.get(mid, ([], "unknown"))
    actual = len(_extracted)
    status = _result_status(result)
    if fc <= actual or status not in _GAP_COUNTED_STATUSES:
        return None
    gap = fc - actual
    cv2._findings_gaps.append({
        "method_id": mid,
        "reported_count": fc,
        "collected_count": actual,
        "gap": gap,
        "status": status,
    })
    summary = str(result.get("summary") or "")[:100]
    return _mk_gap_stat_finding(mid, fc, actual, gap, summary)
def _log_gap_summary(cv2) -> None:
    if not cv2._findings_gaps:
        return
    total_gap = sum(g["gap"] for g in cv2._findings_gaps)
    _high_loss = [g for g in cv2._findings_gaps
                  if g.get("reported_count") and g.get("gap", 0) / g["reported_count"] > 0.5]
    if _high_loss:
        logger.error(
            "[Collect] findings gap 严重: %d/%d 方法收集率<50%% (total_gap=%d): %s",
            len(_high_loss), len(cv2._findings_gaps), total_gap,
            [f"{g['method_id']}:{g.get('gap')}/{g.get('reported_count')}" for g in _high_loss])
    else:
        logger.warning("[Collect] findings gap: %d methods, %d total gap",
                       len(cv2._findings_gaps), total_gap)
def _independent_results(cv2) -> dict:
    results = getattr(cv2, "independent_results", None)
    if isinstance(results, dict):
        return results
    if results:
        logger.warning("[Collect] independent_results 非 dict 形态(%s)，按空结果处理",
                       type(results).__name__)
    return {}
def collect_all_findings(cv2) -> list[dict]:
    results = _independent_results(cv2)
    items = list(results.items())
    _results_map = _extract_and_normalize_all(cv2, items)
    all_findings = []
    _seen_keys = set()
    _dup_count = 0
    for mid in results:
        findings, _status = _results_map.get(mid, ([], "unknown"))
        for f in findings:
            if not _dedup_and_validate(f, _seen_keys):
                _dup_count += 1
                continue
            all_findings.append(f)
    if _dup_count > 0:
        logger.info("[Collect] 去重移除 %d 个重复 finding", _dup_count)
    cv2._findings_gaps = []
    all_findings.extend(_collect_gap_findings(cv2, _results_map))
    _log_gap_summary(cv2)
    return all_findings
def _alias_names(value) -> tuple[str, ...]:
    if isinstance(value, str):
        return (value,) if value else ()
    if isinstance(value, SOURCE_SEQUENCE_TYPES):
        return tuple(name for name in value
                     if isinstance(name, str) and name)
    return ()
_ALIAS_ZERO_IS_PRESENT = frozenset({"confidence", "metric_value"})
def _alias_value_absent(_field: str, value) -> bool:
    if value is None:
        return True
    if isinstance(value, bool):
        return True
    if _field in _ALIAS_ZERO_IS_PRESENT and is_real_number(value):
        return False
    if isinstance(value, str):
        return not value.strip()
    if isinstance(value, float):
        return not math.isfinite(value) or value == 0
    if isinstance(value, int):
        return value == 0
    if isinstance(value, (list, tuple, set, frozenset, dict)):
        return not value
    return False
def _apply_finding_aliases(result: dict, cv2) -> None:
    aliases = getattr(cv2, "FINDING_FIELD_ALIASES", {})
    if not isinstance(aliases, dict):
        logger.warning("[Collect] FINDING_FIELD_ALIASES 非 dict(%s)，别名归一跳过",
                       type(aliases).__name__)
        return
    _pairs = {std_field: _alias_names(alt_names)
              for std_field, alt_names in aliases.items()
              if isinstance(std_field, str) and std_field}
    _owners: dict[str, int] = {}
    for alt_names in _pairs.values():
        for alt in alt_names:
            _owners[alt] = _owners.get(alt, 0) + 1
    for std_field, alt_names in _pairs.items():
        if not _alias_value_absent(std_field, result.get(std_field)):
            continue
        for alt in alt_names:
            if alt == std_field:
                continue
            _alt_value = result.get(alt)
            if _alias_value_absent(alt, _alt_value):
                continue
            result[std_field] = _alt_value
            if _owners.get(alt, 0) <= 1:
                del result[alt]
            break
def _normalize_core_fields(result: dict, cv2) -> None:
    result["rule_id"] = derive_rule_id(result).strip() or "unknown"
    if not result.get("file"):
        result["file"] = finding_file_of(result)
    result.setdefault("file", "")
    result.setdefault("line", 0)
    if not isinstance(result["file"], str):
        result["file"] = identifier_text(result["file"])
    result["line"] = coerce_line(result["line"])
    fpath = str(result.get("file", "") or "")
    if fpath:
        canon = canonical_cv_path(fpath, getattr(cv2, "skill_dir", None))
        if canon and canon != fpath:
            result["_file_original"] = fpath
            result["file"] = canon
    if result.get("severity") is None:
        result["severity"] = DEFAULT_SEVERITY
def _normalize_text_fields(result: dict) -> None:
    _message = _str_fallback(result.get("message"))
    if not _message:
        _message = _str_fallback(result.get("description"))
    _description = _str_fallback(result.get("description"))
    if not _description:
        _description = _message
    result["message"] = _message
    result["description"] = _description
    result.setdefault("_source_method", "unknown")
def _rule_family_from_rid(result: dict) -> None:
    rule_id = str(result["rule_id"])
    if not result.get("rule_family") and rule_id and rule_id != "unknown":
        if rule_id in ALL_FAMILY_KEYS:
            result["rule_family"] = rule_id
        else:
            _mapped_rf = lookup_rule_family(rule_id)
            result["rule_family"] = _mapped_rf if _mapped_rf != rule_id else "diag_general"
def _normalize_confidence(result: dict, cv2) -> None:
    confidence = result.get("confidence")
    source = "calculated" if confidence is not None else "default"
    if confidence is None:
        certainty = result.get("certainty")
        if certainty is not None:
            confidence = certainty
            source = "calculated"
        else:
            confidence = DEFAULT_CONFIDENCE_FALLBACK
    clamped = _finite_number(confidence)
    if clamped is None:
        clamped, source = DEFAULT_CONFIDENCE_FALLBACK, "default"
    result["confidence"] = clamp_unit(clamped)
    result["_confidence_source"] = source
    maturity_mult = _finite_number(
        getattr(cv2, "_test_maturity_multiplier", 1.0))
    if maturity_mult is not None and not math.isclose(maturity_mult, 1.0):
        result["confidence"] = clamp_unit(
            result["confidence"] * maturity_mult)
        result["_maturity_multiplier"] = maturity_mult
        result["_confidence_source"] = "maturity_adjusted"
def _normalize_finding(cv2, finding: dict) -> dict:
    result = dict(finding)
    if result.get("file") == "":
        del result["file"]
    _apply_finding_aliases(result, cv2)
    _normalize_core_fields(result, cv2)
    _normalize_text_fields(result)
    _rule_family_from_rid(result)
    _normalize_confidence(result, cv2)
    return result
def _normalize_finding_items(cv2, items: list) -> list[dict]:
    normalized = []
    for item in items:
        if not isinstance(item, dict):
            continue
        try:
            norm = _normalize_finding(cv2, item)
        except Exception as e:  # noqa: BLE001
            logger.warning("[Collect] 单条 finding 归一失败，已跳过: %s", e)
            continue
        if isinstance(norm, dict) and norm.get("_error"):
            continue
        normalized.append(norm)
    return normalized
def _apply_feedback_multiplier(cv2, f: dict, mid: str) -> None:
    if "_feedback_multiplier" in f:
        return
    multipliers = getattr(cv2, "_method_confidence_multipliers", {}) or {}
    if not isinstance(multipliers, dict):
        return
    mult = _finite_number(multipliers.get(mid))
    conf = _finite_number(f.get("confidence"))
    if mult is None or conf is None:
        return
    adjusted = conf * mult
    if not math.isfinite(adjusted):
        return
    f["confidence"] = clamp_unit(adjusted)
    f["_feedback_multiplier"] = mult
    f["_confidence_source"] = "adjusted"
def _first_hashable(value):
    if isinstance(value, (list, tuple)):
        return value[0] if value else ""
    return value
def normalized_confidence(
        value, fallback: float = DEFAULT_CONFIDENCE_FALLBACK) -> float:
    return clamp_unit(safe_float(value, fallback))
def _sample_severity(f0: dict) -> str:
    sev = f0.get("severity")
    if not isinstance(sev, str):
        return "unknown"
    return sev.strip().upper() or "unknown"
def _sample_str_field(
        f0: dict, *keys, default: str = _EMPTY_TEXT_DEFAULT) -> str:
    for k in keys:
        v = f0.get(k)
        if v:
            return str(v)
    return default
def summarize_findings(findings: list) -> dict:
    try:
        if not findings:
            return {}
        _dict_fs = dict_findings(findings)
        f0 = _dict_fs[0] if _dict_fs else {}
        sev_count = severity_breakdown_of(_dict_fs)
        return {
            "total_findings": len(_dict_fs),
            "severity_breakdown": sev_count,
            "rule_id": _sample_str_field(f0, "rule_id", "rule"),
            "severity": _sample_severity(f0),
            "message": _sample_str_field(f0, "message", "summary")[:MESSAGE_TRUNCATE_LEN],
            "file": os.path.basename(finding_file_of(f0)),
            "line": _finding_line_of(f0),
            "code_snippet": str(f0.get("code_snippet", "") or "")[:500],
            "fix_suggestion": str(f0.get("fix_suggestion", "") or f0.get("suggestion", "") or ""),
        }
    except Exception as e:  # noqa: BLE001
        logger.warning("[XV] findings汇总失败 in summarize_findings(): %s", e)
        return {"_error": True, "_partial": True}
def _index_keys_of(f: dict) -> tuple[str, int, str, str]:
    filepath = finding_file_of(f).strip()
    line = _finding_line_of(f)
    rule_id = (_str_fallback(
        f.get("rule_id") or f.get("type") or "unknown").strip()
        or "unknown")
    rule_family = (_str_fallback(
        f.get("rule_family") or "diag_general").strip()
        or "diag_general")
    return filepath, line, rule_id, rule_family
def _entry_confidence(f: dict):
    conf = _finite_number(f.get("confidence", 0.0))
    if conf is None:
        return None
    conf = clamp_unit(conf)
    if signal_bool(f.get("_partial_degrade")):
        conf *= degrade_factor_of(f)
    return conf if math.isfinite(conf) else None
def _locator_slot(line) -> str | int:
    return line if line and line > 0 else "FILE_LEVEL"
def _locator_of(filepath: str, line, rule_family: str) -> str:
    return f"{filepath}:{_locator_slot(line)}:{rule_family}"
def _accumulate_index_entry(index: dict, f: dict, filepath: str, line: int,
                            rule_id: str, rule_family: str,
                            locator: str) -> None:
    entry = index.setdefault(
        locator, _new_index_entry(locator, filepath, line, rule_id, rule_family))
    if f.get("_fp_shadow"):
        # 影子只等待后续裁决，不得进入来源、置信度或严重度计算，
        # 否则 deferred finding 能抬高自己所在组的结论并完成自我救援。
        entry.setdefault("_shadow_findings", []).append(f)
        return
    _src_method = str(f.get("_source_method") or "unknown")
    entry["sources"].add(_src_method)
    if signal_bool(f.get("_partial_degrade")):
        entry[SIGNAL_PARTIAL_SOURCES].add(_src_method)
    entry["findings"].append(f)
    entry["severities"].add(str(f.get("severity") or DEFAULT_SEVERITY))
    _conf = _entry_confidence(f)
    if _conf is not None:
        entry["max_confidence"] = max(entry["max_confidence"], _conf)
    entry["rule_families"].add(rule_family)
    entry["_grouped_sources"].setdefault(rule_family, set()).add(_src_method)
def _new_index_entry(locator: str, filepath: str, line: int,
                     rule_id: str, rule_family: str) -> dict:
    return {
        "locator": locator,
        "file": filepath,
        "line": line,
        "rule_id": rule_id,
        "rule_family": rule_family,
        "sources": set(),
        SIGNAL_PARTIAL_SOURCES: set(),
        "findings": [],
        "severities": set(),
        "rule_families": set(),
        "_grouped_sources": {},
        "max_confidence": 0.0,
    }
def _serialize_findings_index(index: dict[str, dict]) -> dict[str, dict]:
    result = {}
    for locator, entry in index.items():
        entry["sources"] = sorted(entry["sources"])
        entry[SIGNAL_PARTIAL_SOURCES] = sorted(entry[SIGNAL_PARTIAL_SOURCES])
        entry["severities"] = sorted(entry["severities"])
        entry["source_count"] = len(entry["sources"])
        entry["rule_families"] = sorted(entry["rule_families"])
        entry["_grouped_sources"] = {
            k: sorted(v) for k, v in entry["_grouped_sources"].items()
        }
        result[locator] = entry
    return result
def _index_file_identity(cv2, filepath: str) -> str:
    if not isinstance(filepath, str) or not filepath.strip():
        return ""
    normalized = filepath.strip().replace("\\", "/")
    try:
        if not os.path.isabs(normalized):
            skill_dir = getattr(cv2, "skill_dir", "")
            if isinstance(skill_dir, os.PathLike):
                skill_dir = os.fspath(skill_dir)
            if isinstance(skill_dir, str) and skill_dir:
                normalized = os.path.join(skill_dir, normalized)
        return os.path.normcase(os.path.normpath(os.path.abspath(normalized)))
    except (OSError, ValueError, TypeError) as _path_e:
        logger.warning("[Index] 文件身份归一失败，回退路径键: %r: %s",
                       filepath, _path_e)
        return finding_file_key(filepath)
def build_findings_index(cv2) -> dict[str, dict]:
    index = {}
    locator_aliases = {}
    raw_findings = getattr(cv2, "all_findings", None)
    if raw_findings and not isinstance(raw_findings, (list, tuple)):
        logger.warning("[Index] all_findings 非序列形态(%s)，按空索引处理",
                       type(raw_findings).__name__)
    all_findings = raw_findings if isinstance(raw_findings, (list, tuple)) else []
    for f in all_findings:
        if not isinstance(f, dict):
            logger.warning(
                "[Index] all_findings 含非 dict 元素(%s)，已跳过该条原始 finding",
                type(f).__name__,
            )
            continue
        filepath, line, rule_id, rule_family = _index_keys_of(f)
        identity = (_index_file_identity(cv2, filepath),
                    _locator_slot(line), rule_family)
        locator = locator_aliases.get(identity)
        if locator is None:
            locator = _locator_of(filepath, line, rule_family)
            locator_aliases[identity] = locator
        _accumulate_index_entry(
            index, f, filepath, line, rule_id, rule_family, locator)
    index = _NearMergeIndex(index, cv2).merge()
    result = _serialize_findings_index(index)
    logger.info("[Index] 构建索引: %d locators from %d raw findings",
                len(result), len(all_findings))
    return result
class _NearMergeIndex:
    __slots__ = ("cv2", "index")
    def __init__(self, index: dict[str, dict], cv2=None):
        self.index = index
        self.cv2 = cv2
    @staticmethod
    def tolerance() -> int:
        _val = env_number("JWSGJ_NEAR_MERGE_TOLERANCE", 2, float)
        if _val <= 0:
            return 0
        return int(min(_val, 10))
    def cluster_near_lines(self, ordered: list[str],
                           tol: int) -> list[list[str]]:
        if not ordered:
            return []
        _clusters: list[list[str]] = []
        _cur: list[str] = [ordered[0]]
        for _loc in ordered[1:]:
            _cur_line = self.index[_loc].get("line") or 0
            _head_line = self.index[_cur[0]].get("line") or 0
            _last_line = self.index[_cur[-1]].get("line", 0)
            if _cur_line - _last_line <= tol and _cur_line - _head_line <= tol:
                _cur.append(_loc)
            else:
                _clusters.append(_cur)
                _cur = [_loc]
        _clusters.append(_cur)
        return _clusters
    def groups(self) -> dict[tuple[str, str], list[str]]:
        _groups: dict[tuple[str, str], list[str]] = {}
        for _loc, _entry in self.index.items():
            _key = self.key_of(_entry)
            if _key is not None:
                _groups.setdefault(_key, []).append(_loc)
        return _groups
    def key_of(self, entry) -> tuple[str, str] | None:
        if not isinstance(entry, dict):
            return None
        line = entry.get("line")
        if not isinstance(line, int) or isinstance(line, bool) or line <= 0:
            return None
        family = entry.get("rule_family", "")
        if not family or family == "diag_general":
            return None
        file_id = entry.get("file", "") or ""
        if not isinstance(file_id, str) or not file_id:
            return None
        if self.cv2 is not None:
            file_id = _index_file_identity(self.cv2, file_id)
        if not file_id:
            return None
        return (file_id, family)
    def pairwise_disjoint_sources(self, cluster: list[str]) -> bool:
        _src_sets = [set(self.index[_loc].get("sources") or [])
                     for _loc in cluster]
        for _i in range(len(_src_sets)):
            for _j in range(_i + 1, len(_src_sets)):
                if _src_sets[_i] & _src_sets[_j]:
                    return False
        return True
    def merge_group_clusters(self, locs: list[str], tol: int) -> set[str]:
        _merged_away: set[str] = set()
        _ordered = sorted(
            locs, key=lambda _loc: (self.index[_loc].get("line") or 0, _loc))
        for _cluster in self.cluster_near_lines(_ordered, tol):
            if len(_cluster) < 2:
                continue
            if not self.pairwise_disjoint_sources(_cluster):
                continue
            self.merge_cluster_into_head(_cluster)
            _head_lines = sorted({
                self.index[_loc].get("line") or 0 for _loc in _cluster
            })
            if len(_head_lines) > 1:
                self.index[_cluster[0]]["_near_merged_lines"] = _head_lines
            _merged_away.update(_cluster[1:])
            logger.debug(
                "[Index] 邻近归并: %s ← %s (行号 %s，漂移容忍 ≤%d)",
                _cluster[0], list(_cluster[1:]), _head_lines, tol)
        return _merged_away
    @staticmethod
    def union_evidence_field(head: dict, entry: dict, key: str) -> None:
        head[key] = list(set(head[key]) | set(entry[key]))
    def merge_cluster_into_head(self, cluster: list[str]) -> None:
        _head = self.index[cluster[0]]
        for _other in cluster[1:]:
            _entry = self.index[_other]
            for _key in ("sources", SIGNAL_PARTIAL_SOURCES,
                         "severities", "rule_families"):
                self.union_evidence_field(_head, _entry, _key)
            _grp = _head["_grouped_sources"]
            for _fam_key, _srcs in _entry["_grouped_sources"].items():
                _grp[_fam_key] = sorted(
                    set(_grp.get(_fam_key, [])) | set(_srcs))
            _head["findings"].extend(_entry["findings"])
            _head.setdefault("_shadow_findings", []).extend(
                _entry.get("_shadow_findings", []))
            _head["max_confidence"] = max(
                _head["max_confidence"], _entry["max_confidence"])
    def merge_all_groups(self, groups: dict[tuple[str, str], list[str]],
                         tol: int) -> set[str]:
        merged_away: set[str] = set()
        for locs in groups.values():
            if len(locs) >= 2:
                merged_away |= self.merge_group_clusters(locs, tol)
        return merged_away
    @staticmethod
    def _snapshot_value(value):
        if isinstance(value, list):
            return list(value)
        if isinstance(value, set):
            return set(value)
        if isinstance(value, frozenset):
            return frozenset(value)
        return value
    @classmethod
    def snapshot(cls, index: dict[str, dict]) -> dict[str, dict]:
        snapshot = {}
        for locator, entry in index.items():
            if not isinstance(entry, dict):
                snapshot[locator] = entry
                continue
            copied = {
                key: cls._snapshot_value(value)
                for key, value in entry.items()
            }
            if isinstance(entry.get("_grouped_sources"), dict):
                copied["_grouped_sources"] = {
                    key: cls._snapshot_value(value)
                    for key, value in entry["_grouped_sources"].items()
                }
            snapshot[locator] = copied
        return snapshot
    def merge(self) -> dict[str, dict]:
        index = self.index
        original_index = index
        try:
            original_index = self.snapshot(index)
            tol = self.tolerance()
            if tol <= 0 or len(index) < 2:
                return index
            _merged_away = self.merge_all_groups(self.groups(), tol)
            if _merged_away:
                logger.info(
                    "[Index] 邻近行号归并: %d 个 locator 合并（行号漂移防护）",
                    len(_merged_away))
                index = {
                    _loc: _entry for _loc, _entry in index.items()
                    if _loc not in _merged_away
                }
            return index
        except Exception as _merge_e:  # noqa: BLE001
            logger.warning("[Index] 邻近行号归并降级跳过: %s", _merge_e)
            return original_index
def normalize_finding_input(data) -> tuple[dict, list, list, set]:
    if not isinstance(data, dict):
        data = {}
    data = _normalize_input_sequences(data)
    sources = list(data["sources"])
    partial_sources = {
        source
        for source in clean_source_ids(normalize_sources(
            data.get(SIGNAL_PARTIAL_SOURCES, [])))
        if source in sources
    }
    full_sources = [s for s in sources if s not in partial_sources]
    return data, sources, full_sources, partial_sources
def _normalize_input_sequences(data: dict) -> dict:
    return {
        **data,
        "sources": clean_source_ids(normalize_sources(data.get("sources"))),
        "findings": strict_iterable_list(data.get("findings")),
    }
def _worst_severity_of(rows) -> str:
    _ws = ""
    _wr = _UNKNOWN_SEVERITY_RANK
    for _f in rows:
        _sv = _normalize_severity(
            _f.get("severity") if isinstance(_f, dict) else None)
        _rk = SEVERITY_RANK.get(_sv, _UNKNOWN_SEVERITY_RANK)
        if _rk < _wr:
            _wr = _rk
            _ws = _sv
    return _ws or DEFAULT_SEVERITY
def _review_reasons_of(rows) -> list[str]:
    _review_reasons: list[str] = []
    for _f in rows:
        _r = _f.get("_review_reason")
        if not _r:
            continue
        _r = str(_r)[:200]
        if _r not in _review_reasons:
            _review_reasons.append(_r)
        if len(_review_reasons) >= 5:
            break
    return _review_reasons
_BUBBLE_FLAG_KEYS: tuple[str, ...] = (
    "_batch_source_rule",
    "_known_fp_family_high_sev",
    "_low_confidence_high_severity",
    "_single_group_new_finding",
    "_review_required",
)
def _propagate_boolean_flags(result: dict, rows: list, sources) -> None:
    result["_source_count"] = len(sources)
    for key in _BUBBLE_FLAG_KEYS:
        result[key] = any(_f.get(key, False) for _f in rows)
def _normalize_identity_fields(result: dict, data: dict, first_finding: dict,
                               rows: list) -> None:
    _family_value = data.get("rule_family")
    if not _family_value:
        _family_value = first_finding.get("rule_family", "")
    result["rule_family"] = _str_fallback(_family_value).strip()
    _severity_rows = list(rows)
    for _sev_key in ("severity", "severities"):
        _raw_sev = data.get(_sev_key)
        if isinstance(_raw_sev, (list, tuple, set, frozenset)):
            _severity_rows.extend({"severity": _sv} for _sv in _raw_sev)
        elif _raw_sev is not None:
            _severity_rows.append({"severity": _raw_sev})
    result["severity"] = _worst_severity_of(_severity_rows)
    result["rule_id"] = _str_fallback(
        first_finding.get("rule_id") or data.get("rule_id") or "").strip()
    _file_text = _str_fallback(data.get("file")).strip()
    if not _file_text:
        _file_text = finding_file_of(first_finding).strip()
    result["file"] = _file_text
    _line_value = data.get("line")
    if _line_value is None:
        _line_value = _finding_line_of(first_finding)
    result["line"] = coerce_line(_line_value)
def propagate_finding_metadata(result: dict, data: dict, sources) -> None:
    data = data if isinstance(data, dict) else {}
    sources = sources if isinstance(sources, SOURCE_SEQUENCE_TYPES) else []
    rows = dict_findings(data.get("findings", []))
    first = rows[0] if rows else {}
    _normalize_identity_fields(result, data, first, rows)
    _propagate_boolean_flags(result, rows, sources)
    _review_reasons = _review_reasons_of(rows)
    if _review_reasons:
        result["_review_reasons"] = _review_reasons
        result.setdefault("_review_reason", _review_reasons[0])
def _reg_changed_path_match(fp_norm: str, cf_norm: str) -> bool:
    if not fp_norm or not cf_norm:
        return False
    if fp_norm == cf_norm:
        return True
    fp_absolute = os.path.isabs(fp_norm)
    if fp_absolute == os.path.isabs(cf_norm):
        return False
    absolute, relative = ((fp_norm, cf_norm) if fp_absolute
                          else (cf_norm, fp_norm))
    return absolute.endswith("/" + relative)
def _reg_resolve_finding_filepath(finding: dict) -> str:
    filepath = finding_file_of(finding)
    if filepath:
        return filepath
    for entry in dict_findings(findings_container(finding)):
        filepath = finding_file_of(entry)
        if filepath:
            return filepath
    return ""
_REGRESSION_MARKS: dict[tuple[str, bool], tuple[str, str, str]] = {
    ("investigated", True): (
        "STATUS_NEW_CONFIRMED",
        "变更区域新发现（回归上下文标注，结论保持证据链判定）",
        "marked_new",
    ),
    ("confirmed", False): (
        "STATUS_LEGACY",
        "非变更区域历史存量（回归上下文标注，结论保持证据链判定）",
        "marked_legacy",
    ),
    ("confirmed", True): ("STATUS_NEW_CONFIRMED", "变更区域已确认", "unchanged"),
}
def _reg_in_changed_set(filepath: str, changed_norms: list[str]) -> bool:
    if not filepath:
        return False
    fp_norm = finding_file_key(filepath)
    return bool(fp_norm) and any(
        _reg_changed_path_match(fp_norm, cf_norm) for cf_norm in changed_norms)
def _reg_status(conclusion: Any, in_changed: bool) -> tuple[str | None, str, str]:
    if not isinstance(conclusion, str):
        return None, "", "unchanged"
    return _REGRESSION_MARKS.get(
        (conclusion.strip().lower(), in_changed), (None, "", "unchanged"))
def _reg_mark_finding(finding, changed_norms, stats):
    if not isinstance(finding, dict):
        stats["unchanged"] += 1
        return finding
    finding.pop("_regression_marker", None)
    finding.pop("_regression_note", None)
    in_changed = _reg_in_changed_set(
        _reg_resolve_finding_filepath(finding), changed_norms)
    marker, note, stat_key = _reg_status(
        finding.get("conclusion"), in_changed)
    if marker:
        finding["_regression_marker"] = marker
        finding["_regression_note"] = note
    stats[stat_key] += 1
    return finding
def _reg_changed_norms(regression_ctx: dict[str, Any]) -> list[str] | None:
    raw = regression_ctx.get("changed_files", [])
    if isinstance(raw, str):
        raw = [raw]
    if not isinstance(raw, SOURCE_SEQUENCE_TYPES):
        return None
    norms = list(dict.fromkeys(
        normalized for cf in raw
        if isinstance(cf, str) and cf
        and (normalized := finding_file_key(cf))))
    return norms or None
def fuse_regression_into_xv(
    xv_findings: list[dict[str, Any]],
    regression_ctx: dict[str, Any],
) -> list[dict[str, Any]]:
    if not isinstance(xv_findings, list) or not isinstance(regression_ctx, dict):
        return xv_findings
    changed_norms = _reg_changed_norms(regression_ctx)
    if changed_norms is None:
        return xv_findings
    stats = {"marked_new": 0, "marked_legacy": 0, "unchanged": 0}
    updated = [_reg_mark_finding(f, changed_norms, stats) for f in xv_findings]
    if stats["marked_new"] or stats["marked_legacy"]:
        logger.info(
            "Regression fusion: %d marked_new, %d marked_legacy, %d unchanged",
            stats["marked_new"], stats["marked_legacy"], stats["unchanged"],
        )
    return updated
logger.info("xv_findings_core 已加载: %d 个顶层定义",
            sum(1 for _obj in globals().values()
                if callable(_obj)
                and getattr(_obj, "__module__", "") == __name__))

from __future__ import annotations

import logging
import math
import os
import re
import time
from collections import Counter
from collections.abc import Iterable, Iterator, Mapping
from dataclasses import dataclass
from functools import lru_cache
from typing import Any, NamedTuple

from jwsgj.diag_shared_source_core import (
    read_source,
)
from jwsgj.diag_shared_source_scan import (
    is_suppressed,
    parse_suppressions,
)
from jwsgj.diag_types_normalize import (
    coerce_mapping,
    safe_confidence,
    safe_to_int,
)
from jwsgj.diag_types_vocab import (
    DIAGNOSE_TO_P,
    FINDING_KEY_ALIASES,
    SEVERITY_RANK,
)
from jwsgj.fp_rules_judge import (
    apply_fp_downgrade,
)
from jwsgj.log_config import (
    log_swallowed,
)
from jwsgj.shared_cache_store import CacheNotWarmedError

__all__ = [
    "DETECTOR_SPECS",
    "REGISTRY_BUILDABLE_PARAMS",
    "REGISTRY_CID_EMITS",
    "REGISTRY_KNOWN_PARAMS",
    "REGISTRY_SKIP_IDS",
    "RETIRED_RULE_IDS",
    "DetectorSpec",
    "apply_inline_suppressions",
    "apply_suppress_filter",
    "as_text",
    "build_detector_kwargs",
    "build_issue_envelope",
    "category_from_rule_id",
    "coerce_issue_line",
    "coerce_issue_text",
    "collect_findings",
    "consolidate_findings",
    "deduplicate_issues",
    "detector_entry",
    "detector_entry_map",
    "detector_view_payload",
    "extend_issues",
    "filter_retired_findings",
    "finding_file",
    "finding_line",
    "finding_rule_id",
    "get_detector_spec",
    "group_envelope",
    "group_payload",
    "is_retired_rule",
    "map_external_severity",
    "mechanisms_of",
    "normalize_conf_enum",
    "normalize_id_set",
    "normalize_severity",
    "project_pollution_issues",
    "retired_registry_excludes",
    "retired_rule_key",
    "split_malformed_issues",
    "to_issue_dict",
    "verdict_from_findings",
    "verdict_from_severity_counts",
    "worst_sub_status",
]
_log = logging.getLogger(__name__)
_DEFAULT_FILEPATH = ""
_DEFAULT_SKILL_DIR = ""
def normalize_id_set(ids) -> set[str]:
    if isinstance(ids, str):
        ids = (ids,)
    elif not isinstance(ids, Iterable):
        _log.debug("[Detectors] 检测器 ID 入参不可迭代(%r)，按空集处理", ids)
        return set()
    out: set[str] = set()
    for i in ids:
        _add_normalized_id(out, i)
    return out
def _add_normalized_id(out: set[str], item: Any) -> None:
    if not isinstance(item, str):
        _log.debug("[Detectors] 跳过非法检测器 ID: %r", item)
        return
    _id = item.strip()
    if not _id:
        _log.debug("[Detectors] 跳过空白检测器 ID: %r", item)
        return
    out.add(_id)
    if "-" in _id:
        out.add(_id.replace("-", ""))
_PARAM_SOURCES: dict[str, str] = {
    "tree": "tree",
    "filepath": "filepath",
    "file_path": "filepath",
    "source_lines": "source_lines",
    "source": "code",
    "source_code": "code",
    "code": "code",
}
_PARAM_CONSTANTS: dict[str, Any] = {
    "node": None,
    "context": None,
    "strict_mode": False,
    "base_path": None,
}
_PARAM_DEFERRED = frozenset({"index"})
def build_detector_kwargs(
    params: frozenset,
    tree: Any,
    filepath: str,
    source_lines: list[str],
    code: str,
) -> dict[str, Any]:
    kwargs: dict[str, Any] = ({} if params
                             else {"tree": tree, "filepath": filepath})
    _values = {"tree": tree, "filepath": filepath,
               "source_lines": source_lines, "code": code}
    for _name in params:
        _src = _PARAM_SOURCES.get(_name)
        if _src is not None:
            kwargs[_name] = _values[_src]
        elif _name in _PARAM_CONSTANTS:
            kwargs[_name] = _PARAM_CONSTANTS[_name]
        elif _name not in _PARAM_DEFERRED:
            _log.debug("[Detectors] 构建器无对应来源的形参被跳过: %s", _name)
    return kwargs
def collect_findings(
    result: Any,
    cid: str,
    filepath: str,
    code: str,
    suppress_map: Any,
) -> tuple[list[dict[str, Any]], Any]:
    out: list[dict[str, Any]] = []
    items = _prepare_findings_items(result, cid)
    if items is None:
        return out, suppress_map
    for item in items:
        normalized = _normalize_finding_item(item, cid, filepath)
        if normalized is None:
            continue
        if suppress_map is None:
            suppress_map = parse_suppressions(code)
        if _is_suppressed_finding(normalized, suppress_map):
            continue
        out.append(normalized)
    return out, suppress_map
def _normalize_finding_item(item: Any, cid: str,
                            filepath: str) -> dict[str, Any] | None:
    if item is None:
        return None
    if isinstance(item, (str, bytes)):
        _log.warning(
            "[Detectors] 检测器 %s 产出 str/bytes 标量项（%r），按零产出跳过",
            cid, item[:80] if len(item) > 80 else item,
        )
        return None
    raw = _extract_finding_mapping(item)
    if raw is None or not _looks_like_finding(raw):
        _log.warning(
            "[Detectors] 检测器 %s 产出非 finding 项（%s），按零产出跳过",
            cid, type(item).__name__,
        )
        return None
    return _normalize_registered_finding(item, cid, filepath, raw=raw)
def _is_suppressed_finding(normalized: dict[str, Any],
                           suppress_map: Any) -> bool:
    rid = normalized.get("rule_id", "")
    ln = normalized.get("line") or 0
    if not (rid and ln and suppress_map):
        return False
    if is_suppressed(suppress_map, ln, rid):
        return True
    aliases = normalized.get("suppress_aliases") or ()
    return any(is_suppressed(suppress_map, ln, str(alias))
               for alias in aliases)
def _prepare_findings_items(result: Any, cid: str) -> list | None:
    if result is None:
        return []
    if isinstance(result, (str, bytes, Mapping)) and len(result) == 0:
        return []
    if isinstance(result, (list, tuple)):
        return list(result)
    if isinstance(result, (str, bytes, Mapping)) or not isinstance(
            result, Iterable):
        return [result]
    if isinstance(result, Iterator):
        _log.warning(
            "[Detectors] 检测器 %s 返回惰性迭代形态（%s），按契约零产出跳过",
            cid, type(result).__name__,
        )
        return None
    try:
        return list(result)
    except (TypeError, ValueError, RuntimeError) as _e:
        log_swallowed(
            __name__, _e,
            context=f'_prepare_findings_items:{type(_e).__name__}')
        _log.warning(
            "[Detectors] 检测器 %s 返回不可展开可迭代（%s），按标量项处理",
            cid, type(result).__name__,
        )
        return [result]
REGISTRY_BUILDABLE_PARAMS = (frozenset(_PARAM_SOURCES)
                              | frozenset(_PARAM_CONSTANTS)
                              | _PARAM_DEFERRED)
_NON_BUILDABLE_KNOWN_PARAMS = frozenset({"kwargs", "path_or_code"})
REGISTRY_KNOWN_PARAMS = REGISTRY_BUILDABLE_PARAMS | _NON_BUILDABLE_KNOWN_PARAMS
REGISTRY_SKIP_IDS = frozenset({
    "D36", "D37", "D40",
    "EN01",
    "AF01", "AF02", "AF03", "AF04",
    "MS01",
    "GF16", "GF18",
    "MS02",
    "XT01",
    "TO04",
    "PY09",
    "IO01",
    "IO05",
    "NW03",
    "PY01",
    "AY02",
})
RETIRED_RULE_IDS: frozenset = frozenset({
    "IN-07", "RD-11", "HC-01", "EX-02", "AW-01", "CX-01", "MN-01", "EX-01",
    "CH03-MISPLACED-SYMBOL", "RD-18", "AS-03", "RB-05",
    "ND-01", "SW-01", "IT-02", "RD-13", "EH-03", "DF-01",
    "PERF-003", "RB-15", "PERF-006", "RB-09", "D17-ERROR-IN-LOOP", "RD-25",
    "RD-16", "POL-01", "RD-21", "CC-02", "PX-01", "SZ-01", "HL-01",
    "IN-05", "EP-01", "RD-02", "RD-07", "CC-03", "IN-06", "AT-01",
    "LO-01", "AS-02", "IM-03", "AS-01", "D34", "D38", "D54", "RB-10",
    "D35",
    "PY-06", "VC-02", "SL-03", "SL-04", "D47", "SH-01", "CG-SIG-01",
    "LP-01", "LP-02", "LP-03", "LP-04",
    "TM-SURVIVED",
    "TM-SURVIVED-BATCH",
    "AI-01",
    "AI-04",
    "AI-05",
    "AI-06",
    "AP-C11",
    "AP-C16",
    "AP-C17",
    "AP-C2",
    "AP-C4",
    "AP-C6",
    "AS-04",
    "AS-05",
    "AS-08",
    "AT-03",
    "AW-02",
    "BE-01",
    "BUG-018",
    "C11_duplicates",
    "C16_stubs",
    "C17_dynamic_import",
    "C2_lazy_import",
    "C4_regression",
    "C6_circular",
    "CG-HALLUC-01",
    "CH02-SOFT-CYCLE",
    "CH04-MERGE-CANDIDATE",
    "CH05-SPLIT-CANDIDATE",
    "CM-02",
    "CQ-01",
    "CQ-04",
    "CQ-08",
    "CS-16",
    "CS-NOLOCK",
    "CT-01",
    "D07",
    "D17-LEVEL-MISUSE",
    "D17-PRINT-AS-LOG",
    "D20_merge_preflight",
    "D21-CROSS-MODULE-ASSIGN",
    "D21-DYNAMIC-IMPORT",
    "D21-GETATTR-MODULE",
    "D21-IMPORTLIB",
    "D21-INIT-SIDE-EFFECT",
    "D21-SYS-MODULES",
    "D41",
    "D6-DEAD-FUNC",
    "D6-UNUSED-IMPORT",
    "DB-02",
    "DC-02",
    "DC-04",
    "EH-01",
    "EH-02",
    "EH-06",
    "EH-07",
    "EH-08",
    "EN-02",
    "EX-03",
    "EX-05",
    "GF-05",
    "GF-11",
    "GF-13",
    "H05",
    "IMPLICIT-CONDITIONAL",
    "IMPLICIT-EXCEPTION",
    "IN-02",
    "IN-03",
    "IN-04",
    "IO-02",
    "IO-06",
    "IT-03",
    "JS-02",
    "LK-01",
    "LO-02",
    "LQ-01",
    "LQ-02",
    "MM-02",
    "MM-04",
    "MP-02",
    "NT-02",
    "NT-03",
    "OS-01",
    "PERF-005",
    "PI-03",
    "PX-03",
    "PX-04",
    "PY-SYN",
    "RB-02",
    "RB-06",
    "RB-07",
    "RB-08",
    "RB-12",
    "RB-13",
    "RB-16",
    "RC-03",
    "RD-09",
    "RD-10",
    "RD-20",
    "RD-22",
    "RD-24",
    "RG-01",
    "RS-01",
    "RV-01",
    "RX-01",
    "SCP-01",
    "SCP-02",
    "SJ-01",
    "SK-03",
    "SP-02",
    "ST-01",
    "ST-02",
    "ST-03",
    "ST-04",
    "TC-01",
    "TP-03",
    "TRY-try003_raise_vanilla_args",
    "TRY-try004_type_check_without_type_error",
    "TT-04",
    "TY-04",
    "VC-01",
    "missing_docstring",
    "symbol_conflict",
    "RD-27",
})
_METHOD_RULE_PREFIXES: tuple[str, ...] = (
    "A1-", "A2-", "A3-", "A4-", "B1-", "B2-",
)
def retired_rule_key(rule_id: object) -> str:
    key = str(rule_id or "").strip()
    if not key:
        return ""
    for _prefix in _METHOD_RULE_PREFIXES:
        if key.upper().startswith(_prefix):
            key = key[len(_prefix):]
            break
    return key.replace("-", "").replace("_", "").lower()
@lru_cache(maxsize=1)
def _retired_keys() -> frozenset:
    return frozenset(retired_rule_key(_rid) for _rid in RETIRED_RULE_IDS)
def is_retired_rule(rule_id: object) -> bool:
    return retired_rule_key(rule_id) in _retired_keys()
def filter_retired_findings(findings: object) -> tuple[list, dict]:
    if not isinstance(findings, (list, tuple)):
        if isinstance(findings, (str, bytes, Mapping)) or not isinstance(
                findings, Iterable):
            return [], {}
        findings = list(findings)
    kept: list = []
    retired: dict = {}
    for finding in findings:
        if not isinstance(finding, Mapping):
            kept.append(finding)
            continue
        rid = (finding.get("rule_id") or finding.get("rule_family")
               or finding.get("id") or "")
        if is_retired_rule(rid):
            _key = str(rid)
            retired[_key] = retired.get(_key, 0) + 1
            continue
        kept.append(finding)
    return kept, retired
REGISTRY_CID_EMITS: dict[str, frozenset[str]] = {
    "PY10": frozenset({"PY-10"}),
    "PL-01": frozenset({"BUG-018"}),
    "PL-02": frozenset({"SEC-008"}),
    "PL-03": frozenset({"REF-012"}),
    "PL-04": frozenset({"PERF-005"}),
    "IF-01": frozenset({"IMPLICIT-CONDITIONAL", "IMPLICIT-LOOP",
                         "IMPLICIT-EXCEPTION"}),
}
def retired_registry_excludes() -> frozenset:
    _ids = set(REGISTRY_SKIP_IDS)
    for _rid in RETIRED_RULE_IDS:
        _ids.add(_rid)
        _ids.add(_rid.replace("-", ""))
    for _cid, _emits in REGISTRY_CID_EMITS.items():
        if _emits and _emits <= RETIRED_RULE_IDS:
            _ids.add(_cid)
            _ids.add(_cid.replace("-", ""))
    return frozenset(_ids)
_P_LEVELS = frozenset(f"P{rank}" for rank in set(SEVERITY_RANK.values()))
_SEVERITY_FALLBACK = "P3"
_SEVERITY_ALIASES: dict[str, str] = {
    **{name: f"P{rank}" for name, rank in SEVERITY_RANK.items()},
    **DIAGNOSE_TO_P,
    "BLOCKER": "P0",
}
def _label_text(value: Any) -> str:
    raw = getattr(value, "value", value)
    if not isinstance(raw, str) or not raw.strip():
        name = getattr(value, "name", None)
        if isinstance(name, str) and name.strip():
            raw = name
    return str(raw or "").strip().upper()
def _canonical_severity(sev: Any) -> str:
    text = _label_text(sev)
    if not text:
        return ""
    alias = _SEVERITY_ALIASES.get(text)
    if alias is not None:
        return alias
    _p_level = re.fullmatch(r'P(\d+)', text)
    if _p_level is not None:
        _candidate = f'P{int(_p_level.group(1))}'
        return _candidate if _candidate in _P_LEVELS else ""
    return ""
def normalize_severity(sev: Any) -> str:
    if sev is None:
        return "P2"
    return _canonical_severity(sev) or "P2"
def map_external_severity(value: Any, table: dict | None = None,
                          fallback: str = _SEVERITY_FALLBACK) -> str:
    _sev = _label_text(value)
    if not _sev:
        return fallback
    if _sev in _P_LEVELS:
        return _sev
    _mapped = (table or {}).get(_sev.lower())
    if _mapped is not None:
        return _canonical_severity(_mapped) or fallback
    _rank = SEVERITY_RANK.get(_sev)
    if _rank is not None and f"P{_rank}" in _P_LEVELS:
        return f"P{_rank}"
    return fallback
def _normalize_registered_finding(
    item: Any, fallback_id: str, filepath: str = _DEFAULT_FILEPATH,
    *, raw: Mapping | None = None,
) -> dict[str, Any] | None:
    raw = (_extract_finding_mapping(item) or {}) if raw is None else dict(raw)
    rule_id = _extract_rule_id(raw, fallback_id)
    message = _extract_message(raw)
    line = finding_line(raw)
    _file = finding_file(raw) or as_text(filepath)
    normalized: dict[str, Any] = dict(raw)
    normalized.update({
        "rule_id": rule_id,
        "severity": normalize_severity(raw.get("severity")),
        "file": _file,
        "line": line,
        "message": message,
        "category": _extract_category(raw),
    })
    _attach_optional_finding_keys(normalized, raw)
    return normalized
_FILE_ALIASES: tuple[str, ...] = FINDING_KEY_ALIASES["file"]
_LINE_ALIASES: tuple[str, ...] = FINDING_KEY_ALIASES["line"]
_RULE_ALIASES: tuple[str, ...] = FINDING_KEY_ALIASES["rule_id"]
_MESSAGE_ALIASES: tuple[str, ...] = FINDING_KEY_ALIASES["message"]
_FINDING_IDENTITY_KEYS: tuple[str, ...] = tuple(dict.fromkeys(
    (*_FILE_ALIASES, *_LINE_ALIASES, *_RULE_ALIASES, *_MESSAGE_ALIASES,
     "detail", "pattern_name", "category", "dimension", "severity",
     "confidence", "suggestion", "fix_guidance")
))
def _sequence_items(value: Any) -> list:
    if isinstance(value, (list, tuple, set, frozenset)):
        return list(value)
    return []
def _extract_finding_mapping(item: Any) -> dict | None:
    if isinstance(item, Mapping):
        return dict(item)
    return coerce_mapping(item)
def _looks_like_finding(raw: Mapping) -> bool:
    return any(key in raw for key in _FINDING_IDENTITY_KEYS)
def _first_present(raw: dict, *keys: str) -> Any:
    for key in keys:
        value = raw.get(key)
        if value and (not isinstance(value, str) or value.strip()):
            return value
    return None
def _is_placeholder_rule_id(rule_id: str) -> bool:
    return (not rule_id or rule_id.upper() == "UNKNOWN"
            or "object at 0x" in rule_id)
def _concrete_rule_id(raw: Mapping, aliases: tuple[str, ...]) -> str:
    for alias in aliases:
        candidate = str(raw.get(alias) or "").strip()
        if not _is_placeholder_rule_id(candidate):
            return candidate
    return ""
def _extract_rule_id(raw: dict, fallback_id: str) -> str:
    return _concrete_rule_id(raw, _RULE_ALIASES) or fallback_id
def as_text(value: Any, default: str = "") -> str:
    if not value:
        return default
    return value if isinstance(value, str) else str(value)
def _extract_message(raw: dict) -> str:
    return as_text(_first_present(raw, *_MESSAGE_ALIASES)
                    or raw.get("detail")
                    or raw.get("pattern_name"))
def _extract_category(raw: dict) -> str:
    return as_text(_first_present(raw, "category", "dimension"),
                    "registered_detector")
def _attach_optional_finding_keys(normalized: dict[str, Any], raw: dict) -> None:
    if raw.get("confidence") is not None:
        _value, _label = _confidence_pair(raw.get("confidence"))
        normalized["confidence"] = _value
        if _label is not None:
            normalized["confidence_label"] = _label
    for key in ("suggestion", "code_snippet"):
        text = as_text(raw.get(key))
        if text:
            normalized[key] = text
    for key in ("delegation_type", "facade_type", "function",
                "delegates_to", "source_rule"):
        text = as_text(raw.get(key))
        if text:
            normalized[key] = text
    aliases = raw.get("suppress_aliases")
    if _sequence_items(aliases):
        normalized["suppress_aliases"] = tuple(
            str(alias) for alias in _sequence_items(aliases) if alias)
_OUTPUT_RULE_ID_ALIASES = ("rule_id", "rule", "id", "check_id", "ref_id",
                           "check", "code", "type", "detector_id")
_OUTPUT_MESSAGE_ALIASES = ("message", "title", "description", "text", "msg",
                           "desc", "summary")
_OUTPUT_SEVERITY_ALIASES = ("severity", "level", "grade")
_OUTPUT_LINE_ALIASES = ("lineno", "line_no", "line_number")
_DIMENSION_CATEGORY_VALUES = frozenset({
    "security", "performance", "refactor", "quality", "general"})
_CATEGORY_PREFIX_GROUPS: tuple[tuple[tuple[str, ...], str], ...] = (
    (("SN", "SE", "SA"), "security"),
    (("LP", "PR", "PM"), "performance"),
    (("DC", "RD", "RB", "RC", "ST"), "refactor"),
    (("SZ", "LS", "CC", "CN", "CQ", "DP", "DS", "ID", "NT", "PI"),
     "quality"),
)
def _first_non_empty(norm: Any, aliases: tuple[str, ...]) -> Any:
    for alias in aliases:
        value = norm.get(alias)
        if value is not None and (
                not isinstance(value, str) or value.strip()):
            return value
    return None
def _resolve_rule_id(norm: Any) -> Any:
    rid = finding_rule_id(norm)
    if _is_placeholder_rule_id(rid):
        rid = UNKNOWN_RULE_ID
    norm["rule_id"] = rid
    return rid
def _first_repr_free(norm: Any, aliases: tuple[str, ...]) -> str:
    for alias in aliases:
        value = norm.get(alias)
        if value is None or value == "" or "object at 0x" in str(value):
            continue
        return str(value)
    return ""
def _resolve_message(norm: Any, fallback: str = "") -> None:
    msg = str(_first_non_empty(norm, _OUTPUT_MESSAGE_ALIASES) or fallback or "")
    if "object at 0x" in msg:
        msg = (_first_repr_free(norm, ("title", "description"))
               or "See additional fields for details")
    norm["message"] = msg[:500]
UNKNOWN_RULE_ID = "_UNKNOWN_RULE"
def _resolve_severity(norm: Any) -> None:
    raw = _first_non_empty(norm, _OUTPUT_SEVERITY_ALIASES)
    norm["severity"] = _canonical_severity(raw) or _SEVERITY_FALLBACK
def category_from_rule_id(rid: str) -> str:
    rid = rid.strip().upper()
    for prefixes, category in _CATEGORY_PREFIX_GROUPS:
        if rid.startswith(prefixes):
            return category
    return "general"
def _resolve_category(norm: Any, rid: Any) -> None:
    if norm.get("category"):
        return
    _dim = norm.get("dimension")
    if isinstance(_dim, str):
        normalized_dim = _dim.strip().lower()
        if normalized_dim in _DIMENSION_CATEGORY_VALUES:
            norm["category"] = normalized_dim
            return
    norm["category"] = category_from_rule_id(str(rid))
def _apply_field_resolution(norm: Any, fallback: str = "") -> None:
    rid = _resolve_rule_id(norm)
    _resolve_message(norm, fallback=fallback)
    _resolve_severity(norm)
    norm["line"] = finding_line(norm)
    _resolve_category(norm, rid)
def ensure_issue_dict(issue: Any) -> Any:
    if isinstance(issue, dict):
        return dict(issue)
    _d = _extract_finding_mapping(issue)
    return _d if _d is not None else {
        "message": str(issue), "rule_id": "UNKNOWN"}
def to_issue_dict(item: Any, filepath: Any = _DEFAULT_FILEPATH, *,
                  skill_dir: Any = _DEFAULT_SKILL_DIR) -> dict:
    d = _extract_finding_mapping(item)
    if d is None:
        d = {}
    _apply_field_resolution(
        d, fallback="" if isinstance(item, Mapping) else str(item))
    _file = finding_file(d) or as_text(filepath)
    if _file:
        d['file'] = _file
    d['severity'] = apply_fp_downgrade(
        d.get('rule_id'), d.get('severity'), skill_dir=as_text(skill_dir),
        file_path=str(_file))
    return d
def coerce_issue_line(*vals: Any) -> int:
    for value in vals:
        line = _finding_line_candidate(value)
        if line is not None:
            return line
    return 0
def coerce_issue_text(*vals: Any) -> str:
    for v in vals:
        if isinstance(v, str) and v:
            return v
    return ""
def build_issue_envelope(rule_id: str, severity: Any, line: Any, file: Any,
                         message: Any, category: str, confidence: float,
                         **extra: Any) -> dict:
    return {
        "rule_id": rule_id,
        "severity": normalize_severity(severity),
        "line": coerce_issue_line(line),
        "file": (os.fsdecode(os.fspath(file))
                 if isinstance(file, os.PathLike) else coerce_issue_text(file)),
        "message": message,
        "category": category,
        "confidence": safe_confidence(confidence),
        **extra,
    }
def extend_issues(issues_list: Any, new_items: Any,
                  filepath: Any = _DEFAULT_FILEPATH, *,
                  skill_dir: Any = _DEFAULT_SKILL_DIR) -> None:
    if new_items is None:
        return
    if isinstance(new_items, (str, bytes, Mapping)) or not hasattr(
            new_items, "__iter__"):
        items = [new_items]
    else:
        try:
            items = list(new_items)
        except (TypeError, ValueError, RuntimeError) as _e:
            log_swallowed(
                __name__, _e,
                context=f'extend_issues:{type(_e).__name__}')
            items = [new_items]
    for item in items:
        if item is not None:
            issues_list.append(to_issue_dict(
                item, filepath, skill_dir=skill_dir))
def _issue_container_items(issues: Any) -> list:
    if issues is None:
        return []
    if isinstance(issues, (list, tuple)):
        return list(issues)
    if isinstance(issues, (str, bytes, Mapping)) or not isinstance(
            issues, Iterable):
        return [issues]
    try:
        return list(issues)
    except (TypeError, ValueError, RuntimeError) as _e:
        log_swallowed(
            __name__, _e,
            context=f'_issue_container_items:{type(_e).__name__}')
        return [issues]
def _normalize_issues(issues: Any) -> list:
    normalized = []
    for issue in _issue_container_items(issues):
        norm = ensure_issue_dict(issue)
        _apply_field_resolution(norm)
        normalized.append(norm)
    return normalized
def deduplicate_issues(issues: Any) -> list:
    issues = _normalize_issues(issues)
    seen = set()
    deduped = []
    for issue in issues:
        _line = issue.get('line')
        key = (finding_file(issue), str(issue.get('rule_id', '')),
               0 if _line is None else _line, str(issue.get('message', '')))
        if key not in seen:
            seen.add(key)
            deduped.append(issue)
    return deduped
def split_malformed_issues(issues: Any) -> tuple[int, list]:
    if issues is None:
        return 0, []
    if isinstance(issues, (list, tuple)):
        _items = list(issues)
    elif isinstance(issues, (str, bytes, Mapping)):
        return 1, []
    elif isinstance(issues, Iterable):
        try:
            _items = list(issues)
        except (TypeError, ValueError, RuntimeError) as _e:
            log_swallowed(
                __name__, _e,
                context=f'split_malformed_issues:{type(_e).__name__}')
            return 1, []
    else:
        return 1, []
    _dicts = [f for f in _items if isinstance(f, Mapping)]
    return len(_items) - len(_dicts), _dicts
def _is_suppressed_issue(issue: Any, suppress_map: Any) -> bool:
    if not isinstance(issue, Mapping):
        issue = _extract_finding_mapping(issue)
    if issue is None:
        return False
    line = finding_line(issue)
    if not line:
        return False
    return any(is_suppressed(suppress_map, line, key)
               for key in _finding_suppress_keys(issue))
def apply_suppress_filter(issues: Any, code: Any) -> Any:
    if not issues or not isinstance(code, str):
        return issues
    try:
        suppress_map = parse_suppressions(code)
        if not suppress_map:
            return issues
        _items = _issue_container_items(issues)
        if not _items:
            return issues
        return [issue for issue in _items
                if not _is_suppressed_issue(issue, suppress_map)]
    except (AttributeError, KeyError, TypeError, ValueError, RuntimeError) as e:
        _log.debug('suppress filter failed: %s', e)
        return issues
_FINDING_RULE_ID_LOOKUP_ALIASES = tuple(dict.fromkeys(
    (*_OUTPUT_RULE_ID_ALIASES[1:], *_RULE_ALIASES[1:])))
def finding_rule_id(finding: dict[str, Any]) -> str:
    rid = str(finding.get("rule_id") or "").strip()
    return (_concrete_rule_id(
        finding, ("rule_id", *_FINDING_RULE_ID_LOOKUP_ALIASES)) or rid)
_CONF_BONUS_PER_SUB = 0.05
_CONF_BONUS_CAP = 0.15
_REPORT_CONSUMING_SUBS = frozenset({"E1"})
def _safe_conf(v) -> float:
    if isinstance(v, bool):
        _log.debug("[Detectors] _safe_conf bool 置信度降级为 0.0: %r", v)
        return 0.0
    try:
        fv = float(v)
    except (TypeError, ValueError, OverflowError):
        _log.debug("[Detectors] _safe_conf 非数值置信度降级为 0.0: %r", v)
        return 0.0
    if not math.isfinite(fv):
        _log.debug("[Detectors] _safe_conf 非有限置信度降级为 0.0: %r", v)
        return 0.0
    return min(1.0, max(0.0, fv))
def _findings_of(result) -> list:
    if not isinstance(result, dict):
        return []
    findings = result.get("findings")
    if findings is None:
        return []
    if isinstance(findings, (list, tuple)):
        return list(findings)
    _log.debug("[Detectors] findings 病态容器归一 []（不构成发现载体）: %r",
               type(findings).__name__)
    return []
def _dict_entries(entries) -> list:
    kept: list = []
    if isinstance(entries, Mapping):
        entries = list(entries.values())
    elif isinstance(entries, (str, bytes)) or not isinstance(entries, Iterable):
        return kept
    for entry in entries or ():
        if isinstance(entry, dict):
            kept.append(entry)
        else:
            _log.debug("[Detectors] 非 dict entry 跳过: %r",
                       type(entry).__name__)
    return kept
def _fill_entry_sentinel(entry: dict, result: dict) -> None:
    entry["result"] = result
    entry["sub_status"] = _sub_status_of(result)
    entry["empty_scan"] = _sub_empty_scan(result)
    entry["findings_count"] = len(_findings_of(result))
_STATUS_ALIASES = {"ok": "pass", "pass": "pass",
                   "fail": "fail", "failed": "fail",
                   "error": "error", "timeout": "error", "blocked": "error",
                   "skip": "skip", "warn": "warn", "warning": "warn"}
def _sub_status_of(result: dict) -> str:
    if not isinstance(result, dict):
        return "error"
    _raw_status = result.get("status")
    st = str("pass" if _raw_status is None else _raw_status).strip().lower()
    mapped = _STATUS_ALIASES.get(st)
    if mapped is not None and _raw_status is not None:
        return mapped
    findings = _findings_of(result)
    if findings:
        if result.get("findings_count") == 0:
            _log.debug("[Detectors] findings_count=0 与实际 findings 矛盾，"
                       "按实际发现数判定 warn: %d", len(findings))
        return "warn"
    n = 0
    _count = result.get("findings_count")
    if _count is None:
        n = len(findings)
    elif isinstance(_count, bool):
        _log.debug("[Detectors] findings_count 为 bool（非合法计数形态），"
                   "回退 findings 列表长度: %r", _count)
        n = len(findings)
    else:
        try:
            n = int(_count or 0)
        except (TypeError, ValueError, OverflowError):
            _log.debug("[Detectors] findings_count 非法，回退 findings 列表长度: %r",
                       _count)
            n = len(findings)
    if n > 0:
        return "warn"
    return "pass" if _raw_status is None else "skip"
_STATUS_ORDER = {"pass": 0, "skip": 1, "warn": 2, "fail": 3, "error": 4}
def _normalized_sub_status(value) -> str | None:
    if not isinstance(value, str):
        return None
    normalized = value.strip().lower()
    return _STATUS_ALIASES.get(normalized, normalized)
def _competitive_worst(entries: list) -> tuple:
    worst = "pass"
    worst_level = _STATUS_ORDER["pass"]
    measured = False
    for entry in entries:
        normalized = _normalized_sub_status(entry.get("sub_status"))
        if normalized is None:
            return "error", _STATUS_ORDER["error"]
        measured = True
        level = _STATUS_ORDER.get(normalized, _STATUS_ORDER["error"])
        if level > worst_level:
            worst_level = level
            worst = normalized if normalized in _STATUS_ORDER else "error"
    if not measured:
        return "error", _STATUS_ORDER["error"]
    return worst, worst_level
def _promote_worst(worst: str, worst_level: int, entries: list,
                   merged: list) -> str:
    if merged:
        return "warn" if worst_level <= _STATUS_ORDER["skip"] else worst
    if worst_level > _STATUS_ORDER["pass"]:
        return worst
    empty_by_unit: dict[tuple, bool] = {}
    for index, entry in enumerate(entries):
        detector = entry.get("detector")
        key = (("detector", detector)
               if isinstance(detector, str) and detector else ("entry", index))
        empty = bool(entry.get("empty_scan"))
        empty_by_unit[key] = empty_by_unit.get(key, True) and empty
    return "warn" if any(empty_by_unit.values()) else worst
def worst_sub_status(det_results: list, merged: list) -> str:
    if isinstance(det_results, (list, tuple)) and any(
            not isinstance(entry, dict) for entry in det_results):
        _log.warning("[Detectors] 子通道结果含非 dict 项，终态按 error 上报")
        return "error"
    entries = _dict_entries(det_results)
    if not entries:
        _log.warning("[Detectors] 子通道结果为空或全部非法，终态按 error 上报")
        return "error"
    worst, worst_level = _competitive_worst(entries)
    return _promote_worst(worst, worst_level, entries, merged)
_VERDICT_REASON_P0 = "{count} 个 P0 阻断项"
_VERDICT_REASON_P1 = "{count} 个 P1 项"
def verdict_from_severity_counts(severity_counts: dict) -> tuple[str, str]:
    """按严重度计数派生诊断结论（verdict），不参与执行健康判定。"""
    if not isinstance(severity_counts, dict):
        return "unknown", ""
    p0 = safe_to_int(severity_counts.get("P0")) or 0
    p1 = safe_to_int(severity_counts.get("P1")) or 0
    if p0 > 0:
        return "fail", _VERDICT_REASON_P0.format(count=p0)
    if p1 > 0:
        return "warn", _VERDICT_REASON_P1.format(count=p1)
    return "pass", ""
def verdict_from_findings(findings: list) -> tuple[str, str]:
    """按 findings 严重度派生诊断结论（P0 → fail，P1 → warn）。"""
    dicts = _dict_entries(findings)
    if not dicts:
        return "pass", ""
    severity_counts = Counter(
        normalize_severity(f.get("severity")) for f in dicts)
    return verdict_from_severity_counts(dict(severity_counts))
def _files_scanned_of(result: dict):
    files_scanned = result.get("files_scanned")
    if files_scanned is not None:
        return files_scanned
    payload = result.get("payload") or {}
    return payload.get("files_scanned") if isinstance(payload, dict) else None
def _scan_failed_status(result: dict) -> bool:
    return str(result.get("status", "ok")).lower() in (
        "fail", "failed", "error", "timeout", "blocked")
def _sub_empty_scan(result: dict) -> bool:
    if not isinstance(result, dict):
        return False
    files_scanned = _files_scanned_of(result)
    if _findings_of(result):
        return False
    if isinstance(files_scanned, bool):
        return _scan_failed_status(result)
    if isinstance(files_scanned, float):
        if math.isfinite(files_scanned):
            return files_scanned <= 0
        return _scan_failed_status(result)
    _count = safe_to_int(files_scanned)
    if _count is not None:
        return _count <= 0
    return _scan_failed_status(result)
def _append_empty_scan_warning(entry: dict, sub_id: str) -> None:
    entry["warnings"] = entry.get("warnings", []) + [
        f"{sub_id} 空扫描（0 文件 0 发现），疑似降级"]
class _UnitCtx(NamedTuple):
    logger: object
    engine_tag: str
    kind_label: str
def _invoke_guarded(entry: dict, unit_id: str, invoke,
                    ctx: _UnitCtx) -> dict:
    t0 = time.perf_counter()
    try:
        result = invoke()
        if isinstance(result, dict):
            _fill_entry_ok(entry, unit_id, result)
        else:
            _mark_unit_failure(
                entry,
                f"{unit_id} 返回非 dict 结果: {type(result).__name__}",
                f"TypeError: {ctx.kind_label} {unit_id} 返回 "
                f"{type(result).__name__}，期望 dict")
            ctx.logger.warning("[%s] %s %s 返回非 dict 结果(%s)，归入哨兵 error",
                               ctx.engine_tag, ctx.kind_label, unit_id,
                               type(result).__name__)
    except CacheNotWarmedError:
        raise
    except Exception as e:
        _mark_unit_failure(entry, f"{unit_id} 异常: {e}",
                           f"{type(e).__name__}: {e}")
        ctx.logger.warning("[%s] %s %s 异常: %s", ctx.engine_tag,
                           ctx.kind_label, unit_id, e, exc_info=True)
    if entry.get("empty_scan"):
        _append_empty_scan_warning(entry, unit_id)
    entry["elapsed_ms"] = round((time.perf_counter() - t0) * 1000, 1)
    return entry
def _sub_family_of(f: dict) -> str:
    family = str(f.get("rule_family") or "").strip()
    return family or finding_rule_id(f) or "diag_general"
def _locator_anchor(f: dict, filepath: str, line: int):
    if line > 0:
        return line
    if filepath:
        return "FILE_LEVEL"
    return str(f.get("key") or "") or "FILE_LEVEL"
def finding_file(raw: Mapping) -> str:
    for key in _FILE_ALIASES:
        value = raw.get(key)
        if not value:
            continue
        text = as_text(value).strip()
        if text:
            return text
    return ""
def _finding_line_candidate(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, str):
        return safe_to_int(value)
    return None
def finding_line(raw: Mapping) -> int:
    for key in _LINE_ALIASES:
        value = raw.get(key)
        if not value:
            continue
        line = _finding_line_candidate(value)
        if line is not None:
            return line
    return 0
def _sub_locator(f: dict) -> tuple:
    filepath = finding_file(f)
    return (filepath, _locator_anchor(f, filepath, finding_line(f)),
            _sub_family_of(f))
_SEVERITY_PREFIX_TIERS = {
    "P0": "high", "P1": "high", "P2": "mid", "P3": "low", "P4": "low",
}
def _severity_signal(sev: str) -> str | None:
    canonical = _canonical_severity(sev)
    if not canonical:
        return None
    return _SEVERITY_PREFIX_TIERS.get(canonical, 'low')
def _verdict_signal(f: dict) -> str:
    load = _severity_signal(_label_text(f.get("severity", "")))
    if load is not None:
        return load
    verdict = _label_text(f.get("verdict", "") or f.get("level", ""))
    if verdict in ("HEALTHY", "PASS", "OK"):
        return "pass"
    if verdict:
        return "warn"
    return "unknown"
class _MergeCtx(NamedTuple):
    source_method: str
    merged_from: str
def _append_unique(items: list, value) -> None:
    if value not in items:
        items.append(value)
def _initial_detectors(raw, sub_id: str) -> list:
    terms = list(raw) if isinstance(raw, (list, tuple, set, frozenset)) else []
    _append_unique(terms, sub_id)
    return terms
def _finding_rule_ids(f: dict) -> list:
    rule_ids = _sequence_items(f.get("rule_ids"))
    rid = finding_rule_id(f)
    if rid:
        _append_unique(rule_ids, rid)
    return rule_ids
def _slot_confidence(value) -> float:
    enum_value = _enum_confidence(value)
    return _safe_conf(value) if enum_value is None else enum_value
def _new_locator_slot(f: dict, sig, sub_id: str,
                      source_method: str, merged_from: str) -> dict:
    base = dict(f)
    canonical_rule_id = finding_rule_id(base)
    if canonical_rule_id:
        base["rule_id"] = canonical_rule_id
    base["detectors"] = _initial_detectors(base.get("detectors"), sub_id)
    base["rule_ids"] = _finding_rule_ids(f)
    _enum_conf = _enum_confidence(base.get("confidence"))
    if _enum_conf is not None:
        base["confidence_label"] = str(base["confidence"])
        base["confidence"] = _enum_conf
    base["_source_method"] = source_method
    base["_merged_from"] = merged_from
    return {
        "finding": base,
        "max_conf": _slot_confidence(f.get("confidence", 0.0) or 0.0),
        "sub_count": 1,
        "sub_ids": {sub_id},
        "signals": {sig},
        "severities": {str(f.get("severity", ""))},
    }
def _absorb_into_slot(slot: dict, f: dict, sig, sub_id: str) -> None:
    if sub_id not in slot["sub_ids"]:
        slot["sub_ids"].add(sub_id)
        slot["sub_count"] += 1
    _append_unique(slot["finding"]["detectors"], sub_id)
    for rid in _finding_rule_ids(f):
        _append_unique(slot["finding"]["rule_ids"], rid)
    current_severity = _canonical_severity(slot["finding"].get("severity"))
    incoming_severity = _canonical_severity(f.get("severity"))
    if incoming_severity and (
            not current_severity
            or int(incoming_severity[1:]) < int(current_severity[1:])):
        slot["finding"]["severity"] = f.get("severity")
    slot["max_conf"] = max(
        slot["max_conf"], _slot_confidence(f.get("confidence", 0.0) or 0.0))
    slot["signals"].add(sig)
    slot["severities"].add(str(f.get("severity", "")))
def _slots_of_entry(by_loc: dict, entry, sub_id: str,
                    mctx: _MergeCtx) -> None:
    if not isinstance(entry, dict):
        _log.debug("[Detectors] 非 dict 子引擎 entry 跳过: %s=%r",
                   sub_id, type(entry).__name__)
        return
    res = entry.get("result") if isinstance(entry.get("result"), dict) else {}
    for f in _findings_of(res):
        if isinstance(f, Mapping):
            _locate_slot(by_loc, dict(f), sub_id, mctx)
def _locate_slot(by_loc: dict, f: dict, sub_id: str,
                 mctx: _MergeCtx) -> None:
    key = _sub_locator(f)
    sig = _verdict_signal(f)
    slot = by_loc.get(key)
    if slot is None:
        by_loc[key] = _new_locator_slot(
            f, sig, sub_id, mctx.source_method, mctx.merged_from)
        return
    _absorb_into_slot(slot, f, sig, sub_id)
def _collect_locator_slots(sub_results: dict, source_method: str,
                           merged_from: str) -> dict:
    by_loc: dict = {}
    mctx = _MergeCtx(source_method, merged_from)
    for sub_id, entry in sub_results.items():
        _slots_of_entry(by_loc, entry, sub_id, mctx)
    return by_loc
def _finalize_merged_slots(by_loc: dict) -> tuple[list, list]:
    merged: list = []
    conflicts: list = []
    for key, slot in by_loc.items():
        f = slot["finding"]
        _apply_consensus_bonus(f, slot)
        conflict = _conflict_of(key, slot)
        if conflict is not None:
            conflicts.append(conflict)
        merged.append(f)
    return merged, conflicts
def _apply_consensus_bonus(f: dict, slot: dict) -> None:
    if slot["sub_count"] < 2:
        current_conf = _slot_confidence(f.get("confidence", 0.0) or 0.0)
        if slot["max_conf"] > current_conf:
            f["confidence"] = round(slot["max_conf"], 3)
        return
    bonus = _mechanism_bonus(f.get("detectors") or ())
    try:
        f["confidence"] = round(min(1.0, slot["max_conf"] + bonus), 3)
        f["_conf_bonus"] = round(bonus, 3)
    except (TypeError, ValueError):
        _log.debug("[Detectors] 组内 confidence 聚合失败，保留原值: max_conf=%r bonus=%r",
                   slot["max_conf"], bonus)
    f["_group_consensus"] = True
def _locator_str(key) -> str:
    return ":".join(str(seg) for seg in key)
def _conflict_of(key, slot: dict) -> dict | None:
    if not (len(slot["signals"]) >= 2 and "high" in slot["signals"]
            and slot["signals"] & {"pass", "low"}):
        return None
    f = slot["finding"]
    f["_conflict"] = True
    f["_conflict_signals"] = sorted(slot["signals"])
    return {
        "locator": _locator_str(key),
        "file": key[0],
        "line": key[1],
        "rule_family": key[2],
        "rule_ids": f["rule_ids"],
        "detectors": f["detectors"],
        "severities": sorted(slot["severities"]),
        "reason": "组内结论方向相悖（高危 vs 正常/低危），交 CV 规则 16 优先处理",
    }
def _link_related_findings(merged: list) -> None:
    by_file: dict = {}
    for f in merged:
        by_file.setdefault(_sub_locator(f)[0], []).append(f)
    for filepath_key, file_findings in by_file.items():
        if _is_linkable_group(filepath_key, file_findings):
            _attach_peer_links(file_findings)
def _is_linkable_group(filepath_key: str, file_findings: list) -> bool:
    return bool(filepath_key) and len(file_findings) >= 2
def _peer_keys(keys: list, index: int) -> list:
    return [k for j, k in enumerate(keys) if j != index]
def _merge_related(existing, peers: list) -> list:
    base = _sequence_items(existing)
    return base + [k for k in peers if k not in base]
def _attach_peer_links(file_findings: list) -> None:
    keys = [_locator_str(_sub_locator(x)) for x in file_findings]
    for i, f in enumerate(file_findings):
        f["related"] = _merge_related(f.get("related"), _peer_keys(keys, i))
def _merge_stats(sub_results: dict, merged: list, conflicts: list,
                 by_loc: dict) -> dict:
    return {
        "raw_findings": sum(
            len(_findings_of(entry.get("result")))
            for entry in _dict_entries(sub_results.values())
        ),
        "merged_findings": len(merged),
        "conflicts": len(conflicts),
        "merged_locators": len(by_loc),
    }
def _merge_sub_findings(sub_results: dict, source_method: str,
                        merged_from: str) -> tuple[list, list, dict]:
    by_loc = _collect_locator_slots(sub_results, source_method, merged_from)
    merged, conflicts = _finalize_merged_slots(by_loc)
    _link_related_findings(merged)
    return merged, conflicts, _merge_stats(sub_results, merged, conflicts, by_loc)
@dataclass(frozen=True)
class DetectorSpec:
    detector_id: str
    engine: str
    mechanism: str
    role: str
    description: str
DETECTOR_SPECS: dict[str, DetectorSpec] = {
    "A1": DetectorSpec("A1", "A", "static-ast", "detector", "五维文件分析"),
    "A2": DetectorSpec("A2", "A", "health-scoring", "detector", "健康评估/可发现性评分"),
    "A3": DetectorSpec("A3", "A", "self-introspection", "sentinel", "静默降级哨兵（自省）"),
    "A4": DetectorSpec("A4", "A", "doc-quality", "detector", "文档质量 DR 族"),
    "B1": DetectorSpec("B1", "B", "static-ast", "detector", "detect_all 12-Phase 统一 AST"),
    "B2": DetectorSpec("B2", "B", "historical", "detector", "历史趋势对比"),
    "C1": DetectorSpec("C1", "C", "runtime-callgraph", "detector", "调用图/盲点/孤儿模块"),
    "D1": DetectorSpec("D1", "D", "security-taint", "detector", "污点/漏洞管线"),
    "D2": DetectorSpec("D2", "D", "symbolic-execution", "detector", "跨文件符号执行"),
    "E1": DetectorSpec("E1", "E", "test-suite", "detector", "pytest/coverage 编排"),
    "E2": DetectorSpec("E2", "E", "mutation", "detector", "变异测试"),
    "F1": DetectorSpec("F1", "F", "fix-plan", "actuator", "待AI修复清单生成"),
    "F2": DetectorSpec("F2", "F", "safeops", "actuator", "安全操作"),
    "F3": DetectorSpec("F3", "F", "gate", "actuator", "交付门禁"),
    "F4": DetectorSpec("F4", "F", "equivalence", "actuator", "修复等价性验证"),
    "F5": DetectorSpec("F5", "F", "refactor", "actuator", "重构执行"),
    "F6": DetectorSpec("F6", "F", "cleanup", "actuator", "代码清理"),
}
def get_detector_spec(detector_id: str) -> DetectorSpec | None:
    return DETECTOR_SPECS.get(str(detector_id))
def mechanisms_of(detector_ids) -> set:
    out = set()
    if isinstance(detector_ids, str):
        detector_ids = (detector_ids,)
    try:
        ids_iter = iter(detector_ids or ())
    except TypeError:
        _log.debug("[Detectors] mechanisms_of 非可迭代输入归一空集: %r",
                   type(detector_ids).__name__)
        return out
    for d in ids_iter:
        spec = DETECTOR_SPECS.get(str(d))
        if spec is not None:
            out.add(spec.mechanism)
    return out
def _needs_detector_tag(f) -> bool:
    return (isinstance(f, dict)
            and not f.get("detectors") and not f.get("sub_engines"))
def _fill_entry_ok(entry: dict, detector_id: str, result: dict) -> None:
    for f in _findings_of(result):
        if _needs_detector_tag(f):
            f["detectors"] = [detector_id]
    _fill_entry_sentinel(entry, result)
def _mark_unit_failure(entry: dict, summary: str, error: str) -> None:
    entry["sub_status"] = "error"
    entry["empty_scan"] = True
    entry["findings_count"] = 0
    entry["error"] = error
    entry["result"] = {"status": "error", "findings": [], "summary": summary}
def _resolve_detector_call(detector_id: str, report, fn_kwargs: dict | None):
    extra = dict(fn_kwargs) if fn_kwargs else {}
    resolved = extra.pop("report", report)
    uses_report = detector_id in _REPORT_CONSUMING_SUBS and resolved is not None
    return extra, resolved, uses_report
def detector_entry(detector_id: str, fn, skill_dir: str, cache, *,
                    logger, engine_tag: str, report=None,
                    fn_kwargs: dict | None = None) -> dict:
    spec = DETECTOR_SPECS.get(str(detector_id))
    src_method = (spec.engine if spec is not None
                  else (engine_tag[-1].upper() if engine_tag else ""))
    entry = {"detector": detector_id, "source_method": src_method}
    def _invoke():
        extra, report_value, uses_report = _resolve_detector_call(
            detector_id, report, fn_kwargs)
        if uses_report:
            return fn(skill_dir, cache, report=report_value, **extra)
        return fn(skill_dir, cache, **extra)
    return _invoke_guarded(entry, detector_id, _invoke,
                           _UnitCtx(logger, engine_tag, "检测器"))
def _named_entries(det_results: list) -> list[dict]:
    named: list[dict] = []
    for entry in _dict_entries(det_results):
        det_id = entry.get("detector")
        if not isinstance(det_id, str) or not det_id:
            _log.debug("[Detectors] 聚合 entry 的 detector 键缺失或非 str: "
                       "keys=%r det=%r", sorted(entry.keys()),
                       type(det_id).__name__)
            continue
        named.append(entry)
    return named
def detector_entry_map(det_results: list) -> dict:
    merged: dict = {}
    for entry in _named_entries(det_results):
        det_id = entry["detector"]
        prev = merged.get(det_id)
        merged[det_id] = (entry if prev is None
                          else _merge_duplicate_entry(prev, entry))
    return merged
def _merge_duplicate_entry(prev: dict, new: dict) -> dict:
    merged = {key: value for key, value in prev.items() if key != "result"}
    for key, value in new.items():
        if key != "result":
            merged[key] = value
    prev_result = prev.get("result")
    new_result = new.get("result")
    merged["result"] = _merge_result_pair(
        prev_result if isinstance(prev_result, dict) else {},
        new_result if isinstance(new_result, dict) else {})
    merged["findings_count"] = len(_findings_of(merged["result"]))
    merged["sub_status"] = _sub_status_of(merged["result"])
    merged["empty_scan"] = (
        _sub_empty_scan(prev_result if isinstance(prev_result, dict) else {})
        and _sub_empty_scan(new_result if isinstance(new_result, dict) else {})
    )
    merged["warnings"] = (_sequence_items(prev.get("warnings"))
                           + _sequence_items(new.get("warnings")))
    return merged
def _entry_view(entry: dict) -> dict:
    result = entry.get("result")
    return {
        "sub_status": entry.get("sub_status", "error"),
        "empty_scan": entry.get("empty_scan", False),
        "findings_count": entry.get("findings_count", 0),
        "elapsed_ms": entry.get("elapsed_ms", 0),
        "warnings": entry.get("warnings", []),
        "error": entry.get("error"),
        "summary": (result.get("summary", "")
                    if isinstance(result, dict) else ""),
        "result": result,
    }
def detector_view_payload(det_results: list) -> dict:
    return {det_id: _entry_view(entry)
            for det_id, entry in detector_entry_map(det_results).items()}
def group_payload(engine: str, detector_ids: tuple,
                  detector_payload: dict, stats: dict) -> dict:
    return {
        "engine": engine,
        "sub_engines": detector_ids,
        "detectors": detector_ids,
        "sub_results": detector_payload,
        "detector_results": detector_payload,
        "stats": stats,
    }
def _degrade_reasons(det_results: list) -> str:
    """聚合非 pass 子检测器的摘要，保证引擎级 warn/error 可追溯。

    findings 为空时引擎状态仍可能是 warn（子通道降级但无可修项）。若不把
    降级通道写进摘要，报告只剩「warn + 0 发现」而无法解释。
    """
    parts: list[str] = []
    for entry in _dict_entries(det_results):
        status = _normalized_sub_status(entry.get("sub_status"))
        if status in (None, "pass", "skip"):
            continue
        det_id = str(entry.get("detector") or "").strip()
        result = entry.get("result")
        summary = (str(result.get("summary") or "").strip()
                   if isinstance(result, dict) else "")
        if not summary:
            warnings = entry.get("warnings")
            if isinstance(warnings, (list, tuple)) and warnings:
                summary = str(warnings[0]).strip()
        if not summary:
            continue
        parts.append(f"{det_id}({status}): {summary}" if det_id
                     else f"({status}): {summary}")
    return "；".join(parts)
def group_envelope(engine: str, detector_ids: tuple, status: str,
                   findings: list, stats: dict, det_results: list,
                   t0: float, *, summary: str,
                   conflicts=None, error: str | None = None,
                   verdict: str | None = None,
                   verdict_reason: str = "") -> dict:
    entry_map = detector_entry_map(det_results)
    detector_payload = {det_id: _entry_view(entry)
                        for det_id, entry in entry_map.items()}
    payload = group_payload(engine, detector_ids, detector_payload, stats)
    if verdict is None:
        # 执行异常/跳过的组没有可信结论，不得报 pass；fail 是诊断结论
        # 失败而非执行异常，其余正常完成的组按 findings 严重度派生。
        normalized_status = str(status).strip().lower()
        legacy_fail = normalized_status in ("fail", "failed")
        if normalized_status in ("error", "timeout", "blocked", "skip"):
            verdict = "unknown"
        else:
            _derived_verdict, _derived_reason = verdict_from_findings(
                findings)
            verdict = "fail" if legacy_fail else _derived_verdict
            if not verdict_reason:
                verdict_reason = _derived_reason
            if legacy_fail and not verdict_reason:
                verdict_reason = "诊断结论未通过"
    _summary = summary
    if (not findings
            and str(status).strip().lower() in ("warn", "fail", "failed")):
        _reasons = _degrade_reasons(det_results)
        if _reasons:
            _summary = f"{summary}｜降级原因: {_reasons}"
    envelope = {
        "status": status,
        "engine": engine,
        "verdict": verdict,
        "verdict_reason": verdict_reason,
        "findings_count": len(findings),
        "summary": _summary,
        "findings": findings,
        "payload": payload,
        "sub_results": entry_map,
        "detector_results": entry_map,
        "conflicts": conflicts if conflicts is not None else [],
        "stats": stats,
        "elapsed_ms": round((time.perf_counter() - t0) * 1000, 1),
    }
    if error is not None:
        envelope["error"] = error
    return envelope
def _detector_entries_to_sub_results(det_results: list) -> dict:
    return {
        det_id: {
            "result": (entry.get("result")
                       if isinstance(entry.get("result"), dict) else {})
        }
        for det_id, entry in detector_entry_map(det_results).items()
    }
def _scan_count_or_none(value: Any) -> int | float | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return value if math.isfinite(value) else None
    return safe_to_int(value)
def _preserve_positive_scan_count(combined: dict, prev: dict, res: dict) -> None:
    prev_value = _files_scanned_of(prev)
    new_value = _files_scanned_of(res)
    prev_count = _scan_count_or_none(prev_value)
    new_count = _scan_count_or_none(new_value)
    if (prev_count is not None and prev_count > 0
            and (new_count is None or new_count <= 0)):
        combined["files_scanned"] = prev_value
def _merge_result_pair(prev: dict, res: dict) -> dict:
    combined = dict(prev)
    combined.update(res)
    combined["findings"] = _findings_of(prev) + _findings_of(res)
    combined["findings_count"] = len(combined["findings"])
    _preserve_positive_scan_count(combined, prev, res)
    _preserve_worst_duplicate_status(combined, prev, res)
    return combined
def _preserve_worst_duplicate_status(combined: dict, prev: dict,
                                     res: dict) -> None:
    prev_status = _sub_status_of(prev)
    new_status = _sub_status_of(res)
    if _STATUS_ORDER[prev_status] <= _STATUS_ORDER[new_status]:
        return
    combined["status"] = prev.get("status", prev_status)
    for key in ("summary", "error"):
        if prev.get(key):
            combined[key] = prev[key]
def consolidate_findings(det_results: list, source_method: str,
                          merged_from: str) -> tuple[list, list, dict]:
    sub_results = _detector_entries_to_sub_results(det_results)
    merged, conflicts, stats = _merge_sub_findings(sub_results, source_method, merged_from)
    for f in merged:
        f["_mechanisms"] = sorted(mechanisms_of(f.get("detectors") or ()))
    stats["detector_count"] = len(sub_results)
    stats["mechanisms"] = sorted(mechanisms_of(sub_results.keys()))
    return merged, conflicts, stats
def _mechanism_bonus(detectors) -> float:
    mech = mechanisms_of(detectors)
    if len(mech) < 2:
        return 0.0
    return min(_CONF_BONUS_PER_SUB * (len(mech) - 1), _CONF_BONUS_CAP)
_CONF_ENUM_MAP = {
    "confirmed": 0.9,
    "potential_false_positive": 0.4,
    "external_api": 0.3,
}
def _enum_confidence(value: Any) -> float | None:
    if not isinstance(value, str):
        return None
    return _CONF_ENUM_MAP.get(value.strip().lower())
def _confidence_pair(value: Any) -> tuple[float, str | None]:
    numeric = _enum_confidence(value)
    if numeric is None:
        return safe_confidence(value), None
    return numeric, str(value)
def _normalize_finding_conf(f: dict) -> None:
    numeric, label = _confidence_pair(f.get("confidence"))
    if label is None:
        return
    f["confidence_label"] = label
    f["confidence"] = numeric
def normalize_conf_enum(result: Any) -> Any:
    if not isinstance(result, dict):
        return result
    for f in _findings_of(result):
        if isinstance(f, dict):
            _normalize_finding_conf(f)
    return result
def _finding_suppress_keys(finding: dict) -> list:
    keys: list = []
    for value in (finding.get("type"), finding.get("check"),
                  finding_rule_id(finding)):
        if isinstance(value, str) and value and value not in keys:
            keys.append(value)
    for field_name in ("rule_ids", "suppress_aliases"):
        for value in _sequence_items(finding.get(field_name)):
            _text = str(value)
            if value and _text not in keys:
                keys.append(_text)
    return keys
def _suppression_hit(finding: dict, skill_dir: str,
                     cache: dict) -> str | None:
    filepath = finding_file(finding)
    lineno = finding_line(finding) if filepath else 0
    if not filepath or lineno <= 0:
        return None
    path = filepath if os.path.isabs(filepath) else os.path.join(
        skill_dir, filepath)
    suppressions = cache.get(path)
    if suppressions is None:
        source = read_source(path)
        if source is None:
            _log.debug("抑制文件不可读，按无抑制处理: %s", path)
            suppressions = {}
        else:
            suppressions = parse_suppressions(source)
        cache[path] = suppressions
    if not suppressions:
        return None
    return next((key for key in _finding_suppress_keys(finding)
                 if is_suppressed(suppressions, lineno, key)), None)
def apply_inline_suppressions(findings: list, skill_dir: str) -> tuple:
    kept: list = []
    dropped: dict = {}
    cache: dict = {}
    for finding in findings:
        if not isinstance(finding, Mapping):
            kept.append(finding)
            continue
        _hit = _suppression_hit(finding, skill_dir, cache)
        if _hit is None:
            kept.append(finding)
        else:
            dropped[_hit] = dropped.get(_hit, 0) + 1
    return kept, dropped
def _pollution_item_issue(item: Any) -> dict:
    data = _extract_finding_mapping(item) or {"description": str(item)}
    rule_id = _extract_rule_id(data, "POL-01")
    return {
        "rule_id": rule_id,
        "message": _extract_message(data) or "代码污染检出",
        "line": finding_line(data),
        "severity": apply_fp_downgrade(
            rule_id, data.get("severity") or "P2"),
        "category": "pollution",
    }
def project_pollution_issues(report: Any) -> list:
    if not hasattr(report, "is_clean") or report.is_clean:
        return []
    items = _issue_container_items(getattr(report, "issues", None))
    if not items:
        return [{
            "rule_id": "POL-01",
            "message": (
                "代码污染检出: "
                f"score={getattr(report, 'pollution_score', 0)}"),
            "severity": apply_fp_downgrade(
                "POL-01",
                "P0" if getattr(report, "is_critical", False) else "P2"),
            "category": "pollution",
        }]
    return [_pollution_item_issue(item) for item in items]

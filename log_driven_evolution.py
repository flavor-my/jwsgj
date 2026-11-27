from __future__ import annotations

import copy
import hashlib
import json
import os
import re
import time
from collections import Counter, defaultdict
from collections.abc import Callable, Mapping
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from typing import Any, ClassVar, NamedTuple

from jwsgj.diag_detectors_registry import get_registry as get_detector_registry
from jwsgj.diag_log_coverage import audit_log_coverage
from jwsgj.diag_shared_source_core import (
    count_lines,
    read_source_with_fingerprint,
)
from jwsgj.diag_types_normalize import (
    as_dict,
    as_list,
    as_number,
    as_sequence,
    as_str,
    norm_dict_list,
    now_iso,
    safe_float,
    signal_bool,
)
from jwsgj.log_analysis import (
    DEFAULT_MAX_LOG_ENTRIES,
    analyze_log_patterns,
    analyze_perf_bottlenecks,
    check_log_quality,
    detect_phase_degradation,
    is_delete_event,
    is_high_risk_audit_event,
    is_production_audit_target,
    is_rollback_event,
    load_audit_events,
    load_bug_intercepts,
    load_json_logs,
    load_perf_traces,
    load_swallowed_exceptions,
    normalize_group_key,
    parse_duration_ms,
    phase_of,
    register_resolution,
)
from jwsgj.log_config import (
    get_module_logger,
    get_skill_root,
    log_swallowed,
    now_iso_seconds,
    parse_log_ts,
    write_module_run,
)
from jwsgj.runtime_paths import (
    evolution_state_path,
    read_evolution_section,
    update_evolution_section,
)
from jwsgj.runtime_scope import (
    SCAN_COLLECT_PRUNE_DIRS_LOWER,
    prune_scan_dirnames,
)
from jwsgj.xv_intermediate_store import peek_round_start_ts

_DEFAULT_RULE_SEVERITY = "medium"
_DEFAULT_P_SEVERITY = "P2"
_UNKNOWN_TEXT = "unknown"
_SEVERITY_ALIASES: dict[str, str] = {
    "p0": "critical",
    "p1": "high",
    "p2": "medium",
    "p3": "low",
}
__all__ = [
    'ClosureManager',
    'FindingGenerator',
    'GrowthMonitor',
    'LogFinding',
    'PatternExtractor',
    'extract_rule_candidates',
    'load_audit_summary',
    'load_bug_intercept_summary',
    'load_growth_summary',
    'load_log_quality_summary',
    'load_perf_summary',
    'load_swallowed_summary',
    'register_rule_candidates',
    'run_log_driven_evolution',
]
logger = get_module_logger(__name__, __file__)
_SKILL_ROOT = get_skill_root()
_DEFAULT_CONSUMER_ID = 'rule_evolver_v1'
def _as_count_or(value: Any) -> int | float:
    number = safe_float(value, None)
    if number is None or number < 0:
        return 0
    return int(number) if number.is_integer() else number
@dataclass
class LogFinding:
    finding_id: str = ""
    finding_type: str = ""
    severity: str = ""
    title: str = ""
    description: str = ""
    suggested_action: str = ""
    source: str = ""
    log_evidence: list[dict] = field(default_factory=list)
    pattern_data: dict[str, Any] = field(default_factory=dict)
    status: str = "open"
    created_at: str = ""
    resolved_at: str = ""
    resolution: str = ""
    def __post_init__(self) -> None:
        if not isinstance(self.log_evidence, list):
            self.log_evidence = (list(self.log_evidence)
                                 if isinstance(self.log_evidence,
                                               (tuple, set, frozenset))
                                 else [])
        if not isinstance(self.pattern_data, dict):
            self.pattern_data = (dict(self.pattern_data)
                                 if isinstance(self.pattern_data, Mapping)
                                 else {})
    def to_dict(self) -> dict:
        return {
            "finding_id": self.finding_id,
            "finding_type": self.finding_type,
            "severity": self.severity,
            "title": self.title,
            "description": self.description,
            "suggested_action": self.suggested_action,
            "source": self.source,
            "log_evidence": copy.deepcopy(self.log_evidence[:5]),
            "pattern_data": copy.deepcopy(self.pattern_data),
            "status": self.status,
            "created_at": self.created_at,
            "resolved_at": self.resolved_at,
            "resolution": self.resolution,
        }
_ZERO_BASELINE_DEGRADATION_RATIO = 100000.0
_LOG_QUALITY_RISK_THRESHOLD = 70.0
_UNMEASURED_METRIC = -1.0
class _PerfTrend(NamedTuple):
    recent_avg: float
    historical_avg: float
    ratio: float
def _perf_samples_by_phase(
    traces: list[dict[str, Any]],
) -> dict[str, list[tuple[dict[str, Any], float, datetime | None]]]:
    by_phase: dict[
        str, list[tuple[dict[str, Any], float, datetime | None]]] = defaultdict(
            list)
    for entry in traces:
        if not isinstance(entry, dict):
            continue
        duration = parse_duration_ms(
            entry.get("duration_ms"), label="log_driven_evolution")
        if duration is None:
            continue
        raw_ts = entry.get("ts")
        ts_dt = (parse_log_ts(raw_ts)
                 if isinstance(raw_ts, str) and raw_ts else None)
        by_phase[phase_of(entry, fallback_event=True)].append(
            (entry, duration, ts_dt))
    for samples in by_phase.values():
        samples.sort(key=lambda item: (
            item[2] is not None, item[2] or datetime.min))
    return by_phase
def _phase_durations(
    traces: list[dict[str, Any]],
) -> dict[str, list[float]]:
    return {phase: [duration for _entry, duration, _ts_dt in samples]
            for phase, samples in _perf_samples_by_phase(traces).items()}
def _timestamp_strings(entries: list[dict[str, Any]],
                       limit: int) -> list[str]:
    out: list[str] = []
    for entry in entries:
        ts = entry.get("ts")
        if isinstance(ts, str) and ts:
            out.append(ts)
            if len(out) >= limit:
                break
    return out
def _payload_dict(entry: dict[str, Any]) -> dict[str, Any]:
    payload = entry.get("payload")
    return payload if isinstance(payload, dict) else {}
def _audit_payload_failed(entry: dict[str, Any]) -> bool:
    payload = _payload_dict(entry)
    if "ok" not in payload:
        return False
    ok = payload["ok"]
    if isinstance(ok, str) and ok.strip().lower() == "failed":
        return True
    return not signal_bool(ok)
def _event_text(entry: dict[str, Any]) -> str:
    return str(entry.get("event", ""))
def _log_level(entry: dict[str, Any]) -> str:
    level = entry.get("level")
    return level.strip().upper() if isinstance(level, str) else ""
def _is_rollback_audit(entry: dict[str, Any]) -> bool:
    if not is_rollback_event(_event_text(entry)):
        return False
    if _audit_payload_failed(entry):
        return False
    return is_production_audit_target(entry)
def _is_delete_audit(entry: dict[str, Any]) -> bool:
    if not is_delete_event(_event_text(entry)):
        return False
    if _audit_payload_failed(entry):
        return False
    return is_production_audit_target(entry)
_FIX_DOMAIN_TOKEN_RE = re.compile(
    r"(?:^|_)(?:ai_|hot_?)?fix(?:er|ing|ed)?(?=_|$)")
_FAILURE_TOKEN_RE = re.compile(r"(?:^|_)fail(?:ed|ure|s)?(?=_|$)")
def _is_fix_failure_audit(entry: dict[str, Any]) -> bool:
    text = _event_text(entry).lower()
    if not (_FIX_DOMAIN_TOKEN_RE.search(text)
            and _FAILURE_TOKEN_RE.search(text)):
        return False
    return is_production_audit_target(entry)
_AUDIT_ANOMALY_SPECS: tuple[
    tuple[str, Callable[[dict[str, Any]], bool], str, bool, str, str], ...] = (
    ("frequent_rollback", _is_rollback_audit,
     "检测到 {n} 次回滚操作，修复安全性可能存在系统性缺陷", True,
     "审查修复器安全性，检查修复验证逻辑，考虑降低 auto_safe 标签或增强安全验证",
     "审计异常: 频繁回滚 x{count}"),
    ("frequent_delete", _is_delete_audit,
     "检测到 {n} 次删除操作，清理逻辑可能过于激进", False,
     "审查清理逻辑保守性，检查白名单和置信度过滤，防止过度清理",
     "审计异常: 频繁删除 x{count}"),
    ("fix_failure_sequence", _is_fix_failure_audit,
     "检测到 {n} 次修复失败审计事件，修复器能力可能不足", False,
     "审查修复器覆盖范围和能力，检查修复器匹配逻辑，开发缺失的修复器",
     "审计异常: 修复失败序列 x{count}"),
)
_DEFAULT_AUDIT_VIEW: tuple[str, str] = (
    "审查审计事件序列，定位高危操作根因",
    "审计异常: {anomaly_type} x{count}")
def _audit_view(anomaly_type: str) -> tuple[str, str]:
    for spec in _AUDIT_ANOMALY_SPECS:
        if spec[0] == anomaly_type:
            return (spec[4], spec[5])
    return _DEFAULT_AUDIT_VIEW
class PatternExtractor:
    REPEAT_WINDOW_MINUTES = 30
    REPEAT_THRESHOLD = 3
    AUDIT_ANOMALY_THRESHOLD = 3
    SWALLOW_THRESHOLD = 2
    _PHASE_SPECS: ClassVar[dict[str, tuple[str, tuple[str, ...], str]]] = {
        "diagnosis": ("诊断阶段", ("诊断",), "high"),
        "cv": ("交叉验证阶段", ("交叉验证",), "high"),
        "treatment": ("治疗阶段", ("治疗",), "medium"),
        "review": ("复盘阶段", ("复盘",), "medium"),
        "feedback": ("反哺阶段", ("反哺",), "low"),
        "fupan": ("复盘引擎阶段", ("复盘引擎",), "medium"),
    }
    @staticmethod
    def phase_severity(phase: Any) -> str:
        spec = PatternExtractor._PHASE_SPECS.get(str(phase))
        return spec[2] if spec is not None else "low"
    def extract_all(self, log_data: dict[str, list[dict[str, Any]]]) -> list[dict[str, Any]]:
        if not isinstance(log_data, dict):
            log_data = {}
        json_logs = norm_dict_list(log_data.get("json_logs"))
        perf_traces = norm_dict_list(log_data.get("perf_traces"))
        audit_events = norm_dict_list(log_data.get("audit_events"))
        swallowed = norm_dict_list(
            log_data.get("swallowed_exceptions"))
        patterns: list[dict[str, Any]] = []
        patterns.extend(self._extract_repeated_exceptions(json_logs))
        patterns.extend(self._extract_perf_degradation(perf_traces))
        patterns.extend(self._extract_audit_anomalies(audit_events))
        patterns.extend(self._extract_silent_swallow(swallowed))
        patterns.extend(self._extract_log_gaps(json_logs))
        return patterns
    def _extract_repeated_exceptions(self, json_logs: list[dict[str, Any]]) -> list[dict[str, Any]]:
        patterns: list[dict[str, Any]] = []
        if not json_logs:
            return patterns
        for group_key, entries in self._group_error_logs(json_logs).items():
            if len(entries) < self.REPEAT_THRESHOLD:
                continue
            window = self._analyze_repeat_window(entries)
            logger_name, level, msg_prefix = group_key
            count = window["count"]
            window_minutes = window["window_minutes"]
            ts_reliable = bool(window.get("timestamps_parseable"))
            within_window = bool(window.get("within_window"))
            patterns.append({
                "pattern_type": "repeated_exception",
                "logger": logger_name,
                "level": level,
                "message_prefix": msg_prefix,
                "count": count,
                "window_minutes": round(window_minutes, 1),
                "first_seen": window["first_seen"],
                "last_seen": window["last_seen"],
                "timestamps_parseable": ts_reliable,
                "within_window": within_window,
                "sample_entries": window["sample_entries"],
                "description": self._repeat_description(
                    logger_name, level, count, window_minutes,
                    ts_reliable, within_window),
            })
        return patterns
    @staticmethod
    def _repeat_description(logger_name: str, level: str, count: Any,
                            window_minutes: float, ts_reliable: bool,
                            within_window: bool) -> str:
        if ts_reliable and within_window:
            return (f"模块 {logger_name} 在 {window_minutes:.0f} 分钟内重复出现"
                    f" {level} 级别异常 {count} 次")
        if ts_reliable:
            return (f"模块 {logger_name} 在 {window_minutes:.0f} 分钟内分散出现"
                    f" {level} 级别异常 {count} 次"
                    f"（无 {PatternExtractor.REPEAT_WINDOW_MINUTES} 分钟密集窗口）")
        return (f"模块 {logger_name} 重复出现 {level} 级别异常 {count} 次"
                "（时间戳不足，无法计算窗口）")
    @staticmethod
    def _normalize_message_key(message: str) -> str:
        msg_key = message if message else "empty"
        msg_key = re.sub(r'\d+', 'N', msg_key)
        msg_key = re.sub(r'[A-Za-z]:(?=[/\\])', 'DRV', msg_key)
        msg_key = re.sub(r'(?:[/\\][^\s/\\]+){2,}', '/PATH', msg_key)
        msg_key = re.sub(r'[/\\][^\s/\\]+', '/path', msg_key)
        return msg_key[:80]
    @staticmethod
    def _densest_window_within(ordered: list[tuple], window_seconds: float,
                               ) -> list[tuple]:
        in_window: list[tuple] = []
        left = 0
        for right in range(len(ordered)):
            while ((ordered[right][2] - ordered[left][2])
                    .total_seconds() > window_seconds):
                left += 1
            if right - left + 1 > len(in_window):
                in_window = ordered[left:right + 1]
        return in_window
    def _group_error_logs(self, json_logs: list[dict[str, Any]],
                          ) -> dict[tuple[str, str, str], list[dict[str, Any]]]:
        error_logs = [
            entry for entry in json_logs
            if _log_level(entry) in ("WARNING", "ERROR", "CRITICAL")
        ]
        groups: dict[tuple[str, str, str], list[dict[str, Any]]] = defaultdict(list)
        for entry in error_logs:
            logger_name = normalize_group_key(entry.get("logger") or "unknown")
            message = entry.get("message", "")
            if not isinstance(message, str):
                continue
            groups[(logger_name, _log_level(entry),
                    self._normalize_message_key(message))].append(entry)
        return groups
    def _parse_window_entries(
        self, entries: list[dict[str, Any]],
    ) -> tuple[list[tuple[dict[str, Any], str, datetime | None]],
               list[tuple[dict[str, Any], str, datetime]]]:
        parsed: list[tuple[dict[str, Any], str, datetime | None]] = []
        for entry in entries:
            ts = entry.get("ts", "")
            if isinstance(ts, str) and ts:
                parsed.append((entry, ts, parse_log_ts(ts)))
        parseable = [item for item in parsed if item[2] is not None]
        return parsed, parseable
    def _window_stats(
        self,
        parsed: list[tuple[dict[str, Any], str, datetime | None]],
        parseable: list[tuple[dict[str, Any], str, datetime]],
        total_entries: int,
    ) -> dict[str, Any]:
        if len(parseable) >= self.REPEAT_THRESHOLD:
            ordered = sorted(parseable, key=lambda item: item[2])
            in_window = self._densest_window_within(
                ordered, self.REPEAT_WINDOW_MINUTES * 60.0)
            if len(in_window) >= self.REPEAT_THRESHOLD:
                window_minutes = (
                    in_window[-1][2] - in_window[0][2]).total_seconds() / 60.0
                return {
                    "count": len(in_window),
                    "window_minutes": window_minutes,
                    "timestamps_parseable": True,
                    "within_window": True,
                    "sample_entries": [entry for entry, _ts, _dt
                                       in in_window[:5]],
                    "first_seen": in_window[0][1],
                    "last_seen": in_window[-1][1],
                }
        return self._spread_window_stats(parsed, parseable, total_entries)
    def _spread_window_stats(
        self,
        parsed: list[tuple[dict[str, Any], str, datetime | None]],
        parseable: list[tuple[dict[str, Any], str, datetime]],
        total_entries: int,
    ) -> dict[str, Any]:
        first_seen, last_seen = self._first_last_seen(parsed, parseable)
        span_minutes = 0.0
        if len(parseable) >= 2:
            span_minutes = (
                max(item[2] for item in parseable)
                - min(item[2] for item in parseable)).total_seconds() / 60.0
        return {
            "count": total_entries,
            "window_minutes": span_minutes,
            "timestamps_parseable": len(parseable) >= self.REPEAT_THRESHOLD,
            "within_window": False,
            "sample_entries": [entry for entry, _ts, _dt in parsed[:5]],
            "first_seen": first_seen,
            "last_seen": last_seen,
        }
    @staticmethod
    def _first_last_seen(
        parsed: list[tuple[dict[str, Any], str, datetime | None]],
        parseable: list[tuple[dict[str, Any], str, datetime]],
    ) -> tuple[str, str]:
        if parseable:
            return (min(parseable, key=lambda item: item[2])[1],
                    max(parseable, key=lambda item: item[2])[1])
        if not parsed:
            return ("", "")
        return (min(ts for _entry, ts, _dt in parsed),
                max(ts for _entry, ts, _dt in parsed))
    def _analyze_repeat_window(self, entries: list[dict[str, Any]],
                               ) -> dict[str, Any]:
        parsed, parseable = self._parse_window_entries(entries)
        if not parsed:
            return {
                "count": len(entries),
                "window_minutes": 0.0,
                "timestamps_parseable": False,
                "within_window": False,
                "sample_entries": entries[:5],
                "first_seen": "",
                "last_seen": "",
            }
        return self._window_stats(parsed, parseable, len(entries))
    def _extract_perf_degradation(self, perf_traces: list[dict[str, Any]]) -> list[dict[str, Any]]:
        patterns: list[dict[str, Any]] = []
        for phase, samples in _perf_samples_by_phase(perf_traces).items():
            finding = self._classify_phase_degradation(phase, samples)
            if finding is not None:
                patterns.append(finding)
        return patterns
    def _classify_phase_degradation(self, phase: str, durations: list[tuple],
                                    ) -> dict[str, Any] | None:
        degradation = detect_phase_degradation(
            [duration for _entry, duration, _ts in durations])
        if not degradation:
            return None
        recent_avg = as_number(degradation.get("recent_ms"), 0.0)
        historical_avg = as_number(
            degradation.get("historical_avg_ms"), 0.0)
        ratio = (recent_avg / historical_avg if historical_avg > 0
                 else _ZERO_BASELINE_DEGRADATION_RATIO)
        if historical_avg <= 0:
            description = (
                f"阶段 {phase} 耗时从 0ms 激增到 {recent_avg:.0f}ms"
                "（零基线质变，倍率数学无界取哨兵值）")
        else:
            description = (
                f"阶段 {phase} 耗时从 {historical_avg:.0f}ms 退化到 "
                f"{recent_avg:.0f}ms (增长 {ratio - 1:.0%})")
        return self._perf_degradation_pattern(
            phase, _PerfTrend(recent_avg, historical_avg, ratio),
            durations, description)
    @staticmethod
    def _perf_degradation_pattern(phase: str, trend: _PerfTrend,
                                  durations: list[tuple],
                                  description: str) -> dict[str, Any]:
        zero_baseline = trend.historical_avg <= 0
        return {
            "pattern_type": "perf_degradation",
            "phase": phase,
            "recent_avg_ms": round(trend.recent_avg, 1),
            "historical_avg_ms": round(trend.historical_avg, 1),
            "degradation_ratio": (None if zero_baseline
                                  else round(trend.ratio, 2)),
            "zero_baseline": zero_baseline,
            "sample_count": len(durations),
            "last_entry": durations[-1][0],
            "description": description,
        }
    def _audit_anomaly_pattern(
        self, audit_events: list[dict[str, Any]], anomaly_type: str,
        predicate: Callable[[dict[str, Any]], bool],
        description_tpl: str, with_timestamps: bool,
    ) -> dict[str, Any] | None:
        matched = [e for e in audit_events if predicate(e)]
        if len(matched) < self.AUDIT_ANOMALY_THRESHOLD:
            return None
        pattern: dict[str, Any] = {
            "pattern_type": "audit_anomaly",
            "anomaly_type": anomaly_type,
            "count": len(matched),
        }
        if with_timestamps:
            pattern["timestamps"] = _timestamp_strings(matched[-10:], limit=10)
        pattern["sample_entries"] = matched[-5:]
        pattern["description"] = description_tpl.format(n=len(matched))
        return pattern
    def _extract_audit_anomalies(self, audit_events: list[dict[str, Any]]) -> list[dict[str, Any]]:
        if not audit_events:
            return []
        patterns: list[dict[str, Any]] = []
        for spec in _AUDIT_ANOMALY_SPECS:
            pattern = self._audit_anomaly_pattern(audit_events, *spec[:4])
            if pattern is not None:
                patterns.append(pattern)
        return patterns
    def _exc_type_distribution(self, entries: list[dict[str, Any]]) -> Counter:
        exc_types = Counter()
        for e in entries:
            exc_type = normalize_group_key(_payload_dict(e).get("exc_type"))
            exc_types[exc_type] += 1
        return exc_types
    def _extract_silent_swallow(self, swallowed: list[dict[str, Any]]) -> list[dict[str, Any]]:
        patterns: list[dict[str, Any]] = []
        if not swallowed:
            return patterns
        by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)
        for entry in swallowed:
            module = normalize_group_key(
                _payload_dict(entry).get("module")
                or entry.get("logger") or "unknown")
            by_module[module].append(entry)
        for module, entries in by_module.items():
            if len(entries) >= self.SWALLOW_THRESHOLD:
                exc_types = self._exc_type_distribution(entries)
                patterns.append({
                    "pattern_type": "silent_swallow",
                    "module": module,
                    "count": len(entries),
                    "exc_type_distribution": dict(exc_types.most_common(5)),
                    "sample_entries": entries[-5:],
                    "description": f"模块 {module} 有 {len(entries)} 个静默吞没的异常（类型: {dict(exc_types.most_common(3))}）",
                })
        return patterns
    @staticmethod
    def _phase_tokens_of(phase: Any) -> frozenset[str]:
        if not isinstance(phase, str) or not phase:
            return frozenset()
        return frozenset(
            t for t in re.split(r"[^a-z0-9]+", phase.lower()) if t)
    @staticmethod
    def _marker_spans(
        expected_phases: dict[str, tuple[str, tuple[str, ...], str]],
    ) -> tuple[tuple[int, str, str], ...]:
        return tuple(sorted(
            ((len(marker), phase, marker)
             for phase, (_desc, markers, _sev) in expected_phases.items()
             for marker in markers if marker),
            key=lambda item: (-item[0], item[2])))
    @staticmethod
    def _marker_hits(text: str,
                     spans: tuple[tuple[int, str, str], ...]) -> set[str]:
        remaining = text
        hits: set[str] = set()
        for _size, phase, marker in spans:
            if marker in remaining:
                hits.add(phase)
                remaining = remaining.replace(marker, " ")
        return hits
    def _entry_seen_phases(self, phase: Any, message: Any,
                           expected_phases: dict[str, tuple[str, tuple[str, ...], str]],
                           marker_spans: tuple[tuple[int, str, str], ...],
                           ) -> set[str]:
        phase_tokens = self._phase_tokens_of(phase)
        if "pending" in phase_tokens:
            phase_tokens = frozenset()
            text = str(message).lower()
        else:
            text = f"{message} {phase}".lower()
        text_tokens = frozenset(_PHASE_WORD_TOKEN_RE.findall(text))
        marker_hits = self._marker_hits(text, marker_spans)
        return {
            expected for expected in expected_phases
            if (expected in phase_tokens
                or expected in text_tokens
                or expected in marker_hits)
        }
    def _extract_log_gaps(self, json_logs: list[dict[str, Any]]) -> list[dict[str, Any]]:
        patterns: list[dict[str, Any]] = []
        if not json_logs:
            return patterns
        expected_phases = self._PHASE_SPECS
        marker_spans = self._marker_spans(expected_phases)
        seen_phases: set[str] = set()
        for entry in json_logs:
            seen_phases |= self._entry_seen_phases(
                entry.get("phase", ""), entry.get("message", ""),
                expected_phases, marker_spans)
            if len(seen_phases) == len(expected_phases):
                break
        for phase, (desc, _markers, _sev) in expected_phases.items():
            if phase not in seen_phases:
                patterns.append({
                    "pattern_type": "log_gap",
                    "missing_phase": phase,
                    "description_text": f"{desc}({phase})在日志中无记录，可能管道断裂或日志缺失",
                })
        return patterns
class FindingGenerator:
    SEVERITY_MAP: ClassVar[dict[str, dict[str, float | str]]] = {
        "repeated_exception": {
            "high": 10,
            "medium": 5,
            "low": 3,
        },
        "perf_degradation": {
            "high": 3.0,
            "medium": 2.0,
            "low": 1.5,
        },
        "audit_anomaly": {
            "critical": 10,
            "high": 5,
            "medium": 3,
        },
        "silent_swallow": {
            "high": 5,
            "medium": 3,
            "low": 2,
        },
    }
    def generate(self, patterns: list[dict[str, Any]]) -> list[LogFinding]:
        findings: list[LogFinding] = []
        for pattern in patterns:
            if not isinstance(pattern, dict):
                continue
            finding = self._pattern_to_finding(pattern)
            if finding:
                findings.append(finding)
        return findings
    def _pattern_to_finding(self, pattern: dict[str, Any]) -> LogFinding | None:
        handlers = {
            "repeated_exception": self._make_repeated_exception_finding,
            "perf_degradation": self._make_perf_finding,
            "audit_anomaly": self._make_audit_finding,
            "silent_swallow": self._make_swallow_finding,
            "log_gap": self._make_log_gap_finding,
        }
        handler = handlers.get(pattern.get("pattern_type", ""))
        return handler(pattern) if handler is not None else None
    def _make_repeated_exception_finding(self, p: dict[str, Any]) -> LogFinding:
        count = _as_count_or(p.get("count"))
        severity = self._compute_severity("repeated_exception", count)
        logger_name = p.get("logger") or _UNKNOWN_TEXT
        level = p.get("level") or "WARNING"
        msg_prefix = normalize_group_key(p.get("message_prefix"), fallback="")
        action = self._repeated_exception_action(logger_name, msg_prefix, level)
        return LogFinding(
            finding_id=self._make_id("rep_exc", logger_name, level, msg_prefix),
            finding_type="repeated_exception",
            severity=severity,
            title=f"重复异常: {logger_name} {level} x{count}",
            description=p.get("description") or "",
            suggested_action=action,
            source="json_log",
            log_evidence=p.get("sample_entries", []),
            pattern_data={
                "logger": logger_name,
                "level": level,
                "count": count,
                "window_minutes": safe_float(p.get("window_minutes"), 0.0),
                "first_seen": as_str(p.get("first_seen")),
                "last_seen": as_str(p.get("last_seen")),
                "timestamps_parseable": signal_bool(
                    p.get("timestamps_parseable")),
                "within_window": signal_bool(p.get("within_window")),
            },
            created_at=now_iso_seconds(),
        )
    def _repeated_exception_action(self, logger_name: str,
                                   msg_prefix: str, level: str) -> str:
        if ("importerror" in msg_prefix.lower()
                or _IMPORT_WORD_RE.search(msg_prefix.lower())):
            return f"检查模块 {logger_name} 的导入链，可能存在循环导入或缺失依赖"
        for marker, action in _EXCEPTION_ACTION_RULES:
            if marker in msg_prefix:
                return action.format(logger_name=logger_name)
        return f"分析模块 {logger_name} 的 {level} 级别异常根因，添加针对性异常处理"
    def _make_perf_finding(self, p: dict[str, Any]) -> LogFinding:
        ratio = safe_float(p.get("degradation_ratio"), 1.0)
        recent_avg_ms = safe_float(p.get("recent_avg_ms"), 0.0)
        phase = p.get("phase") or _UNKNOWN_TEXT
        historical_avg_ms = safe_float(p.get("historical_avg_ms"), 0.0)
        zero_baseline = signal_bool(p.get("zero_baseline")) or historical_avg_ms <= 0
        severity_value = (_ZERO_BASELINE_DEGRADATION_RATIO
                          if zero_baseline else ratio)
        severity = self._compute_severity("perf_degradation", severity_value)
        ratio_label = ("零基线" if zero_baseline else f"{ratio:.0%}")
        action = f"优化阶段 {phase} 的执行性能，检查是否有新增的耗时操作或数据量增长"
        return LogFinding(
            finding_id=self._make_id("perf_deg", phase),
            finding_type="perf_degradation",
            severity=severity,
            title=f"性能退化: {phase} {recent_avg_ms:.0f}ms ({ratio_label})",
            description=p.get("description") or "",
            suggested_action=action,
            source="perf_trace",
            log_evidence=[p.get("last_entry") or {}],
            pattern_data={
                "phase": phase,
                "recent_avg_ms": recent_avg_ms,
                "historical_avg_ms": historical_avg_ms,
                "degradation_ratio": None if zero_baseline else ratio,
                "zero_baseline": zero_baseline,
            },
            created_at=now_iso_seconds(),
        )
    def _make_audit_finding(self, p: dict[str, Any]) -> LogFinding:
        anomaly_type = p.get("anomaly_type") or _UNKNOWN_TEXT
        count = _as_count_or(p.get("count"))
        severity = self._compute_severity("audit_anomaly", count)
        action, title_tpl = _audit_view(anomaly_type)
        title = title_tpl.format(count=count, anomaly_type=anomaly_type)
        return LogFinding(
            finding_id=self._make_id("audit", anomaly_type),
            finding_type="audit_anomaly",
            severity=severity,
            title=title,
            description=p.get("description") or "",
            suggested_action=action,
            source="audit_events",
            log_evidence=p.get("sample_entries", []),
            pattern_data={
                "anomaly_type": anomaly_type,
                "count": count,
            },
            created_at=now_iso_seconds(),
        )
    def _make_swallow_finding(self, p: dict[str, Any]) -> LogFinding:
        count = _as_count_or(p.get("count"))
        severity = self._compute_severity("silent_swallow", count)
        module = p.get("module") or _UNKNOWN_TEXT
        action = (f"审查模块 {module} 的 {count} 次异常吞没"
                  f"（已由 log_swallowed 留痕）：确认每次吞没是否必要，"
                  f"能显式处理的改为显式处理，必须兜底的收敛吞没范围")
        return LogFinding(
            finding_id=self._make_id("swallow", module),
            finding_type="silent_swallow",
            severity=severity,
            title=f"静默异常: {module} x{count}",
            description=p.get("description") or "",
            suggested_action=action,
            source="swallowed_exceptions",
            log_evidence=p.get("sample_entries", []),
            pattern_data={
                "module": module,
                "count": count,
                "exc_type_distribution": p.get("exc_type_distribution") or {},
            },
            created_at=now_iso_seconds(),
        )
    def _make_log_gap_finding(self, p: dict[str, Any]) -> LogFinding:
        missing_phase = normalize_group_key(p.get("missing_phase"))
        severity = self._compute_severity("log_gap", missing_phase)
        description_text = p.get("description_text") or ""
        action = (f"确认管道 {missing_phase} 阶段是否执行；已执行则补充该阶段"
                  "日志输出，未执行则检查上游阶段衔接")
        return LogFinding(
            finding_id=self._make_id("log_gap", missing_phase),
            finding_type="log_gap",
            severity=severity,
            title=f"日志缺口: {missing_phase} 阶段无记录",
            description=description_text,
            suggested_action=action,
            source="json_log",
            log_evidence=[],
            pattern_data={
                "missing_phase": missing_phase,
            },
            created_at=now_iso_seconds(),
        )
    def _compute_severity(self, ptype: str, value: Any) -> str:
        severity_map = self.SEVERITY_MAP.get(ptype, {})
        if ptype == "log_gap":
            return PatternExtractor.phase_severity(value)
        try:
            v = float(value)
        except (ValueError, TypeError, OverflowError) as _e:
            logger.debug("[FindingGenerator] severity值转换失败: %s", _e)
            return "low"
        if ptype == "audit_anomaly" and v >= severity_map.get("critical", float('inf')):
            return "critical"
        if v >= severity_map.get("high", float('inf')):
            return "high"
        if v >= severity_map.get("medium", float('inf')):
            return "medium"
        return "low"
    @staticmethod
    def _make_id(prefix: str, *parts: str) -> str:
        raw = f"{prefix}|{'|'.join(str(p) for p in parts)}"
        return "LDE-" + hashlib.md5(raw.encode("utf-8"), usedforsecurity=False).hexdigest()[:12]
_IMPORT_WORD_RE = re.compile(r"\bimport(?:s|ing|ed)?\b")
_PHASE_WORD_TOKEN_RE = re.compile(r"[a-z0-9_]+")
_EXCEPTION_ACTION_RULES = (
    ("NameError", "检查模块 {logger_name} 中未定义的变量/函数引用，修复 NameError"),
    ("TypeError", "检查模块 {logger_name} 中的类型不匹配问题，添加类型守卫或参数校验"),
    ("AttributeError", "检查模块 {logger_name} 中的属性访问，添加 hasattr 守卫或修复属性名"),
    ("FileNotFoundError", "检查模块 {logger_name} 的文件路径处理，添加路径存在性检查"),
    ("OSError", "检查模块 {logger_name} 的文件路径处理，添加路径存在性检查"),
)
def _resolve_root(project_root: Any) -> str:
    if not project_root:
        return _SKILL_ROOT
    try:
        return os.path.abspath(os.fsdecode(os.fspath(project_root)))
    except TypeError as _e:
        log_swallowed(__name__, _e, context="_resolve_root:fspath")
        return _SKILL_ROOT
def _closure_record_timestamp(record: dict[str, Any]) -> datetime:
    timestamps = [
        parsed
        for field in ("resolved_at", "last_recurred_at", "timestamp")
        if (parsed := parse_log_ts(record.get(field))) is not None
    ]
    return max(timestamps, default=datetime.min)
def _has_post_closure_evidence(
    record: dict[str, Any], finding: LogFinding,
) -> bool:
    resolved_at = parse_log_ts(
        record.get("resolved_at") or record.get("timestamp"))
    if resolved_at is None:
        return False
    raw_timestamps = [finding.pattern_data.get("last_seen")]
    raw_timestamps.extend(
        entry.get("ts") for entry in finding.log_evidence
        if isinstance(entry, dict))
    return any(
        (evidence_at := parse_log_ts(raw)) is not None
        and evidence_at > resolved_at
        for raw in raw_timestamps)
def _merge_fresher_closure_record(
    records: dict[str, dict[str, Any]], finding_id: str,
    candidate: dict[str, Any],
) -> None:
    current = records.get(finding_id)
    if (current is not None
            and _closure_record_timestamp(candidate)
            < _closure_record_timestamp(current)):
        return
    records[finding_id] = candidate
def _recurrence_count(record: dict[str, Any]) -> int:
    try:
        return int(record.get("recurrence_count", 0) or 0)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e, context='_recurrence_count:recurrence_count')
        return 0
def _is_recurrence(record: dict[str, Any]) -> bool:
    if _recurrence_count(record) > 0:
        return True
    resolution = str(record.get("resolution") or "").lower()
    return "recur" in resolution or "reopen" in resolution
_LOG_SEVERITY_ORDER: dict[str, int] = {
    "low": 1, "medium": 2, "high": 3, "critical": 4,
}
_SEVERITIES = frozenset(_LOG_SEVERITY_ORDER)
def _normalize_severity(value: Any, fallback: str = "low") -> str:
    text = as_str(value).strip().lower()
    text = _SEVERITY_ALIASES.get(text, text)
    return text if text in _SEVERITIES else fallback
class ClosureManager:
    CLOSURE_TTL_DAYS = 30
    MAX_CLOSURE_RECORDS = 2000
    def __init__(self, project_root: str | os.PathLike[str] | None = None) -> None:
        self._removed_ids: set[str] = set()
        self._removed_records: dict[str, dict[str, Any]] = {}
        self._dirty_ids: set[str] = set()
        self._skill_dir = _resolve_root(project_root)
        try:
            evolution_state_path(self._skill_dir)
        except (OSError, RuntimeError, ValueError):
            logger.warning(
                "[ClosureManager] 技能根定位失败（%s），销项记录降级为内存模式",
                self._skill_dir,
            )
            self._closure_path = None
            self._records: dict[str, dict[str, Any]] = {}
            return
        self._closure_path = "finding_closure"
        disk_records = self._read_disk_records(warn=True)
        self._records: dict[str, dict[str, Any]] = (
            disk_records if disk_records is not None else {})
    @staticmethod
    def _valid_records(data: Any) -> dict[str, dict[str, Any]] | None:
        if not isinstance(data, dict):
            return {}
        records: dict[str, dict[str, Any]] = {}
        for fid, rec in data.items():
            key = ClosureManager._key(fid)
            if not key or not isinstance(rec, dict):
                return None
            records[key] = rec
        return records
    def _read_disk_records(
        self, *, warn: bool,
    ) -> dict[str, dict[str, Any]] | None:
        if not self._closure_path:
            return {}
        try:
            data = read_evolution_section(self._skill_dir, "finding_closure")
        except (OSError, ValueError, TypeError) as error:
            if warn:
                logger.warning("[ClosureManager] 加载销项记录失败: %s", error)
            return None
        if data is None:
            return {}
        if not isinstance(data, dict):
            if warn:
                logger.warning(
                    "[ClosureManager] 加载销项记录失败: 顶层非对象(%s)",
                    type(data).__name__)
            return None
        records = self._valid_records(data)
        if records is None and warn:
            logger.warning(
                "[ClosureManager] 加载销项记录失败: 记录键或值结构非法")
        return records
    def _merged_disk_records(
        self, disk: dict[str, dict[str, Any]],
    ) -> dict[str, dict[str, Any]]:
        merged = dict(disk)
        for fid in self._removed_ids:
            if fid not in merged:
                continue
            removed_record = self._removed_records.get(fid)
            if removed_record is None or merged[fid] == removed_record:
                merged.pop(fid, None)
        for fid in self._dirty_ids:
            record = self._records.get(fid)
            if record is not None:
                _merge_fresher_closure_record(merged, fid, record)
        return merged
    def _sync_from_disk(self) -> None:
        if not self._closure_path:
            return
        disk = self._read_disk_records(warn=False)
        if disk is None:
            return
        self._records = self._merged_disk_records(disk)
    def _records_for_save(
        self, data: Any,
    ) -> dict[str, dict[str, Any]]:
        if data is None:
            disk = {}
        else:
            if not isinstance(data, dict):
                raise ValueError("销项台账顶层非对象，拒绝覆盖既有证据")
            disk = self._valid_records(data)
            if disk is None:
                raise ValueError("销项台账记录结构非法，拒绝覆盖既有证据")
        merged = self._merged_disk_records(disk)
        for fid in self._evicted_ids(merged):
            merged.pop(fid, None)
        return merged
    def _save(self) -> bool:
        if not self._closure_path:
            self._dirty_ids.clear()
            self._removed_ids.clear()
            self._removed_records.clear()
            return True
        try:
            saved, payload = update_evolution_section(
                self._skill_dir, "finding_closure", self._records_for_save)
            if not saved:
                return False
            self._records = payload
            self._dirty_ids.clear()
            self._removed_ids.clear()
            self._removed_records.clear()
            return True
        except (OSError, ValueError, TypeError, RecursionError) as e:
            logger.warning("[ClosureManager] 保存销项记录失败: %s", e)
            return False
    @staticmethod
    def _key(finding_id: Any) -> str:
        if finding_id is None:
            return ""
        return str(finding_id).strip()
    def is_closed(self, finding_id: str) -> bool:
        key = self._key(finding_id)
        if not key:
            return False
        self._sync_from_disk()
        record = self._records.get(key)
        return record is not None and not signal_bool(record.get("reopened"))
    @staticmethod
    def _mark_recurrence(record: dict[str, Any]) -> None:
        record["recurrence_count"] = _recurrence_count(record) + 1
        record["last_recurred_at"] = now_iso_seconds()
    def filter_open(self, findings: list[LogFinding]) -> list[LogFinding]:
        self._sync_from_disk()
        result = []
        recurred = False
        for f in findings:
            key = self._key(f.finding_id)
            if not key:
                result.append(f)
                continue
            rec = self._records.get(key)
            if rec is None:
                result.append(f)
                continue
            if signal_bool(rec.get("reopened")):
                result.append(f)
                continue
            evidence_recurred = _has_post_closure_evidence(rec, f)
            old_severity = _normalize_severity(rec.get("severity"), "")
            if old_severity not in _SEVERITIES:
                if not evidence_recurred:
                    logger.debug(
                        "[ClosureManager] 销项记录缺有效严重度基线，保持已关闭: %s",
                        key)
                    continue
                old_sev = 0
            else:
                old_sev = _LOG_SEVERITY_ORDER[old_severity]
            new_sev = _LOG_SEVERITY_ORDER.get(
                _normalize_severity(f.severity, ""), 0)
            if evidence_recurred or new_sev > old_sev:
                self._mark_recurrence(rec)
                rec["reopened"] = True
                rec["severity"] = f.severity
                self._dirty_ids.add(key)
                recurred = True
                result.append(f)
        if recurred:
            self._save()
        return result
    def close_many(self, finding_ids: list[str], resolution: str = "",
                   severity_by_id: dict[str, str] | None = None) -> None:
        ts = now_iso_seconds()
        skill_dir = self._skill_dir
        _rst = peek_round_start_ts(skill_dir)
        self._sync_from_disk()
        severity_map = (severity_by_id
                        if isinstance(severity_by_id, dict) else {})
        for fid in finding_ids:
            key = self._key(fid)
            if not key:
                continue
            prev = self._records.get(key) or {}
            record = {
                "resolved_at": ts,
                "timestamp": ts,
                "round_start_ts": _rst,
                "skill_dir": skill_dir,
                "resolution": resolution,
            }
            severity = severity_map.get(fid) or severity_map.get(key)
            if not severity:
                severity = prev.get("severity")
            if severity:
                record["severity"] = severity
            if prev.get("recurrence_count"):
                record["recurrence_count"] = prev["recurrence_count"]
            if prev.get("last_recurred_at"):
                record["last_recurred_at"] = prev["last_recurred_at"]
            self._records[key] = record
            self._removed_ids.discard(key)
            self._removed_records.pop(key, None)
            self._dirty_ids.add(key)
        self._save()
    def _expired_ids(self, now: float) -> list[str]:
        expired: list[str] = []
        cutoff = datetime.fromtimestamp(now) - timedelta(
            days=self.CLOSURE_TTL_DAYS)
        for fid, record in self._records.items():
            if signal_bool(record.get("reopened")):
                continue
            resolved_at = record.get("resolved_at", "")
            dt = parse_log_ts(resolved_at)
            if dt is None:
                logger.debug(
                    "[ClosureManager] 过期清理解析失败 fid=%s resolved_at=%r",
                    fid, resolved_at)
                continue
            if dt < cutoff:
                expired.append(fid)
        return expired
    def _evicted_ids(self, records: dict[str, dict[str, Any]]) -> list[str]:
        overflow = len(records) - self.MAX_CLOSURE_RECORDS
        if overflow <= 0:
            return []
        oldest = sorted(
            records.items(),
            key=lambda item: (
                signal_bool(item[1].get("reopened")),
                _closure_record_timestamp(item[1])),
        )[:overflow]
        return [fid for fid, _record in oldest]
    def _remove_record(self, fid: str) -> None:
        record = self._records.pop(fid, None)
        if record is None:
            return
        self._dirty_ids.discard(fid)
        self._removed_ids.add(fid)
        self._removed_records[fid] = copy.deepcopy(record)
    def cleanup_expired(self) -> int:
        self._sync_from_disk()
        before = len(self._records)
        for fid in [fid for fid in self._records if not str(fid).strip()]:
            self._remove_record(fid)
        for fid in self._expired_ids(time.time()):
            self._remove_record(fid)
        for fid in self._evicted_ids(self._records):
            self._remove_record(fid)
        deleted = before - len(self._records)
        if not deleted:
            if self._removed_ids or self._dirty_ids:
                self._save()
            return 0
        self._save()
        return deleted
    def get_stats(self, open_count: int = 0) -> dict[str, Any]:
        self._sync_from_disk()
        total_records = len(self._records)
        reopened = sum(
            1 for r in self._records.values() if signal_bool(r.get("reopened")))
        total_closed = total_records - reopened
        total_seen = total_closed + open_count
        recurred = sum(1 for r in self._records.values() if _is_recurrence(r))
        recurrence_rate = (recurred / total_records
                           if total_records > 0 else 0.0)
        return {
            "total_closed": total_closed,
            "active_open": open_count,
            "total_seen": total_seen,
            "recurrence_rate": round(recurrence_rate, 4),
            "closure_path": self._closure_path,
        }
def _coverage_audit_brief(report: dict[str, Any] | None) -> dict[str, Any]:
    if not isinstance(report, dict) or not report:
        return {"status": "skipped"}
    if report.get("status") != "ok":
        return {"status": "error", "message": str(report.get("message") or "")}
    codebase = as_dict(report.get("codebase"))
    silent_paths = as_dict(report.get("silent_paths"))
    hotspots = norm_dict_list(silent_paths.get("hotspots"))
    zero_sample = norm_dict_list(
        codebase.get("zero_instrumentation_sample"))
    return {
        "status": "ok",
        "summary": as_dict(report.get("summary")),
        "zero_instrumentation_sample": [z.get("module") for z in zero_sample],
        "hotspot_modules": [
            {"module": h.get("module"), "count": h.get("count")}
            for h in hotspots[:5]
        ],
    }
_AI_EXECUTION_HINT: dict[str, str] = {
    "next_action": "review_and_execute_evolution_fixes",
    "instruction": (
        "逐项审核 findings（重复异常/性能退化/审计异常/静默吞错/日志"
        "缺口）；确认后直接修复源码（备份→改→compile+import 验证），"
        "修复后复跑 run_log_driven_evolution 确认销项；不成立的发现"
        "标记理由并经 jwsgj.fp_rules_judge.fixate_fp_rules 固化防复发"
    ),
}
def _empty_result(status: str, message: str) -> dict[str, Any]:
    return {
        "status": status,
        "findings": [],
        "total_patterns": 0,
        "total_findings": 0,
        "open_findings": 0,
        "closed_findings": 0,
        "by_severity": {},
        "by_type": {},
        "closure_stats": {},
        "coverage_audit": {"status": "skipped"},
        "log_summary": {},
        "log_channel_errors": {},
        "ai_execution": dict(_AI_EXECUTION_HINT),
        "message": message,
    }
def _log_channel_loaders(
    max_log_entries: int,
) -> dict[str, Callable[[], list[dict[str, Any]]]]:
    return {
        "json_logs": lambda: load_json_logs(max_entries=max_log_entries),
        "audit_events": load_audit_events,
        "perf_traces": load_perf_traces,
        "swallowed_exceptions": load_swallowed_exceptions,
    }
def _load_log_channels(
    max_log_entries: int,
) -> tuple[dict[str, list[dict[str, Any]]], dict[str, int], dict[str, str]]:
    log_data: dict[str, list[dict[str, Any]]] = {}
    log_summary: dict[str, int] = {}
    channel_errors: dict[str, str] = {}
    for channel, loader in _log_channel_loaders(max_log_entries).items():
        try:
            entries = loader()
        except Exception as _e:
            logger.warning(
                "[LogDrivenEvolution] 日志通道 %s 读取失败: %s",
                channel, _e, exc_info=True)
            channel_errors[channel] = f"{type(_e).__name__}: {str(_e)[:200]}"
            entries = []
        if not isinstance(entries, list):
            logger.warning(
                "[LogDrivenEvolution] 日志通道 %s 返回非 list（%s），按空通道处理",
                channel, type(entries).__name__)
            channel_errors[channel] = (
                f"non-list payload: {type(entries).__name__}")
            entries = []
        valid_entries = [entry for entry in entries if isinstance(entry, dict)]
        invalid_count = len(entries) - len(valid_entries)
        if invalid_count:
            logger.warning(
                "[LogDrivenEvolution] 日志通道 %s 跳过 %d 条非 dict 条目",
                channel, invalid_count)
            channel_errors[channel] = f"non-dict entries: {invalid_count}"
        log_data[channel] = valid_entries
        log_summary[channel] = len(valid_entries)
    return log_data, log_summary, channel_errors
def _run_coverage_audit(max_log_entries: int) -> tuple[Any, list]:
    coverage_report: dict[str, Any] | None = None
    coverage_findings: list = []
    try:
        coverage_report = audit_log_coverage(
            max_log_entries=max_log_entries)
        if (isinstance(coverage_report, dict)
                and coverage_report.get("status") == "ok"):
            coverage_findings = [
                _coverage_finding_from_dict(cd)
                for cd in as_list(coverage_report.get("findings"))
                if isinstance(cd, dict)
            ]
            logger.info(
                "[LogDrivenEvolution] 覆盖度审计: %s",
                coverage_report.get("summary", {}))
    except Exception as _cov_err:
        logger.warning("[LogDrivenEvolution] 覆盖度审计跳过: %s", _cov_err)
    return coverage_report, coverage_findings
def _coverage_finding_from_dict(cd: dict[str, Any]) -> LogFinding:
    return LogFinding(
        finding_id=as_str(cd.get("finding_id")),
        finding_type=as_str(cd.get("finding_type")),
        severity=_normalize_severity(cd.get("severity")),
        title=as_str(cd.get("title")),
        description=as_str(cd.get("description")),
        suggested_action=as_str(cd.get("suggested_action")),
        source=as_str(cd.get("source")) or "codebase_scan",
        log_evidence=as_list(cd.get("log_evidence")),
        pattern_data=as_dict(cd.get("pattern_data")),
        created_at=as_str(cd.get("created_at")),
    )
class _DetectionOutcome(NamedTuple):
    patterns: list
    all_findings: list
    open_findings: list
    closure: Any
def _detect_and_filter(log_data: dict[str, Any], coverage_findings: list,
                       close_resolved: bool) -> _DetectionOutcome:
    patterns = PatternExtractor().extract_all(log_data)
    logger.info("[LogDrivenEvolution] 模式提取: %d 个", len(patterns))
    all_findings = FindingGenerator().generate(patterns)
    all_findings.extend(coverage_findings)
    logger.info(
        "[LogDrivenEvolution] 发现生成: %d 条 (模式 %d + 覆盖度 %d)",
        len(all_findings), len(all_findings) - len(coverage_findings),
        len(coverage_findings))
    closure = ClosureManager()
    closure.cleanup_expired()
    open_findings = (
        closure.filter_open(all_findings) if close_resolved
        else list(all_findings))
    return _DetectionOutcome(patterns, all_findings, open_findings, closure)
def _build_evolution_result(outcome: _DetectionOutcome,
                            coverage_report: Any, log_summary: dict,
                            ) -> dict[str, Any]:
    patterns = outcome.patterns
    all_findings = outcome.all_findings
    open_findings = outcome.open_findings
    findings_dicts = [f.to_dict() for f in open_findings]
    by_severity = Counter(f.severity for f in open_findings)
    by_type = Counter(f.finding_type for f in open_findings)
    result = _empty_result(
        "ok",
        f"日志驱动分析完成: {len(patterns)} 模式 → {len(all_findings)} 发现"
        f" → {len(open_findings)} 待处理")
    result.update({
        "findings": findings_dicts,
        "total_patterns": len(patterns),
        "total_findings": len(all_findings),
        "open_findings": len(open_findings),
        "closed_findings": len(all_findings) - len(open_findings),
        "by_severity": dict(by_severity),
        "by_type": dict(by_type),
        "closure_stats": outcome.closure.get_stats(
            open_count=len(open_findings)),
        "coverage_audit": _coverage_audit_brief(coverage_report),
        "log_summary": log_summary,
    })
    result["ai_execution"] = dict(_AI_EXECUTION_HINT)
    return result
def run_log_driven_evolution(
    *,
    close_resolved: bool = True,
    max_log_entries: int = DEFAULT_MAX_LOG_ENTRIES,
) -> dict[str, Any]:
    try:
        _t0 = time.monotonic()
        close_resolved = signal_bool(close_resolved)
        log_data, log_summary, channel_errors = _load_log_channels(
            max_log_entries)
        logger.info("[LogDrivenEvolution] 日志读取: %s", log_summary)
        if channel_errors:
            logger.warning("[LogDrivenEvolution] 通道降级: %s", channel_errors)
        coverage_report, coverage_findings = _run_coverage_audit(
            max_log_entries)
        total_log_entries = sum(log_summary.values())
        if total_log_entries == 0 and not coverage_findings:
            complete_log_outage = (
                bool(log_data) and len(channel_errors) == len(log_data))
            result_status = "error" if complete_log_outage else "ok"
            write_module_run(
                "log_driven_evolution", "run_log_driven_evolution",
                outcome="error" if complete_log_outage else "ok_no_data",
                duration_ms=(time.monotonic() - _t0) * 1000.0)
            message = "无日志数据可分析"
            if channel_errors:
                message += (
                    "（日志通道读取失败: "
                    + ", ".join(sorted(channel_errors)) + "）")
            result = _empty_result(result_status, message)
            result["coverage_audit"] = _coverage_audit_brief(coverage_report)
            result["log_summary"] = log_summary
            result["log_channel_errors"] = channel_errors
            return result
        outcome = _detect_and_filter(log_data, coverage_findings, close_resolved)
        result = _build_evolution_result(
            outcome, coverage_report, log_summary)
        result["log_channel_errors"] = channel_errors
        logger.info(
            "[LogDrivenEvolution] 完成: %d模式 → %d发现 → %d待处理 (已销项%d)",
            len(outcome.patterns), len(outcome.all_findings),
            len(outcome.open_findings), result["closed_findings"],
        )
        write_module_run(
            "log_driven_evolution", "run_log_driven_evolution",
            duration_ms=(time.monotonic() - _t0) * 1000.0,
            patterns=len(outcome.patterns), findings=len(outcome.all_findings),
            open_findings=len(outcome.open_findings),
            channel_errors=len(channel_errors))
        return result
    except Exception as e:
        logger.exception("[LogDrivenEvolution] 失败")
        try:
            write_module_run(
                "log_driven_evolution", "run_log_driven_evolution",
                outcome="error",
                error=str(e)[:200])
        except Exception:
            logger.debug("[LogDrivenEvolution] 异常出口留痕失败")
        return _empty_result(
            "error", f"日志驱动分析失败: {str(e)[:200]}")
_SMOKE_TEST_SOURCE = "try:\n    pass\nexcept:\n    pass\n"
_HEURISTIC_BARE_EXCEPT_PATTERN = "bareexcept"
_HEURISTIC_ASSERT_PATTERN = "assert"
_REPEATED_FAILURE_RULE_PREFIX = "detect_repeated_failure"
_AUDIT_SEQUENCE_PATTERN = r"rollback|revert|delete"
_CANDIDATE_PATTERN_RULES = (
    (("except", "silent"), ("ast", _HEURISTIC_BARE_EXCEPT_PATTERN),
     _SMOKE_TEST_SOURCE),
    (("repeated", "failure"), ("ast", _HEURISTIC_ASSERT_PATTERN),
     "assert done\n"),
    (("audit",), ("regex", _AUDIT_SEQUENCE_PATTERN), "db.rollback()\n"),
)
def _infer_candidate_pattern(*identifiers: Any) -> tuple[str, str]:
    haystacks = [str(item).lower() for item in identifiers
                 if isinstance(item, str) and item]
    for tokens, pattern, _smoke_source in _CANDIDATE_PATTERN_RULES:
        if any(token in text for text in haystacks for token in tokens):
            return pattern
    return "ast", _HEURISTIC_BARE_EXCEPT_PATTERN
def _candidate_pattern(cand: dict[str, Any],
                       rule_name: str) -> tuple[str, str]:
    if rule_name.startswith(_REPEATED_FAILURE_RULE_PREFIX + "_"):
        return "", ""
    pattern_type = cand.get("pattern_type")
    pattern = cand.get("pattern")
    if (isinstance(pattern_type, str) and pattern_type in ("ast", "regex")
            and isinstance(pattern, str) and pattern):
        return pattern_type, pattern
    return _infer_candidate_pattern(rule_name, cand.get("detection_logic"))
def _candidate_smoke_source(pattern_type: str, pattern: str) -> str:
    for _tokens, candidate_pattern, smoke_source in _CANDIDATE_PATTERN_RULES:
        if candidate_pattern == (pattern_type, pattern):
            return smoke_source
    return _SMOKE_TEST_SOURCE
_CANDIDATE_SEVERITIES = {"critical": "P0", "high": "P1", "low": "P3"}
def _candidate_p_severity(severity: Any) -> str:
    normalized = _normalize_severity(severity, _DEFAULT_RULE_SEVERITY)
    return _CANDIDATE_SEVERITIES.get(normalized, _DEFAULT_P_SEVERITY)
def _verify_registered_rule(
    registry: Any, rule_name: str, source_code: str,
) -> dict[str, Any]:
    try:
        test_findings = registry.run(
            rule_name, source_code=source_code, file_path="<test>")
        finding_count = len(test_findings) if isinstance(test_findings, list) else 0
        return {
            "verified": finding_count > 0,
            "test_findings_count": finding_count,
        }
    except Exception as _ve:
        logger.debug("register_rule_candidates: verify %s failed: %s", rule_name, _ve)
        return {"verified": False, "verify_error": str(_ve)[:200]}
def _resolve_candidate_issue(
    consumer_id: str, issue_sig: str, rule_name: str,
) -> None:
    if not issue_sig:
        return
    try:
        register_resolution(
            consumer_id, issue_sig,
            f"Rule {rule_name} registered to DetectorRegistry")
    except Exception:
        logger.debug("register_rule_candidates: resolution failed for %s", issue_sig)
def _candidate_issue_signatures(cand: dict[str, Any]) -> list[str]:
    raw = cand.get("issue_signatures")
    values = (list(raw) if isinstance(raw, (list, tuple, set, frozenset))
              else [raw])
    values.append(cand.get("issue_signature"))
    return list(dict.fromkeys(
        value for value in values if isinstance(value, str) and value))
def _verify_candidate_registration(
    registry: Any,
    cand: dict[str, Any],
    rule_name: str,
    consumer_id: str,
) -> dict[str, Any]:
    pattern_type, pattern = _candidate_pattern(cand, rule_name)
    if not pattern_type or not pattern:
        return {
            "verified": False,
            "verify_error": "重复失败属于日志序列语义，无等价的源码静态探针",
        }
    detail = _verify_registered_rule(
        registry, rule_name, _candidate_smoke_source(pattern_type, pattern))
    if detail.get("verified"):
        for issue_sig in _candidate_issue_signatures(cand):
            _resolve_candidate_issue(consumer_id, issue_sig, rule_name)
    return detail
def _apply_ast_candidate(
    registry: Any,
    cand: dict[str, Any],
    rule_name: str,
    consumer_id: str,
) -> tuple[str, dict[str, Any]]:
    pattern_type, pattern = _candidate_pattern(cand, rule_name)
    if not pattern_type or not pattern:
        return "skipped", {
            "rule_name": rule_name,
            "status": "skipped",
            "reason": "重复失败属于日志序列语义，拒绝固化为不匹配的源码检测器",
        }
    has_known_positive_probe = any(
        candidate_pattern == (pattern_type, pattern)
        for _tokens, candidate_pattern, _smoke_source
        in _CANDIDATE_PATTERN_RULES)
    try:
        registry.register_solidified_rule(
            rule_id=rule_name,
            pattern_type=pattern_type,
            pattern=pattern,
            severity=_candidate_p_severity(
                cand.get("severity", _DEFAULT_RULE_SEVERITY)),
        )
    except Exception as _re:
        logger.debug("register_rule_candidates: register %s failed: %s", rule_name, _re)
        return "failed", {
            "rule_name": rule_name,
            "status": "failed",
            "error": str(_re)[:200],
        }
    detail: dict[str, Any] = {"rule_name": rule_name, "status": "registered"}
    detail.update(_verify_candidate_registration(
        registry, cand, rule_name, consumer_id))
    if has_known_positive_probe and not detail.get("verified"):
        registry.unregister(rule_name)
        detail["status"] = "verification_failed"
        detail["error"] = "阳性探针未命中，已撤销本次新注册"
        return "failed", detail
    return "registered", detail
_IN_MEMORY_RULE_TYPES = frozenset({"cv_rule", "perf_threshold"})
def _skipped_detail(reason: str, rule_name: Any = "") -> tuple[str, dict[str, Any]]:
    return "skipped", {
        "rule_name": rule_name,
        "status": "skipped",
        "reason": reason,
    }
def _in_memory_candidate_detail(
    cand: dict[str, Any], rule_name: str,
) -> dict[str, Any]:
    rule_type = cand.get("rule_type", "")
    record: dict[str, Any] = {
        "rule_name": rule_name,
        "status": f"{rule_type}_candidate",
        "rule_type": rule_type,
        "severity": _normalize_severity(
            cand.get("severity"), _DEFAULT_RULE_SEVERITY),
        "registration_target": cand.get("registration_target", ""),
    }
    if rule_type == "perf_threshold":
        record["threshold_ms"] = cand.get("threshold_ms", 0)
    else:
        record["detection_logic"] = cand.get("detection_logic") or ""
    return record
def _as_candidate_list(value: Any) -> list[Any] | None:
    if value is None:
        return None
    if isinstance(value, list):
        return value
    if isinstance(value, (tuple, set, frozenset)):
        return list(value)
    return [value]
def _candidate_identity(cand: Any) -> tuple[str, tuple[str, dict[str, Any]] | None]:
    if not isinstance(cand, dict):
        return "", _skipped_detail(f"non-dict candidate: {type(cand).__name__}")
    rule_name = cand.get("rule_name", "")
    if not rule_name:
        return "", _skipped_detail("no rule_name", rule_name)
    if not isinstance(rule_name, str):
        rule_name = str(rule_name)
    return rule_name, None
def _apply_rule_candidate(
    registry: Any,
    cand: Any,
    consumer_id: str,
) -> tuple[str, dict[str, Any]]:
    rule_name, skip = _candidate_identity(cand)
    if skip is not None:
        return skip
    rule_type = cand.get("rule_type", "")
    if rule_type in _IN_MEMORY_RULE_TYPES:
        return "candidate", _in_memory_candidate_detail(cand, rule_name)
    if rule_type != "ast_detector":
        return _skipped_detail(f"unknown rule_type: {rule_type}", rule_name)
    if registry is None:
        return "failed", {
            "rule_name": rule_name,
            "status": "failed",
            "error": "registry unavailable",
        }
    if registry.is_registered(rule_name):
        detail: dict[str, Any] = {
            "rule_name": rule_name, "status": "already_registered",
        }
        detail.update(_verify_candidate_registration(
            registry, cand, rule_name, consumer_id))
        return "skipped", detail
    return _apply_ast_candidate(registry, cand, rule_name, consumer_id)
class _RuleSpec(NamedTuple):
    rule_type: str
    registration_target: str
    name_prefix: str
    subject_key: str
    description: str
    detection_logic: str
    default_severity: str
    pattern_type: str = ""
    pattern: str = ""
_RULE_SPECS: dict[str, _RuleSpec] = {
    "repeated_failure": _RuleSpec(
        "cv_rule", "XVRuleRegistry", _REPEATED_FAILURE_RULE_PREFIX,
        "method_id", "检测方法 {subject} 的重复失败模式",
        "扫描该方法相关的 ERROR 日志，统计同一方法在多次审计中反复失败",
        "medium"),
    "silent_exception": _RuleSpec(
        "ast_detector", "DetectorRegistry", "detect_silent_exception",
        "module", "检测模块 {subject} 的静默异常吞没模式",
        "扫描该模块的 except 块，检查是否有日志输出或 re-raise",
        "medium", "ast", _HEURISTIC_BARE_EXCEPT_PATTERN),
    "audit_anomaly_sequence": _RuleSpec(
        "cv_rule", "XVRuleRegistry", "detect_audit_anomaly",
        "issue_signature",
        "交叉验证审计事件序列中的异常模式（修复后回滚/删除后未恢复）",
        "分析统一日志（jwsgj.log 的 audit 事件）序列，检测修复后回滚或删除后未恢复模式",
        "high", "regex", _AUDIT_SEQUENCE_PATTERN),
    "perf_threshold": _RuleSpec(
        "perf_threshold", "PerfMonitor", "perf_threshold", "phase",
        "性能阈值规则：阶段 {subject} 耗时超过 {threshold_ms}ms",
        "监控阶段 {subject} 的耗时，超过 {threshold_ms}ms 触发警告",
        "medium"),
}
def _new_rule_candidate(spec: _RuleSpec, subject: str, source_findings: int,
                        severity: str | None = None,
                        issue_signature: str | None = None,
                        **extra: Any) -> dict[str, Any]:
    record: dict[str, Any] = {
        "rule_type": spec.rule_type,
        "rule_name": f"{spec.name_prefix}_{subject}",
        "description": spec.description.format(subject=subject, **extra),
        "detection_logic": spec.detection_logic.format(
            subject=subject, **extra),
        "severity": severity or spec.default_severity,
        "source_findings": source_findings,
    }
    if spec.pattern_type and spec.pattern:
        record["pattern_type"] = spec.pattern_type
        record["pattern"] = spec.pattern
    if issue_signature is not None:
        record["issue_signature"] = issue_signature
    record["registration_target"] = spec.registration_target
    record["registration_status"] = "candidate"
    record.update(extra)
    return record
def _finding_subject(finding: dict[str, Any], subject_key: str) -> str:
    raw = finding.get(subject_key)
    if raw is None:
        return ""
    return str(raw).strip()
def _rule_candidate_of_finding(finding: dict[str, Any],
                               source_findings: int,
                               ) -> dict[str, Any] | None:
    spec = _RULE_SPECS.get(str(finding.get("type")))
    if spec is None:
        return None
    subject = _finding_subject(finding, spec.subject_key)
    if not subject:
        return None
    return _new_rule_candidate(
        spec, subject, source_findings,
        severity=_normalize_severity(
            finding.get("severity"), spec.default_severity),
        issue_signature=finding.get("issue_signature", ""))
def _rule_type_summary(rule_candidates: list[dict[str, Any]]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for candidate in rule_candidates:
        rule_type = candidate["rule_type"]
        counts[rule_type] = counts.get(rule_type, 0) + 1
    return dict(sorted(counts.items()))
def _pattern_candidates(findings: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[tuple[str, str, str], dict[str, Any]] = {}
    for finding in findings:
        finding_type = str(finding.get("type"))
        spec = _RULE_SPECS.get(finding_type)
        if spec is None:
            continue
        subject = _finding_subject(finding, spec.subject_key)
        if not subject:
            continue
        key = (finding_type, spec.rule_type, subject)
        aggregate = grouped.get(key)
        if aggregate is None:
            aggregate = {"finding": finding, "source_findings": 0,
                         "issue_signatures": []}
            grouped[key] = aggregate
        aggregate["source_findings"] += 1
        issue_signature = finding.get("issue_signature")
        if (isinstance(issue_signature, str) and issue_signature
                and issue_signature not in aggregate["issue_signatures"]):
            aggregate["issue_signatures"].append(issue_signature)
        if aggregate["source_findings"] == 1:
            continue
        current = aggregate["finding"]
        new_weight = _LOG_SEVERITY_ORDER.get(
            _normalize_severity(finding.get("severity"), "low"), 0)
        current_weight = _LOG_SEVERITY_ORDER.get(
            _normalize_severity(current.get("severity"), "low"), 0)
        if new_weight > current_weight:
            aggregate["finding"] = finding
    candidates: list[dict[str, Any]] = []
    for aggregate in grouped.values():
        candidate = _rule_candidate_of_finding(
            aggregate["finding"], aggregate["source_findings"])
        if candidate is not None:
            if aggregate["issue_signatures"]:
                candidate["issue_signatures"] = list(
                    aggregate["issue_signatures"])
            candidates.append(candidate)
    return candidates
def _perf_candidates(perf_result: dict[str, Any]) -> list[dict[str, Any]]:
    if not isinstance(perf_result, dict):
        return []
    candidates: list[dict[str, Any]] = []
    for bottleneck in as_list(perf_result.get("bottlenecks")):
        if not isinstance(bottleneck, dict):
            continue
        phase = as_str(bottleneck.get("phase")).strip()
        threshold_ms = safe_float(bottleneck.get("avg_ms"), None)
        if not phase or threshold_ms is None or threshold_ms <= 0:
            continue
        candidates.append(_new_rule_candidate(
            _RULE_SPECS["perf_threshold"], phase, 1,
            severity=_normalize_severity(
                bottleneck.get("priority"), _DEFAULT_RULE_SEVERITY),
            threshold_ms=threshold_ms))
    return candidates
def extract_rule_candidates(
    consumer_id: str = _DEFAULT_CONSUMER_ID,
) -> dict[str, Any]:
    try:
        pattern_result = analyze_log_patterns(
            consumer_id=consumer_id, advance_cursor=False)
    except Exception as _e:
        logger.warning("extract_rule_candidates: 日志模式分析失败: %s",
                       _e, exc_info=True)
        pattern_result = {}
    try:
        perf_result = analyze_perf_bottlenecks()
    except Exception as _e:
        logger.warning("extract_rule_candidates: 性能分析失败: %s",
                       _e, exc_info=True)
        perf_result = {}
    if not isinstance(pattern_result, dict):
        logger.warning(
            "extract_rule_candidates: 日志模式结果非 dict（%s），按空通道处理",
            type(pattern_result).__name__)
        pattern_result = {}
    if not isinstance(perf_result, dict):
        logger.warning(
            "extract_rule_candidates: 性能分析结果非 dict（%s），按空通道处理",
            type(perf_result).__name__)
        perf_result = {}
    rule_candidates = _pattern_candidates(
        as_list(pattern_result.get("findings")))
    rule_candidates += _perf_candidates(perf_result)
    return {
        "rule_candidates": rule_candidates,
        "summary": {
            "total": len(rule_candidates),
            "by_type": _rule_type_summary(rule_candidates),
        },
        "consumer_id": consumer_id,
    }
def register_rule_candidates(
    candidates: list[dict[str, Any]] | None = None,
    *,
    consumer_id: str = _DEFAULT_CONSUMER_ID,
) -> dict[str, Any]:
    candidates = _as_candidate_list(candidates)
    if candidates is None:
        result = extract_rule_candidates(consumer_id=consumer_id)
        candidates = _as_candidate_list(result.get("rule_candidates"))
    if not candidates:
        return {
            "registered": 0, "skipped": 0, "failed": 0, "verified": 0,
            "details": [], "status": "ok",
            "message": "无规则候选可注册",
            "total_candidates": 0,
        }
    registered = 0
    skipped = 0
    failed = 0
    verified = 0
    details: list[dict[str, Any]] = []
    try:
        registry = get_detector_registry()
    except Exception as _e:
        logger.warning(
            "register_rule_candidates: get_detector_registry failed: %s", _e)
        registry = None
    for cand in candidates:
        try:
            outcome, detail = _apply_rule_candidate(
                registry, cand, consumer_id)
        except Exception as _e:
            logger.warning(
                "register_rule_candidates: 候选登记异常: %s", _e,
                exc_info=True)
            outcome = "failed"
            detail = {
                "rule_name": (cand.get("rule_name", "")
                              if isinstance(cand, dict) else ""),
                "status": "failed",
                "error": str(_e)[:200],
            }
        details.append(detail)
        if outcome == "registered":
            registered += 1
        elif outcome == "failed":
            failed += 1
        else:
            skipped += 1
        if detail.get("verified"):
            verified += 1
    logger.info(
        "register_rule_candidates: registered=%d, skipped=%d, "
        "failed=%d, verified=%d",
        registered, skipped, failed, verified,
    )
    return {
        "registered": registered,
        "skipped": skipped,
        "failed": failed,
        "verified": verified,
        "details": details,
        "status": "ok",
        "total_candidates": len(candidates),
    }
def _as_dict(val, default: dict) -> dict:
    return val if isinstance(val, dict) else copy.deepcopy(default)
def _payload_str(payload: Any, key: str) -> str:
    if not isinstance(payload, dict):
        return "unknown"
    return str(payload.get(key) or "unknown")
_AUDIT_BASE: dict[str, Any] = {
    "total": 0, "by_event": {}, "high_risk_count": 0,
    "high_risk_events": [], "rollback_count": 0,
}
_PERF_BASE: dict[str, Any] = {
    "total": 0, "degraded": False, "signals": [], "per_phase": {},
}
_SWALLOWED_BASE: dict[str, Any] = {
    "total": 0, "by_module": {}, "by_exc_type": {}, "high_freq_modules": [],
}
_BUG_INTERCEPT_BASE: dict[str, Any] = {
    "total": 0, "by_check": {}, "by_severity": {}, "high_freq": [],
}
def _top_freq(counts: dict[str, int], min_count: int = 3,
              limit: int = 10) -> list[tuple[str, int]]:
    return sorted(
        [(k, c) for k, c in counts.items() if c >= min_count],
        key=lambda x: (-x[1], x[0]),
    )[:limit]
def _load_event_list(loader, label: str) -> list[dict[str, Any]] | None:
    try:
        events = loader()
    except Exception as e:
        logger.warning("%s: 事件加载失败: %s", label, e, exc_info=True)
        return None
    if not isinstance(events, list):
        logger.warning("%s: 事件加载结果非 list（%s），按空数据处理",
                       label, type(events).__name__)
        return None
    entries = [ev for ev in events if isinstance(ev, dict)]
    if len(entries) != len(events):
        logger.warning("%s: 跳过 %d 条非 dict 事件", label,
                       len(events) - len(entries))
    return entries
def load_audit_summary() -> dict[str, Any]:
    events = _load_event_list(load_audit_events, "load_audit_summary")
    if not events:
        return copy.deepcopy(_AUDIT_BASE)
    by_event: dict[str, int] = {}
    high_risk: list[dict[str, Any]] = []
    high_risk_count = 0
    rollback_count = 0
    for ev in events:
        event_type = str(ev.get("event") or "unknown")
        by_event[event_type] = by_event.get(event_type, 0) + 1
        if _is_rollback_audit(ev):
            rollback_count += 1
        if not is_high_risk_audit_event(ev):
            continue
        high_risk.append(ev)
        high_risk_count += 1
    return {
        "total": len(events),
        "by_event": by_event,
        "high_risk_count": high_risk_count,
        "high_risk_events": high_risk[-20:],
        "rollback_count": rollback_count,
    }
def _phase_perf_stats(durations: list[float]) -> dict[str, Any]:
    if not durations:
        return {"avg_ms": 0.0, "max_ms": 0.0, "min_ms": 0.0, "calls": 0}
    return {
        "avg_ms": round(sum(durations) / len(durations), 1),
        "max_ms": round(max(durations), 1),
        "min_ms": round(min(durations), 1),
        "calls": len(durations),
    }
def _phase_degradation_signal(phase: str, durations: list[float]) -> str:
    deg = detect_phase_degradation(durations)
    if not deg:
        return ""
    historical_avg_ms = as_number(deg.get("historical_avg_ms"), 0.0)
    growth = ("零基线" if historical_avg_ms <= 0
              else f"+{as_number(deg.get('degradation_pct'), 0.0):.0f}%")
    return (f"{phase}: 最近耗时 {as_number(deg.get('recent_ms'), 0.0):.1f}ms vs "
            f"历史平均 {historical_avg_ms:.1f}ms（{growth}）")
def load_perf_summary() -> dict[str, Any]:
    traces = _load_event_list(load_perf_traces, "load_perf_summary")
    if not traces:
        return copy.deepcopy(_PERF_BASE)
    try:
        per_phase: dict[str, dict[str, Any]] = {}
        degraded_signals: list[str] = []
        for phase, durations in _phase_durations(traces).items():
            if not durations:
                continue
            per_phase[phase] = _phase_perf_stats(durations)
            signal = _phase_degradation_signal(phase, durations)
            if signal:
                degraded_signals.append(signal)
        return {
            "total": len(traces),
            "degraded": len(degraded_signals) > 0,
            "signals": degraded_signals,
            "per_phase": per_phase,
        }
    except Exception as e:
        logger.warning("load_perf_summary: except Exception: %s", e, exc_info=True)
        return copy.deepcopy(_PERF_BASE)
def load_swallowed_summary() -> dict[str, Any]:
    events = _load_event_list(load_swallowed_exceptions, "load_swallowed_summary")
    if not events:
        return copy.deepcopy(_SWALLOWED_BASE)
    by_module: dict[str, int] = {}
    by_exc_type: dict[str, int] = {}
    for ev in events:
        payload = _payload_dict(ev)
        module = normalize_group_key(
            payload.get("module") or ev.get("logger") or "unknown")
        exc_type = _payload_str(payload, "exc_type")
        by_module[module] = by_module.get(module, 0) + 1
        by_exc_type[exc_type] = by_exc_type.get(exc_type, 0) + 1
    high_freq = _top_freq(by_module)
    return {
        "total": len(events),
        "by_module": by_module,
        "by_exc_type": by_exc_type,
        "high_freq_modules": high_freq,
    }
def load_bug_intercept_summary() -> dict[str, Any]:
    events = _load_event_list(load_bug_intercepts, "load_bug_intercept_summary")
    if not events:
        return copy.deepcopy(_BUG_INTERCEPT_BASE)
    by_check: dict[str, int] = {}
    by_severity: dict[str, int] = {}
    for ev in events:
        payload = ev.get("payload", {})
        check_id = _payload_str(payload, "check_id")
        severity = _payload_str(payload, "severity")
        by_check[check_id] = by_check.get(check_id, 0) + 1
        by_severity[severity] = by_severity.get(severity, 0) + 1
    high_freq = _top_freq(by_check)
    return {
        "total": len(events),
        "by_check": by_check,
        "by_severity": by_severity,
        "high_freq": high_freq,
    }
_LOG_QUALITY_BASE: dict[str, Any] = {
    "quality_score": _UNMEASURED_METRIC, "issues": [],
    "total_entries": 0, "field_completeness": _UNMEASURED_METRIC,
    "parse_error_count": 0, "timestamp_disorder_count": 0,
    "chain_break_count": 0, "volume_anomaly": False,
}
_LOG_PATTERNS_BASE: dict[str, Any] = {"findings": [], "summary": {"total": 0}}
_LOG_BOTTLENECKS_BASE: dict[str, Any] = {
    "optimization_suggestions": [], "bottlenecks": [],
    "summary": {"bottleneck_count": 0},
}
def _load_source(loader, base: dict, label: str) -> dict[str, Any]:
    try:
        raw = loader()
    except Exception as e:
        logger.warning("日志质量数据源 %s 加载失败: %s", label, e, exc_info=True)
        raw = None
    return _as_dict(raw, base)
def _load_quality_sources() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    return (
        _load_source(check_log_quality, _LOG_QUALITY_BASE, "check_log_quality"),
        _load_source(lambda: analyze_log_patterns(advance_cursor=False),
                     _LOG_PATTERNS_BASE, "analyze_log_patterns"),
        _load_source(analyze_perf_bottlenecks, _LOG_BOTTLENECKS_BASE,
                     "analyze_perf_bottlenecks"),
    )
def _iter_dict_entries(seq: list):
    for item in seq:
        if isinstance(item, dict):
            yield item
def _assemble_log_improvements(issues: list, findings: list,
                               perf_suggestions: list) -> list[str]:
    return (
        [_log_issue_text(i) for i in _iter_dict_entries(issues)]
        + [_log_finding_text(f2) for f2 in _iter_dict_entries(findings)]
        + [_perf_suggestion_text(s) for s in _iter_dict_entries(perf_suggestions)]
    )
def _log_issue_text(issue: dict) -> str:
    return f"[日志改进] {issue.get('type') or ''}: {issue.get('detail') or ''}"
def _log_finding_text(finding: dict) -> str:
    return f"[日志发现] {finding.get('type') or ''}: {finding.get('suggestion') or ''}"
def _perf_suggestion_text(suggestion: dict) -> str:
    return (f"[性能优化] {suggestion.get('target') or ''}: "
            f"{suggestion.get('direction') or ''}"
            f"（优先级: {suggestion.get('priority') or ''}）")
def load_log_quality_summary() -> dict[str, Any]:
    quality, patterns, bottlenecks = _load_quality_sources()
    quality_score = safe_float(
        quality.get("quality_score"), _UNMEASURED_METRIC)
    if quality_score is None:
        quality_score = _UNMEASURED_METRIC
    field_completeness = safe_float(
        quality.get("field_completeness"), _UNMEASURED_METRIC)
    if field_completeness is None:
        field_completeness = _UNMEASURED_METRIC
    parse_error_count = _as_count_or(quality.get("parse_error_count"))
    timestamp_disorder_count = _as_count_or(
        quality.get("timestamp_disorder_count"))
    chain_break_count = _as_count_or(quality.get("chain_break_count"))
    total_entries = _as_count_or(quality.get("total_entries"))
    volume_anomaly = signal_bool(quality.get("volume_anomaly"))
    issues = as_list(quality.get("issues"))
    findings = as_list(patterns.get("findings"))
    perf_suggestions = as_list(bottlenecks.get("optimization_suggestions"))
    metrics_available = quality_score >= 0
    completeness_text = (
        f"{field_completeness:.2%}" if field_completeness >= 0
        else "不可度量")
    log_quality_risk = None
    if not metrics_available:
        log_quality_risk = (
            "[日志质量] 日志质量不可度量（质量采集通道未产出有效评分），"
            "不能按满分处理，请检查日志目录与质量采集链路")
    elif quality_score < _LOG_QUALITY_RISK_THRESHOLD:
        log_quality_risk = (
            f"[日志质量] 日志质量评分 {quality_score:.1f}/100 低于阈值 "
            f"{_LOG_QUALITY_RISK_THRESHOLD:.0f}"
            f"（字段完整性 {completeness_text}"
            f"，解析错误 {parse_error_count}"
            f"，断裂 {chain_break_count}）"
        )
    log_improvements = _assemble_log_improvements(
        issues, findings, perf_suggestions)
    return {
        "quality_score": quality_score,
        "metrics_available": metrics_available,
        "issues": issues,
        "total_entries": total_entries,
        "field_completeness": field_completeness,
        "parse_error_count": parse_error_count,
        "timestamp_disorder_count": timestamp_disorder_count,
        "chain_break_count": chain_break_count,
        "volume_anomaly": volume_anomaly,
        "log_findings": findings,
        "perf_suggestions": perf_suggestions,
        "log_quality_risk": log_quality_risk,
        "log_improvements": log_improvements,
    }
_GROWTH_BASE: dict[str, Any] = {
    "ok": False, "snapshot": {}, "degraded": False,
    "signals": [], "history_count": 0,
}
_DEGRADATION_ZERO: dict[str, Any] = {
    "avg_lines_growth": 0.0, "files_growth": 0.0, "lines_growth": 0.0,
    "continuous_growth": False, "short_term_degraded": False,
    "zero_baseline": False,
}
def _ratio_value(value: Any) -> float:
    return 0.0 if value is None else as_number(value, 0.0)
def _growth_pct(value: float | None) -> str:
    return "基线为 0（不可计算）" if value is None else f"{value * 100:.1f}%"
def load_growth_summary(project_root: str | None = None) -> dict[str, Any]:
    try:
        skill_root = project_root or _SKILL_ROOT
        if not skill_root or not os.path.isdir(skill_root):
            return copy.deepcopy(_GROWTH_BASE)
        monitor = GrowthMonitor(skill_root)
        snapshot = monitor.run(skill_root)
        if not snapshot.get("ok"):
            return {"ok": False, "snapshot": snapshot, "degraded": False,
                    "signals": [], "history_count": len(monitor.get_history())}
        deg = monitor.detect_degradation()
        return {
            "ok": True,
            "snapshot": {k: snapshot.get(k) for k in
                         ("py_files", "total_lines", "avg_lines_per_file", "timestamp")},
            "degraded": bool(deg.get("degraded")),
            "signals": as_sequence(deg.get("signals")),
            "history_count": len(monitor.get_history()),
        }
    except Exception as e:
        logger.warning("load_growth_summary: %s", e, exc_info=True)
        return copy.deepcopy(_GROWTH_BASE)
_GROWTH_EXCLUDED_DIRS = SCAN_COLLECT_PRUNE_DIRS_LOWER | frozenset({"_build", "env.bak"})
class GrowthMonitor:
    _HISTORY_FILE = "_growth_history.json"
    _MAX_HISTORY = 200
    _MIN_HISTORY_SNAPSHOTS = 2
    _RECENT_GROWTH_SNAPSHOTS = 5
    _GROWTH_CONFIRM_SNAPSHOTS = 3
    _AVG_LINES_GROWTH_LIMIT = 0.3
    _FRAGMENTED_FILES_GROWTH_LIMIT = 0.1
    _FRAGMENTED_LINES_RATIO = 0.5
    _SHORT_TERM_GROWTH_RATIO = 1.1
    def __init__(self, project_path: str = "") -> None:
        self._project_path = project_path
        self._history: list[dict] = []
        if project_path:
            self.load_history()
    def run(self, project_path: str = "") -> dict:
        path = project_path or self._project_path
        if not path:
            return {"ok": False, "engine": "GrowthMonitor",
                    "error": "未提供项目路径（拒绝以进程当前目录兜底）"}
        if not os.path.isdir(path):
            return {"ok": False, "engine": "GrowthMonitor",
                    "error": f"路径不存在或不是目录: {path}"}
        self._rebase_if_needed(project_path)
        py_files, total_lines, counted_files = self._count_py_scale(path)
        if py_files > 0 and counted_files == 0:
            return {
                "ok": False, "engine": "GrowthMonitor", "project_path": path,
                "py_files": py_files, "total_lines": 0,
                "counted_files": counted_files,
                "error": "所有 Python 文件均不可读，拒绝记录零值增长快照",
            }
        _snap_root = os.path.abspath(path)
        snapshot = {
            "ok": True,
            "engine": "GrowthMonitor",
            "project_path": path,
            "skill_dir": _snap_root,
            "round_start_ts": peek_round_start_ts(_snap_root),
            "py_files": py_files,
            "total_lines": total_lines,
            "avg_lines_per_file": round(total_lines / max(counted_files, 1), 1),
            "timestamp": now_iso(),
        }
        self._record_snapshot(snapshot)
        return snapshot
    def _rebase_if_needed(self, project_path: str) -> None:
        if not project_path:
            return
        if (self._project_path
                and self._normalized_base(project_path)
                == self._normalized_base(self._project_path)):
            return
        self._project_path = project_path
        self._history = []
        self.load_history()
    @staticmethod
    def _normalized_base(path: str) -> str:
        """项目根归一：realpath 解析符号链接，与 ``path_scoped_namespace`` 同口径。

        ``target_skills/jwsgj`` 是 ``user_skills/jwsgj`` 的链接，只用 abspath
        会把同一项目拆成两个归属。
        """
        return os.path.normcase(os.path.realpath(os.path.abspath(path)))
    def _filter_own_entries(self, entries: list[dict]) -> list[dict]:
        """共享账本里只回看本项目的增长快照。

        ``growth_history`` 是反哺进化的共享节，而 ``py_files``/``total_lines``
        是项目规模指标；跨项目混算会让增长率与碎片化趋势失真。快照自带
        ``project_path``/``skill_dir`` 归属，无归属的旧条目保守丢弃。
        """
        base = self._normalized_base(self._project_path)
        own: list[dict] = []
        for entry in entries:
            owner = str(
                entry.get("project_path") or entry.get("skill_dir") or "")
            if owner and self._normalized_base(owner) == base:
                own.append(entry)
        return own
    @staticmethod
    def _read_py_line_count(fp: str) -> int | None:
        text, _fp = read_source_with_fingerprint(fp)
        return None if text is None else count_lines(text)
    @staticmethod
    def _iter_py_files(path: str):
        def _on_walk_error(exc: OSError) -> None:
            logger.warning("GrowthMonitor.run: 目录遍历失败跳过: %s", exc)
        for root, dirs, files in os.walk(path, onerror=_on_walk_error):
            prune_scan_dirnames(dirs, _GROWTH_EXCLUDED_DIRS)
            for f in files:
                if f.lower().endswith('.py'):
                    yield os.path.join(root, f)
    @classmethod
    def _count_py_scale(cls, path: str) -> tuple[int, int, int]:
        py_files = 0
        counted_files = 0
        total_lines = 0
        for fp in cls._iter_py_files(path):
            py_files += 1
            try:
                line_count = cls._read_py_line_count(fp)
            except (OSError, LookupError, UnicodeDecodeError) as exc:
                logger.warning("GrowthMonitor.run: 文件读取失败跳过: %s (%s)",
                               fp, exc)
                continue
            if line_count is None:
                logger.warning("GrowthMonitor.run: 文件读取失败跳过: %s (None)", fp)
                continue
            counted_files += 1
            total_lines += line_count
        return py_files, total_lines, counted_files
    @staticmethod
    def _ordered_history(entries: list[dict]) -> list[dict]:
        dated = [(parse_log_ts(entry.get("timestamp")), entry)
                 for entry in entries]
        if any(timestamp is None for timestamp, _entry in dated):
            return entries
        dated.sort(key=lambda item: item[0])
        return [entry for _timestamp, entry in dated]
    @classmethod
    def _snapshot_identity(cls, entry: dict) -> tuple[Any, ...]:
        owner = str(
            entry.get("project_path") or entry.get("skill_dir") or "")
        project_key = cls._normalized_base(owner) if owner else ""
        return (
            project_key,
            entry.get("timestamp"),
            entry.get("py_files"),
            entry.get("total_lines"),
            entry.get("avg_lines_per_file"),
        )
    @classmethod
    def _merge_history(cls, entries: list[dict], pending: list[dict]) -> list[dict]:
        merged = list(entries)
        for latest in pending:
            identity = cls._snapshot_identity(latest)
            matches = [
                index for index, entry in enumerate(merged)
                if entry == latest or cls._snapshot_identity(entry) == identity
            ]
            if not matches:
                merged.append(latest)
                continue
            merged[matches[0]] = latest
            for index in reversed(matches[1:]):
                merged.pop(index)
        return GrowthMonitor._ordered_history(merged)
    @classmethod
    def _trimmed(cls, entries: list[dict]) -> list[dict]:
        if len(entries) > cls._MAX_HISTORY:
            return [entries[0]] + entries[-(cls._MAX_HISTORY - 1):]
        return entries
    def _history_for_save(self, data: Any) -> list[dict]:
        if data is None:
            entries = []
        elif (not isinstance(data, list)
              or not all(isinstance(x, dict) for x in data)):
            raise ValueError("磁盘增长历史不可解析，拒绝覆盖既有基线")
        else:
            entries = data
        if entries:
            merged = self._merge_history(entries, list(self._history))
        else:
            merged = list(self._history)
        merged = self._trimmed(merged)
        # 保存载荷是跨项目共享账本；内存历史只保留本项目条目，与 load_history
        # 口径一致，避免保存后 detect_degradation 把其他项目的规模算进本项目趋势
        self._history = self._filter_own_entries(merged)
        return merged
    def _persist_history(self) -> bool:
        if not self._project_path or not self._history:
            return False
        try:
            saved, _history = update_evolution_section(
                self._project_path, "growth_history", self._history_for_save)
            return saved
        except Exception as e:
            logger.warning("GrowthMonitor 保存历史失败: %s", e)
            return False
    def _record_snapshot(self, snapshot: dict) -> bool:
        self._history.append(copy.deepcopy(snapshot))
        return self._persist_history()
    @staticmethod
    def _read_history_entries(project_path: str) -> list[dict] | None:
        try:
            data = read_evolution_section(project_path, "growth_history")
        except (OSError, ValueError, TypeError):
            return None
        if data is None:
            return []
        if not isinstance(data, list) or not all(isinstance(x, dict) for x in data):
            return None
        return data
    def load_history(self) -> bool:
        if not self._project_path:
            return False
        try:
            entries = self._read_history_entries(self._project_path)
            if entries is None:
                logger.warning(
                    "GrowthMonitor.load_history 结构异常（非 dict 元素列表），"
                    "降级空历史: %s", self._project_path)
                self._history = []
                return False
            entries = self._filter_own_entries(entries)
            if not entries:
                return False
            self._history = self._ordered_history(entries)
            return True
        except Exception as e:
            logger.warning("GrowthMonitor.load_history failed: %s", e)
            return False
    @staticmethod
    def _history_metric(entry: dict, key: str) -> float | None:
        value = safe_float(entry.get(key), None)
        return value if value is not None and value >= 0 else None
    @staticmethod
    def _growth_ratio(latest_v: float, earliest_v: float) -> float | None:
        if earliest_v > 0:
            return (latest_v - earliest_v) / earliest_v
        return None if latest_v > 0 else 0.0
    def _detect_continuous_growth(self) -> tuple[int, bool]:
        recent_count = min(self._RECENT_GROWTH_SNAPSHOTS,
                           len(self._history))
        if recent_count <= 0:
            return 0, False
        recent = self._history[-recent_count:]
        _line_seq = [self._history_metric(r, "total_lines") for r in recent]
        continuous_growth = (
            len(_line_seq) >= 2
            and all(value is not None for value in _line_seq)
            and all(_line_seq[i - 1] < _line_seq[i]
                    for i in range(1, len(_line_seq)))
        )
        return recent_count, continuous_growth
    def _compute_growth_metrics(self) -> dict[str, Any]:
        if len(self._history) < 2:
            return {
                **_DEGRADATION_ZERO,
                "avg_lines_degraded": False,
                "fragmented": False,
                "recent_count": 0,
            }
        latest = self._history[-1]
        earliest = self._history[0]

        def growth_for(key: str) -> float | None:
            latest_value = self._history_metric(latest, key)
            earliest_value = self._history_metric(earliest, key)
            if latest_value is None or earliest_value is None:
                return None
            return self._growth_ratio(latest_value, earliest_value)

        avg_lines_growth = growth_for("avg_lines_per_file")
        files_growth = growth_for("py_files")
        lines_growth = growth_for("total_lines")
        recent_count, continuous_growth = self._detect_continuous_growth()
        avg_lines_prev = self._history_metric(
            self._history[-2], "avg_lines_per_file")
        avg_lines_latest = self._history_metric(latest, "avg_lines_per_file")
        files_ratio = _ratio_value(files_growth)
        lines_ratio = _ratio_value(lines_growth)
        return {
            "avg_lines_growth": avg_lines_growth,
            "files_growth": files_growth,
            "lines_growth": lines_growth,
            "zero_baseline": any(
                value is None
                for value in (avg_lines_growth, files_growth, lines_growth)),
            "avg_lines_degraded": (
                avg_lines_growth is not None
                and avg_lines_growth > self._AVG_LINES_GROWTH_LIMIT),
            "fragmented": (
                files_growth is not None and lines_growth is not None
                and files_ratio > self._FRAGMENTED_FILES_GROWTH_LIMIT
                and lines_ratio < (files_ratio
                                   * self._FRAGMENTED_LINES_RATIO)),
            "recent_count": recent_count,
            "continuous_growth": continuous_growth,
            "short_term_degraded": (
                avg_lines_prev is not None and avg_lines_latest is not None
                and avg_lines_prev > 0
                and avg_lines_latest > (
                    avg_lines_prev * self._SHORT_TERM_GROWTH_RATIO)),
        }
    def _degradation_payload(self, *, degraded: bool, reason: str,
                            signals: list[str],
                            metrics: dict[str, Any]) -> dict:
        return {
            "degraded": degraded,
            "reason": reason,
            "signals": signals,
            "avg_lines_growth": round(
                _ratio_value(metrics.get("avg_lines_growth")), 4),
            "files_growth": round(
                _ratio_value(metrics.get("files_growth")), 4),
            "lines_growth": round(
                _ratio_value(metrics.get("lines_growth")), 4),
            "zero_baseline": bool(metrics.get("zero_baseline", False)),
            "continuous_growth": bool(metrics.get("continuous_growth", False)),
            "short_term_degraded": bool(metrics.get("short_term_degraded", False)),
            "history_count": len(self._history),
        }
    def detect_degradation(self) -> dict:
        if len(self._history) < self._MIN_HISTORY_SNAPSHOTS:
            return self._degradation_payload(
                degraded=False,
                reason=(f"历史数据不足（需要至少"
                        f"{self._MIN_HISTORY_SNAPSHOTS}次快照）"),
                signals=[],
                metrics=_DEGRADATION_ZERO,
            )
        m = self._compute_growth_metrics()
        _growth_confirmed = (
            m["continuous_growth"]
            and m["recent_count"] >= self._GROWTH_CONFIRM_SNAPSHOTS)
        degraded = (m["avg_lines_degraded"] or m["fragmented"]
                    or m["short_term_degraded"] or _growth_confirmed)
        return self._degradation_payload(
            degraded=degraded, reason="",
            signals=self._degradation_signals(m, _growth_confirmed), metrics=m)
    @classmethod
    def _degradation_signals(cls, metrics: dict[str, Any],
                             growth_confirmed: bool) -> list[str]:
        signal_specs = [
            (metrics["avg_lines_degraded"],
             f"平均文件行数增长 {_growth_pct(metrics['avg_lines_growth'])}（膨胀检测）"),
            (metrics["fragmented"],
             (f"文件数增长 {_growth_pct(metrics['files_growth'])} 但行数仅增长 "
              f"{_growth_pct(metrics['lines_growth'])}（碎片化）")),
            (growth_confirmed,
             f"最近 {metrics['recent_count']} 次快照显示规模持续增长"),
            (metrics["short_term_degraded"],
             ("最近一次快照平均文件行数增长超过 "
              f"{(cls._SHORT_TERM_GROWTH_RATIO - 1) * 100:.0f}%")),
        ]
        return [text for hit, text in signal_specs if hit]
    def get_history(self) -> list[dict]:
        return copy.deepcopy(self._history)
if __name__ == "__main__":
    result = run_log_driven_evolution()
    print(json.dumps(result, ensure_ascii=False, indent=2, default=str))

from __future__ import annotations

import logging
import math
import os
from dataclasses import asdict, dataclass, field
from datetime import datetime
from difflib import SequenceMatcher
from functools import partial
from typing import Any

from jwsgj.diag_detectors_registry import run_bounded_channel
from jwsgj.diag_guard_io import (
    atomic_write_text,
)
from jwsgj.diag_guard_state import (
    read_json_artifact,
    serialize_json,
)
from jwsgj.diag_types_normalize import (
    as_number,
    dict_or_empty,
    int_or,
)
from jwsgj.diag_types_vocab import (
    DEFAULT_FINDING_CONFIDENCE,
    FIELD_EXPECTED_IMPACT,
    FIELD_SUGGESTED_VALUE,
    RULE_TYPE_MAP,
    TYPE_ALL,
    HallucinationType,
)
from jwsgj.hallucination_norms import (
    HallucinationScanResult,
    boost_known_pattern_confidence,
    produce_cv_findings,
    scan_hallucinations,
)
from jwsgj.hallucination_prewrite import get_constraints_for_task
from jwsgj.log_config import log_swallowed
from jwsgj.retrospective_ledger import (
    append_pending_enhancements,
    enhancement_dedup_key,
    get_retrospective_history,
    load_retrospective_summary,
)
from jwsgj.runtime_paths import (
    hallucination_registry_path,
)
from jwsgj.runtime_scope import (
    collect_scan_py_files,
    is_scan_scope_path,
)
from jwsgj.shared_cache import (
    get_warmed_cache,
)
from jwsgj.shared_cache_store import (
    clean_pycache_before_scan,
)

__all__ = [
    "HallucinationPipelineResult",
    "HallucinationRecord",
    "HallucinationRegistry",
    "HallucinationRegistryEntry",
    "HallucinationStats",
    "HallucinationTracker",
    "get_hallucination_metrics",
    "get_hallucination_stats",
    "get_norm_iteration_suggestions",
    "get_tracker",
    "integrate_with_full_audit",
    "load_known_rule_ids",
    "register_hallucination_pattern",
    "run_hallucination_detector",
    "run_hallucination_pipeline",
    "track_hallucination_findings",
]
_log = logging.getLogger(__name__)
_PRIORITY_DOMAIN = frozenset({"P0", "P1", "P2", "P3"})
_RECORD_STATUS_DOMAIN = frozenset({"detected", "fixed", "rolled_back", "manual"})
_ENTRY_STATUS_DOMAIN = frozenset({"active", "mitigated", "resolved"})
_DEFAULT_RECORD_STATUS = "detected"
_DEFAULT_ENTRY_STATUS = "active"
_DEFAULT_SEVERITY = "P2"
_KNOWN_PATTERN_MIN_OCCURRENCES = 3
def _zero_count_bucket() -> dict[str, int]:
    return {"detected": 0, "fixed": 0, "rolled_back": 0}
@dataclass
class HallucinationRecord:
    rule_id: str
    hallucination_type: str
    severity: str
    title: str
    file_path: str
    line_num: int
    confidence: float
    status: str = _DEFAULT_RECORD_STATUS
    session_id: str = ""
    timestamp: str = ""
    suggestion: str = ""
@dataclass
class HallucinationRegistryEntry:
    pattern_id: str
    pattern: str
    hallucination_type: str
    detection_rule: str
    fix_strategy: str
    first_seen: str
    last_seen: str
    occurrences: int = 0
    status: str = _DEFAULT_ENTRY_STATUS
    example: str = ""
@dataclass
class HallucinationStats:
    total_detected: int = 0
    total_fixed: int = 0
    total_rolled_back: int = 0
    by_type: dict[str, dict[str, int]] = field(default_factory=dict)
    by_severity: dict[str, int] = field(default_factory=dict)
    by_rule: dict[str, int] = field(default_factory=dict)
    fix_rate: float = 0.0
    hallucination_rate: float = 0.0
    def __post_init__(self):
        if not isinstance(self.by_type, dict):
            self.by_type = {}
        if not isinstance(self.by_severity, dict):
            self.by_severity = {}
        if not isinstance(self.by_rule, dict):
            self.by_rule = {}
        for ht in TYPE_ALL:
            bucket = self.by_type.get(ht)
            if not isinstance(bucket, dict):
                bucket = {}
                self.by_type[ht] = bucket
            for key, default in _zero_count_bucket().items():
                bucket.setdefault(key, default)
        for severity in sorted(_PRIORITY_DOMAIN):
            self.by_severity.setdefault(severity, 0)
        self.refresh_rates()
    def refresh_rates(self, total_lines: int = 0) -> HallucinationStats:
        total_lines = int_or(total_lines, 0)
        self.fix_rate = (
            self.total_fixed / self.total_detected
            if self.total_detected > 0 else 0.0)
        self.hallucination_rate = (
            self.total_detected / total_lines * 1000
            if total_lines > 0 else 0.0)
        return self
def _norm_str(val, default: str = "") -> str:
    return val if isinstance(val, str) else default
def _norm_enum(val, domain: frozenset, default: str) -> str:
    s = (val if isinstance(val, str) else default).strip()
    if s in domain:
        return s
    folded = s.casefold()
    for candidate in domain:
        if candidate.casefold() == folded:
            return candidate
    return default
_norm_record_severity = partial(
    _norm_enum, domain=_PRIORITY_DOMAIN, default=_DEFAULT_SEVERITY)
def _norm_occurrences(value: Any) -> int:
    return max(0, int_or(value, 0))
_SEED_SEEN = "baseline"
_SEED_OCCURRENCES_ESTABLISHED = _KNOWN_PATTERN_MIN_OCCURRENCES
_SEED_OCCURRENCES_ONCE = 1
_SEED_ESTABLISHED_IDS: frozenset[str] = frozenset({
    "HC-001", "HC-003", "HC-004", "HC-006", "HC-007", "HC-009",
})
_PREDEFINED_PATTERN_SPECS: tuple[dict[str, Any], ...] = tuple(
    {
        "pattern_id": pid,
        "pattern": pattern,
        "hallucination_type": htype,
        "detection_rule": rule,
        "fix_strategy": strategy,
        "first_seen": _SEED_SEEN,
        "last_seen": _SEED_SEEN,
        "occurrences": (_SEED_OCCURRENCES_ESTABLISHED
                        if pid in _SEED_ESTABLISHED_IDS
                        else _SEED_OCCURRENCES_ONCE),
        "status": status,
        "example": example,
    }
    for pid, pattern, htype, rule, strategy, status, example in (
        ("HC-001",
         "调用不存在的函数/方法/别名（臆造辅助函数或近似拼写）",
         HallucinationType.NAMING.value, "H01",
         "搜索相似函数名→替换为真实函数", "mitigated",
         "调用了从未定义的辅助函数，且全库无导入与定义证据"),
        ("HC-002",
         "from X import * 后使用 _ 前缀符号",
         HallucinationType.RESOURCE.value, "H02",
         "显式导入或__all__声明", "resolved",
         "from module import * 后使用 _private_func"),
        ("HC-003",
         "except:pass静默吞掉NameError/ImportError",
         HallucinationType.LOGIC.value, "H03",
         "精确捕获+日志记录", "mitigated",
         "except Exception: pass — 吞掉幻觉 API 导致的 NameError"),
        ("HC-004",
         "exec沙箱移除__import__后getattr+__subclasses__仍可逃逸",
         HallucinationType.SECURITY.value, "H08",
         "移除globals/locals/vars/dir/setattr+AST拦截", "resolved",
         "exec 沙箱白名单残留 getattr 可经 __subclasses__ 链逃逸"),
        ("HC-005",
         "记忆记录'已实现'但函数从未定义（幻觉记忆）",
         HallucinationType.MEMORY.value, "H07",
         "AST验证记忆声明→修正记忆", "resolved",
         "记忆声明已实现并通过验证，源码中没有对应定义"),
        ("HC-006",
         "修复器缺自验证方法，声称'已修复'但未验证",
         HallucinationType.LOGIC.value, "H03",
         "每个修复器实现自验证方法", "mitigated",
         "修复器声称已修复，但缺少自验证方法或验证调用"),
        ("HC-007",
         "__init__.py wrapper函数体全部错位",
         HallucinationType.MAPPING.value, "H04",
         "纠正所有调用目标+函数内延迟导入", "resolved",
         "包装函数批量调用错误的底层目标"),
        ("HC-008",
         "json.dump缺default=str致中间文件静默不落盘",
         HallucinationType.LOGIC.value, "H03",
         "添加default=str参数+异常级别提升", "resolved",
         "json.dump 缺少 default=str 导致 TypeError 被外层 except 静默吞没"),
        ("HC-009",
         "函数体仅含pass/return常量/占位注释无实质逻辑",
         HallucinationType.AI_SLOP.value, "H05",
         "实现完整业务逻辑或标注为abstractmethod", "mitigated",
         "桩函数声明已实现，但函数体仅返回入参或占位常量"),
        ("HC-010",
         "测试用例使用硬编码期望值或跳过断言",
         HallucinationType.TEST_ILLUSION.value, "H06",
         "使用动态期望值+完整断言+覆盖率验证", "mitigated",
         "测试函数仅检查返回类型不验证返回值正确性"),
    )
)
def _predefined_patterns() -> list[HallucinationRegistryEntry]:
    return [HallucinationRegistryEntry(**spec)
            for spec in _PREDEFINED_PATTERN_SPECS]
def _entry_from_dict(
    ed: dict, pid: str, current: HallucinationRegistryEntry | None = None,
) -> HallucinationRegistryEntry:
    def text(key: str) -> str:
        value = ed.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
        return getattr(current, key, "")
    status_default = getattr(current, "status", _DEFAULT_ENTRY_STATUS)
    entry = HallucinationRegistryEntry(
        pattern_id=pid, pattern=text("pattern"),
        hallucination_type=text("hallucination_type"),
        detection_rule=text("detection_rule"), fix_strategy=text("fix_strategy"),
        first_seen=text("first_seen"), last_seen=text("last_seen"),
        occurrences=_norm_occurrences(ed.get("occurrences")),
        status=_norm_enum(ed.get("status", status_default),
                          _ENTRY_STATUS_DOMAIN, status_default),
        example=text("example"),
    )
    return entry
def _first_seen_sort_key(value: Any) -> tuple[int, str]:
    text = _norm_str(value)
    if text == _SEED_SEEN:
        return 0, ""
    return (1, text) if text else (2, "")
def _last_seen_sort_key(value: Any) -> tuple[int, str]:
    text = _norm_str(value)
    return (0, "") if not text or text == _SEED_SEEN else (1, text)
def _entry_is_fresh(
    incoming: HallucinationRegistryEntry,
    current: HallucinationRegistryEntry,
) -> bool:
    incoming_last = _norm_str(incoming.last_seen)
    return bool(incoming_last) and (
        _last_seen_sort_key(incoming_last)
        >= _last_seen_sort_key(_norm_str(current.last_seen)))
def _merge_registry_entry(
    current: HallucinationRegistryEntry,
    incoming: HallucinationRegistryEntry,
    *, take_text: bool = True,
    take_status: bool = False,
) -> bool:
    changed = False
    if take_text:
        for name in ("pattern", "hallucination_type", "detection_rule",
                     "fix_strategy", "example"):
            new = _norm_str(getattr(incoming, name, ""))
            if new and new != getattr(current, name, ""):
                setattr(current, name, new)
                changed = True
    first_seen = _norm_str(getattr(incoming, "first_seen", ""))
    current_first = _norm_str(getattr(current, "first_seen", ""))
    if _first_seen_sort_key(first_seen) < _first_seen_sort_key(current_first):
        current.first_seen = first_seen
        changed = True
    last_seen = _norm_str(getattr(incoming, "last_seen", ""))
    current_last = _norm_str(getattr(current, "last_seen", ""))
    if _last_seen_sort_key(last_seen) > _last_seen_sort_key(current_last):
        current.last_seen = last_seen
        changed = True
    occurrences = _norm_occurrences(getattr(incoming, "occurrences", 0))
    if occurrences > _norm_occurrences(getattr(current, "occurrences", 0)):
        current.occurrences = occurrences
        changed = True
    if take_status:
        status = _norm_enum(getattr(incoming, "status", ""),
                            _ENTRY_STATUS_DOMAIN, current.status)
        if status != current.status:
            current.status = status
            changed = True
    return changed
def _normalize_registry_entry(entry: HallucinationRegistryEntry) -> None:
    entry.pattern_id = _norm_str(entry.pattern_id).strip()
    for _n in ("pattern", "hallucination_type", "detection_rule",
               "fix_strategy", "first_seen", "last_seen", "example"):
        setattr(entry, _n, _norm_str(getattr(entry, _n, "")).strip())
    entry.occurrences = _norm_occurrences(getattr(entry, "occurrences", 0))
    entry.status = _norm_enum(getattr(entry, "status", ""),
                              _ENTRY_STATUS_DOMAIN, _DEFAULT_ENTRY_STATUS)
def _similarity_score(left: str, right: str) -> float:
    return SequenceMatcher(
        None, str(left or "").lower(), str(right or "").lower()).ratio()
def _registry_entries_payload(data: Any) -> list[dict] | None:
    if not isinstance(data, dict):
        _log.warning("幻觉注册表加载失败: 顶层结构非 dict (%s)",
                       type(data).__name__)
        return None
    entries = data.get("entries", [])
    if not isinstance(entries, list):
        _log.warning("幻觉注册表加载失败: entries 非列表 (%s)",
                       type(entries).__name__)
        return None
    return [ed for ed in entries if isinstance(ed, dict)]
class HallucinationRegistry:
    MAX_REGISTRY_ENTRIES = 200
    def __init__(self):
        self._entries: dict[str, HallucinationRegistryEntry] = {
            e.pattern_id: e for e in _predefined_patterns()
        }
    def _can_admit_new(self, pattern_id: str) -> bool:
        return (pattern_id in self._entries
                or len(self._entries) < self.MAX_REGISTRY_ENTRIES)
    def register(self, entry: HallucinationRegistryEntry) -> bool:
        _normalize_registry_entry(entry)
        if not entry.pattern_id:
            _log.warning(
                "拒绝注册无身份键的幻觉模式: %r",
                entry.pattern[:50])
            return False
        if not entry.pattern.strip():
            _log.warning(
                "拒绝注册无模式文本的幻觉模式: %s", entry.pattern_id)
            return False
        existing = self._entries.get(entry.pattern_id)
        if existing is not None:
            fresh = _entry_is_fresh(entry, existing)
            _merge_registry_entry(existing, entry,
                                  take_text=fresh, take_status=fresh)
            _log.info("合并幻觉模式: %s (occurrences=%d)",
                      entry.pattern_id, existing.occurrences)
            return True
        if not self._can_admit_new(entry.pattern_id):
            _log.debug(
                "注册表已满 %d，拒绝新模式: %s",
                self.MAX_REGISTRY_ENTRIES, entry.pattern_id)
            return False
        self._entries[entry.pattern_id] = entry
        _log.info("注册幻觉模式: %s (%s...)",
                    entry.pattern_id, entry.pattern[:50])
        return True
    def _load_single_entry(self, ed: dict) -> bool:
        pid = _norm_str(ed.get("pattern_id", "")).strip()
        if not pid:
            return False
        existing = self._entries.get(pid)
        if existing is not None:
            incoming = _entry_from_dict(ed, pid, current=existing)
            fresh = (bool(_norm_str(ed.get("last_seen")).strip())
                     and _entry_is_fresh(incoming, existing))
            _merge_registry_entry(existing, incoming,
                                  take_text=fresh, take_status=fresh)
            return False
        return self.register(_entry_from_dict(ed, pid))
    def find_similar(
        self, pattern: str, hallucination_type: str = ""
    ) -> HallucinationRegistryEntry | None:
        if not _norm_str(pattern).strip():
            return None
        best_match: HallucinationRegistryEntry | None = None
        best_score: float = 0.0
        for entry in self._entries.values():
            if hallucination_type and entry.hallucination_type != hallucination_type:
                continue
            score = _similarity_score(pattern, entry.pattern)
            if score > best_score:
                best_score = score
                best_match = entry
        if best_score >= 0.5:
            return best_match
        return None
    def get_by_status(self, status: str) -> list[HallucinationRegistryEntry]:
        return [e for e in self._entries.values() if e.status == status]
    def get_all(self) -> list[HallucinationRegistryEntry]:
        return list(self._entries.values())
    def get_known_pattern_ids(
            self, min_occurrences: int = _KNOWN_PATTERN_MIN_OCCURRENCES) -> set[str]:
        threshold = int_or(min_occurrences, _KNOWN_PATTERN_MIN_OCCURRENCES)
        return {rule for e in self._entries.values()
                if (rule := _norm_str(
                    getattr(e, "detection_rule", "")).strip())
                and _norm_occurrences(getattr(e, "occurrences", 0)) >= threshold}
    def to_dict(self) -> list[dict[str, Any]]:
        return [asdict(e) for e in self._entries.values()]
    def save_to_file(self, file_path: str) -> bool:
        try:
            data = {
                "version": "1.0",
                "saved_at": datetime.now().isoformat(),
                "entries": self.to_dict(),
            }
            os.makedirs(os.path.dirname(os.path.abspath(file_path)), exist_ok=True)
            atomic_write_text(
                file_path,
                serialize_json(data, indent=2),
                tag="HallucinationRegistry")
            _log.info("幻觉注册表持久化: %d条 → %s", len(self._entries), file_path)
            return True
        except (OSError, TypeError, UnicodeEncodeError) as e:
            _log.warning("幻觉注册表持久化失败: %s", e)
            return False
    def load_from_file(self, file_path: str) -> int:
        try:
            data, _status, _ = read_json_artifact(file_path)
            if _status != "ok":
                return 0
            entries_data = _registry_entries_payload(data)
            if entries_data is None:
                return 0
            loaded = 0
            for ed in entries_data:
                if self._load_single_entry(ed):
                    loaded += 1
            _log.info("幻觉注册表加载: %s → 新增 %d 条（其余已存在）",
                      file_path, loaded)
            return loaded
        except (OSError, TypeError, UnicodeDecodeError, RecursionError) as e:
            _log.warning("幻觉注册表加载失败: %s", e)
            return 0
def _count_by_field(rows: list[dict[str, Any]], field_name: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for row in rows:
        key = _norm_str(row.get(field_name)).strip() if isinstance(row, dict) else ""
        if not key:
            continue
        counts[key] = counts.get(key, 0) + 1
    return counts
def _accumulate_record_stats(record, stats: HallucinationStats) -> None:
    stats.total_detected += 1
    h_type = _norm_str(getattr(record, "hallucination_type", "")) or "logic"
    severity = _norm_record_severity(getattr(record, "severity", ""))
    rule_id = _norm_str(getattr(record, "rule_id", ""))
    status = _norm_enum(getattr(record, "status", ""), _RECORD_STATUS_DOMAIN,
                        _DEFAULT_RECORD_STATUS)
    bucket = stats.by_type.get(h_type)
    if bucket is None:
        bucket = _zero_count_bucket()
        stats.by_type[h_type] = bucket
    bucket["detected"] += 1
    if status == "fixed":
        stats.total_fixed += 1
        bucket["fixed"] += 1
    elif status == "rolled_back":
        stats.total_rolled_back += 1
        bucket["rolled_back"] += 1
    stats.by_severity[severity] = stats.by_severity.get(severity, 0) + 1
    if rule_id:
        stats.by_rule[rule_id] = stats.by_rule.get(rule_id, 0) + 1
def _session_filter(session_ids) -> frozenset[str] | None:
    if session_ids is None:
        return None
    if isinstance(session_ids, str):
        return frozenset({session_ids}) if session_ids else frozenset()
    try:
        return frozenset(str(sid) for sid in session_ids)
    except TypeError as _e:
        _log.warning("会话过滤条件不可迭代(按空集处理): %r: %s",
                     session_ids, _e)
        return frozenset()
def _accumulate_trend_record(record, session_ids, sessions, first_seen) -> None:
    sid = record.session_id or "unknown"
    if session_ids is not None and sid not in session_ids:
        return
    bucket = _ensure_trend_bucket(sid, record.timestamp, sessions, first_seen)
    bucket["detected"] += 1
    if record.status in ("fixed", "rolled_back"):
        bucket[record.status] += 1
def _ensure_trend_bucket(sid: str, timestamp: str | None,
                         sessions: dict[str, dict[str, int]],
                         first_seen: dict[str, str]) -> dict[str, int]:
    bucket = sessions.get(sid)
    if bucket is None:
        bucket = _zero_count_bucket()
        sessions[sid] = bucket
        first_seen[sid] = timestamp or ""
        return bucket
    ts = timestamp or ""
    if ts and (not first_seen[sid] or ts < first_seen[sid]):
        first_seen[sid] = ts
    return bucket
class HallucinationTracker:
    def __init__(self):
        self._records: list[HallucinationRecord] = []
        self._registry = HallucinationRegistry()
        self._registry_scope: str | None = None
        self._norm_violations: list[dict[str, Any]] = []
        self._registered_upto: int = 0
    def bind_registry_scope(self, scope_key: str) -> HallucinationRegistry:
        if self._registry_scope is not None and scope_key != self._registry_scope:
            self._registry = HallucinationRegistry()
            self._records.clear()
            self._norm_violations.clear()
            self._registered_upto = 0
        self._registry_scope = scope_key
        return self._registry
    def record_finding(
        self,
        rule_id: str,
        hallucination_type: str,
        severity: str,
        title: str,
        file_path: str,
        line_num: int,
        confidence: float = DEFAULT_FINDING_CONFIDENCE,
        session_id: str = "",
        suggestion: str = "",
    ) -> HallucinationRecord:
        confidence = self._clamp_confidence(confidence)
        rule_id = _norm_str(rule_id).strip()
        hallucination_type = _norm_str(hallucination_type).strip()
        if not hallucination_type:
            hallucination_type = RULE_TYPE_MAP.get(rule_id, "logic")
        record = HallucinationRecord(
            rule_id=rule_id,
            hallucination_type=hallucination_type,
            severity=_norm_record_severity(severity),
            title=_norm_str(title),
            file_path=_norm_str(file_path),
            line_num=max(0, int_or(line_num, 0)),
            confidence=confidence,
            session_id=_norm_str(session_id),
            timestamp=datetime.now().isoformat(),
            suggestion=_norm_str(suggestion),
        )
        self._records.append(record)
        return record
    @staticmethod
    def _clamp_confidence(confidence) -> float:
        if (isinstance(confidence, bool) or not isinstance(confidence, (int, float))
                or (isinstance(confidence, float) and not math.isfinite(confidence))):
            return DEFAULT_FINDING_CONFIDENCE
        return float(max(0.0, min(1.0, confidence)))
    def record_norm_violation(
        self, rule_id: str, category: str, severity: str,
        name: str, detail: str,
    ) -> None:
        self._norm_violations.append({
            "rule_id": _norm_str(rule_id),
            "category": _norm_str(category),
            "severity": _norm_record_severity(severity),
            "name": _norm_str(name),
            "detail": _norm_str(detail),
            "timestamp": datetime.now().isoformat(),
        })
    def update_status(self, record_index: int, status: str) -> None:
        if isinstance(record_index, bool) or not isinstance(record_index, int):
            raise TypeError(f"record_index 非 int: {type(record_index).__name__}")
        if 0 <= record_index < len(self._records):
            record = self._records[record_index]
            record.status = _norm_enum(
                status, _RECORD_STATUS_DOMAIN, record.status)
            return
        _log.debug("忽略越界记录索引: %d（当前 %d 条）",
                   record_index, len(self._records))
    def register_discovered_patterns(self) -> int:
        existing_ids = {e.pattern_id for e in self._registry.get_all()}
        new_count = 0
        for record in self._records[self._registered_upto:]:
            new_count += self._absorb_record(record, existing_ids)
        self._registered_upto = len(self._records)
        return new_count
    def _absorb_record(self, record, existing_ids: set[str]) -> int:
        similar = self._registry.find_similar(
            record.title or "", record.hallucination_type or "")
        if similar:
            similar.occurrences += 1
            similar.last_seen = datetime.now().isoformat()
            return 0
        entry = self._build_discovered_entry(record, existing_ids)
        if not self._registry.register(entry):
            return 0
        existing_ids.add(entry.pattern_id)
        return 1
    def _build_discovered_entry(self, record,
                                existing_ids: set[str] | None = None) -> HallucinationRegistryEntry:
        if existing_ids is None:
            existing_ids = {e.pattern_id for e in self._registry.get_all()}
        seq = len(existing_ids) + 1
        while f"HC-DISC-{seq:03d}" in existing_ids:
            seq += 1
        now_iso = datetime.now().isoformat()
        return HallucinationRegistryEntry(
            pattern_id=f"HC-DISC-{seq:03d}",
            pattern=str(record.title or "")[:200],
            hallucination_type=record.hallucination_type or "logic",
            detection_rule=record.rule_id or "",
            fix_strategy=str(record.suggestion or "")[:200],
            first_seen=now_iso,
            last_seen=now_iso,
            occurrences=1,
            status=_DEFAULT_ENTRY_STATUS,
            example=f"{record.file_path}:{record.line_num}",
        )
    def get_known_pattern_ids_for_scope(
            self, scope_key: str,
            min_occurrences: int | None = None) -> set[str]:
        registry = (self._registry
                    if self._registry_scope in (None, scope_key)
                    else HallucinationRegistry())
        if min_occurrences is None:
            return registry.get_known_pattern_ids()
        return registry.get_known_pattern_ids(min_occurrences)
    def get_stats(self, total_lines: int = 0) -> HallucinationStats:
        stats = HallucinationStats()
        for record in self._records:
            _accumulate_record_stats(record, stats)
        return stats.refresh_rates(total_lines)
    def get_norm_stats(self) -> dict[str, Any]:
        return {
            "total": len(self._norm_violations),
            "by_category": _count_by_field(self._norm_violations, "category"),
            "by_severity": _count_by_field(self._norm_violations, "severity"),
            "by_rule": _count_by_field(self._norm_violations, "rule_id"),
        }
    @property
    def registry(self) -> HallucinationRegistry:
        return self._registry
    def get_trend(self, session_ids: list[str] | None = None) -> dict[str, Any]:
        sessions: dict[str, dict[str, int]] = {}
        first_seen: dict[str, str] = {}
        session_filter = _session_filter(session_ids)
        for record in self._records:
            _accumulate_trend_record(record, session_filter, sessions, first_seen)
        ordered = [
            sessions[sid] for sid in sorted(sessions, key=lambda s: first_seen[s])
        ]
        return {
            "sessions": sessions,
            "total_sessions": len(sessions),
            "trend": "improving" if len(ordered) >= 2 and
                     ordered[-1]["detected"] <= ordered[-2]["detected"]
                     else "unknown",
        }
_tracker = HallucinationTracker()
def get_tracker() -> HallucinationTracker:
    return _tracker
def track_hallucination_findings(
    findings: list[dict[str, Any]],
    session_id: str = "",
) -> None:
    tracker = get_tracker()
    for f in findings or []:
        if not isinstance(f, dict):
            continue
        tracker.record_finding(
            rule_id=f.get("rule_id"),
            hallucination_type=f.get("hallucination_type"),
            severity=f.get("severity"),
            title=f.get("title"),
            file_path=f.get("file_path"),
            line_num=f.get("line_num"),
            confidence=f.get("confidence", DEFAULT_FINDING_CONFIDENCE),
            session_id=session_id,
            suggestion=f.get("suggestion"),
        )
    tracker.register_discovered_patterns()
def register_hallucination_pattern(
    pattern_id: str,
    pattern: str,
    hallucination_type: str,
    detection_rule: str,
    fix_strategy: str,
    example: str = "",
) -> bool:
    tracker = get_tracker()
    now_iso = datetime.now().isoformat()
    pid = _norm_str(pattern_id).strip()
    if not _norm_str(pattern).strip():
        _log.warning("拒绝注册无模式文本的幻觉模式: %s", pid)
        return False
    existing = next(
        (e for e in tracker.registry.get_all() if e.pattern_id == pid), None)
    if existing is not None:
        payload = {name: value for name, value in (
            ("pattern", pattern), ("hallucination_type", hallucination_type),
            ("detection_rule", detection_rule),
            ("fix_strategy", fix_strategy), ("example", example),
        ) if _norm_str(value)}
        payload["occurrences"] = _norm_occurrences(existing.occurrences) + 1
        payload["last_seen"] = now_iso
        _merge_registry_entry(
            existing, _entry_from_dict(payload, pid),
            take_text=True, take_status=False)
        _log.info("追加幻觉观察: %s (occurrences=%d)",
                    pid, existing.occurrences)
        return True
    entry = _entry_from_dict({
        "pattern": pattern, "hallucination_type": hallucination_type,
        "detection_rule": detection_rule, "fix_strategy": fix_strategy,
        "example": example, "first_seen": now_iso, "last_seen": now_iso,
        "occurrences": 1, "status": _DEFAULT_ENTRY_STATUS}, pid)
    return tracker.registry.register(entry)
def get_hallucination_stats(total_lines: int = 0) -> dict[str, Any]:
    tracker = get_tracker()
    stats = tracker.get_stats(total_lines)
    norm_stats = tracker.get_norm_stats()
    trend = tracker.get_trend()
    return {
        "hallucination": asdict(stats),
        "norm_violations": norm_stats,
        "trend": trend,
        "registry_size": len(tracker.registry.get_all()),
    }
def load_known_rule_ids(skill_dir: str) -> set[str]:
    root = (os.fsdecode(os.fspath(skill_dir))
            if isinstance(skill_dir, (str, os.PathLike)) else "")
    scope_key = os.path.normcase(os.path.abspath(root)) if root else ""
    try:
        known_ids = get_tracker().get_known_pattern_ids_for_scope(scope_key)
    except Exception as e:
        _log.warning("获取内存幻觉模式失败(非阻断，继续使用文件注册表): %s",
                     e, exc_info=True)
        known_ids = set()
    if not root:
        return known_ids
    registry = HallucinationRegistry()
    try:
        _reg_path = hallucination_registry_path(root)
        if os.path.isfile(_reg_path):
            loaded_count = registry.load_from_file(_reg_path)
            if loaded_count:
                _log.info("加载%s条历史幻觉模式", loaded_count)
            known_ids.update(registry.get_known_pattern_ids())
    except Exception as e:
        _log.warning("加载幻觉注册表失败(非阻断，继续使用内存模式集): %s",
                     e, exc_info=True)
    return known_ids
@dataclass
class HallucinationPipelineResult:
    constraints: list[dict[str, str]] = field(default_factory=list)
    scan_results: dict[str, HallucinationScanResult] = field(default_factory=dict)
    tracking: dict[str, Any] = field(default_factory=dict)
    norm_suggestions: list[dict[str, str]] = field(default_factory=list)
    norm_suggestions_queued: int = 0
    total_findings: int = 0
    total_norm_violations: int = 0
    is_blocked: bool = False
def get_norm_iteration_suggestions() -> list[dict[str, Any]]:
    tracker = get_tracker()
    norm_stats = tracker.get_norm_stats()
    suggestions: list[dict[str, Any]] = []
    suggestions.extend(_norm_rule_violation_suggestions(norm_stats.get("by_rule", {})))
    hall_stats = tracker.get_stats()
    suggestions.extend(_new_fixer_suggestions(hall_stats))
    suggestions.extend(_enhance_fixer_suggestions(hall_stats))
    return suggestions
def _norm_rule_violation_suggestions(by_rule: dict) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for rule_id, count in sorted(by_rule.items(), key=lambda x: -x[1]):
        if count >= 3 and rule_id.strip():
            out.append({
                "rule_id": rule_id,
                "suggestion": f"铁律 {rule_id} 被违反 {count} 次，建议增强检查函数或在提示词中加强约束",
                "priority": "high" if count >= 5 else "medium",
                "evidence": {"kind": "norm_violation",
                             "rule_id": rule_id,
                             "violation_count": count},
                "suggested_value": (
                    f"增强铁律 {rule_id} 的检查函数检测面，"
                    f"并在编写前约束注入中加强该条提示"),
                "expected_impact": (
                    f"铁律 {rule_id} 高频违反（{count} 次）得到针对性"
                    f"防控，编写时拦截率提升，诊断后修复量下降"),
                "action_type": "process_improve",
            })
    return out
def _type_advice(*, branch: str, h_type: str, counts: dict[str, int],
                 priority: str, headline: str, suggested_value: str,
                 expected_impact: str) -> dict[str, Any]:
    return {
        "rule_id": branch,
        "suggestion": headline,
        "priority": priority,
        "evidence": {"kind": "hallucination_type",
                     "hallucination_type": h_type,
                     "detected": counts["detected"],
                     "fixed": counts["fixed"]},
        "suggested_value": suggested_value,
        "expected_impact": expected_impact,
        "action_type": "process_improve",
    }
def _bucket_counts(counts: Any) -> dict[str, int]:
    bucket = dict_or_empty(counts)
    return {"detected": _metric_count(bucket.get("detected")),
            "fixed": _metric_count(bucket.get("fixed"))}
def _new_fixer_suggestions(hall_stats) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for h_type, counts in dict_or_empty(getattr(hall_stats, "by_type", {})).items():
        bucket = _bucket_counts(counts)
        if bucket["detected"] > 0 and bucket["fixed"] == 0:
            out.append(_type_advice(
                branch="NEW", h_type=h_type, counts=bucket,
                priority="high",
                headline=(f"幻觉类型 '{h_type}' 检测到 {bucket['detected']} 次"
                          f"但修复率为0，建议新增专用修复器"),
                suggested_value=f"为幻觉类型 '{h_type}' 新增专用修复器",
                expected_impact=(
                    f"'{h_type}' 类幻觉（已检出 {bucket['detected']} 次）"
                    f"从不可修复转为可自动修复，修复率脱离 0%")))
    return out
def _enhance_fixer_suggestions(hall_stats) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for h_type, counts in dict_or_empty(getattr(hall_stats, "by_type", {})).items():
        bucket = _bucket_counts(counts)
        if (bucket["detected"] >= 3
                and 0 < bucket["fixed"] < bucket["detected"] * 0.5):
            out.append(_type_advice(
                branch="ENHANCE", h_type=h_type, counts=bucket,
                priority="medium",
                headline=(f"幻觉类型 '{h_type}' 修复率 "
                          f"{bucket['fixed']}/{bucket['detected']} < 50%，"
                          f"建议增强修复器能力"),
                suggested_value=(
                    f"增强幻觉类型 '{h_type}' 现有修复器的覆盖率与成功率"),
                expected_impact=(
                    f"'{h_type}' 类幻觉修复率从 "
                    f"{bucket['fixed']}/{bucket['detected']} 提升至 50% 以上")))
    return out
def _global_stats_digest() -> dict[str, Any]:
    try:
        _trk = get_tracker()
        _hst = _trk.get_stats()
        _by_rule = dict_or_empty(_trk.get_norm_stats()).get("by_rule") or {}
        return {
            "fix_rate": round(_metric_rate(getattr(_hst, "fix_rate", 0)), 4),
            "total_detected": _metric_count(getattr(_hst, "total_detected", 0)),
            "total_fixed": _metric_count(getattr(_hst, "total_fixed", 0)),
            "norm_by_rule_top": dict(sorted(
                ((_k, _metric_count(_v))
                 for _k, _v in dict_or_empty(_by_rule).items()),
                key=lambda _kv: -_kv[1])[:5]),
            "hallucination_by_type": {
                _t: {"detected": _metric_count(_c.get("detected")),
                     "fixed": _metric_count(_c.get("fixed"))}
                for _t, _c in dict_or_empty(getattr(_hst, "by_type", {})).items()
                if isinstance(_c, dict)
                and (_metric_count(_c.get("detected"))
                     or _metric_count(_c.get("fixed")))
            },
        }
    except Exception as _e:
        log_swallowed(__name__, _e,
                      context='_global_stats_digest')
        return {}
def _load_retro_context(target_path: str) -> dict[str, Any]:
    try:
        _retro_ctx = load_retrospective_summary(target_path)
        return _retro_ctx if isinstance(_retro_ctx, dict) else {}
    except Exception as _e:
        log_swallowed(__name__, _e,
                      context='_load_retro_context')
        return {}
_PRIORITY_CONFIDENCE = {"high": 0.8, "medium": 0.6}
def _suggest_text(s: dict, key: str, fallback: str = "") -> str:
    return str(s.get(key, fallback) or fallback)
def _build_norm_enhancement_entry(s: Any, session_id: str,
                                  global_digest: dict[str, Any],
                                  retro_ctx: dict[str, Any]) -> dict[str, Any] | None:
    if not (isinstance(s, dict) and s.get("suggestion")):
        return None
    _rid = _suggest_text(s, "rule_id")
    _prio = _suggest_text(s, "priority", "medium")
    _dc = _norm_diagnosis_context(s, _rid, _prio, global_digest)
    _entry = {
        "target": f"hallucination_norm:{_rid}",
        "description": _suggest_text(s, "suggestion"),
        "status": "pending",
        "source": "run_hallucination_pipeline",
        "priority": _prio,
        "session_id": session_id,
        "rule_id": _rid,
        "action_type": _suggest_text(s, "action_type", "process_improve"),
        "confidence": _PRIORITY_CONFIDENCE.get(_prio, 0.6),
        FIELD_SUGGESTED_VALUE: _suggest_text(s, "suggested_value"),
        FIELD_EXPECTED_IMPACT: _suggest_text(s, "expected_impact"),
        "phase": "hallucination_review",
        "diagnosis_context": _dc,
    }
    if retro_ctx:
        _entry["retrospective_context"] = dict(retro_ctx)
    return _entry
def _norm_diagnosis_context(s: Any, _rid: str, _prio: str,
                            global_digest: dict[str, Any]) -> dict:
    _ev = s.get("evidence")
    _dc: dict = {
        "rule_id": _rid,
        "priority": _prio,
        "evidence": _ev if isinstance(_ev, dict) else {},
    }
    if global_digest:
        _dc["global_stats_digest"] = global_digest
    return _dc
def _filter_settled_norm_entries(
        target_path: str, entries: list[dict[str, Any]]) -> list[dict[str, Any]]:
    try:
        settled = {
            enhancement_dedup_key(e)
            for e in get_retrospective_history(target_path).get("entries", [])
            if isinstance(e, dict) and e.get("status") in ("applied", "rejected")
        }
        return [e for e in entries
                if enhancement_dedup_key(e) not in settled]
    except Exception as e:
        _log.warning("读取增强历史失败(不过滤入队): %s", e, exc_info=True)
        return entries
def _enqueue_norm_suggestions(target_path: str, session_id: str,
                              suggestions: list[dict[str, str]]) -> int:
    _global_digest = _global_stats_digest()
    _retro_ctx = _load_retro_context(target_path)
    entries: list[dict] = []
    for s in suggestions:
        _entry = _build_norm_enhancement_entry(
            s, session_id, _global_digest, _retro_ctx)
        if _entry is not None:
            entries.append(_entry)
    entries = _filter_settled_norm_entries(target_path, entries)
    try:
        return append_pending_enhancements(target_path, entries)
    except Exception as e:
        _log.warning("规范迭代建议入队失败(非阻断): %s", e, exc_info=True)
    return 0
def _scope_dir_for_target(target_path: str) -> str:
    return (target_path if os.path.isdir(target_path)
            else os.path.dirname(os.path.abspath(target_path)))
def _resolve_registry_path(target_path: str) -> str | None:
    if not os.path.isdir(target_path):
        return None
    try:
        return hallucination_registry_path(target_path)
    except RuntimeError as e:
        _log.warning("幻觉注册表路径不可用(非阻断，跳过跨会话注册表): %s", e)
        return None
def _scan_pipeline_files(result: HallucinationPipelineResult,
                         target_path: str) -> list[dict[str, Any]]:
    all_findings: list[dict[str, Any]] = []
    py_files = collect_scan_py_files(target_path)
    if not py_files:
        result.is_blocked = True
        reason = ("单文件目标不是可扫描的 .py 文件"
                  if os.path.isfile(target_path) else "没有可扫描的 Python 文件")
        _log.warning("幻觉扫描%s %s；结果未知，整体按阻断处理",
                     reason, target_path)
        return all_findings
    for py_file in py_files:
        try:
            scan_result = scan_hallucinations(py_file)
        except Exception as e:
            result.is_blocked = True
            _log.warning(
                "幻觉扫描失败 %s: %s；该文件结果未知，整体按阻断处理",
                py_file, e, exc_info=True)
            continue
        if not isinstance(scan_result, HallucinationScanResult):
            result.is_blocked = True
            _log.warning(
                "幻觉扫描返回非法结果 %s(%s)；该文件结果未知，整体按阻断处理",
                py_file, type(scan_result).__name__)
            continue
        result.scan_results[py_file] = scan_result
        if scan_result.blocked:
            result.is_blocked = True
        all_findings.extend(scan_result.hallucination_findings or [])
        result.total_norm_violations += len(scan_result.norm_violations or [])
    result.total_findings = len(all_findings)
    return all_findings
def _track_pipeline_findings(result: HallucinationPipelineResult,
                             all_findings: list[dict[str, Any]],
                             session_id: str) -> None:
    track_hallucination_findings(all_findings, session_id)
    tracker = get_tracker()
    for scan_result in result.scan_results.values():
        for v in scan_result.norm_violations or []:
            if not isinstance(v, dict):
                continue
            tracker.record_norm_violation(
                rule_id=v.get("rule_id", ""),
                category=v.get("category", ""),
                severity=v.get("severity", ""),
                name=v.get("name", ""),
                detail=v.get("detail", ""),
            )
    result.tracking = get_hallucination_stats()
def _capture_tracking_state(tracker: HallucinationTracker) -> dict[str, Any]:
    return {
        "records": tuple(tracker._records),
        "registry": tracker._registry,
        "registry_scope": tracker._registry_scope,
        "registry_entries": tuple(
            (pid, entry, dict(entry.__dict__))
            for pid, entry in tracker._registry._entries.items()),
        "norm_violations": tuple(tracker._norm_violations),
        "registered_upto": tracker._registered_upto,
    }
def _restore_tracking_state(
        tracker: HallucinationTracker, state: dict[str, Any],
) -> None:
    tracker._records[:] = state["records"]
    tracker._registry = state["registry"]
    tracker._registry_scope = state["registry_scope"]
    entries = tracker._registry._entries
    entries.clear()
    for pid, entry, values in state["registry_entries"]:
        entry.__dict__.clear()
        entry.__dict__.update(values)
        entries[pid] = entry
    tracker._norm_violations[:] = state["norm_violations"]
    tracker._registered_upto = state["registered_upto"]
def _load_registry_layer(registry_path: str | None) -> None:
    if not registry_path:
        return
    try:
        loaded_count = get_tracker().registry.load_from_file(registry_path)
        if loaded_count:
            _log.info("加载%s条历史幻觉模式", loaded_count)
    except Exception as e:
        _log.warning("加载幻觉注册表失败(非阻断): %s", e, exc_info=True)
def _warm_scan_cache(target_path: str) -> None:
    if not os.path.isdir(target_path):
        _log.debug("单文件目标跳过共享缓存预热（扫描按文件隔离）: %s",
                   target_path)
        return
    try:
        get_warmed_cache(target_path)
    except (RuntimeError, OSError, ValueError) as e:
        _log.warning(
            "共享缓存预热未通过(降级为逐文件解析，不阻断扫描): %s", e)
def _clean_pycache(target_path: str) -> None:
    try:
        cleaned = clean_pycache_before_scan(target_path)
    except Exception as e:
        _log.warning("清理 __pycache__ 失败(非阻断): %s", e, exc_info=True)
        return
    if cleaned:
        _log.info("已清除 %s 个__pycache__目录", cleaned)
def _prepare_pipeline_run(
    target_path: str, clean_cache: bool,
) -> tuple[str, str | None]:
    if not os.path.exists(target_path):
        raise FileNotFoundError(
            f"run_hallucination_pipeline: target_path 不存在: {target_path!r}")
    _warm_scan_cache(target_path)
    if clean_cache:
        _clean_pycache(target_path)
    scope_dir = _scope_dir_for_target(target_path)
    registry_path = _resolve_registry_path(scope_dir)
    scope_key = os.path.normcase(os.path.abspath(scope_dir))
    get_tracker().bind_registry_scope(scope_key)
    _load_registry_layer(registry_path)
    return scope_dir, registry_path
def _known_pattern_ids() -> frozenset[str]:
    try:
        return frozenset(get_tracker().registry.get_known_pattern_ids())
    except Exception as e:
        _log.warning("获取已知模式集合失败(非阻断): %s", e, exc_info=True)
        return frozenset()
def run_hallucination_pipeline(
    target_path: str,
    session_id: str = "",
    clean_cache: bool = False,
    track_results: bool = True,
) -> HallucinationPipelineResult:
    tracker = get_tracker()
    tracking_state = _capture_tracking_state(tracker)
    result = HallucinationPipelineResult()
    completed = False
    try:
        scope_dir, registry_path = _prepare_pipeline_run(target_path, clean_cache)
        result.constraints = get_constraints_for_task(skill_dir=scope_dir)
        all_findings = _scan_pipeline_files(result, target_path)
        boost_known_pattern_confidence(all_findings, _known_pattern_ids())
        if track_results:
            _track_pipeline_findings(result, all_findings, session_id)
        result.norm_suggestions = get_norm_iteration_suggestions()
        if track_results and result.norm_suggestions and not result.is_blocked:
            result.norm_suggestions_queued = _enqueue_norm_suggestions(
                scope_dir, session_id, result.norm_suggestions)
        if result.is_blocked and registry_path:
            _log.warning(
                "幻觉扫描未完整完成，跳过注册表持久化: %s", registry_path)
        elif registry_path and track_results:
            try:
                tracker.registry.save_to_file(registry_path)
            except Exception as e:
                _log.warning("保存幻觉注册表失败(非阻断): %s", e, exc_info=True)
        completed = True
    finally:
        if not track_results or result.is_blocked or not completed:
            _restore_tracking_state(tracker, tracking_state)
            if track_results:
                result.tracking = get_hallucination_stats()
                result.norm_suggestions = get_norm_iteration_suggestions()
            if result.is_blocked:
                _log.warning("幻觉扫描阻断，本轮内存跟踪变更已回滚")
    return result
def _audit_integration_summary(pipeline_result) -> dict[str, Any]:
    return {
        "status": "blocked" if pipeline_result.is_blocked else "ok",
        "is_blocked": pipeline_result.is_blocked,
        "total_findings": pipeline_result.total_findings,
        "total_norm_violations": pipeline_result.total_norm_violations,
        "p0_findings": sum(
            1 for sr in pipeline_result.scan_results.values()
            for f in (sr.hallucination_findings or [])
            if isinstance(f, dict)
            and _norm_record_severity(f.get("severity")) == "P0"
        ),
        "tracking": pipeline_result.tracking,
        "norm_suggestions": pipeline_result.norm_suggestions,
        "norm_suggestions_queued": pipeline_result.norm_suggestions_queued,
        "files_scanned": len(pipeline_result.scan_results),
        "constraints_injected": len(pipeline_result.constraints),
        "metrics": get_hallucination_metrics(pipeline_result),
    }
def integrate_with_full_audit(
    skill_dir: str,
    session_id: str = "",
) -> dict[str, Any]:
    pipeline_result = run_hallucination_pipeline(
        skill_dir,
        session_id=session_id,
        clean_cache=False,
        track_results=True,
    )
    return _audit_integration_summary(pipeline_result)
def get_hallucination_metrics(pipeline_result: HallucinationPipelineResult | None = None) -> dict[str, Any]:
    snapshot = (dict_or_empty(getattr(pipeline_result, "tracking", {}))
                if pipeline_result is not None else {})
    stats = (snapshot if pipeline_result is not None
             else dict_or_empty(get_hallucination_stats()))
    hall_stats = dict_or_empty(stats.get("hallucination"))
    norm_stats = dict_or_empty(stats.get("norm_violations"))
    metrics = {
        "hallucination_total": _metric_count(hall_stats.get("total_detected")),
        "hallucination_by_type": _hallucination_type_counts(hall_stats),
        "norm_violations": _metric_count(norm_stats.get("total")),
        "norm_by_category": dict_or_empty(norm_stats.get("by_category")),
        "detection_rate": 0.0,
        "fix_rate": _metric_rate(hall_stats.get("fix_rate")),
        "blocked": False,
    }
    if pipeline_result:
        _apply_pipeline_metrics(metrics, pipeline_result)
    return metrics
def _metric_count(value: Any, default: int = 0) -> int | float:
    return max(0, as_number(value, default))
def _metric_rate(value: Any, default: float = 0.0) -> float:
    parsed = as_number(value, default)
    return min(1.0, max(0.0, float(parsed)))
def _hallucination_type_counts(hall_stats: dict[str, Any]) -> dict[str, int | float]:
    by_type = dict_or_empty(hall_stats.get("by_type"))
    counts: dict[str, int | float] = {}
    for type_name in dict.fromkeys((*TYPE_ALL, *by_type)):
        bucket = by_type.get(type_name)
        counts[type_name] = (
            _metric_count(bucket.get("detected"))
            if isinstance(bucket, dict) else 0)
    return counts
def _apply_pipeline_metrics(metrics: dict[str, Any],
                            pipeline_result: HallucinationPipelineResult) -> None:
    total = _metric_count(getattr(pipeline_result, "total_findings", 0))
    if total > 0:
        total_norm = _metric_count(
            getattr(pipeline_result, "total_norm_violations", 0))
        metrics["detection_rate"] = round(
            _metric_rate(total / max(total + total_norm, 1)), 4)
    metrics["blocked"] = bool(getattr(pipeline_result, "is_blocked", False))
def run_hallucination_detector(skill_dir: str) -> list[dict]:
    def _produce() -> Any:
        findings = produce_cv_findings(
            skill_dir,
            include_file=partial(is_scan_scope_path, include_tests=False,
                                 root_dir=skill_dir),
            known_rule_ids=load_known_rule_ids(skill_dir))
        if not isinstance(findings, list):
            return findings
        normalized: list[dict] = []
        for f in findings:
            if not isinstance(f, dict):
                raise TypeError(
                    "幻觉检测器产出非 dict finding: "
                    f"{type(f).__name__}")
            item = dict(f)
            item["severity"] = _norm_record_severity(item.get("severity"))
            item["confidence"] = HallucinationTracker._clamp_confidence(
                item.get("confidence"))
            if not _norm_str(item.get("category")).strip():
                item["category"] = "hallucination"
            normalized.append(item)
        return normalized
    return run_bounded_channel(
        "hallucination_ledger", "run_hallucination_detector", _produce,
        label="H1 hallucination")
_log.info("hallucination_ledger 幻觉观测域已加载: %d 项导出", len(__all__))

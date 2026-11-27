from __future__ import annotations

import logging
import os
import re
from collections.abc import Callable, Iterable
from dataclasses import asdict, dataclass, field, is_dataclass, replace
from enum import Enum
from functools import partial
from pathlib import Path
from typing import Any, ClassVar, Self

from jwsgj.arch_coexistence_pairs import (
    run_arch_strategies,
    scan_config_files,
)
from jwsgj.arch_coexistence_scan import (
    ArchCoexistenceReport,
    ArchScanContext,
)
from jwsgj.build_code_quality import CodeCleaner
from jwsgj.build_discover_text_doc import DocCleaner
from jwsgj.cleanup_file_hygiene import (
    FileCleaner,
    require_skill_dir,
)
from jwsgj.cleanup_residue import (
    default_ai_review,
    enqueue_cleanup_plan,
    read_cleanup_plan,
    to_queue_priority,
    write_cleanup_plan,
)
from jwsgj.coexistence_detect import (
    NOISE_REFS,
    CoexistenceItem,
    CrossFileIndex,
    DefEntry,
    ScanContext,
    build_cross_file_index,
    is_unspecified_target,
    run_coexistence_strategies,
)
from jwsgj.diag_types_normalize import (
    normalize_str_seq,
    safe_confidence,
)
from jwsgj.pipeline_steps_phases import run_traced_entry
from jwsgj.runtime_scope import PROTECTED_CORE_FILES

__all__ = [
    'ARCH_DEFAULT_MIN_CONFIDENCE',
    'DEFAULT_MIN_CONFIDENCE',
    'AccuracyRecord',
    'AccuracyTracker',
    'ArchCoexistenceDetector',
    'CoexistenceCleaner',
    'CoexistenceDetector',
    'CoexistenceReport',
    'CoexistenceVerifier',
    'ConfidenceFilter',
    'ConfidenceLevel',
    'SafeCleaner',
    'SafeCleanupReport',
    'WhitelistManager',
    'arch_item_to_cleanup_plan',
    'coexistence_item_to_cleanup_plan',
    'enqueue_arch_coexistence_plans',
    'normalize_min_confidence',
    'quick_arch_coexistence_scan',
    'quick_cleanup',
    'quick_coexistence_scan',
]
DEFAULT_MIN_CONFIDENCE = 0.8
def normalize_min_confidence(
        value: object, default: float = DEFAULT_MIN_CONFIDENCE) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float, str)):
        return default
    return safe_confidence(value, default)
_log = logging.getLogger(__name__)
ARCH_DEFAULT_MIN_CONFIDENCE = 0.6
class ArchCoexistenceDetector:
    def __init__(self, skill_dir: str) -> None:
        self.skill_dir = os.path.abspath(str(require_skill_dir(skill_dir)))
        self._ctx = ArchScanContext(skill_dir=self.skill_dir)
    def detect(
            self, min_confidence: float | None = None
    ) -> ArchCoexistenceReport:
        min_confidence = normalize_min_confidence(
            min_confidence, ARCH_DEFAULT_MIN_CONFIDENCE)
        ctx = self._ctx = ArchScanContext(skill_dir=self.skill_dir)
        report = ArchCoexistenceReport(skill_dir=self.skill_dir)
        try:
            ctx.scan_files(report)
            config_files = scan_config_files(self.skill_dir, report)
            if ctx.modules or config_files:
                ctx.build_call_index()
                report.items.extend(run_arch_strategies(
                    ctx, min_confidence, config_files, report.errors))
                for item in report.items:
                    report.by_strategy[item.strategy] = report.by_strategy.get(item.strategy, 0) + 1
                report.items.sort(key=lambda x: x.confidence, reverse=True)
        except Exception as e:  # noqa: BLE001
            _log.warning("coexistence_cleaner:arch_detect: except Exception: %s", e,
                         exc_info=True)
            report.errors.append(f"检测异常: {type(e).__name__}: {e}")
        _log.info(
            "arch_coexistence detect 完成: files=%d items=%d errors=%d strategies=%s",
            report.total_files_scanned, len(report.items),
            len(report.errors), dict(sorted(report.by_strategy.items())))
        return report
@dataclass
class CoexistenceReport:
    skill_dir: str = ""
    total_files_scanned: int = 0
    total_definitions: int = 0
    items: list[CoexistenceItem] = field(default_factory=list)
    by_pattern: dict[str, int] = field(default_factory=dict)
    blocked_items: int = 0
    verified_items: int = 0
    errors: list[str] = field(default_factory=list)
    index_complete: bool = True
    @property
    def total_items(self) -> int:
        return len(self.items)
def _as_text(value: Any) -> str:
    if not value:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    if isinstance(value, str):
        return value
    return str(value)
def _whitelist_file_key(value: Any) -> str:
    text = _as_text(value)
    return os.path.normcase(os.path.normpath(text)) if text else ""
def _line_at(lines: Any, index: int) -> int:
    if isinstance(lines, (tuple, list)) and len(lines) > index:
        value = lines[index]
        if isinstance(value, int) and not isinstance(value, bool):
            return value
    return 0
def _deletion_scope(old_lines: Any) -> dict[str, int]:
    if not isinstance(old_lines, (tuple, list)) or len(old_lines) < 2:
        return {}
    start, end = old_lines[0], old_lines[1]
    if (not isinstance(start, int) or not isinstance(end, int)
            or isinstance(start, bool) or isinstance(end, bool)):
        return {}
    if start < 1 or end < start:
        return {}
    return {"line_count": end - start + 1, "end_line": end}
def coexistence_item_to_cleanup_plan(item: CoexistenceItem) -> dict:
    old_lines = item.old_lines or (0, 0)
    plan = {
        "file_path": item.old_file or "",
        "line": _line_at(old_lines, 0),
        "category": item.category or "coexistence",
        "operation": "remove_old_version",
        "description": f"新旧共存[{item.pattern_type}] {item.old_name} -> {item.new_name}",
        "suggestion": item.suggestion or item.reason or "",
        "symbol": item.old_name or "",
        "confidence": _normalize_item_confidence(item),
        "severity": to_queue_priority(item.severity),
        "verified": bool(item.verified),
        "verify_reason": item.reason or "",
    }
    plan.update(_deletion_scope(old_lines))
    return plan
def _item_value(item: Any, names: tuple[str, ...], default: Any = None) -> Any:
    if isinstance(item, dict):
        for name in names:
            if name in item and item[name] is not None:
                return item[name]
        return default
    for name in names:
        value = getattr(item, name, None)
        if value is not None:
            return value
    return default
def _first_positive_int(*values: Any) -> int:
    for value in values:
        if isinstance(value, int) and not isinstance(value, bool) and value > 0:
            return value
    return 0
def _normalize_item_confidence(item: Any) -> float:
    raw = _item_value(item, ("confidence",), None)
    if raw is None:
        return 1.0
    if isinstance(raw, bool):
        return 0.0
    return safe_confidence(raw, 0.0)
def _base_item_to_cleanup_plan(item: Any, default_file: str = "") -> dict[str, Any]:
    file_path = _as_text(
        _first_present(item, ("file_path", "file"))).strip()
    if not file_path:
        file_path = _as_text(default_file).strip()
    line_start = _first_positive_int(
        _item_value(item, ("line_start",), 0),
        _item_value(item, ("line",), 0),
        _item_value(item, ("lineno",), 0),
    )
    line_end = _first_positive_int(
        _item_value(item, ("end_line",), 0),
        _item_value(item, ("line_end",), 0),
        _item_value(item, ("end_lineno",), 0),
    )
    line_count = _first_positive_int(
        _item_value(item, ("line_count",), 0),
        _item_value(item, ("lines",), 0),
    )
    plan = {
        "file_path": file_path,
        "line": line_start,
        "category": _as_text(_item_value(item, ("category",), "")),
        "operation": _as_text(
            _first_present(
                item, ("operation", "action", "kind"), "cleanup")
        ) or "cleanup",
        "description": _as_text(
            _first_present(item, ("description", "message"))),
        "suggestion": _as_text(
            _first_present(item, ("suggestion", "reason"))),
        "confidence": _normalize_item_confidence(item),
        "severity": to_queue_priority(_item_value(item, ("severity",), None)),
        "symbol": _as_text(_first_present(item, ("symbol", "func_name"))),
    }
    if line_start >= 1:
        if line_end >= line_start:
            line_count = line_end - line_start + 1
        elif line_count > 0:
            line_end = line_start + line_count - 1
        if line_count > 0:
            plan["line_count"] = line_count
            plan["end_line"] = line_end
    return plan
def _enqueue_coexistence_plans(skill_dir: Path, report: CoexistenceReport) -> dict:
    try:
        verified_candidates = [it for it in report.items if it.verified]
        unverified = len(report.items) - len(verified_candidates)
        if unverified:
            _log.warning(
                "coexistence_cleaner: %d 个共存项未通过验证，禁止入队清理计划", unverified)
        whitelist = _default_whitelist()
        verified_items: list[CoexistenceItem] = []
        protected = 0
        for item in verified_candidates:
            if _item_whitelisted(whitelist, item):
                protected += 1
                continue
            verified_items.append(item)
        if protected:
            _log.info(
                "coexistence_cleaner: %d 个共存项命中保护名单，禁止入队", protected)
        plans = [coexistence_item_to_cleanup_plan(it) for it in verified_items]
        return _ai_review_enqueue_result(
            enqueue_cleanup_plan(
                str(skill_dir), plans, source="coexistence_cleaner"),
            "coexistence_cleaner")
    except Exception as e:  # noqa: BLE001
        _log.warning(
            "coexistence_cleaner.py:_enqueue_coexistence_plans: %s", e, exc_info=True
        )
        failed = default_ai_review(f"coexistence_cleaner 入队失败: {e}")
        failed.update({
            "plan_file": "",
            "blocked_items": 0,
            "require_confirm_items": 0,
        })
        return failed
def _dedup_items(items: list[CoexistenceItem]) -> list[CoexistenceItem]:
    seen: dict[tuple[str, int, int, str, str, str], CoexistenceItem] = {}
    for item in items:
        key = (
            item.old_file,
            _line_at(item.old_lines, 0),
            _line_at(item.old_lines, 1),
            item.pattern_type,
            item.old_name,
            item.new_name,
        )
        if key not in seen or item.confidence > seen[key].confidence:
            seen[key] = item
    return list(seen.values())
class CoexistenceVerifier:
    _UNLOCATED_TARGET_PATTERNS: ClassVar[frozenset[str]] = frozenset({
        "migration_marker", "conditional_routing", "dual_write_read",
    })
    _UNSPECIFIED_REASONS: ClassVar[dict[str, str]] = {
        "migration_marker": (
            "迁移标记 '{old}' 未指明替代目标，需人工确认迁移方向后再处理"
        ),
        "conditional_routing": (
            "条件路由 '{old}' 的 if/else 分支未识别到新版调用，"
            "需人工确认新实现方向后再处理"
        ),
    }
    _COMPOSITE_MIGRATION_REASONS: ClassVar[dict[str, str]] = {
        "conditional_routing": (
            "条件路由 '{old}' 的删除范围覆盖包含新旧分支的整个函数，"
            "不能按旧版本整体移除；需人工仅移除旧分支并迁移调用方"
        ),
        "dual_write_read": (
            "双写/双读 '{old}' 的删除范围覆盖包含新旧 API 调用的整个函数，"
            "不能按旧版本整体移除；需人工仅移除旧 API 调用并验证读写一致性"
        ),
    }
    def __init__(self) -> None:
        self._index: CrossFileIndex | None = None
        self._module_stems: frozenset[str] = frozenset()
    def set_index(self: Self, index: CrossFileIndex,
                  py_files: Iterable[str] = ()) -> None:
        self._index = index
        module_stems = {
            os.path.splitext(os.path.basename(entry.file_path))[0]
            for entries in index.definitions.values()
            for entry in entries
        }
        for file_path in py_files:
            path = Path(file_path)
            stem = path.parent.name if path.stem == "__init__" else path.stem
            if stem:
                module_stems.add(stem)
        self._module_stems = frozenset(module_stems)
    def verify(self: Self, item: CoexistenceItem) -> tuple[bool, str]:
        if self._index is None:
            return False, "索引未初始化"
        if item.pattern_type == "import_bridge":
            return self._verify_import_bridge(item)
        composite_reason = self._COMPOSITE_MIGRATION_REASONS.get(
            item.pattern_type)
        if composite_reason is not None:
            return False, composite_reason.format(old=item.old_name)
        if is_unspecified_target(item.new_name):
            return False, self._unspecified_target_reason(item)
        new_names = self._normalize_new_names(item.new_name)
        new_entries = self._resolve_new_entries(item, new_names)
        if not new_entries:
            if item.pattern_type not in self._UNLOCATED_TARGET_PATTERNS:
                return False, (
                    f"新版 '{item.new_name}' 定义无法在索引中精确定位，"
                    "需人工确认后再处理")
            return False, f"新版 '{item.new_name}' 不在代码库中"
        _independent_ok, _independent_reason = (
            self._has_independent_real_entry(item, new_entries))
        if not _independent_ok:
            return False, _independent_reason
        coverage_failure = self._coverage_failure(item, new_entries)
        if coverage_failure is not None:
            return False, coverage_failure
        return self._check_call_chain(item, new_names)
    def _resolve_new_entries(
        self: Self, item: CoexistenceItem, new_names: list[str]
    ) -> list[DefEntry]:
        if item.pattern_type not in self._UNLOCATED_TARGET_PATTERNS:
            entries = []
            for target_name in new_names:
                entry = self._find_entry(
                    target_name, item.new_file, _line_at(item.new_lines, 0))
                if entry is not None:
                    entries.append(entry)
            return entries
        return [
            entry
            for target_name in new_names
            for entry in self._index.definitions.get(target_name, [])
        ]
    def _has_independent_real_entry(
        self: Self, item: CoexistenceItem, entries: list[DefEntry]
    ) -> tuple[bool, str]:
        old_entry = self._find_entry(
            item.old_name, item.old_file, _line_at(item.old_lines, 0))
        if old_entry is None:
            return False, (
                f"旧版 '{item.old_name}' 定义无法在索引中精确定位，"
                "需人工确认后再处理")
        candidates = self._independent_real_entries(entries, old_entry)
        if not candidates:
            return False, (
                f"新版 '{item.new_name}' 无可用的真实实现"
                "（全部为桩或旧版自身定义），无法替代旧版")
        if item.pattern_type == "migration_marker":
            locations = {
                (entry.file_path, entry.lineno, entry.kind)
                for entry in candidates
            }
            if len(locations) > 1:
                return False, (
                    f"新版 '{item.new_name}' 存在 {len(locations)} 个独立真实定义，"
                    "替代目标有歧义，需人工指定唯一实现后再处理")
        return True, ""
    @staticmethod
    def _independent_real_entries(
        entries: list[DefEntry], old_entry: DefEntry | None,
    ) -> list[DefEntry]:
        return [
            entry for entry in entries
            if not entry.is_stub and entry is not old_entry
        ]
    def _unspecified_target_reason(self: Self, item: CoexistenceItem) -> str:
        reason_template = self._UNSPECIFIED_REASONS.get(item.pattern_type)
        if reason_template is None:
            return (f"替代目标未指明（'{item.old_name}'），"
                    f"需人工确认迁移方向后再处理")
        return reason_template.format(old=item.old_name)
    def _verify_import_bridge(
        self: Self, item: CoexistenceItem
    ) -> tuple[bool, str]:
        module_leaf = str(item.new_name).split(".")[-1]
        if module_leaf not in self._module_stems:
            return False, f"新版模块 '{item.new_name}' 不在代码库中"
        return False, (
            f"新旧模块并存（'{item.old_name}' → '{item.new_name}'）："
            f"需先将导入迁移到新模块后再移除旧模块"
        )
    @staticmethod
    def _normalize_new_names(new_name: str) -> list[str]:
        new_names = []
        for raw_seg in str(new_name).split(","):
            seg = raw_seg.strip()
            if not seg:
                continue
            new_names.append(seg.rsplit(".", 1)[-1])
        return new_names
    def _coverage_failure(
        self: Self, item: CoexistenceItem, new_entries: list[DefEntry]
    ) -> str | None:
        old_entry = self._find_entry(
            item.old_name, item.old_file, _line_at(item.old_lines, 0))
        if old_entry is None:
            return None
        candidates = self._independent_real_entries(
            new_entries, old_entry)
        coverage = max(
            (self._coverage_ratio(old_entry, entry) for entry in candidates),
            default=0.0,
        )
        if coverage < 0.5:
            return (
                f"新版 '{item.new_name}' 仅覆盖旧版 {coverage:.0%} 的引用名称，"
                f"可能存在功能缺失"
            )
        return None
    def _check_call_chain(
        self: Self, item: CoexistenceItem, new_names: list[str]
    ) -> tuple[bool, str]:
        if not self._index.is_referenced(item.old_name):
            return True, f"旧版 '{item.old_name}' 未被引用，可安全移除"
        new_is_referenced = any(
            self._index.is_referenced(target_name) for target_name in new_names)
        new_reference_state = (
            f"新版 '{item.new_name}' 也已被引用" if new_is_referenced
            else f"新版 '{item.new_name}' 尚未被引用")
        return False, (
            f"旧版 '{item.old_name}' 仍被引用，{new_reference_state}；"
            "委托或废弃标记不代表调用方已迁移，须先迁移全部引用后再删除"
        )
    def _find_entry(
        self: Self, name: str, file_path: str, lineno: int
    ) -> DefEntry | None:
        for entry in self._index.definitions.get(name, []):
            if entry.file_path == file_path and entry.lineno == lineno:
                return entry
        return None
    @staticmethod
    def _coverage_ratio(old_entry: DefEntry, new_entry: DefEntry) -> float:
        sig_old = old_entry.referenced_names - NOISE_REFS
        if not sig_old:
            return 1.0
        covered = sig_old & (new_entry.referenced_names - NOISE_REFS)
        return len(covered) / len(sig_old)
class CoexistenceDetector:
    def __init__(self, skill_dir: str) -> None:
        self._skill_dir = require_skill_dir(skill_dir)
        self._ctx: ScanContext | None = None
    @property
    def index(self) -> CrossFileIndex:
        if self._ctx is None:
            raise RuntimeError("索引未构建：请先调用 detect()")
        return self._ctx.index
    @property
    def py_files(self) -> tuple[str, ...]:
        if self._ctx is None:
            raise RuntimeError("文件清单未构建：请先调用 detect()")
        return tuple(self._ctx.py_files)
    def detect(self) -> CoexistenceReport:
        ctx = self._ctx = build_cross_file_index(self._skill_dir)
        report = CoexistenceReport(skill_dir=str(self._skill_dir))
        report.total_files_scanned = len(ctx.py_files)
        report.total_definitions = sum(len(e) for e in ctx.index.definitions.values())
        unindexed_files = sorted(set(ctx.py_files) - set(ctx.file_trees))
        report.index_complete = not unindexed_files
        if unindexed_files:
            report.errors.append(
                f"代码索引不完整：{len(unindexed_files)} 个 Python 文件未能读取或解析，"
                f"禁止安全移除验证；文件: {unindexed_files[:5]}")
        report.items = _dedup_items(
            run_coexistence_strategies(ctx, report.errors))
        by_pattern: dict[str, int] = {}
        for item in report.items:
            by_pattern[item.pattern_type] = by_pattern.get(item.pattern_type, 0) + 1
        report.by_pattern = by_pattern
        return report
class CoexistenceCleaner:
    def __init__(self, skill_dir: str) -> None:
        self._skill_dir = require_skill_dir(skill_dir)
        self._detector = CoexistenceDetector(str(self._skill_dir))
        self._verifier = CoexistenceVerifier()
    def analyze(
        self: Self, min_confidence: float | None = None
    ) -> CoexistenceReport:
        min_confidence = normalize_min_confidence(min_confidence)
        report = self._detector.detect()
        self._verifier.set_index(
            self._detector.index, self._detector.py_files)
        for item in report.items:
            if not report.index_complete:
                item.verified = False
                item.reason = (
                    "代码索引不完整，缺失文件中的引用关系不可见，"
                    "禁止安全移除；请先修复 report.errors 中的读取或解析错误")
                report.blocked_items += 1
            elif self._apply_verification(item, min_confidence):
                report.verified_items += 1
            else:
                report.blocked_items += 1
        return report
    def _apply_verification(
        self: Self, item: CoexistenceItem, min_confidence: float
    ) -> bool:
        confidence = _normalize_item_confidence(item)
        item.confidence = confidence
        if confidence < min_confidence:
            item.verified = False
            item.reason = (
                f"置信度 {confidence:.2f} 低于阈值 {min_confidence}"
            )
            return False
        can_remove, reason = self._verifier.verify(item)
        item.verified = can_remove
        item.reason = reason
        return can_remove
    @staticmethod
    def _item_summary(item: CoexistenceItem) -> dict:
        return {
            "pattern_type": item.pattern_type,
            "old_name": item.old_name,
            "new_name": item.new_name,
            "old_file": item.old_file,
            "confidence": item.confidence,
            "verified": item.verified,
            "reason": item.reason,
            "suggestion": item.suggestion,
        }
    def clean(
        self: Self, min_confidence: float | None = None,
        dry_run: bool = True,
    ) -> dict:
        report = self.analyze(min_confidence=min_confidence)
        ai_review = _enqueue_coexistence_plans(self._skill_dir, report)
        item_views = [(item, self._item_summary(item)) for item in report.items]
        result = {
            "status": "analyzed",
            "ai_review": ai_review,
            "dry_run": bool(dry_run),
            "total_items": report.total_items,
            "errors": list(report.errors),
            "verified_items": report.verified_items,
            "blocked_items": report.blocked_items,
            "by_pattern": report.by_pattern,
            "items": [view for _item, view in item_views],
            "ai_action": "AI 审核共存清理方案并执行相关操作, 再验证",
        }
        _append_ai_review_error(result["errors"], ai_review)
        if report.blocked_items > 0:
            result["status"] = "blocked"
            result["blocked_details"] = [
                view for item, view in item_views if not item.verified
            ]
            result["message"] = (
                f"{report.blocked_items} 个共存项未通过验证，禁止清理。"
                "请确认这些项的业务功能已在新版中实现后再清理。"
            )
        return result
def _accuracy_category(value: Any) -> str:
    if isinstance(value, str):
        return value or "unknown"
    if not value:
        return "unknown"
    return str(value)
def _first_present(item: Any, names: tuple[str, ...], default: Any = "") -> Any:
    for name in names:
        value = _item_value(item, (name,), None)
        if value:
            return value
    return default
def _accuracy_snapshot(report: Any) -> dict[str, Any]:
    records = getattr(report, "accuracy", None) or {}
    return {
        str(_accuracy_category(category)): (
            asdict(record) if is_dataclass(record) else record)
        for category, record in records.items()
    }
def _detection_dedup_key(item: Any, category: str) -> tuple:
    file_id = _first_present(item, ("file_path", "old_file"))
    if not file_id:
        old_files = _item_value(item, ("old_files",), None) or ()
        norm_files = normalize_str_seq(old_files)
        file_id = norm_files if norm_files else str(old_files)
    line = str(_first_present(item, ("line", "line_start"), 0))
    old_lines = _item_value(item, ("old_lines",), None)
    old_scope = (_line_at(old_lines, 0), _line_at(old_lines, 1))
    symbol = _first_present(item, ("func_name", "symbol", "old_name"))
    if not symbol:
        old_symbols = normalize_str_seq(_item_value(item, ("old_symbols",), None))
        symbol = old_symbols or _first_present(item, ("strategy",))
    description = _first_present(
        item, ("description", "pattern_type", "summary"))
    new_id = _first_present(item, ("new_name",))
    if not new_id:
        new_id = normalize_str_seq(_item_value(item, ("new_symbols",), None))
    strategy = _item_value(item, ("strategy",), "")
    return (category, str(file_id), line, old_scope, str(symbol),
            str(description), str(strategy), str(new_id))
class ConfidenceLevel(str, Enum):
    LOW = "low"
    MEDIUM = "medium"
    HIGH = "high"
    @classmethod
    def from_score(cls: type[Self], score: float) -> ConfidenceLevel:
        if score >= 1.0:
            return cls.HIGH
        if score >= 0.8:
            return cls.MEDIUM
        return cls.LOW
@dataclass
class AccuracyRecord:
    category: str = ""
    total_detected: int = 0
    true_positive: int = 0
    false_positive: int = 0
@dataclass
class SafeCleanupReport:
    skill_dir: str = ""
    dry_run: bool = True
    min_confidence: float = DEFAULT_MIN_CONFIDENCE
    total_items: int = 0
    items_by_confidence: dict[str, int] = field(default_factory=dict)
    whitelist_hits: int = 0
    accuracy: dict[str, AccuracyRecord] = field(default_factory=dict)
    debt: Any = None
    errors: list[str] = field(default_factory=list)
class WhitelistManager:
    ALWAYS_PROTECTED_FILES = PROTECTED_CORE_FILES
    _ALWAYS_PROTECTED_NORMCASE = frozenset(
        os.path.normcase(name) for name in PROTECTED_CORE_FILES)
    ALWAYS_PROTECTED_SYMBOLS = frozenset({
        "__init__", "__new__", "__call__", "__str__", "__repr__",
        "__eq__", "__hash__", "__len__", "__iter__", "__next__",
        "__getitem__", "__setitem__", "__delitem__", "__contains__",
        "__enter__", "__exit__", "__aenter__", "__aexit__",
        "__getattr__", "__setattr__", "__delattr__", "__get__", "__set__",
        "__add__", "__sub__", "__mul__", "__truediv__",
        "setUp", "tearDown", "setUpClass", "tearDownClass",
    })
    ALWAYS_PROTECTED_PREFIXES = ("test_", "Test")
    def __init__(self: Self) -> None:
        self._hit_count = 0
        self._file_whitelist: set[str] = set()
        self._symbol_whitelist: set[str] = set()
        self._pattern_whitelist: list[re.Pattern] = []
    def record_hit(self: Self) -> None:
        self._hit_count += 1
    def is_file_protected(self: Self, file_path: str) -> bool:
        file_path = _as_text(file_path)
        basename = os.path.basename(file_path) if file_path else ""
        if os.path.normcase(basename) in self._ALWAYS_PROTECTED_NORMCASE:
            return True
        if not file_path:
            return False
        file_key = _whitelist_file_key(file_path)
        if (file_key in self._file_whitelist
                or _whitelist_file_key(basename) in self._file_whitelist):
            return True
        return any(
            not os.path.isabs(registered)
            and file_key.endswith(f"{os.sep}{registered}")
            for registered in self._file_whitelist
        )
    def is_symbol_protected(self: Self, symbol: str) -> bool:
        symbol = _as_text(symbol)
        if not symbol:
            return False
        leaf_symbol = symbol.rsplit(".", 1)[-1]
        if (symbol in self.ALWAYS_PROTECTED_SYMBOLS
                or leaf_symbol in self.ALWAYS_PROTECTED_SYMBOLS):
            return True
        return (
            symbol in self._symbol_whitelist
            or leaf_symbol in self._symbol_whitelist
            or symbol.startswith(self.ALWAYS_PROTECTED_PREFIXES)
            or leaf_symbol.startswith(self.ALWAYS_PROTECTED_PREFIXES)
        )
    def is_code_protected(self: Self, snippet: str) -> bool:
        snippet = _as_text(snippet)
        if not snippet:
            return False
        return any(p.search(snippet) for p in self._pattern_whitelist)
    def add_file(self: Self, name: Any) -> None:
        text = _as_text(name)
        if text:
            self._file_whitelist.add(_whitelist_file_key(text))
    def add_symbol(self: Self, name: Any) -> None:
        text = _as_text(name)
        if text:
            self._symbol_whitelist.add(text)
    def add_pattern(self: Self, pattern: Any) -> None:
        text = _as_text(pattern)
        if text:
            self._pattern_whitelist.append(re.compile(text))
    def hits(self: Self) -> int:
        return self._hit_count
class ConfidenceFilter:
    def __init__(self: Self, threshold: float | None = None) -> None:
        self.set_threshold(threshold)
    def should_include(self: Self, confidence: float) -> bool:
        return safe_confidence(confidence, 0.0) >= self._threshold
    def set_threshold(self: Self, threshold: float) -> None:
        self._threshold = normalize_min_confidence(threshold)
    def get_threshold(self: Self) -> float:
        return self._threshold
class AccuracyTracker:
    def __init__(self: Self) -> None:
        self._records: dict[str, AccuracyRecord] = {}
    def record_detection(self: Self, category: str) -> None:
        if category not in self._records:
            self._records[category] = AccuracyRecord(category=category)
        self._records[category].total_detected += 1
    def record_outcome(self: Self, category: str, true_positive: bool = True) -> None:
        if category not in self._records:
            self._records[category] = AccuracyRecord(category=category)
        rec = self._records[category]
        if true_positive:
            rec.true_positive += 1
        else:
            rec.false_positive += 1
    def get_all(self: Self) -> dict:
        return {category: replace(record)
                for category, record in self._records.items()}
def _report_items(report: Any) -> list[Any]:
    items = _item_value(report, ("items",), None)
    return list(items) if isinstance(items, (list, tuple)) else []
def _layer_errors(layer_report: Any, label: str = "") -> list[str]:
    errors = (layer_report.get("errors")
              if isinstance(layer_report, dict)
              else getattr(layer_report, "errors", None))
    if not isinstance(errors, (list, tuple)):
        return []
    prefix = f"{label}: " if label else ""
    return [f"{prefix}{err}" for err in errors if err]
def _layer_cache_get_or_run(cache: dict[tuple, Any], keepalive: dict[int, Any],
                            layer: Any, cache_tag: Any, run: Any) -> Any:
    key = (id(layer), cache_tag)
    if key in cache:
        return cache[key]
    keepalive[id(layer)] = layer
    try:
        layer_report = run()
    except Exception as exc:  # noqa: BLE001
        _log.warning(
            "[SafeCleaner] %s 层分析失败(跳过): %s",
            type(layer).__name__, exc, exc_info=True)
        layer_report = {
            "items": [], "errors": [str(exc) or type(exc).__name__],
        }
    cache[key] = layer_report
    return layer_report
def _accumulate_item_stats(report: SafeCleanupReport, item: Any,
                           record_detection: Any,
                           confidence_filter: ConfidenceFilter) -> None:
    record_detection(item)
    confidence = _normalize_item_confidence(item)
    level = ConfidenceLevel.from_score(confidence)
    report.items_by_confidence[level.value] = \
        report.items_by_confidence.get(level.value, 0) + 1
    if confidence_filter.should_include(confidence):
        report.total_items += 1
def _extend_layer_items(items: list, layer_report: Any, whitelisted: Any,
                        transform: Any = None,
                        actionable: Any = None) -> None:
    for it in _report_items(layer_report):
        if whitelisted(it):
            continue
        if actionable is not None and not actionable(it):
            continue
        transformed = it if transform is None else transform(it)
        if isinstance(transformed, list):
            items.extend(transformed)
        else:
            items.append(transformed)
def _is_consumed_terminal(p: Any, consumed_ids: set[str]) -> bool:
    outcome = _terminal_outcome(p)
    return outcome is not None and outcome[0] in consumed_ids
def _terminal_outcome(p: Any) -> tuple[str, str] | None:
    if not isinstance(p, dict):
        return None
    status = p.get("status", "")
    if status not in ("resolved", "rejected"):
        return None
    plan_id = p.get("plan_id", "")
    if not isinstance(plan_id, str) or not plan_id:
        return None
    return plan_id, status
def _backfill_terminal_entries(
    plan: dict, backfilled_plans: set[str], accuracy: AccuracyTracker
) -> set[str]:
    consumed_ids: set[str] = set()
    for entry in plan.get("plans", []) or []:
        outcome = _terminal_outcome(entry)
        if outcome is None:
            continue
        plan_id, status = outcome
        if plan_id not in backfilled_plans:
            backfilled_plans.add(plan_id)
            accuracy.record_outcome(
                _accuracy_category(entry.get("category", "")),
                true_positive=(status == "resolved"))
        consumed_ids.add(plan_id)
    return consumed_ids
def _prune_consumed_plans(
    skill_dir: str, plan: dict, consumed_ids: set[str]
) -> None:
    try:
        plan["plans"] = [
            p for p in (plan.get("plans", []) or [])
            if not _is_consumed_terminal(p, consumed_ids)
        ]
        write_cleanup_plan(skill_dir, plan)
        _log.info("[SafeCleaner] 已回填 %d 条终态裁决并从队列清理", len(consumed_ids))
    except Exception as _e:  # noqa: BLE001
        _log.warning("[SafeCleaner] 清理已消费终态记录失败(不影响回填结果): %s", _e)
class SafeCleaner:
    def __init__(self: Self, skill_dir: str,
                 enable_code: bool = True,
                 enable_file: bool = True,
                 enable_doc: bool = True) -> None:
        self._skill_dir = require_skill_dir(skill_dir)
        self.whitelist = _default_whitelist()
        self._item_whitelist_predicate = partial(_item_whitelisted, self.whitelist)
        self._arch_whitelist_predicate = partial(
            _arch_item_whitelisted, self.whitelist)
        self._confidence_filter = ConfidenceFilter()
        self._accuracy = AccuracyTracker()
        self._backfilled_plans: set[str] = set()
        self._detected_item_keys: set[tuple] = set()
        self._coexistence_cleaner = None
        self._arch_detector = None
        self._layer_report_cache: dict[tuple, Any] = {}
        self._layer_cache_keepalive: dict[int, Any] = {}
        self._effective_min_confidence = DEFAULT_MIN_CONFIDENCE
        self._code_cleaner = self._build_layer(CodeCleaner, enable_code)
        self._file_cleaner = self._build_layer(FileCleaner, enable_file)
        self._doc_cleaner = self._build_layer(DocCleaner, enable_doc)
    def _build_layer(self: Self, cleaner_type: type, enabled: bool) -> Any:
        return cleaner_type(skill_dir=str(self._skill_dir)) if enabled else None
    def _cached_analyze(self: Self, cleaner: Any,
                        min_confidence: float | None = None) -> Any:
        if min_confidence is None:
            return _layer_cache_get_or_run(
                self._layer_report_cache, self._layer_cache_keepalive,
                cleaner, None, cleaner.analyze)
        return _layer_cache_get_or_run(
            self._layer_report_cache, self._layer_cache_keepalive,
            cleaner, min_confidence,
            lambda: cleaner.analyze(min_confidence=min_confidence))
    def _record_detection_once(self: Self, item: Any) -> None:
        category = _accuracy_category(_item_value(item, ("category",), None))
        key = _detection_dedup_key(item, category)
        if key in self._detected_item_keys:
            return
        self._detected_item_keys.add(key)
        self._accuracy.record_detection(category)
    def _accumulate_report_items(self: Self, report: SafeCleanupReport,
                                 layer_report: Any, whitelisted: Any,
                                 label: str = "") -> None:
        debt = _item_value(layer_report, ("debt",), None)
        if debt is not None:
            report.debt = debt
        report.errors.extend(_layer_errors(layer_report, label))
        for item in _report_items(layer_report):
            if whitelisted(item):
                continue
            _accumulate_item_stats(
                report, item, self._record_detection_once,
                self._confidence_filter)
    def _analyze_layer(self: Self, cleaner: Any, report: SafeCleanupReport,
                       min_confidence: float | None = None,
                       label: str = "") -> None:
        layer_report = self._cached_analyze(cleaner, min_confidence)
        self._accumulate_report_items(
            report, layer_report, self._item_whitelist_predicate, label)
    def analyze(
        self: Self, min_confidence: float | None = None
    ) -> SafeCleanupReport:
        self._layer_report_cache.clear()
        self._layer_cache_keepalive.clear()
        self._confidence_filter.set_threshold(min_confidence)
        effective_confidence = self._confidence_filter.get_threshold()
        self._effective_min_confidence = effective_confidence
        report = SafeCleanupReport(
            skill_dir=str(self._skill_dir),
            dry_run=True,
            min_confidence=effective_confidence,
            items_by_confidence={"high": 0, "medium": 0, "low": 0},
        )
        for layer_name, cleaner in (("code", self._code_cleaner),
                                    ("file", self._file_cleaner),
                                    ("doc", self._doc_cleaner)):
            if cleaner is None:
                continue
            try:
                self._analyze_layer(cleaner, report, label=layer_name)
            except Exception as _e:  # noqa: BLE001
                _log.warning("[SafeCleaner] %s 层分析失败(跳过): %s",
                               layer_name, _e, exc_info=True)
                report.errors.append(f"{layer_name}: {_e}")
        self._analyze_coexistence_layer(report, effective_confidence)
        self._analyze_arch_layer(report, effective_confidence)
        self._backfill_review_outcomes()
        report.whitelist_hits = self.whitelist.hits()
        report.accuracy = self._accuracy.get_all()
        return report
    def _analyze_coexistence_layer(self: Self, report: SafeCleanupReport,
                                    effective_confidence: float) -> None:
        if self._coexistence_cleaner is None:
            return
        try:
            self._analyze_layer(self._coexistence_cleaner, report,
                                min_confidence=effective_confidence,
                                label="coexistence")
        except Exception as _e:  # noqa: BLE001
            _log.warning("[SafeCleaner] 共存层分析失败(跳过): %s", _e, exc_info=True)
            report.errors.append(f"coexistence: {_e}")
    def _cached_arch_detect(self: Self, min_confidence: float) -> Any:
        return _layer_cache_get_or_run(
            self._layer_report_cache, self._layer_cache_keepalive,
            self._arch_detector, min_confidence,
            lambda: self._arch_detector.detect(
                min_confidence=min_confidence))
    def _analyze_arch_layer(self: Self, report: SafeCleanupReport,
                            effective_confidence: float) -> None:
        if self._arch_detector is None:
            return
        try:
            arch_report = self._cached_arch_detect(effective_confidence)
            self._accumulate_report_items(
                report, arch_report, self._arch_whitelist_predicate, "arch")
        except Exception as _e:  # noqa: BLE001
            _log.warning("[SafeCleaner] 架构层分析失败(跳过): %s", _e, exc_info=True)
            report.errors.append(f"arch: {_e}")
    def _backfill_review_outcomes(self: Self) -> None:
        try:
            plan = read_cleanup_plan(str(self._skill_dir))
        except Exception as _e:  # noqa: BLE001
            _log.warning("[SafeCleaner] 回读清理队列裁决失败(跳过回填): %s", _e)
            return
        consumed_ids = _backfill_terminal_entries(
            plan, self._backfilled_plans, self._accuracy)
        if not consumed_ids:
            return
        _prune_consumed_plans(str(self._skill_dir), plan, consumed_ids)
    def enable_coexistence(self: Self) -> None:
        self._coexistence_cleaner = CoexistenceCleaner(str(self._skill_dir))
    def enable_arch_coexistence(self: Self) -> None:
        self._arch_detector = ArchCoexistenceDetector(str(self._skill_dir))
    def collect_cleanup_items(self: Self) -> list:
        items: list = self._collect_base_layers_items()
        items.extend(self._collect_optional_layer(
            self._coexistence_cleaner is not None,
            lambda: self._cached_analyze(
                self._coexistence_cleaner, self._effective_min_confidence),
            self._item_whitelist_predicate,
            coexistence_item_to_cleanup_plan,
            self._coexistence_item_actionable))
        items.extend(self._collect_optional_layer(
            self._arch_detector is not None,
            lambda: self._cached_arch_detect(
                self._effective_min_confidence),
            self._arch_whitelist_predicate,
            _arch_item_to_cleanup_plans,
            self._collect_confidence_ok))
        return items
    def _collect_confidence_ok(self: Self, item: Any) -> bool:
        confidence = _normalize_item_confidence(item)
        return self._confidence_filter.should_include(confidence)
    def _coexistence_item_actionable(self: Self, item: Any) -> bool:
        return self._collect_confidence_ok(item) and bool(
            _item_value(item, ("verified",), False))
    def _collect_base_layers_items(self: Self) -> list:
        items: list = []
        layers = (self._code_cleaner, self._file_cleaner, self._doc_cleaner)
        for cleaner in layers:
            if cleaner is None:
                continue
            report = self._cached_analyze(cleaner)
            default_file = _as_text(
                _item_value(report, ("doc_path",), "") or "")
            _extend_layer_items(
                items, report, self._item_whitelist_predicate,
                lambda item, default_file=default_file: (
                    _base_item_to_cleanup_plan(item, default_file)),
                self._collect_confidence_ok)
        return items
    def _collect_optional_layer(
        self: Self, enabled: bool, fetch: Any, whitelisted: Any,
        transform: Any, actionable: Any = None,
    ) -> list:
        items: list = []
        if not enabled:
            return items
        _extend_layer_items(
            items, fetch(), whitelisted, transform, actionable)
        return items
    def clean(self: Self) -> dict:
        clean_report = self.analyze()
        ai_enqueue = _enqueue_cleanup_items(
            self, str(self._skill_dir), "safe_cleaner")
        errors = list(clean_report.errors)
        _append_ai_review_error(errors, ai_enqueue)
        return {
            "status": "analyzed",
            "cleaned": 0,
            "skipped": 0,
            "errors": errors,
            "total_items": clean_report.total_items,
            "items_by_confidence": clean_report.items_by_confidence,
            "accuracy": _accuracy_snapshot(clean_report),
            "dry_run": True,
            "ai_action": "AI 审核清理方案并执行相关操作, 再验证",
            "ai_review": ai_enqueue,
        }
def _default_whitelist() -> WhitelistManager:
    whitelist = WhitelistManager()
    whitelist.add_pattern(r"raise\s+NotImplementedError")
    whitelist.add_pattern(r"if\s+False\s*:")
    whitelist.add_symbol("__all__")
    whitelist.add_symbol("__version__")
    return whitelist
def _item_whitelisted(whitelist: WhitelistManager, item: Any) -> bool:
    file_path = _first_present(item, ("file_path", "old_file"))
    symbol = _first_present(item, ("func_name", "symbol", "old_name"))
    snippet = _item_value(item, ("snippet",), "")
    return (
        _whitelist_hit(
            whitelist, file_path, whitelist.is_file_protected)
        or _whitelist_hit(
            whitelist, symbol, whitelist.is_symbol_protected)
        or _whitelist_hit(
            whitelist, snippet, whitelist.is_code_protected)
    )
def _whitelist_hit(whitelist: WhitelistManager, value: Any,
                   predicate: Callable[[str], bool]) -> bool:
    if value and predicate(value):
        whitelist.record_hit()
        return True
    return False
def _any_whitelisted(whitelist: WhitelistManager, values: Any,
                     predicate: Callable[[str], bool]) -> bool:
    return any(_whitelist_hit(whitelist, value, predicate)
               for value in values)
def _arch_item_whitelisted(whitelist: WhitelistManager, item: Any) -> bool:
    return (
        _any_whitelisted(
            whitelist,
            normalize_str_seq(_item_value(item, ("old_files",), None)),
            whitelist.is_file_protected)
        or _any_whitelisted(
            whitelist,
            normalize_str_seq(_item_value(item, ("old_symbols",), None)),
            whitelist.is_symbol_protected)
    )
def _append_ai_review_error(errors: list[str], ai_review: dict[str, Any]) -> None:
    error = ai_review.get("error") if isinstance(ai_review, dict) else None
    if error:
        message = f"ai_review: {error}"
        if message not in errors:
            errors.append(message)
def _ai_review_enqueue_result(queued: Any, entry: str) -> dict[str, Any]:
    if isinstance(queued, dict):
        return queued
    _log.warning(
        "%s 入队返回非 dict（契约违约，ai_review 回退默认值）: %r",
        entry, queued)
    return default_ai_review(
        f"{entry} 入队返回非 dict（{type(queued).__name__}），契约校验失败")
def _enqueue_ai_review(entry: str, enqueue: Callable[[], Any]) -> dict[str, Any]:
    try:
        return _ai_review_enqueue_result(enqueue(), entry)
    except Exception as exc:  # noqa: BLE001
        _log.warning("%s 入队失败(主报告仍返回): %s", entry, exc, exc_info=True)
        return default_ai_review(f"{entry} 入队失败: {exc}")
def _enqueue_cleanup_items(cleaner: SafeCleaner,
                           skill_dir: str, entry: str) -> dict[str, Any]:
    try:
        cleanup_items = cleaner.collect_cleanup_items()
    except Exception as exc:  # noqa: BLE001
        _log.warning(
            "%s 清理项收集失败(分析结果仍返回): %s", entry, exc, exc_info=True)
        return default_ai_review(f"{entry} 清理项收集失败: {exc}")
    return _enqueue_ai_review(
        entry,
        lambda: enqueue_cleanup_plan(
            skill_dir, cleanup_items, source=entry))
def arch_item_to_cleanup_plan(item: Any) -> dict[str, Any]:
    old_files = normalize_str_seq(_item_value(item, ("old_files",), None))
    strategy = _as_text(_item_value(item, ("strategy",), ""))
    summary = _as_text(_first_present(item, ("summary", "description")))
    confidence = _normalize_item_confidence(item)
    return {
        "file_path": old_files[0] if old_files else "",
        "line": 0,
        "category": (_as_text(_item_value(item, ("category",), ""))
                     or "arch_coexistence"),
        "operation": "remove_old_architecture",
        "description": f"架构共存[{strategy}] {summary}".strip(),
        "suggestion": _as_text(_item_value(item, ("suggestion",), "")),
        "confidence": confidence,
        "severity": to_queue_priority(_item_value(item, ("severity",), None)),
        "verified": False,
        "verify_reason": "",
    }
def _arch_item_to_cleanup_plans(item: Any) -> list[dict[str, Any]]:
    old_files = normalize_str_seq(_item_value(item, ("old_files",), None))
    base_plan = arch_item_to_cleanup_plan(item)
    if not old_files:
        return [base_plan]
    return [
        {**base_plan, "file_path": file_path}
        for file_path in old_files
    ]
def enqueue_arch_coexistence_plans(skill_dir: str,
                                   report: Any) -> dict[str, Any]:
    whitelist = _default_whitelist()
    try:
        plans: list[dict[str, Any]] = []
        protected = 0
        for item in _report_items(report):
            if _arch_item_whitelisted(whitelist, item):
                protected += 1
                continue
            plans.extend(_arch_item_to_cleanup_plans(item))
        if protected:
            _log.info("%s 架构共存 %d 项命中保护名单，禁止入队",
                      "coexistence_cleaner", protected)
        return _ai_review_enqueue_result(
            enqueue_cleanup_plan(
                skill_dir, plans, source="arch_coexistence_scan"),
            "arch_coexistence_scan")
    except Exception as e:  # noqa: BLE001
        _log.warning(
            "coexistence_cleaner:enqueue_arch_coexistence_plans: %s", e,
            exc_info=True)
        return default_ai_review(f"arch_coexistence_scan 入队失败: {e}")
def _debt_payload(debt: Any) -> Any:
    if debt is None:
        return None
    to_dict = getattr(debt, "to_dict", None)
    return to_dict() if callable(to_dict) else debt
def _cleanup_report_payload(skill_dir: str, report: Any,
                            ai_review: dict[str, Any],
                            layers: dict[str, bool],
                            dry_run: bool) -> dict[str, Any]:
    errors = list(report.errors)
    _append_ai_review_error(errors, ai_review)
    return {
        "ok": True,
        "skill_dir": skill_dir,
        "dry_run": bool(dry_run),
        "status": "analyzed",
        "total_items": report.total_items,
        "items_by_confidence": report.items_by_confidence,
        "accuracy": _accuracy_snapshot(report),
        "whitelist_hits": report.whitelist_hits,
        "debt": _debt_payload(report.debt),
        "errors": errors,
        "layers": layers,
        "ai_review": ai_review,
    }
def quick_cleanup(skill_dir: str, dry_run: bool = True,
                  enable_code: bool = True,
                  enable_file: bool = True,
                  enable_doc: bool = True,
                  enable_coexistence: bool = False,
                  enable_arch_coexistence: bool = False) -> dict[str, Any]:
    def _body() -> dict[str, Any]:
        cleaner = SafeCleaner(
            skill_dir,
            enable_code=enable_code,
            enable_file=enable_file,
            enable_doc=enable_doc,
        )
        if enable_coexistence:
            cleaner.enable_coexistence()
        if enable_arch_coexistence:
            cleaner.enable_arch_coexistence()
        report = cleaner.analyze()
        ai_enqueue = _enqueue_cleanup_items(cleaner, skill_dir, "quick_cleanup")
        return _cleanup_report_payload(
            skill_dir, report, ai_enqueue,
            {"code": enable_code, "file": enable_file, "doc": enable_doc,
             "coexistence": enable_coexistence,
             "arch_coexistence": enable_arch_coexistence},
            dry_run=dry_run)
    return run_traced_entry("quick_cleanup", "cleanup_scan", skill_dir, _body)
def quick_coexistence_scan(skill_dir: str, dry_run: bool = True,
                           min_confidence: float | None = None,
                           ) -> dict[str, Any]:
    def _body() -> Any:
        cleaner = CoexistenceCleaner(skill_dir)
        result = cleaner.clean(
            min_confidence=min_confidence, dry_run=dry_run)
        if isinstance(result, dict):
            result.setdefault("ok", True)
        return result
    return run_traced_entry(
        "quick_coexistence_scan", "coexistence_scan", skill_dir, _body)
def quick_arch_coexistence_scan(
        skill_dir: str,
        min_confidence: float | None = None) -> dict[str, Any]:
    def _body() -> dict[str, Any]:
        validated_dir = str(require_skill_dir(skill_dir))
        detector = ArchCoexistenceDetector(validated_dir)
        report = detector.detect(min_confidence=min_confidence)
        result = report.to_dict()
        result["ok"] = True
        result["ai_review"] = _enqueue_ai_review(
            "quick_arch_coexistence_scan",
            lambda: enqueue_arch_coexistence_plans(validated_dir, report))
        errors = list(result.get("errors") or [])
        _append_ai_review_error(errors, result["ai_review"])
        result["errors"] = errors
        return result
    return run_traced_entry(
        "quick_arch_coexistence_scan", "arch_coexistence_scan",
        skill_dir, _body)

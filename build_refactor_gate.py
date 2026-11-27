from __future__ import annotations

import hashlib
import json
import logging
import math
import os
import time
from collections import Counter
from collections.abc import Iterable
from dataclasses import MISSING, asdict, dataclass, field, fields
from enum import Enum
from operator import gt, lt
from typing import Any, get_type_hints

from jwsgj.build_refactor_policy import (
    action_field,
    build_decision_record,
    decision_target_key,
    validate_merge_argument,
)
from jwsgj.build_safe_rollback import execute_rollback
from jwsgj.diag_guard_dirfile import DirFileGuard, dirfile_warning_lines
from jwsgj.diag_guard_io import (
    guarded_open,
)
from jwsgj.diag_guard_scale import (
    ArchitectureCapacityValidator,
    BatchQualityTrendMonitor,
    FunctionMappingGenerator,
)
from jwsgj.diag_guard_state import (
    write_json_artifact,
)
from jwsgj.diag_module_topology import capture_governance_metrics
from jwsgj.diag_types_defs import (
    ContractViolationError,
)
from jwsgj.diag_types_normalize import (
    FALSE_SIGNAL_TEXT,
    finite_float_or_none,
    timestamp_ms,
)
from jwsgj.log_config import (
    append_jsonl_locked,
    log_swallowed,
    now_iso_seconds,
    prune_jsonl_file,
)
from jwsgj.runtime_paths import (
    get_temp_base,
    governance_acceptance_path,
    governance_baseline_path,
    governance_decisions_path,
)
from jwsgj.runtime_scope import (
    collect_baseline_py_files,
    normalize_skill_dir,
)

__all__ = [
    'ACCEPTANCE_FILENAME',
    'ACCEPTANCE_METRICS',
    'BASELINE_FILENAME',
    'BATCH_STRATEGIES',
    'DECISIONS_FILENAME',
    'EFFORT_UNITS',
    'IDEAL_BATCH_EU',
    'LINES_SPLIT_THRESHOLD',
    'MAX_BATCH_EU',
    'MAX_BATCH_SUBSYSTEMS',
    'MAX_BATCH_SUBSYSTEM_FUNCS',
    'MIN_BATCH_EU',
    'SNAPSHOT_FLOAT_FIELDS',
    'SNAPSHOT_INT_FIELDS',
    'SNAPSHOT_STR_FIELDS',
    'TEST_STATUS_VALUES',
    'BatchQualityMonitor',
    'BatchQualitySnapshot',
    'EffortLevel',
    'FileWorkload',
    'OverallQualityReport',
    'QualityThresholds',
    'QualityVerdict',
    'RefactoringBatch',
    'WorkloadReport',
    'build_snapshot_from_baseline',
    'capture_baseline',
    'check_acceptance',
    'effort_level_for_lines',
    'format_acceptance_checklist',
    'load_baseline',
    'load_decisions',
    'merge_decisions_recorded',
    'merge_target_key',
    'norm_baseline_field',
    'quick_quality_check',
    'quick_rebuild_check',
    'record_acceptance',
    'record_decision',
    'save_baseline',
]
_log = logging.getLogger(__name__)
_log.info("build_refactor_gate 已加载: %d 项导出", len(__all__))
MAX_BATCH_SUBSYSTEMS = 15
MAX_BATCH_SUBSYSTEM_FUNCS = 300
MAX_BATCH_EU = 8.0
MIN_BATCH_EU = 1.0
IDEAL_BATCH_EU = 4.0
BATCH_STRATEGIES: dict[str, dict] = {
    "leaf_first": {"name": "叶子优先", "risk_base": 90, "description": "从依赖树叶子节点开始,逐层向内重构", "适用": "大型项目依赖关系清晰时"},
    "by_layer": {"name": "按架构层", "risk_base": 85, "description": "从基础设施层->领域层->应用层->表示层重构", "适用": "分层架构清晰的项目"},
    "by_smell_density": {"name": "按坏味道密度", "risk_base": 80, "description": "优先处理坏味道密度最高的批次", "适用": "代码质量恶化严重时"},
    "strangler_fig": {"name": "渐进式绞杀", "risk_base": 75, "description": "逐批重构,新代码验证后切换调用方", "适用": "不可中断的线上系统重构"},
    "big_bang": {"name": "大爆炸式", "risk_base": 30, "description": "所有批次一次性重构", "适用": "小项目(<20文件)且全部在控制中"},
}
class EffortLevel(Enum):
    TRIVIAL = "trivial"
    LIGHT = "light"
    MODERATE = "moderate"
    HEAVY = "heavy"
    CRITICAL = "critical"
EFFORT_UNITS: dict[EffortLevel, float] = {
    EffortLevel.TRIVIAL: 0.1,
    EffortLevel.LIGHT: 0.3,
    EffortLevel.MODERATE: 0.6,
    EffortLevel.HEAVY: 1.0,
    EffortLevel.CRITICAL: 2.0,
}
LINES_SPLIT_THRESHOLD = 3000
_EFFORT_LEVEL_BOUNDS: tuple[tuple[int, EffortLevel], ...] = (
    (100, EffortLevel.TRIVIAL),
    (400, EffortLevel.LIGHT),
    (1200, EffortLevel.MODERATE),
    (LINES_SPLIT_THRESHOLD, EffortLevel.HEAVY),
)
def _with_effort_level_value(payload: dict) -> dict:
    if isinstance(payload.get("effort_level"), EffortLevel):
        payload["effort_level"] = payload["effort_level"].value
    return payload
def effort_level_for_lines(lines: int) -> EffortLevel:
    for bound, level in _EFFORT_LEVEL_BOUNDS:
        if lines < bound:
            return level
    return EffortLevel.CRITICAL
@dataclass
class FileWorkload:
    file_path: str
    relative_path: str = ""
    effective_lines: int = 0
    functions: int = 0
    classes: int = 0
    imports: list = field(default_factory=list)
    imported_by: list = field(default_factory=list)
    smell_count: int = 0
    critical_issues: int = 0
    high_issues: int = 0
    complexity_score: int = 0
    effort_level: EffortLevel = EffortLevel.TRIVIAL
    effort_units: float = 0.0
    needs_split: bool = False
    split_candidates: list = field(default_factory=list)
    module_name: str = ""
    layer: str = "unknown"
    def to_dict(self) -> dict:
        return _with_effort_level_value(asdict(self))
@dataclass
class RefactoringBatch:
    batch_id: str
    name: str
    total_lines: int = 0
    total_eu: float = 0.0
    estimated_hours: float = 0.0
    dependency_count: int = 0
    strategy: str = "leaf_first"
    risk: str = "low"
    pre_checks: list = field(default_factory=list)
    post_checks: list = field(default_factory=list)
    notes: list = field(default_factory=list)
    status: str = "pending"
    def to_dict(self) -> dict:
        return asdict(self)
@dataclass
class WorkloadReport:
    project_path: str
    total_files: int
    total_eu: float
    files: list = field(default_factory=list)
    dependency_graph: dict = field(default_factory=dict)
    layer_distribution: dict = field(default_factory=dict)
    effort_distribution: dict = field(default_factory=dict)
    hard_block_files: list = field(default_factory=list)
    summary: str = ""
    def to_dict(self) -> dict:
        d = asdict(self)
        for item in d["files"]:
            if isinstance(item, dict):
                _with_effort_level_value(item)
        return d
_UNMEASURED_PCT: float = -1.0
class QualityVerdict(Enum):
    PASS = "PASS"
    WARN = "WARN"
    BLOCK = "BLOCK"
    PENDING = "PENDING"
_VALID_SNAPSHOT_VERDICTS = frozenset(v.value for v in QualityVerdict)
_PENDING_VERDICT = QualityVerdict.PENDING.value
_VALID_FINAL_VERDICTS = frozenset({
    QualityVerdict.PASS.value,
    QualityVerdict.BLOCK.value,
    _PENDING_VERDICT,
})
DEFAULT_TEST_STATUS = "not_run"
_DEFAULT_AUTO_ROLLBACK = True
class QualityThresholds:
    BLOCK_FUNCTION_COVERAGE = 70.0
    BLOCK_STUB_RATIO = 40.0
    BLOCK_IMPORT_INTEGRITY = 80.0
    BLOCK_SUBSYSTEMS_PRESERVED = 60.0
    BLOCK_SYNTAX_PASS = 95.0
    WARN_FUNCTION_COVERAGE = 85.0
    WARN_STUB_RATIO = 20.0
    WARN_IMPORT_INTEGRITY = 90.0
    WARN_SUBSYSTEMS_PRESERVED = 80.0
    DELIVERY_MIN_FUNCTION_COVERAGE = 85.0
    DELIVERY_MAX_STUB_RATIO = 15.0
    DELIVERY_MIN_IMPORT_INTEGRITY = 95.0
    DELIVERY_MIN_SUBSYSTEMS_PRESERVED = 90.0
    DELIVERY_MAX_BLOCKED_BATCHES = 0
@dataclass
class BatchQualitySnapshot:
    batch_id: str
    batch_label: str
    timestamp: float = field(default_factory=time.time)
    files_processed: int = 0
    files_total: int = 0
    lines_before: int = 0
    lines_after: int = 0
    public_functions_before: int = 0
    public_functions_after: int = 0
    function_coverage_pct: float = _UNMEASURED_PCT
    stub_count: int = 0
    stub_ratio_pct: float = _UNMEASURED_PCT
    import_chain_total: int = 0
    import_chain_broken: int = 0
    import_integrity_pct: float = _UNMEASURED_PCT
    syntax_errors: int = 0
    syntax_pass_pct: float = _UNMEASURED_PCT
    subsystems_before: int = 0
    subsystems_after: int = 0
    subsystems_preserved_pct: float = _UNMEASURED_PCT
    verdict: str = _PENDING_VERDICT
    blocking_reasons: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    elapsed_seconds: float = 0.0
    rollback_count: int = 0
    def __post_init__(self) -> None:
        if isinstance(self.verdict, QualityVerdict):
            self.verdict = self.verdict.value
        if not isinstance(self.verdict, str) or self.verdict not in _VALID_SNAPSHOT_VERDICTS:
            _log.warning(
                "BatchQualitySnapshot: 未知 verdict %r（合法值 %s），"
                "降级为 PENDING——未知状态不得被当作非阻断",
                self.verdict, sorted(_VALID_SNAPSHOT_VERDICTS))
            self.verdict = QualityVerdict.PENDING.value
    def to_dict(self) -> dict:
        return asdict(self)
    @property
    def is_blocking(self) -> bool:
        return self.verdict == QualityVerdict.BLOCK.value
@dataclass
class OverallQualityReport:
    project_path: str
    total_batches: int = 0
    completed_batches: int = 0
    blocked_batches: int = 0
    snapshots: dict[str, BatchQualitySnapshot] = field(default_factory=dict)
    avg_function_coverage: float = _UNMEASURED_PCT
    avg_stub_ratio: float = _UNMEASURED_PCT
    avg_import_integrity: float = _UNMEASURED_PCT
    avg_subsystems_preserved: float = _UNMEASURED_PCT
    trend_coverage: list[float] = field(default_factory=list)
    trend_stub: list[float] = field(default_factory=list)
    trend_import: list[float] = field(default_factory=list)
    final_verdict: str = _PENDING_VERDICT
    total_blocking_reasons: list[str] = field(default_factory=list)
    delivery_ready: bool = False
    delivery_blockers: list[str] = field(default_factory=list)
def _degrade_field(subject: str, key: str, raw: Any, default: Any) -> Any:
    _log.warning(
        "BatchQualityMonitor: %s %s 类型非法（实际为 %s，应为 %s），"
        "降级为 %r", subject, key, type(raw).__name__,
        type(default).__name__, default)
    return default
def norm_baseline_field(data: dict, key: str, default: Any) -> Any:
    raw = data.get(key, default)
    if type(raw) is type(default):
        return raw
    return _degrade_field("基线字段", key, raw, default)
SNAPSHOT_INT_FIELDS = (
    "files_processed", "files_total", "lines_before", "lines_after",
    "public_functions_before", "public_functions_after", "stub_count",
    "import_chain_total", "import_chain_broken", "syntax_errors",
    "subsystems_before", "subsystems_after", "rollback_count",
)
SNAPSHOT_FLOAT_FIELDS = (
    "timestamp", "function_coverage_pct", "stub_ratio_pct",
    "import_integrity_pct", "syntax_pass_pct", "subsystems_preserved_pct",
    "elapsed_seconds",
)
SNAPSHOT_STR_FIELDS = ("batch_id", "batch_label", "verdict")
_SNAPSHOT_PCT_FIELDS = (
    "function_coverage_pct", "stub_ratio_pct", "import_integrity_pct",
    "syntax_pass_pct", "subsystems_preserved_pct",
)
_SNAPSHOT_LIST_FIELDS = ("blocking_reasons", "warnings")
_SNAPSHOT_BASELINE_DEFAULT_OVERRIDES: dict[str, Any] = {
    "batch_id": "",
    "batch_label": "",
    "timestamp": 0.0,
}
def _snapshot_field_default(field_: Any) -> Any:
    if field_.name in _SNAPSHOT_BASELINE_DEFAULT_OVERRIDES:
        return _SNAPSHOT_BASELINE_DEFAULT_OVERRIDES[field_.name]
    if field_.default is not MISSING:
        return field_.default
    if field_.default_factory is not MISSING:
        return field_.default_factory()
    raise RuntimeError(f"快照必填字段缺少基线缺省值: {field_.name}")
_SNAPSHOT_FIELD_DEFAULTS: dict[str, Any] = {
    item.name: _snapshot_field_default(item)
    for item in fields(BatchQualitySnapshot)
}
def _assert_type_arms(typed: tuple[str, ...], defaults: set[str]) -> None:
    duplicated = sorted({name for name in typed if typed.count(name) > 1})
    if duplicated:
        raise RuntimeError(
            f"快照字段类型臂重复登记（归一分支会静默取胜）: {duplicated}")
    typed_set = set(typed)
    if typed_set != defaults:
        untyped = sorted(defaults - typed_set)
        unknown = sorted(typed_set - defaults)
        raise RuntimeError(
            f"快照字段类型表与默认值表漂移: "
            f"untyped={untyped}, unknown={unknown}")
def _assert_pct_arms(pct: tuple[str, ...],
                     floats: tuple[str, ...]) -> None:
    stray = sorted(set(pct) - set(floats))
    if stray:
        raise RuntimeError(
            f"百分比字段表必须是 float 字段表的子集: {stray}")
    duplicated = sorted({name for name in pct if pct.count(name) > 1})
    if duplicated:
        raise RuntimeError(f"百分比字段重复登记: {duplicated}")
def _assert_snapshot_field_contract() -> None:
    _assert_type_arms((*SNAPSHOT_INT_FIELDS, *SNAPSHOT_FLOAT_FIELDS,
                       *SNAPSHOT_STR_FIELDS, *_SNAPSHOT_LIST_FIELDS),
                      set(_SNAPSHOT_FIELD_DEFAULTS))
    _assert_pct_arms(_SNAPSHOT_PCT_FIELDS, SNAPSHOT_FLOAT_FIELDS)
_assert_snapshot_field_contract()
def _normalize_snapshot_value(key: str, raw: Any) -> tuple[Any, bool]:
    if key in SNAPSHOT_INT_FIELDS:
        return raw, type(raw) is int
    if key in SNAPSHOT_FLOAT_FIELDS:
        if not _field_type_ok(float, raw):
            return raw, False
        return float(raw), True
    if key in SNAPSHOT_STR_FIELDS:
        return raw, type(raw) is str
    if key in _SNAPSHOT_LIST_FIELDS:
        if type(raw) is not list:
            return raw, False
        return list(raw), True
    raise KeyError(f"未登记的基线快照字段: {key}")
def _pct_in_range(value: float) -> bool:
    return value == _UNMEASURED_PCT or 0.0 <= value <= 100.0
def _degrade_pct(subject: str, key: str, raw: Any) -> float:
    _log.warning(
        "BatchQualityMonitor: %s %s 越界（实际为 %r，合法区间 [0, 100] "
        "或未度量哨兵 %r），降级为未度量",
        subject, key, raw, _UNMEASURED_PCT)
    return _UNMEASURED_PCT
def _degrade_negative_count(subject: str, key: str, raw: Any,
                            default: Any) -> Any:
    _log.warning(
        "BatchQualityMonitor: %s %s 为负值（实际为 %r，计数须非负），"
        "降级为 %r", subject, key, raw, default)
    return default
def _norm_snapshot_field(bid: str, sdata: dict, key: str) -> Any:
    default = _SNAPSHOT_FIELD_DEFAULTS[key]
    raw = sdata.get(key, default)
    if key in SNAPSHOT_INT_FIELDS and type(raw) is int and raw < 0:
        return _degrade_negative_count(
            f"基线快照 {bid} 字段", key, raw, default)
    normalized, ok = _normalize_snapshot_value(key, raw)
    if not ok:
        return _degrade_field(f"基线快照 {bid} 字段", key, raw, default)
    if key in _SNAPSHOT_PCT_FIELDS and not _pct_in_range(normalized):
        return _degrade_pct(f"基线快照 {bid} 字段", key, raw)
    return normalized
def build_snapshot_from_baseline(
        bid: str, sdata: dict) -> BatchQualitySnapshot:
    kwargs = {key: _norm_snapshot_field(bid, sdata, key)
              for key in _SNAPSHOT_FIELD_DEFAULTS}
    raw_id = sdata.get("batch_id")
    kwargs["batch_id"] = raw_id if isinstance(raw_id, str) else bid
    return BatchQualitySnapshot(**kwargs)
_COMPLETE_BATCH_KEYS: dict[str, str] = {
    "files_after": "files_processed",
    "files_before": "files_total",
    "lines_before": "lines_before",
    "lines_after": "lines_after",
    "public_functions_before": "public_functions_before",
    "public_functions_after": "public_functions_after",
    "stub_count": "stub_count",
    "import_chain_total": "import_chain_total",
    "import_chain_broken": "import_chain_broken",
    "syntax_errors": "syntax_errors",
    "subsystems_before": "subsystems_before",
    "subsystems_after": "subsystems_after",
    "rollback_count": "rollback_count",
}
_BATCH_BEFORE_KEYS: tuple[str, ...] = tuple(
    key for key in _COMPLETE_BATCH_KEYS if key.endswith("_before"))
_WORKLOAD_FIELD_HINTS: dict[str, Any] = get_type_hints(FileWorkload)
_BATCH_FIELD_HINTS: dict[str, Any] = get_type_hints(RefactoringBatch)
def _check_record_field_types(caller: str, hints: dict[str, Any],
                              values: dict[str, Any]) -> None:
    for name, value in values.items():
        expected = hints.get(name)
        if expected is None:
            continue
        if not _field_type_ok(expected, value):
            finite_hint = "（数值位须有限）" if expected is float else ""
            raise TypeError(
                f"{caller}: 字段 {name} 须为 "
                f"{getattr(expected, '__name__', expected)}{finite_hint}，实际为 "
                f"{type(value).__name__}（值 {value!r}）")
        if expected in (int, float) and value < 0:
            raise ValueError(
                f"{caller}: 字段 {name} 须为非负数值，实际为 {value!r}")
def _field_type_ok(expected: Any, value: Any) -> bool:
    if isinstance(expected, type) and issubclass(expected, Enum):
        return isinstance(value, expected)
    if expected is float:
        if not isinstance(value, (int, float)) or isinstance(value, bool):
            return False
        try:
            return math.isfinite(value)
        except (OverflowError, ValueError) as _swallow_e:
            log_swallowed(__name__, _swallow_e, context='_field_type_ok:OverflowError+ValueError')
            return False
    return type(value) is expected
def _norm_final_verdict(raw: str) -> str:
    if raw in _VALID_FINAL_VERDICTS:
        return raw
    _log.warning(
        "BatchQualityMonitor: 基线 final_verdict 非法（实际为 %r，合法值 %s），"
        "降级为 PENDING", raw, sorted(_VALID_FINAL_VERDICTS))
    return _PENDING_VERDICT
def _require_nonempty_str(caller: str, name: str, value: Any,
                          expectation: str = "非空 str") -> None:
    if not isinstance(value, str) or not value:
        raise ValueError(
            f"{caller}: {name} 须为{expectation}，实际为 {value!r}")
_FLAG_TRUE_TEXT = frozenset({"1", "true", "yes", "y", "on", "t"})
_FLAG_FALSE_TEXT = frozenset(FALSE_SIGNAL_TEXT | {"n", "off", "f"})
def _coerce_flag(caller: str, name: str, value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if value is None:
        return False
    if isinstance(value, int) and value in (0, 1):
        return bool(value)
    if isinstance(value, str):
        text = value.strip().lower()
        if text in _FLAG_TRUE_TEXT:
            return True
        if text in _FLAG_FALSE_TEXT:
            return False
    raise TypeError(
        f"{caller}: {name} 须为布尔开关（bool/0/1/true/false/yes/no），"
        f"实际为 {type(value).__name__}（值 {value!r}）；"
        "无法判定的开关不得静默按真值放行")
def _require_str(caller: str, name: str, value: Any,
                 label: str = "") -> None:
    if not isinstance(value, str):
        raise TypeError(
            f"{caller}: {label}{name} 须为 str，实际为 "
            f"{type(value).__name__}（值 {value!r}）")
def _skill_root(caller: str, value: Any,
                require_existing: bool = False) -> str:
    if not isinstance(value, str):
        raise TypeError(
            f"{caller}: skill_dir 须为 str 路径，实际为 "
            f"{type(value).__name__}（值 {value!r}）")
    if not value.strip():
        raise ValueError(
            f"{caller}: skill_dir 不得为空（空路径会被解析成进程 cwd，"
            "导致基线与台账落到无关目录）")
    resolved = normalize_skill_dir(value)
    if require_existing and not os.path.isdir(resolved):
        raise ValueError(
            f"{caller}: skill_dir 目录不存在: {resolved!r}")
    return resolved
def _require_int_metric(caller: str, name: str, value: Any) -> None:
    if type(value) is not int:
        raise TypeError(
            f"{caller}: 指标 {name} 须为 int，实际为 "
            f"{type(value).__name__}（值 {value!r}）")
    if value < 0:
        raise ValueError(
            f"{caller}: 计数指标 {name} 须为非负整数，"
            f"实际为 {value}")
def _require_float_metric(caller: str, name: str, value: Any) -> None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise TypeError(
            f"{caller}: 指标 {name} 须为数值（int/float），"
            f"实际为 {type(value).__name__}（值 {value!r}）")
    try:
        finite = math.isfinite(value)
    except OverflowError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_require_float_metric:OverflowError')
        finite = False
    if not finite:
        raise ValueError(
            f"{caller}: 指标 {name} 须为有限数值，实际为 {value!r}")
def _check_metric_types(caller: str, metrics: dict[str, Any]) -> None:
    for name, value in metrics.items():
        if name in SNAPSHOT_INT_FIELDS:
            _require_int_metric(caller, name, value)
        elif name in SNAPSHOT_FLOAT_FIELDS:
            _require_float_metric(caller, name, value)
        elif name in SNAPSHOT_STR_FIELDS:
            _require_str(caller, name, value, label="指标 ")
def _check_metric_consistency(caller: str, metrics: dict[str, Any]) -> None:
    files_total = metrics.get("files_total", 0)
    _require_subset(
        caller, "files_processed", metrics.get("files_processed", 0),
        "files_total", files_total,
        "处理文件须为声明批次文件子集，矛盾计数会破坏完成度与语法度量")
    _require_subset(caller, "import_chain_broken",
                    metrics.get("import_chain_broken", 0),
                    "import_chain_total", metrics.get("import_chain_total", 0),
                    "断裂链须为总链子集，矛盾计数会产出负导入完整性率")
    files_denom = metrics.get("files_processed", 0)
    _require_subset(caller, "syntax_errors", metrics.get("syntax_errors", 0),
                    "文件分母", files_denom,
                    "语法错误文件须为处理文件子集，矛盾计数会产出负语法通过率")
    _require_subset(caller, "stub_count", metrics.get("stub_count", 0),
                    "public_functions_after",
                    metrics.get("public_functions_after", 0),
                    "空桩函数须为重构后函数子集，矛盾计数会产出超 100% 空桩率")
def _require_subset(caller: str, part_name: str, part: Any,
                    whole_name: str, whole: Any, consequence: str) -> None:
    if part > whole:
        raise ValueError(
            f"{caller}: {part_name}({part}) 超过 {whole_name}({whole})——{consequence}")
def _check_batch_metric_values(caller: str,
                                metrics: dict[str, Any]) -> None:
    _check_metric_types(caller, metrics)
    _check_metric_consistency(caller, metrics)
_BATCH_METRIC_ALIASES: dict[str, str] = {
    "files_processed": "files_after",
    "files_total": "files_before",
}
def _consume_batch_aliases(metrics: dict[str, Any]) -> None:
    for alias, canonical in _BATCH_METRIC_ALIASES.items():
        if alias not in metrics:
            continue
        value = metrics.pop(alias)
        if canonical in metrics and metrics[canonical] != value:
            raise ValueError(
                f"complete_batch: {alias} 与 {canonical} 同时给出且不一致"
                f"（{value!r} vs {metrics[canonical]!r}）")
        metrics.setdefault(canonical, value)
_BATCH_THRESHOLDS: tuple[tuple[str, str, str | None, str, str], ...] = (
    ("function_coverage_pct", "BLOCK_FUNCTION_COVERAGE", "WARN_FUNCTION_COVERAGE", "min", "函数覆盖率"),
    ("stub_ratio_pct", "BLOCK_STUB_RATIO", "WARN_STUB_RATIO", "max", "空桩率"),
    ("import_integrity_pct", "BLOCK_IMPORT_INTEGRITY", "WARN_IMPORT_INTEGRITY", "min", "导入完整性"),
    ("subsystems_preserved_pct", "BLOCK_SUBSYSTEMS_PRESERVED", "WARN_SUBSYSTEMS_PRESERVED", "min", "子系统保留率"),
    ("syntax_pass_pct", "BLOCK_SYNTAX_PASS", None, "min", "语法通过率"),
)
_DELIVERY_AVG_RULES: tuple[tuple[str, str, str, str], ...] = (
    ("avg_function_coverage", "DELIVERY_MIN_FUNCTION_COVERAGE", "min", "平均函数覆盖率"),
    ("avg_stub_ratio", "DELIVERY_MAX_STUB_RATIO", "max", "平均空桩率"),
    ("avg_import_integrity", "DELIVERY_MIN_IMPORT_INTEGRITY", "min", "平均导入完整性"),
    ("avg_subsystems_preserved", "DELIVERY_MIN_SUBSYSTEMS_PRESERVED", "min", "平均子系统保留率"),
)
_AVG_TO_SNAPSHOT_ATTR: dict[str, str] = {
    "avg_function_coverage": "function_coverage_pct",
    "avg_stub_ratio": "stub_ratio_pct",
    "avg_import_integrity": "import_integrity_pct",
    "avg_subsystems_preserved": "subsystems_preserved_pct",
}
def _normalized_lower_path(path: str) -> str:
    normalized = normalize_skill_dir(path).replace("\\", "/").rstrip("/")
    return (normalized or "/").lower()
def _own_temp_root(project_path: str) -> str:
    try:
        return _normalized_lower_path(get_temp_base(project_path))
    except RuntimeError as _e:
        log_swallowed(__name__, _e, context='_own_temp_root:RuntimeError')
        return ""
def _is_own_artifact_path(project_path: str) -> bool:
    own_temp = _own_temp_root(project_path)
    proj = _normalized_lower_path(project_path)
    temp_prefix = own_temp if own_temp.endswith("/") else own_temp + "/"
    return bool(own_temp and (proj == own_temp or proj.startswith(temp_prefix)))
def _resolve_baseline_dir(baseline_dir: str | None,
                          persist_baseline: bool,
                          project_path: str) -> str:
    if baseline_dir is not None:
        _require_nonempty_str("BatchQualityMonitor", "baseline_dir",
                              baseline_dir, expectation="非空 str 或 None")
        return baseline_dir
    if not persist_baseline:
        return ""
    return os.path.join(get_temp_base(project_path), "baselines")
_THRESHOLD_DIRECTIONS: frozenset[str] = frozenset({"min", "max"})
def _assert_threshold_tables() -> None:
    threshold_names = set(vars(QualityThresholds))
    pct_fields = set(_SNAPSHOT_PCT_FIELDS)
    for attr_name, block_key, warn_key, direction, _label in _BATCH_THRESHOLDS:
        if attr_name not in pct_fields:
            raise RuntimeError(f"批次阈值表引用非百分比快照字段: {attr_name}")
        missing = [key for key in (block_key, warn_key)
                   if key is not None and key not in threshold_names]
        if missing:
            raise RuntimeError(f"批次阈值表引用未定义门限: {missing}")
        if direction not in _THRESHOLD_DIRECTIONS:
            raise RuntimeError(
                f"批次阈值方向非法（未知值会静默按 max 判定）: {direction!r}")
    for attr_name, limit_key, direction, _label in _DELIVERY_AVG_RULES:
        if attr_name not in _AVG_TO_SNAPSHOT_ATTR:
            raise RuntimeError(f"交付平均阈值引用未登记聚合字段: {attr_name}")
        if limit_key not in threshold_names:
            raise RuntimeError(f"交付平均阈值引用未定义门限: {limit_key}")
        if direction not in _THRESHOLD_DIRECTIONS:
            raise RuntimeError(
                f"交付平均阈值方向非法（未知值会静默按 max 判定）: {direction!r}")
    for attr_name, snap_attr in _AVG_TO_SNAPSHOT_ATTR.items():
        if snap_attr not in pct_fields:
            raise RuntimeError(
                "交付平均阈值聚合字段引用非百分比快照字段: "
                f"{attr_name}→{snap_attr}")
_assert_threshold_tables()
def _direction_ops(direction: str) -> tuple[Any, str]:
    return (lt, "<") if direction == "min" else (gt, ">")
def _metric_denominators(snapshot: BatchQualitySnapshot) -> dict[str, int]:
    return {
        "function_coverage_pct": snapshot.public_functions_before,
        "stub_ratio_pct": snapshot.public_functions_after,
        "import_integrity_pct": snapshot.import_chain_total,
        "syntax_pass_pct": snapshot.files_processed,
        "subsystems_preserved_pct": snapshot.subsystems_before,
    }
def _measured_values(snaps: list[BatchQualitySnapshot],
                     attr: str) -> list[float]:
    return [value for value in (getattr(s, attr) for s in snaps)
            if value >= 0]
def _unmeasured_threshold_rows(
        snapshot: BatchQualitySnapshot,
) -> list[tuple[str, str, str | None, str, str]]:
    return [row for row in _BATCH_THRESHOLDS
            if getattr(snapshot, row[0]) < 0]
def _unmeasured_metric_labels(snapshot: BatchQualitySnapshot) -> list[str]:
    return [row[4] for row in _unmeasured_threshold_rows(snapshot)]
def _avg_snapshot_pct(snaps: list[BatchQualitySnapshot],
                      attr: str) -> float | None:
    values = _measured_values(snaps, attr)
    if not values:
        return None
    return round(sum(values) / len(values), 1)
def _pct_rate(numerator: int, denominator: int) -> float:
    if denominator <= 0:
        return _UNMEASURED_PCT
    try:
        ratio = numerator / denominator * 100
    except (OverflowError, ZeroDivisionError) as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_pct_rate:OverflowError')
        return _UNMEASURED_PCT
    return round(min(100.0, ratio), 1)
class BatchQualityMonitor:
    def __init__(self, project_path: str, baseline_dir: str | None = None,
                 persist_baseline: bool = True) -> None:
        project_path = _skill_root("BatchQualityMonitor", project_path)
        persist_baseline = _coerce_flag(
            "BatchQualityMonitor", "persist_baseline", persist_baseline)
        self.project_path = project_path
        self.baseline_dir = _resolve_baseline_dir(
            baseline_dir, persist_baseline, project_path)
        self.persist_baseline = persist_baseline
        self.baseline_file = (
            os.path.join(
                self.baseline_dir, _quality_baseline_filename(project_path))
            if self.baseline_dir else "")
        self._legacy_baseline_file = (
            os.path.join(
                self.baseline_dir,
                f"quality_baseline_{os.path.basename(os.path.normpath(project_path))}.json"
            ) if self.baseline_dir else "")
        self.thresholds = QualityThresholds()
        self._current_batch: str | None = None
        self._batch_start_time: float = 0.0
        self._pending_before: dict[str, int] = {}
        self._pending_label: str = ""
        self._rejected_snapshots: list[str] = []
        self._baseline_load_failed = False
        self.report: OverallQualityReport = OverallQualityReport(project_path=project_path)
        self._file_workloads: list[FileWorkload] = []
        self._refactoring_batches: list[RefactoringBatch] = []
        self._load_baseline()
    def record_file_workload(self, file_path: str, **kwargs: Any) -> FileWorkload:
        _require_nonempty_str(
            "record_file_workload", "file_path", file_path)
        _check_record_field_types(
            "record_file_workload", _WORKLOAD_FIELD_HINTS, kwargs)
        workload = FileWorkload(file_path=file_path, **kwargs)
        self._derive_workload_effort(workload, kwargs)
        self._file_workloads.append(workload)
        return workload
    @staticmethod
    def _derive_workload_effort(workload: FileWorkload,
                                given: dict[str, Any]) -> None:
        if "effort_level" not in given and workload.effective_lines > 0:
            workload.effort_level = effort_level_for_lines(
                workload.effective_lines)
        if "effort_units" not in given and (
                workload.effective_lines > 0 or "effort_level" in given):
            workload.effort_units = EFFORT_UNITS[workload.effort_level]
        if "needs_split" not in given:
            workload.needs_split = (
                workload.effective_lines >= LINES_SPLIT_THRESHOLD)
    def create_refactoring_batch(self, batch_id: str, name: str, **kwargs: Any) -> RefactoringBatch:
        _require_nonempty_str(
            "create_refactoring_batch", "batch_id", batch_id)
        _require_str("create_refactoring_batch", "name", name)
        _check_record_field_types(
            "create_refactoring_batch", _BATCH_FIELD_HINTS, kwargs)
        batch = RefactoringBatch(batch_id=batch_id, name=name, **kwargs)
        self._refactoring_batches.append(batch)
        self._sync_snapshot_counters()
        self._evaluate_delivery_readiness()
        return batch
    @property
    def refactoring_batches(self) -> list[RefactoringBatch]:
        return list(self._refactoring_batches)
    def generate_workload_report(self) -> WorkloadReport:
        total_eu = sum(wl.effort_units for wl in self._file_workloads)
        layer_distribution: dict[str, int] = {}
        effort_distribution: dict[str, int] = {}
        hard_block_files: list[str] = []
        dependency_graph: dict[str, list] = {}
        for wl in self._file_workloads:
            layer_distribution[wl.layer] = (
                layer_distribution.get(wl.layer, 0) + 1)
            effort_key = wl.effort_level.value
            effort_distribution[effort_key] = (
                effort_distribution.get(effort_key, 0) + 1)
            if wl.critical_issues > 0:
                hard_block_files.append(wl.file_path)
            dependency_graph[wl.file_path] = list(wl.imports)
        split_count = sum(1 for wl in self._file_workloads if wl.needs_split)
        summary = (
            f"文件 {len(self._file_workloads)} 个, 总工作量 {total_eu:.2f} EU, "
            f"需拆分 {split_count} 个, 硬阻断 {len(hard_block_files)} 个")
        return WorkloadReport(
            project_path=self.project_path,
            total_files=len(self._file_workloads),
            total_eu=total_eu,
            files=[wl.to_dict() for wl in self._file_workloads],
            dependency_graph=dependency_graph,
            layer_distribution=layer_distribution,
            effort_distribution=effort_distribution,
            hard_block_files=hard_block_files,
            summary=summary,
        )
    def start_batch(self, batch_id: str, batch_label: str = "",
                    files_before: int = 0, lines_before: int = 0,
                    public_functions_before: int = 0,
                    subsystems_before: int = 0) -> BatchQualitySnapshot:
        _require_nonempty_str("start_batch", "batch_id", batch_id)
        _require_str("start_batch", "batch_label", batch_label)
        _check_batch_metric_values(
            "start_batch",
            {"files_total": files_before, "lines_before": lines_before,
             "public_functions_before": public_functions_before,
             "subsystems_before": subsystems_before})
        if self._current_batch:
            raise ValueError(
                f"Active batch {self._current_batch!r}. Call complete_batch() "
                "before starting another batch.")
        self._current_batch = batch_id
        self._batch_start_time = time.time()
        self._pending_before = {
            "files_before": files_before,
            "lines_before": lines_before,
            "public_functions_before": public_functions_before,
            "subsystems_before": subsystems_before,
        }
        self._pending_label = batch_label
        self._evaluate_delivery_readiness()
        return BatchQualitySnapshot(
            batch_id=batch_id, batch_label=batch_label,
            files_total=files_before, lines_before=lines_before,
            public_functions_before=public_functions_before,
            subsystems_before=subsystems_before,
        )
    def _merge_batch_kwargs(self, metrics: dict[str, Any]) -> tuple[dict[str, Any], Any]:
        _consume_batch_aliases(metrics)
        _before = self._pending_before or {}
        kwargs: dict[str, Any] = {}
        for key, attr in _COMPLETE_BATCH_KEYS.items():
            if key in metrics:
                kwargs[attr] = metrics.pop(key)
            elif key in _before:
                kwargs[attr] = _before[key]
        batch_label = metrics.pop("batch_label", self._pending_label)
        return kwargs, batch_label
    def complete_batch(self, **metrics: Any) -> BatchQualitySnapshot:
        if not self._current_batch:
            raise ValueError("No active batch. Call start_batch() first.")
        batch_id = self._current_batch
        kwargs, batch_label = self._merge_batch_kwargs(metrics)
        _check_batch_metric_values("complete_batch", kwargs)
        _require_str("complete_batch", "batch_label", batch_label)
        if metrics:
            valid_keys = set(_COMPLETE_BATCH_KEYS) | set(_BATCH_METRIC_ALIASES)
            valid_keys.add("batch_label")
            raise TypeError(
                "complete_batch: 未登记的批次指标键 "
                f"{sorted(metrics)!r}；合法键为 {sorted(valid_keys)!r}")
        snapshot = BatchQualitySnapshot(
            batch_id=batch_id,
            batch_label=batch_label,
            elapsed_seconds=time.time() - self._batch_start_time,
            **kwargs,
        )
        self._current_batch = None
        self._batch_start_time = 0.0
        self._pending_before = {}
        self._pending_label = ""
        self._absorb_snapshot(snapshot)
        return snapshot
    def _absorb_snapshot(self, snapshot: BatchQualitySnapshot) -> None:
        self._compute_derived_metrics(snapshot)
        self._evaluate_batch(snapshot)
        self.report.snapshots[snapshot.batch_id] = snapshot
        self._sync_snapshot_counters()
        self._update_aggregates()
        self._save_baseline()
    def _sync_snapshot_counters(self) -> None:
        self.report.completed_batches = len(self.report.snapshots)
        self.report.blocked_batches = sum(
            1 for s in self.report.snapshots.values() if s.is_blocking)
        declared_ids = {batch.batch_id for batch in self._refactoring_batches}
        declared_ids.update(self.report.snapshots)
        self.report.total_batches = max(
            self.report.total_batches, len(declared_ids))
    def _compute_derived_metrics(self, snapshot: BatchQualitySnapshot) -> None:
        denominators = _metric_denominators(snapshot)
        numerators = {
            "function_coverage_pct": snapshot.public_functions_after,
            "stub_ratio_pct": snapshot.stub_count,
            "import_integrity_pct": (snapshot.import_chain_total
                                     - snapshot.import_chain_broken),
            "syntax_pass_pct": (denominators["syntax_pass_pct"]
                                - snapshot.syntax_errors),
            "subsystems_preserved_pct": snapshot.subsystems_after,
        }
        for attr, denominator in denominators.items():
            if denominator > 0:
                setattr(snapshot, attr,
                        _pct_rate(numerators[attr], denominator))
            else:
                setattr(snapshot, attr, _UNMEASURED_PCT)
    def _evaluate_batch(self, snapshot: BatchQualitySnapshot) -> None:
        reasons: list[str] = []
        if snapshot.files_processed < snapshot.files_total:
            reasons.append(
                f"文件处理不完整 {snapshot.files_processed}/{snapshot.files_total}："
                "未处理文件不得计为已验收")
        warnings: list[str] = []
        unmeasured_rows = _unmeasured_threshold_rows(snapshot)
        skip_attrs = {row[0] for row in unmeasured_rows}
        unmeasured = [
            f"{row[4]}未度量（缺分母数据，本次不判定）"
            for row in unmeasured_rows]
        T = self.thresholds
        for attr_name, block_key, warn_key, direction, label in _BATCH_THRESHOLDS:
            if attr_name in skip_attrs:
                continue
            value = getattr(snapshot, attr_name)
            block = getattr(T, block_key)
            compare, op = _direction_ops(direction)
            if compare(value, block):
                reasons.append(f"{label} {value}% {op} {block}%")
            elif warn_key is not None:
                warn = getattr(T, warn_key)
                if compare(value, warn):
                    warnings.append(f"{label} {value}% {op} {warn}%")
        snapshot.blocking_reasons = reasons
        snapshot.warnings = warnings + unmeasured
        if reasons:
            snapshot.verdict = QualityVerdict.BLOCK.value
        elif unmeasured:
            snapshot.verdict = _PENDING_VERDICT
        elif warnings:
            snapshot.verdict = QualityVerdict.WARN.value
        else:
            snapshot.verdict = QualityVerdict.PASS.value
    def _update_aggregates(self) -> None:
        snaps = list(self.report.snapshots.values())
        if snaps:
            for report_attr, snap_attr in _AVG_TO_SNAPSHOT_ATTR.items():
                avg = _avg_snapshot_pct(snaps, snap_attr)
                setattr(self.report, report_attr,
                        _UNMEASURED_PCT if avg is None else avg)
            self.report.trend_coverage = _measured_values(
                snaps, "function_coverage_pct")
            self.report.trend_stub = _measured_values(
                snaps, "stub_ratio_pct")
            self.report.trend_import = _measured_values(
                snaps, "import_integrity_pct")
            all_blockings: list[str] = []
            for s in snaps:
                if s.is_blocking:
                    all_blockings.extend(s.blocking_reasons)
            self.report.total_blocking_reasons = all_blockings
        else:
            for report_attr in _AVG_TO_SNAPSHOT_ATTR:
                setattr(self.report, report_attr, _UNMEASURED_PCT)
            self.report.trend_coverage = []
            self.report.trend_stub = []
            self.report.trend_import = []
            self.report.total_blocking_reasons = []
        self._evaluate_delivery_readiness()
    def _evaluate_delivery_readiness(self) -> None:
        T = self.thresholds
        snaps = list(self.report.snapshots.values())
        violations: list[str] = []
        unverified: list[str] = []
        if self._baseline_load_failed:
            unverified.append(
                "既有质量基线读取或归属校验失败，历史证据不完整；"
                "原基线保留且禁止覆盖，不得仅凭新批次判定交付就绪")
        if self._current_batch:
            unverified.append(
                f"批次 {self._current_batch} 进行中（完成前无本轮验收快照），"
                "不得沿用既有批次结论判定交付就绪")
        if self.report.blocked_batches > T.DELIVERY_MAX_BLOCKED_BATCHES:
            violations.append(
                f"存在 {self.report.blocked_batches} 个被阻断批次")
        pending = [s.batch_id for s in snaps
                   if s.verdict == _PENDING_VERDICT]
        if pending:
            unverified.append(
                f"存在 {len(pending)} 个 PENDING 批次（{', '.join(pending)}），"
                "度量未完成，不得判定交付就绪")
        if self._rejected_snapshots:
            unverified.append(
                "基线快照数据损坏（"
                f"{', '.join(sorted(self._rejected_snapshots))}），"
                "度量不完整，不得判定交付就绪")
        missing_batches = max(0, self.report.total_batches - len(snaps))
        if missing_batches:
            unverified.append(
                f"批次台账与快照不一致（声明 {self.report.total_batches} 批，"
                f"快照 {len(snaps)} 份，缺 {missing_batches} 份），"
                "证据不完整，不得判定交付就绪")
        incomplete = [f"{s.batch_id}:{label}" for s in snaps
                      for label in _unmeasured_metric_labels(s)]
        if incomplete:
            preview = ', '.join(incomplete[:5])
            suffix = f" 等 {len(incomplete)} 项" if len(incomplete) > 5 else ""
            unverified.append(
                f"批次指标未度量（{preview}{suffix}），"
                "度量未完成，不得判定交付就绪")
        for attr_name, limit_key, direction, label in _DELIVERY_AVG_RULES:
            if not _measured_values(snaps, _AVG_TO_SNAPSHOT_ATTR[attr_name]):
                unverified.append(
                    f"{label}无有效度量（缺分母数据），不得判定交付就绪")
                continue
            value = getattr(self.report, attr_name)
            limit = getattr(T, limit_key)
            compare, op = _direction_ops(direction)
            if compare(value, limit):
                violations.append(f"{label} {value}% {op} {limit}%")
        self.report.delivery_blockers = violations + unverified
        self.report.delivery_ready = not violations and not unverified
        if violations:
            self.report.final_verdict = QualityVerdict.BLOCK.value
        elif unverified:
            self.report.final_verdict = _PENDING_VERDICT
        else:
            self.report.final_verdict = QualityVerdict.PASS.value
    def _restore_snapshots(self, raw_snapshots: dict) -> list[str]:
        rejected: list[str] = []
        for bid, sdata in raw_snapshots.items():
            try:
                if not isinstance(sdata, dict):
                    raise TypeError(
                        f"快照值非 dict（实际为 {type(sdata).__name__}）")
                _check_batch_metric_values(
                    f"基线快照 {bid}",
                    {key: sdata[key] for key in SNAPSHOT_INT_FIELDS
                     if key in sdata})
                snapshot = build_snapshot_from_baseline(bid, sdata)
                _check_metric_consistency(
                    f"基线快照 {bid}",
                    {key: getattr(snapshot, key) for key in SNAPSHOT_INT_FIELDS})
            except (KeyError, TypeError, ValueError) as e:
                _log.warning(
                    "BatchQualityMonitor: 基线快照 %s 损坏跳过 (%s)", bid, e)
                rejected.append(str(bid))
                continue
            if snapshot.batch_id != bid:
                _log.warning(
                    "BatchQualityMonitor: 基线快照注册键 %r 与内部 batch_id "
                    "%r 不一致，以注册键为准（键即快照身份 SSOT）",
                    bid, snapshot.batch_id)
                snapshot.batch_id = bid
            self._compute_derived_metrics(snapshot)
            self._evaluate_batch(snapshot)
            self.report.snapshots[bid] = snapshot
        return rejected
    def _save_baseline(self) -> None:
        if not self.persist_baseline:
            return
        if self._baseline_load_failed:
            _log.warning(
                "BatchQualityMonitor: 既有基线不可信，拒绝覆盖原文件: %s",
                self.baseline_file)
            return
        if _is_own_artifact_path(self.project_path):
            return
        self._write_baseline_payload(self._baseline_payload())
    def _baseline_payload(self) -> dict:
        return {
            "project_path": os.path.abspath(self.project_path),
            "total_batches": self.report.total_batches,
            "completed_batches": self.report.completed_batches,
            "blocked_batches": self.report.blocked_batches,
            "snapshots": {bid: s.to_dict() for bid, s in self.report.snapshots.items()},
            "rejected_snapshots": list(self._rejected_snapshots),
            "delivery_ready": self.report.delivery_ready,
            "delivery_blockers": self.report.delivery_blockers,
            "final_verdict": self.report.final_verdict,
        }
    def _write_baseline_payload(self, data: dict) -> None:
        try:
            os.makedirs(self.baseline_dir, exist_ok=True)
            payload = json.dumps(data, indent=2, ensure_ascii=False,
                                 default=str)
            with guarded_open(self.baseline_file, "w",
                              encoding="utf-8") as f:
                f.write(payload)
        except (OSError, ValueError, TypeError, RuntimeError,
                RecursionError, ContractViolationError):
            _log.warning("BatchQualityMonitor: 基线写入失败", exc_info=True)
    def _load_baseline(self) -> None:
        if not self.persist_baseline:
            return
        baseline_file = self.baseline_file
        require_project_path = False
        if not os.path.exists(baseline_file):
            baseline_file = self._legacy_baseline_file
            require_project_path = True
        if not baseline_file or not os.path.exists(baseline_file):
            return
        try:
            data = self._read_baseline_payload(
                baseline_file, require_project_path)
            if data is None:
                self._mark_baseline_load_failed()
                return
            self._apply_baseline_payload(data)
        except (AttributeError, KeyError, TypeError, ValueError, RuntimeError,
                RecursionError, OSError) as e:
            self._mark_baseline_load_failed()
            _log.warning("BatchQualityMonitor: 基线加载失败 (%s)", e)
    def _mark_baseline_load_failed(self) -> None:
        self._baseline_load_failed = True
        # _load_baseline 仅在初始化时调用；丢弃部分恢复状态，避免残缺快照参与验收。
        self.report = OverallQualityReport(project_path=self.project_path)
        self._evaluate_delivery_readiness()

    def _read_baseline_payload(self, baseline_file: str,
                               require_project_path: bool) -> dict | None:
        with open(baseline_file, encoding="utf-8-sig") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            _log.warning(
                "BatchQualityMonitor: 基线文件顶层非 dict（实际为 %s），"
                "降级为空基线", type(data).__name__)
            return None
        recorded_project = data.get("project_path")
        if recorded_project is None:
            if require_project_path:
                _log.warning(
                    "BatchQualityMonitor: 旧基线缺少 project_path，无法证明归属，"
                    "拒绝复用同名项目文件 %s", baseline_file)
                return None
            return data
        if not isinstance(recorded_project, str) or not recorded_project:
            _log.warning(
                "BatchQualityMonitor: 基线项目标识非法（实际为 %r），"
                "降级为空基线", recorded_project)
            return None
        if (_norm_project_path(recorded_project)
                != _norm_project_path(self.project_path)):
            _log.warning(
                "BatchQualityMonitor: 基线属于其他项目（%s），"
                "当前项目 %s，拒绝复用同名项目快照",
                recorded_project, self.project_path)
            return None
        return data
    def _apply_baseline_payload(self, data: dict) -> None:
        self.report.total_batches = norm_baseline_field(data, "total_batches", 0)
        declared_completed = norm_baseline_field(data, "completed_batches", 0)
        declared_blocked = norm_baseline_field(data, "blocked_batches", 0)
        raw_snapshots = data.get("snapshots", {})
        invalid_snapshot_section = not isinstance(raw_snapshots, dict)
        if invalid_snapshot_section:
            _log.warning(
                "BatchQualityMonitor: 基线 snapshots 非字典（实际为 %s），"
                "快照区降级为空", type(raw_snapshots).__name__)
            raw_snapshots = {}
        rejected_snapshots = self._restore_snapshots(raw_snapshots)
        if invalid_snapshot_section:
            rejected_snapshots.append("<快照区>")
        persisted_rejected = data.get("rejected_snapshots", [])
        if (not isinstance(persisted_rejected, list)
                or any(not isinstance(bid, str) or not bid
                       for bid in persisted_rejected)):
            _log.warning(
                "BatchQualityMonitor: 基线 rejected_snapshots 形态非法"
                "（实际为 %r），按存在历史损坏证据处理", persisted_rejected)
            rejected_snapshots.append("<历史损坏快照清单>")
            persisted_rejected = []
        self._rejected_snapshots = sorted(
            set(rejected_snapshots) | set(persisted_rejected))
        persisted_ready = (
            norm_baseline_field(data, "delivery_ready", False)
            if "delivery_ready" in data else None)
        persisted_verdict = (
            _norm_final_verdict(
                norm_baseline_field(data, "final_verdict", _PENDING_VERDICT))
            if "final_verdict" in data else None)
        self._sync_snapshot_counters()
        self._warn_counter_drift(declared_completed, declared_blocked)
        self._update_aggregates()
        self._warn_delivery_drift(persisted_ready, persisted_verdict)
    def _warn_counter_drift(self, declared_completed: int,
                            declared_blocked: int) -> None:
        if (declared_completed == self.report.completed_batches
                and declared_blocked == self.report.blocked_batches):
            return
        _log.warning(
            "BatchQualityMonitor: 基线批次计数与快照派生不一致"
            "（落盘 completed=%r/blocked=%r，派生 completed=%r/blocked=%r），"
            "以快照派生为准",
            declared_completed, declared_blocked,
            self.report.completed_batches, self.report.blocked_batches)
    def _warn_delivery_drift(self, persisted_ready: bool | None,
                             persisted_verdict: str | None) -> None:
        recomputed_ready = self.report.delivery_ready
        recomputed_verdict = self.report.final_verdict
        ready_diff = (persisted_ready is not None
                      and persisted_ready != recomputed_ready)
        verdict_diff = (persisted_verdict is not None
                        and persisted_verdict != recomputed_verdict)
        if not ready_diff and not verdict_diff:
            return
        _log.warning(
            "BatchQualityMonitor: 基线交付信号与快照重算不一致"
            "（落盘 ready=%r/verdict=%r，重算 ready=%r/verdict=%r），"
            "以快照重算为准",
            persisted_ready, persisted_verdict,
            recomputed_ready, recomputed_verdict)
_DIR_WARNINGS_PREVIEW = 10
def quick_quality_check(project_path: str, **metrics: Any) -> BatchQualitySnapshot:
    monitor = BatchQualityMonitor(project_path, persist_baseline=False)
    monitor.start_batch(
        "QUICK-CHECK", "快速检查",
        **{key: metrics[key] for key in _BATCH_BEFORE_KEYS if key in metrics})
    snapshot = monitor.complete_batch(**metrics)
    try:
        dir_warnings = dirfile_warning_lines(
            DirFileGuard().check_directory(monitor.project_path))
        if dir_warnings:
            snapshot.warnings.extend(
                dir_warnings[:_DIR_WARNINGS_PREVIEW])
            if len(dir_warnings) > _DIR_WARNINGS_PREVIEW:
                snapshot.warnings.append(
                    f"（目录检查共 {len(dir_warnings)} 项，仅展示前 "
                    f"{_DIR_WARNINGS_PREVIEW} 项）")
            if snapshot.verdict == QualityVerdict.PASS.value:
                snapshot.verdict = QualityVerdict.WARN.value
            _log.warning(
                "目录 %s 大小检查发现 %d 项问题（建议拆分子目录/整合小文件）",
                project_path, len(dir_warnings))
    except (OSError, AttributeError, KeyError, TypeError, ValueError, RuntimeError) as e:
        _log.warning("directory size check failed（目录检查未执行，快照结论缺少该项证据）: %s", e, exc_info=True)
        snapshot.warnings.append(
            f"目录检查未执行（{type(e).__name__}: {e}）")
        if snapshot.verdict == QualityVerdict.PASS.value:
            snapshot.verdict = QualityVerdict.WARN.value
    return snapshot
def _rebuild_coverage_errors(coverage_rate: float, stub_rate: float,
                             subsystem_loss: list) -> list[str]:
    errors: list[str] = []
    if coverage_rate < QualityThresholds.BLOCK_FUNCTION_COVERAGE / 100.0:
        errors.append(
            f"API覆盖率{coverage_rate*100:.0f}%"
            f" < {QualityThresholds.BLOCK_FUNCTION_COVERAGE:.0f}%阈值")
    if stub_rate > QualityThresholds.BLOCK_STUB_RATIO / 100.0:
        errors.append(
            f"空桩率{stub_rate*100:.0f}%"
            f" > {QualityThresholds.BLOCK_STUB_RATIO:.0f}%阈值")
    if subsystem_loss:
        errors.append(f"函数丢失（基线有而新架构无）: {subsystem_loss}")
    return errors
def _rebuild_scan_completeness_errors(
        old_path: str, new_path: str,
        old_stats: dict, new_stats: dict) -> list[str]:
    errors: list[str] = []
    for label, path, stats in (
            ("旧项目", old_path, old_stats), ("新项目", new_path, new_stats)):
        source_count = len(collect_baseline_py_files(path))
        parsed_count = stats["total_files"]
        if source_count == 0:
            errors.append(
                f"{label}源码扫描未度量：未找到 Python 源文件；"
                "空项目不得按 100% 函数覆盖与架构容量判定通过")
            continue
        if parsed_count != source_count:
            errors.append(
                f"{label}源码扫描不完整：成功解析 {parsed_count}/{source_count} "
                "个 Python 文件；不可读或不可解析文件不得被跳过后代入 "
                "100% 函数覆盖与架构容量判定，须先修复扫描输入")
    return errors
def quick_rebuild_check(old_path: str, new_path: str) -> dict:
    old_path = _skill_root("quick_rebuild_check", old_path)
    new_path = _skill_root("quick_rebuild_check", new_path)
    old_stats = ArchitectureCapacityValidator.quick_scan(old_path)
    new_stats = ArchitectureCapacityValidator.quick_scan(new_path)
    scan_errors = _rebuild_scan_completeness_errors(
        old_path, new_path, old_stats, new_stats)
    if scan_errors:
        return {"passed": False, "phase": "capacity",
                "errors": scan_errors}
    verdict = ArchitectureCapacityValidator.validate(
        old_stats,
        {
            "total_files": new_stats["total_files"],
            "target_files_by_subsystem": {
                name: info.get("files", 0)
                for name, info in new_stats["subsystems"].items()
            },
        })
    if not verdict.passed:
        return {"passed": False, "phase": "capacity",
                "errors": list(verdict.errors)}
    old_functions = FunctionMappingGenerator(old_path).extract_functions()
    new_gen = FunctionMappingGenerator(new_path)
    new_functions = new_gen.extract_functions()
    mapping_result = new_gen.generate_mapping(old_functions, new_functions)
    trend = BatchQualityTrendMonitor().analyze(old_functions, new_functions)
    coverage_rate = mapping_result["coverage_rate"]
    stub_rate = trend["stub_rate"]
    subsystem_loss = trend["subsystem_loss"]
    errors = _rebuild_coverage_errors(coverage_rate, stub_rate, subsystem_loss)
    return {
        "passed": not errors,
        "phase": "verify",
        "errors": errors,
        "data": {
            "coverage_rate": coverage_rate,
            "missing_functions": mapping_result["missing_count"],
            "stub_rate": stub_rate,
            "subsystem_loss": subsystem_loss,
            "quality_score": trend["quality_score"],
        },
    }
BASELINE_FILENAME = "governance_baseline.json"
DECISIONS_FILENAME = "governance_decisions.jsonl"
ACCEPTANCE_FILENAME = "governance_acceptance.jsonl"
_JSONL_MAX_BYTES = 8 * 1024 * 1024
TEST_STATUS_VALUES: tuple[str, ...] = (
    "passed", "failed", "error", "skipped", "not_run",
)
ACCEPTANCE_METRICS: tuple[dict[str, str], ...] = (
    {
        "key": "cycles",
        "name": "循环依赖数",
        "rule": "不高于基线，且环集合无新增",
        "direction": "not_increase",
    },
    {
        "key": "illegal_imports",
        "name": "跨模块非法导入数",
        "rule": "为 0（深层路径/内部符号/未登记子模块/星号导入）",
        "direction": "zero",
    },
    {
        "key": "public_api",
        "name": "公共 API 数量",
        "rule": "不膨胀；新增/删除导出符号须显式声明并评估影响",
        "direction": "not_expand_undeclared",
    },
    {
        "key": "complexity",
        "name": "复杂度指标",
        "rule": "平均/最大圈复杂度不劣化；提供健康分时健康分不下降",
        "direction": "not_worse",
    },
    {
        "key": "tests",
        "name": "测试",
        "rule": "全部通过（failed/error/skipped/not_run 均不达标）",
        "direction": "all_pass",
    },
    {
        "key": "merge_decisions",
        "name": "合并决策",
        "rule": "每个合并动作有 pros/cons/net_benefit=positive 的留痕记录",
        "direction": "recorded",
    },
)
_METRIC_SPECS: dict[str, dict[str, str]] = {
    item["key"]: item for item in ACCEPTANCE_METRICS
}
_GOVERNANCE_ARTIFACT_RESOLVERS = {
    BASELINE_FILENAME: governance_baseline_path,
    DECISIONS_FILENAME: governance_decisions_path,
    ACCEPTANCE_FILENAME: governance_acceptance_path,
}
def _jinhua_file(skill_dir: str, filename: str) -> str:
    resolver = _GOVERNANCE_ARTIFACT_RESOLVERS.get(filename)
    if resolver is None:
        raise ValueError(
            f"{filename!r} 不是治理门禁产物；已登记: "
            f"{sorted(_GOVERNANCE_ARTIFACT_RESOLVERS)}")
    return resolver(skill_dir)
def capture_baseline(
        skill_dir: str, include_tests: bool = False,
        health_score: float | None = None,
        round_start_ts: str = "") -> dict[str, Any]:
    skill_dir = _skill_root(
        "capture_baseline", skill_dir, require_existing=True)
    include_tests = _coerce_flag(
        "capture_baseline", "include_tests", include_tests)
    metrics = capture_governance_metrics(skill_dir, include_tests, health_score)
    return {
        "schema_version": 1,
        "captured_at": now_iso_seconds(),
        "captured_at_ts": timestamp_ms(),
        "round_start_ts": str(round_start_ts or ""),
        "skill_dir": os.path.abspath(skill_dir),
        "include_tests": include_tests,
        "metrics": metrics,
    }
def save_baseline(skill_dir: str, baseline: dict | None = None,
                  **kwargs: Any) -> str:
    if baseline is not None and not isinstance(baseline, dict):
        raise TypeError(
            "save_baseline: baseline 须为 dict 或 None，实际为 "
            f"{type(baseline).__name__}")
    skill_dir = _skill_root(
        "save_baseline", skill_dir, require_existing=True)
    payload = capture_baseline(
        skill_dir, **kwargs) if baseline is None else baseline
    path = _jinhua_file(skill_dir, BASELINE_FILENAME)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    try:
        write_json_artifact(path, payload, indent=1)
    except RecursionError as exc:
        raise ValueError(f"基线载荷嵌套过深，无法序列化: {exc}") from exc
    _log.info("[Governance] 基线已保存: %s", path)
    return path
def load_baseline(skill_dir: str) -> dict | None:
    path = _jinhua_file(_skill_root("load_baseline", skill_dir),
                        BASELINE_FILENAME)
    try:
        with open(path, encoding="utf-8-sig") as handle:
            data = json.load(handle)
    except (OSError, ValueError, RuntimeError, RecursionError) as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='load_baseline:OSError+')
        return None
    return data if isinstance(data, dict) else None
def _append_jsonl(path: str, entry: dict) -> None:
    try:
        line = json.dumps(entry, ensure_ascii=False, default=str)
        if not append_jsonl_locked(path, line):
            _log.warning("[Governance] 留痕写入失败（不阻断）: %s", path)
            return
        prune_jsonl_file(path, _JSONL_MAX_BYTES)
    except (OSError, TypeError, ValueError, RecursionError) as exc:
        _log.warning("[Governance] 留痕写入失败（不阻断）: %s", exc)
def record_decision(
        skill_dir: str, kind: str, target: Any,
        payload: dict | None = None, decision: str = "",
        rationale: str = "", approved_by: str = "") -> dict[str, Any]:
    skill_dir = _skill_root("record_decision", skill_dir)
    entry = build_decision_record(
        kind=kind, target=target, payload=payload, decision=decision,
        rationale=rationale, approved_by=approved_by, skill_dir=skill_dir)
    _append_jsonl(_jinhua_file(skill_dir, DECISIONS_FILENAME), entry)
    return entry
def _acceptance_passed_flag(value: Any) -> bool:
    if value is True:
        return True
    if value is not False and value is not None:
        _log.warning("[Acceptance] passed 非布尔(%s)，按未通过留痕: %r",
                     type(value).__name__, value)
    return False
def _failed_metric_names(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value] if value else []
    if not isinstance(value, (list, tuple)):
        if value is not None:
            _log.warning(
                "[Acceptance] failed_metrics 形态非法(%s)，按空处理: %r",
                type(value).__name__, value)
        return []
    return [item for item in value if isinstance(item, str) and item]
def _rollback_entry(value: Any) -> dict:
    if isinstance(value, dict):
        return dict(value)
    if value is not None:
        _log.warning("[Acceptance] rollback 形态非法(%s)，按空计划留痕: %r",
                     type(value).__name__, value)
    return {}
def _accepted_metric_entries(value: Any) -> list[dict]:
    if isinstance(value, (list, tuple)):
        entries = [item for item in value if isinstance(item, dict)]
        dropped = len(value) - len(entries)
        if dropped:
            _log.warning(
                "[Acceptance] metrics 有 %d 项非 mapping，已剔除: %r",
                dropped, value)
        return entries
    if value is not None:
        _log.warning("[Acceptance] metrics 形态非法(%s)，按空处理: %r",
                     type(value).__name__, value)
    return []
def record_acceptance(skill_dir: str, result: dict[str, Any]) -> dict[str, Any]:
    if not isinstance(result, dict):
        raise TypeError(
            "record_acceptance: result 须为 dict，实际为 "
            f"{type(result).__name__}")
    skill_dir = _skill_root("record_acceptance", skill_dir)
    entry = {
        "kind": "acceptance",
        "at": now_iso_seconds(),
        "at_ts": timestamp_ms(),
        "trace_version": 1,
        "passed": _acceptance_passed_flag(result.get("passed")),
        "failed_metrics": _failed_metric_names(result.get("failed_metrics")),
        "rollback": _rollback_entry(result.get("rollback")),
        "metrics": _accepted_metric_entries(result.get("metrics")),
        "baseline_at": result.get("baseline_at", ""),
        "round_start_ts": result.get("round_start_ts", ""),
    }
    _append_jsonl(_jinhua_file(skill_dir, ACCEPTANCE_FILENAME), entry)
    return entry
def _decision_from_line(line: str) -> dict | None:
    text = line.strip()
    if not text:
        return None
    try:
        entry = json.loads(text)
    except (ValueError, RecursionError) as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_decision_from_line:ValueError+')
        return None
    return entry if isinstance(entry, dict) else None
def load_decisions(skill_dir: str, kind: str = "") -> list[dict]:
    path = _jinhua_file(_skill_root("load_decisions", skill_dir),
                        DECISIONS_FILENAME)
    try:
        with open(path, encoding="utf-8-sig", errors="replace") as handle:
            lines = handle.readlines()
    except OSError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='load_decisions:OSError')
        return []
    results: list[dict] = []
    for line in lines:
        entry = _decision_from_line(line)
        if entry is None or (kind and entry.get("kind") != kind):
            continue
        results.append(entry)
    return results
def merge_target_key(action: Any, skill_dir: str) -> str:
    skill_dir = normalize_skill_dir(skill_dir) if skill_dir else ""
    sources = (action_field(action, "source_files")
               or action_field(action, "merge_sources")
               or action_field(action, "source")
               or action_field(action, "target") or [])
    if isinstance(sources, str):
        sources = [sources]
    keys: list[str] = []
    for item in sources:
        key = decision_target_key(item, skill_dir)
        if not key:
            return ""
        keys.append(key)
    keys = sorted(keys)
    # 单来源自身也可能含分隔符；所有来源统一转义才能避免跨来源形状碰撞。
    keys = [key.replace("%", "%25").replace(",", "%2c")
            for key in keys]
    return ",".join(keys)
def _merge_action_list(merge_actions: Iterable[Any] | None) -> list[Any]:
    if merge_actions is None:
        return []
    if isinstance(merge_actions, dict):
        return [merge_actions]
    if isinstance(merge_actions, (str, bytes)):
        raise TypeError(
            "merge_actions 须为合并动作或可迭代动作清单，"
            f"不得为 {type(merge_actions).__name__}；"
            "非法形状不能等价于无合并动作")
    return list(merge_actions)
def merge_decisions_recorded(
        skill_dir: str, merge_actions: Iterable[Any] | None = None,
        since_ts: str = "") -> tuple[bool, list[str]]:
    skill_dir = _skill_root("merge_decisions_recorded", skill_dir)
    actions = _merge_action_list(merge_actions)
    if not actions:
        return True, []
    since = str(since_ts or "")
    indexed = {decision_target_key(record.get("target", ""), skill_dir): record
               for record in load_decisions(skill_dir, kind="merge")
               if str(record.get("at_ts", "")) >= since}
    missing = [problem for action in actions
               if (problem := _merge_decision_problem(
                   action, indexed, skill_dir))]
    return (not missing), missing
_DECISION_APPROVE_VALUES = frozenset({
    "approve", "approve_and_fix", "approved", "accept", "accepted",
    "pass", "passed",
})
def _merge_decision_problem(
        action: Any, indexed: dict[str, dict], skill_dir: str) -> str:
    key = merge_target_key(action, skill_dir)
    if not key:
        return ("合并动作 <unknown> 无决策留痕：缺少 "
                "source_files/merge_sources/source/target，"
                "不得与空目标台账记录匹配")
    record = indexed.get(key)
    if record is None:
        return f"合并动作 {key} 无决策留痕"
    decision = str(record.get("decision") or "").strip().lower()
    if decision not in _DECISION_APPROVE_VALUES:
        return (f"合并动作 {key} 的决策为 {decision!r}（未批准），"
                "不得以论证合规为由放行")
    payload = record.get("payload")
    if not isinstance(payload, dict):
        payload = {}
    valid, errors = validate_merge_argument(
        payload.get("pros"), payload.get("cons"),
        payload.get("net_benefit"), payload.get("risk", ""))
    if valid:
        return ""
    return f"合并动作 {key} 论证不合规：" + "；".join(errors)
def _metric_result(key: str, passed: bool, baseline: Any, current: Any,
                   detail: str = "", waived: bool = False) -> dict[str, Any]:
    spec = _METRIC_SPECS[key]
    return {
        "key": key,
        "name": spec["name"],
        "rule": spec["rule"],
        "verdict": "pass" if passed else "fail",
        "baseline": baseline,
        "current": current,
        "detail": detail,
        "waived": bool(waived),
    }
def _diff_sets(current: Iterable[str], baseline: Iterable[str]) -> tuple[set, set]:
    cur = set(current or ())
    base = set(baseline or ())
    return cur - base, base - cur
_VIOLATION_KEY_FIELDS = 6
_VIOLATION_LINE_INDEX = 2
def _violation_identity(key: Any) -> str:
    parts = str(key).split("|")
    if len(parts) != _VIOLATION_KEY_FIELDS:
        return str(key)
    return "|".join(parts[:_VIOLATION_LINE_INDEX]
                      + parts[_VIOLATION_LINE_INDEX + 1:])
def _baseline_missing_result(skill_dir: str, rollback_id: str,
                             record: bool, auto_rollback: bool,
                             reason: str = "") -> dict[str, Any]:
    rollback = _rollback_plan(
        [{"verdict": "fail",
          "detail": (reason or
                     "基线缺失：须先 capture_baseline/save_baseline 再治理")}],
        rollback_id, auto_rollback)
    result = {
        "passed": False,
        "failed_metrics": ["baseline"],
        "metrics": [],
        "rollback": rollback,
        "baseline_at": "",
        "checked_at": now_iso_seconds(),
        "skill_dir": os.path.abspath(skill_dir),
    }
    if record:
        _record_acceptance_outcome(skill_dir, result)
    return result
def _baseline_project_mismatch(skill_dir: str,
                               baseline: dict[str, Any]) -> str:
    recorded = str(baseline.get("skill_dir") or "").strip()
    if not recorded:
        return ""
    if (_norm_project_path(recorded)
            == _norm_project_path(skill_dir)):
        return ""
    return ("基线项目不匹配：基线属于 "
            f"{os.path.abspath(recorded)}，当前项目 "
            f"{os.path.abspath(skill_dir)}；须重新 capture_baseline")
def _norm_project_path(path: str) -> str:
    return os.path.normcase(os.path.realpath(
        normalize_skill_dir(os.path.expanduser(path))))
def _quality_baseline_filename(project_path: str) -> str:
    identity = _norm_project_path(project_path).encode("utf-8", "surrogatepass")
    digest = hashlib.sha256(identity).hexdigest()
    return f"quality_baseline_{digest}.json"
def _baseline_str_list(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value] if value else []
    if not isinstance(value, (list, tuple, set, frozenset)):
        return []
    return [str(item) for item in value if str(item).strip()]
def _baseline_int(value: Any, default: int = 0) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        return default
    return value
def _metrics_scan_completeness_error(metrics: Any, subject: str) -> str:
    if not isinstance(metrics, dict):
        return ""
    complexity = metrics.get("complexity")
    if not isinstance(complexity, dict):
        return ""
    scanned = metrics.get("scanned_files")
    parsed = complexity.get("scanned_files")
    if type(scanned) is not int or type(parsed) is not int:
        return (f"{subject}源码扫描计数缺失或非法"
                f"（scanned_files={scanned!r}，"
                f"complexity.scanned_files={parsed!r}），证据无效")
    if scanned < 0 or parsed < 0:
        return f"{subject}源码扫描计数为负（{scanned}/{parsed}），证据无效"
    if parsed != scanned:
        return (f"{subject}源码扫描不完整：边界扫描 {scanned} 个 Python 文件，"
                f"复杂度成功解析 {parsed} 个；不可解析文件不得从验收中消失")
    if scanned == 0:
        return (f"{subject}源码扫描未度量：未找到 Python 源文件；"
                "空扫描不得按六项指标全部通过")
    return ""
def _baseline_metrics_shape_errors(metrics: Any) -> list[str]:
    if not isinstance(metrics, dict):
        return ["metrics 非 dict"]
    errors: list[str] = []
    for key in ("cycles", "illegal_imports"):
        value = metrics.get(key)
        if value is None:
            errors.append(f"{key} 缺失或为 null")
        elif not isinstance(value, (list, tuple)):
            errors.append(f"{key} 非序列")
    public = metrics.get("public_api")
    if public is None:
        errors.append("public_api 缺失或为 null")
    elif not isinstance(public, dict):
        errors.append("public_api 非 dict")
    else:
        symbols = public.get("symbols")
        if symbols is not None and not isinstance(symbols, (list, tuple)):
            errors.append("public_api.symbols 非序列")
        count = public.get("count")
        if count is not None and (isinstance(count, bool)
                                  or not isinstance(count, int)):
            errors.append("public_api.count 非整数")
        if "complete" in public and type(public["complete"]) is not bool:
            errors.append("public_api.complete 非布尔值")
    complexity = metrics.get("complexity")
    if complexity is not None:
        if not isinstance(complexity, dict):
            errors.append("complexity 非 dict")
        else:
            avg = complexity.get("avg_complexity")
            if avg is not None and finite_float_or_none(avg) is None:
                errors.append("complexity.avg_complexity 非有限数值")
            maximum = complexity.get("max_complexity")
            if maximum is not None and (isinstance(maximum, bool)
                                        or not isinstance(maximum, int)):
                errors.append("complexity.max_complexity 非整数")
    health_score = metrics.get("health_score")
    if health_score is not None and finite_float_or_none(health_score) is None:
        errors.append("health_score 类型非法或非有限数值")
    scan_error = _metrics_scan_completeness_error(metrics, "基线")
    if scan_error:
        errors.append(scan_error)
    return errors
def _normalize_baseline_metrics(metrics: Any) -> dict[str, Any]:
    src = metrics if isinstance(metrics, dict) else {}
    public = src.get("public_api")
    public = public if isinstance(public, dict) else {}
    complexity = src.get("complexity")
    complexity = complexity if isinstance(complexity, dict) else {}
    return {
        "cycles": _baseline_str_list(src.get("cycles")),
        "illegal_imports": _baseline_str_list(src.get("illegal_imports")),
        "public_api": {
            "count": _baseline_int(public.get("count")),
            "symbols": _baseline_str_list(public.get("symbols")),
            "has_all": public.get("has_all") is True,
            "complete": public.get("complete", True) is not False,
            "symbols_known": "symbols" in public,
        },
        "complexity": {
            "function_count": _baseline_int(complexity.get("function_count")),
            "total_complexity": _baseline_int(complexity.get("total_complexity")),
            "max_complexity": _baseline_int(complexity.get("max_complexity")),
            "avg_complexity": finite_float_or_none(
                complexity.get("avg_complexity")) or 0.0,
            "scanned_files": _baseline_int(complexity.get("scanned_files")),
            "available": bool(complexity) and all(
                complexity.get(key) is not None
                for key in ("avg_complexity", "max_complexity")),
        },
        "health_score": finite_float_or_none(src.get("health_score")),
        "scanned_files": _baseline_int(src.get("scanned_files")),
    }
def _cycles_metric(base_metrics: dict, current: dict) -> dict[str, Any]:
    base_cycles = list(base_metrics.get("cycles") or ())
    current_cycles = list(current["cycles"])
    new_cycles, gone_cycles = _diff_sets(current_cycles, base_cycles)
    count_increased = len(current_cycles) > len(base_cycles)
    detail = ("新增环: " + "; ".join(sorted(new_cycles)) if new_cycles
              else f"无新增环（消除 {len(gone_cycles)} 个）")
    if count_increased:
        detail = (f"环数量增加: {len(base_cycles)}→{len(current_cycles)}；"
                  + detail)
    return _metric_result(
        "cycles", not new_cycles and not count_increased,
        len(base_cycles), len(current_cycles), detail=detail)
def _illegal_imports_metric(base_metrics: dict, current: dict,
                            allow_legacy_imports: bool) -> dict[str, Any]:
    base_keys = list(base_metrics.get("illegal_imports") or ())
    cur_illegal = current["illegal_imports"]
    base_counts = Counter(_violation_identity(key) for key in base_keys)
    cur_counts = Counter(_violation_identity(key) for key in cur_illegal)
    added_counts = cur_counts - base_counts
    new_count = sum(added_counts.values())
    if allow_legacy_imports:
        passed = not new_count
        detail = (f"legacy ratchet 模式：新增 {new_count}，"
                  f"存量 {len(cur_illegal)}/{len(base_keys)}")
        if any(base_counts[key] and count > base_counts[key]
               for key, count in cur_counts.items()):
            detail += "（同型违规重复，存量超基线）"
    else:
        passed = not cur_illegal
        detail = (f"严格模式：当前 {len(cur_illegal)} 条"
                  + (f"，新增 {new_count} 条" if new_count else ""))
    return _metric_result(
        "illegal_imports", passed, len(base_keys), len(cur_illegal),
        detail=detail,
        waived=bool(allow_legacy_imports and passed and cur_illegal))
def _declared_symbol_set(declarations: Iterable[str] | None) -> set[str]:
    if isinstance(declarations, str):
        return {declarations} if declarations else set()
    return set(declarations or ())
def _public_api_metric(base_metrics: dict, current: dict,
                       declared_additions: Iterable[str] | None,
                       declared_removals: Iterable[str] | None
                       ) -> dict[str, Any]:
    base_api = base_metrics.get("public_api") or {}
    cur_api = current["public_api"]
    base_count = base_api.get("count", 0)
    cur_count = cur_api["count"]
    incomplete_sources = [
        label for label, api in (("基线", base_api), ("当前", cur_api))
        if api.get("complete") is False
    ]
    if incomplete_sources:
        return _metric_result(
            "public_api", False, base_count, cur_count,
            detail=("、".join(incomplete_sources)
                    + "公共 API 导出不完整（动态 __all__ 无法静态定论），"
                      "无法判定符号级新增/删除：须补充可静态定论的导出声明"
                      "后重跑验收"))
    if base_count and not base_api.get("symbols_known", True):
        return _metric_result(
            "public_api", False, base_count, cur_count,
            detail=(f"基线缺公共 API 符号表（count={base_count}），"
                    "无法判定符号级新增/删除：须重跑 "
                    "capture_baseline/save_baseline"))
    base_symbols = set(base_api.get("symbols") or ())
    cur_symbols = set(cur_api.get("symbols") or ())
    added, removed = _diff_sets(cur_symbols, base_symbols)
    declared_add = _declared_symbol_set(declared_additions)
    declared_del = _declared_symbol_set(declared_removals)
    undeclared = (added - declared_add) | (removed - declared_del)
    expected_count = base_count + len(added) - len(removed)
    count_gap = cur_count != expected_count
    detail = _api_change_detail(added, removed, undeclared)
    if count_gap:
        detail = "；".join(filter(None, [detail, (
            f"计数不一致: 基线 {base_count} + 新增 {len(added)} "
            f"- 删除 {len(removed)} = {expected_count}，当前 {cur_count}")]))
    return _metric_result(
        "public_api", not undeclared and not count_gap,
        base_count, cur_count, detail=detail)
def _api_change_detail(added: set[str], removed: set[str],
                       undeclared: set[str]) -> str:
    parts: list[str] = []
    if added:
        parts.append("新增: " + ",".join(sorted(added)))
    if removed:
        parts.append("删除: " + ",".join(sorted(removed)))
    if undeclared:
        parts.append("未声明变更: " + ",".join(sorted(undeclared)))
    return "；".join(parts) or "公共 API 无变化"
def _coerce_health_score(value: Any) -> float | None:
    score = finite_float_or_none(value)
    if value is None or score is not None:
        return score
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        _log.warning("[Acceptance] health_score 类型非法(%s)，按缺失处理",
                     type(value).__name__)
    else:
        _log.warning("[Acceptance] health_score 非有限值(%s)，按缺失处理",
                     type(value).__name__)
    return None
def _complexity_metric(base_metrics: dict, current: dict,
                       health_score: float | None) -> dict[str, Any]:
    base_cx = base_metrics.get("complexity") or {}
    raw_health_score = health_score
    health_score = _coerce_health_score(health_score)
    invalid_health = raw_health_score is not None and health_score is None
    cur_cx = current["complexity"]
    if not base_cx.get("available", True):
        return _metric_result(
            "complexity", False,
            {"avg": None, "max": None, "health": None},
            {"avg": cur_cx["avg_complexity"],
             "max": cur_cx["max_complexity"], "health": health_score},
            detail=("基线缺复杂度指标（complexity 段缺失、为空或缺平均/最大复杂度），"
                    "无法判定劣化：须重跑 "
                    "capture_baseline/save_baseline"))
    passed = (
        cur_cx["avg_complexity"] <= float(base_cx.get("avg_complexity", 0)) + 1e-9
        and cur_cx["max_complexity"] <= int(base_cx.get("max_complexity", 0)))
    detail = (
        f"平均 {base_cx.get('avg_complexity', 0)}→{cur_cx['avg_complexity']}，"
        f"最大 {base_cx.get('max_complexity', 0)}→{cur_cx['max_complexity']}")
    scan_error = _metrics_scan_completeness_error(current, "当前")
    if scan_error:
        passed = False
        detail = scan_error + "；" + detail
    base_health = base_metrics.get("health_score")
    if invalid_health:
        passed = False
        detail += (f"，健康分 {raw_health_score!r} 类型非法或非有限，"
                   "不得按未提供跳过验收")
    elif (health_score is not None
            and isinstance(base_health, (int, float))
            and not isinstance(base_health, bool)):
        passed = passed and float(health_score) >= float(base_health) - 1e-9
        detail += f"，健康分 {base_health}→{health_score}"
    return _metric_result(
        "complexity", passed,
        {"avg": base_cx.get("avg_complexity", 0),
         "max": base_cx.get("max_complexity", 0),
         "health": base_health},
        {"avg": cur_cx["avg_complexity"], "max": cur_cx["max_complexity"],
         "health": health_score},
        detail=detail)
def _tests_metric(test_status: str) -> dict[str, Any]:
    status = str(test_status or DEFAULT_TEST_STATUS)
    if status not in TEST_STATUS_VALUES:
        _log.warning(
            "[Acceptance] 测试状态 %r 不在值域 %s，按不达标判定",
            status, list(TEST_STATUS_VALUES))
    passed = status == "passed"
    return _metric_result(
        "tests", passed, "passed", status,
        detail=("全部通过" if passed
                else f"测试状态 {status!r} 不达标（须为 passed）"))
def _merge_decisions_metric(skill_dir: str, base: dict,
                            merge_actions: Iterable[Any] | None
                            ) -> dict[str, Any]:
    actions = _merge_action_list(merge_actions)
    ok, missing = merge_decisions_recorded(
        skill_dir, actions, str(base.get("captured_at_ts", "")))
    return _metric_result(
        "merge_decisions", ok,
        "有记录" if not actions else f"{len(actions)} 个合并动作",
        "有记录" if ok else "缺失/不合规",
        detail=("；".join(missing) if missing
                else ("无合并动作" if not actions else "全部合并动作有合规论证留痕")))
def _execute_rollback(rollback_id: str) -> dict[str, Any]:
    try:
        return {"executed": execute_rollback(rollback_id),
                "executed_at": now_iso_seconds()}
    except Exception as exc:
        _log.warning("[Governance] 定向回滚执行失败: %s", exc)
        return {"executed": {rollback_id: False}, "error": str(exc)}
def _rollback_plan(metrics: list[dict[str, Any]], rollback_id: str,
                   auto_rollback: bool) -> dict[str, Any]:
    auto_rollback = _coerce_flag(
        "_rollback_plan", "auto_rollback", auto_rollback)
    failed = [item for item in metrics if item["verdict"] != "pass"]
    required = bool(failed)
    plan: dict[str, Any] = {
        "required": required,
        "rollback_id": rollback_id,
        "reason": ("；".join(item["detail"] for item in failed)
                   if failed else ""),
        "command": (f"execute_rollback({rollback_id!r})"
                    if (required and rollback_id) else ""),
    }
    if required and auto_rollback and rollback_id:
        plan.update(_execute_rollback(rollback_id))
    return plan
def _record_acceptance_outcome(
        skill_dir: str, result: dict[str, Any]) -> None:
    record_acceptance(skill_dir, result)
    failed = result["failed_metrics"]
    rollback = result["rollback"]
    record_decision(
        skill_dir, "acceptance",
        target="六项基线验收",
        payload={"failed_metrics": failed},
        decision="pass" if result["passed"] else "rollback",
        rationale=rollback["reason"] or "六项指标全部达标")
def check_acceptance(
        skill_dir: str, baseline: dict | None = None,
        test_status: str = DEFAULT_TEST_STATUS,
        merge_actions: Iterable[Any] | None = None,
        declared_api_additions: Iterable[str] | None = None,
        declared_api_removals: Iterable[str] | None = None,
        allow_legacy_imports: bool = False,
        health_score: float | None = None,
        rollback_id: str = "",
        record: bool = True,
        auto_rollback: bool = _DEFAULT_AUTO_ROLLBACK) -> dict[str, Any]:
    skill_dir = _skill_root(
        "check_acceptance", skill_dir, require_existing=True)
    if baseline is not None and not isinstance(baseline, dict):
        raise TypeError(
            "check_acceptance: baseline 须为 dict 或 None，实际为 "
            f"{type(baseline).__name__}")
    allow_legacy_imports = _coerce_flag(
        "check_acceptance", "allow_legacy_imports", allow_legacy_imports)
    record = _coerce_flag("check_acceptance", "record", record)
    auto_rollback = _coerce_flag(
        "check_acceptance", "auto_rollback", auto_rollback)
    base = load_baseline(skill_dir) if baseline is None else baseline
    if not isinstance(base, dict):
        return _baseline_missing_result(
            skill_dir, rollback_id, record, auto_rollback)
    mismatch = _baseline_project_mismatch(skill_dir, base)
    if mismatch:
        return _baseline_missing_result(
            skill_dir, rollback_id, record, auto_rollback, reason=mismatch)
    try:
        include_tests = _coerce_flag(
            "check_acceptance", "baseline.include_tests",
            base.get("include_tests", False))
    except TypeError as exc:
        return _baseline_missing_result(
            skill_dir, rollback_id, record, auto_rollback,
            reason=f"基线 include_tests 非法（{exc}）；须重新 capture_baseline/save_baseline")
    raw_metrics = base.get("metrics")
    shape_errors = _baseline_metrics_shape_errors(raw_metrics)
    if shape_errors:
        return _baseline_missing_result(
            skill_dir, rollback_id, record, auto_rollback,
            reason=("基线指标段格式非法（" + "；".join(shape_errors)
                    + "）：须重新 capture_baseline/save_baseline 再治理"))
    base_metrics = _normalize_baseline_metrics(raw_metrics)
    current = capture_governance_metrics(
        skill_dir, include_tests, health_score)
    metrics = [
        _cycles_metric(base_metrics, current),
        _illegal_imports_metric(base_metrics, current, allow_legacy_imports),
        _public_api_metric(base_metrics, current, declared_api_additions,
                           declared_api_removals),
        _complexity_metric(base_metrics, current, health_score),
        _tests_metric(test_status),
        _merge_decisions_metric(skill_dir, base, merge_actions),
    ]
    failed = [item["key"] for item in metrics if item["verdict"] != "pass"]
    rollback = _rollback_plan(metrics, rollback_id, auto_rollback)
    result = {
        "passed": not failed,
        "failed_metrics": failed,
        "metrics": metrics,
        "rollback": rollback,
        "baseline_at": str(base.get("captured_at") or ""),
        "round_start_ts": str(base.get("round_start_ts") or ""),
        "checked_at": now_iso_seconds(),
        "skill_dir": os.path.abspath(skill_dir),
    }
    if record:
        _record_acceptance_outcome(skill_dir, result)
    return result
def format_acceptance_checklist(result: dict[str, Any]) -> str:
    lines = [
        "| # | 指标 | 判定规则 | 基线 | 当前 | 结论 | 证据 |",
        "|---|---|---|---|---|---|---|",
    ]
    for index, item in enumerate(result.get("metrics") or (), 1):
        verdict = "PASS" if item.get("verdict") == "pass" else "FAIL"
        if item.get("waived"):
            verdict += "（豁免）"
        lines.append(
            f"| {index} | {item.get('name', '')} | {item.get('rule', '')} "
            f"| {item.get('baseline', '')} | {item.get('current', '')} "
            f"| {verdict} | {item.get('detail', '')} |")
    rollback = result.get("rollback") or {}
    if result.get("passed"):
        lines.append("")
        lines.append("结论：六项指标全部达标，治理可结项。")
    else:
        lines.append("")
        lines.append(
            "结论：不达标，定向回滚。失败项="
            + ",".join(result.get("failed_metrics") or [])
            + (f"；回滚指令 `{rollback.get('command')}`"
               if rollback.get("command")
               else "；未提供 rollback_id，须补定向回滚锚"))
    return "\n".join(lines)

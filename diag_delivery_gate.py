from __future__ import annotations

import hashlib
import json
import logging
import math
import os
import time
from collections import Counter
from dataclasses import MISSING, asdict, dataclass, field, fields
from enum import Enum
from typing import Any, ClassVar, NamedTuple

from jwsgj.diag_guard_io import (
    guarded_open,
    safe_delete,
)
from jwsgj.diag_guard_scale import GateImportVerifier, GateProjectScanner
from jwsgj.diag_types_normalize import is_real_number, signal_bool
from jwsgj.diag_types_vocab import (
    FMT_DATETIME,
    PROJECT_ROOT_MARKERS,
    GateThresholds,
)
from jwsgj.log_config import (
    lock_region_nonblocking,
    log_swallowed,
    trace_module_run,
    unlock_region,
)
from jwsgj.runtime_paths import get_temp_base
from jwsgj.runtime_scope import resolve_search_root

_log = logging.getLogger(__name__)
class GateStatus(Enum):
    PASS = "PASS"
    FAIL = "FAIL"
    WARN = "WARN"
    SKIP = "SKIP"
class DeliveryVerdict(Enum):
    APPROVED = "APPROVED"
    REJECTED = "REJECTED"
    CONDITIONAL = "CONDITIONAL"
    PENDING = "PENDING"
_COUNT_DIM_SPEC: tuple[tuple[str, str, str], ...] = (
    ("file_count", "baseline_file_count", "current_file_count"),
    ("function_count", "baseline_function_count", "current_function_count"),
    ("line_count", "baseline_line_count", "current_line_count"),
    ("subsystem_count", "baseline_subsystem_count", "current_subsystem_count"),
)
_COUNT_DIM_NAMES = frozenset(dim for dim, _baseline, _current in _COUNT_DIM_SPEC)
def _counts_available(dims: frozenset) -> bool:
    return bool(dims)
def _as_finite_float(value: object) -> float | None:
    if not is_real_number(value):
        return None
    try:
        normalized = float(value)
    except (OverflowError, TypeError, ValueError) as exc:
        log_swallowed(
            __name__, exc,
            context=f'_as_finite_float:{type(exc).__name__}')
        return None
    return normalized if math.isfinite(normalized) else None
_SCORE_FULL = 100.0
_SCORE_ZERO = 0.0
_DEFAULT_OVERRIDE_CODE = ""
_DEFAULT_FORCE = False
@dataclass
class GateResult:
    gate_name: str = ""
    gate_id: str = ""
    description: str = ""
    threshold: float = 0.0
    status: str = "PENDING"
    actual_value: float = 0.0
    score: float = 0.0
    failure_reasons: list = field(default_factory=list)
    recommendations: list = field(default_factory=list)
    details: dict = field(default_factory=dict)
    elapsed_ms: float = 0.0
@dataclass
class DeliveryGateReport:
    project_path: str = ""
    project_name: str = ""
    timestamp: float = field(default_factory=time.time)
    gates: dict = field(default_factory=dict)
    passed_gates: int = 0
    failed_gates: int = 0
    skipped_gates: int = 0
    warn_gates: int = 0
    verdict: str = "PENDING"
    overall_score: float = 0.0
    blocking_issues: list = field(default_factory=list)
    warnings: list = field(default_factory=list)
    override_code: str = ""
    override_reason: str = ""
    delivery_hash: str = ""
    baseline_file_count: int = 0
    baseline_function_count: int = 0
    baseline_line_count: int = 0
    baseline_subsystem_count: int = 0
    current_file_count: int = 0
    current_function_count: int = 0
    current_line_count: int = 0
    current_subsystem_count: int = 0
    current_counts_available: bool = False
    current_count_dims: frozenset = field(default_factory=frozenset)
    def to_dict(self) -> dict:
        data = asdict(self)
        data['timestamp'] = _restore_timestamp(self.timestamp)
        _dims = _coerce_count_dims(self.current_count_dims)
        _dims = frozenset() if _dims is None else _dims
        data['current_count_dims'] = sorted(_dims)
        data['current_counts_available'] = _counts_available(_dims)
        return data
def _skip_neutral(result: GateResult) -> GateResult:
    result.status = GateStatus.SKIP.value
    result.score = _SCORE_FULL
    result.actual_value = 0
    return result
def _skip_with_reason(result: GateResult, reason: str) -> GateResult:
    _skip_neutral(result)
    result.recommendations.append(reason)
    return result
def _fail_component_error(result: GateResult, component: str,
                         exc: Exception) -> GateResult:
    _log.warning("%s失败", component, exc_info=True)
    result.status = GateStatus.FAIL.value
    result.score = _SCORE_ZERO
    result.actual_value = 0
    result.failure_reasons.append(f"{component}异常: {exc}")
    return result
def _skip_if_no_project(result: GateResult, project_path: str) -> bool:
    if not project_path or not os.path.isdir(project_path):
        _skip_with_reason(
            result,
            "项目路径缺失或不是目录（无可扫描的项目根），该门禁不参与评估")
        return True
    return False
def _count_invalid_reason(value: object) -> str | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return "类型非法"
    if value < 0:
        return "为负值（计数为基数）"
    if not is_real_number(value):
        return "不可取整（非有限数值）"
    if _as_finite_float(value) is None:
        return "超出浮点证据可计算范围"
    if isinstance(value, float) and not value.is_integer():
        return "非整数（计数为基数）"
    return None
def _as_non_negative_int(value: object) -> int | None:
    if _count_invalid_reason(value) is not None:
        return None
    try:
        return int(value)
    except (OverflowError, ValueError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc,
            context=f'_as_non_negative_int:{type(_swallowed_exc).__name__}')
        return None
def _round_evidence(value: float, threshold: float) -> float:
    if _as_finite_float(value) is None:
        return 0.0
    scaled = value * 10.0
    if not is_real_number(scaled):
        return round(value, 1)
    if value < threshold:
        return math.floor(scaled) / 10.0
    return math.ceil(scaled) / 10.0
def _normalize_file_sizes(raw_sizes: object) -> dict[str, int]:
    if not isinstance(raw_sizes, dict):
        raise TypeError(
            f"file_sizes 形态违约: {type(raw_sizes).__name__}（期望 dict）")
    file_sizes: dict[str, int] = {}
    for path, lines in raw_sizes.items():
        count = _as_non_negative_int(lines)
        if not isinstance(path, str) or count is None:
            raise ValueError(
                f"file_sizes 条目非法: path={path!r}, lines={lines!r}")
        file_sizes[path] = count
    return file_sizes
def _normalize_func_lines(raw_funcs: object) -> list[int]:
    if not isinstance(raw_funcs, (list, tuple)):
        raise TypeError(
            f"func_lines 形态违约: {type(raw_funcs).__name__}（期望 list 或 tuple）")
    func_lines: list[int] = []
    for lines in raw_funcs:
        count = _as_non_negative_int(lines)
        if count is None:
            raise ValueError(f"func_lines 条目非法: {lines!r}")
        func_lines.append(count)
    return func_lines
def _normalize_size_data(raw: object) -> dict:
    if not isinstance(raw, dict):
        raise TypeError(
            f"体积数据形态违约: {type(raw).__name__}（期望 dict）")
    file_sizes = _normalize_file_sizes(raw.get("file_sizes"))
    return {
        "file_sizes": file_sizes,
        "func_lines": _normalize_func_lines(raw.get("func_lines")),
        "total_files": len(file_sizes),
        "total_lines": sum(file_sizes.values()),
    }
def _normalize_stub_counts(raw: object) -> tuple[int, int]:
    if not isinstance(raw, (tuple, list)) or len(raw) != 2:
        raise ValueError(
            f"空桩扫描返回形态违约: {type(raw).__name__}（期望 (stub, total) 二元组）")
    stub_count = _as_non_negative_int(raw[0])
    total_count = _as_non_negative_int(raw[1])
    if stub_count is None or total_count is None or stub_count > total_count:
        raise ValueError(
            f"空桩扫描返回数值非法: {raw!r}（期望 0 <= stub <= total 的整数）")
    return stub_count, total_count
def _normalize_import_result(raw: object) -> tuple[float, list, str]:
    if not isinstance(raw, (tuple, list)) or len(raw) != 3:
        raise ValueError(
            f"导入验证返回形态违约: {type(raw).__name__}（期望 (pct, failed, mode) 三元组）")
    pct, failed, mode = raw
    normalized_pct = _as_finite_float(pct)
    if normalized_pct is None or not 0.0 <= normalized_pct <= 100.0:
        raise ValueError(
            f"导入验证成功率非法: {pct!r}（期望 [0, 100] 有限实数）")
    if not isinstance(failed, (list, tuple)):
        raise TypeError(
            f"导入验证失败清单形态违约: {type(failed).__name__}（期望 list）")
    if not isinstance(mode, str):
        raise TypeError(
            f"导入验证模式形态违约: {type(mode).__name__}（期望 str）")
    return normalized_pct, list(failed), mode
class CountingGateEvaluator:
    _COUNT_DIMS: ClassVar[tuple[tuple[str, str, str], ...]] = _COUNT_DIM_SPEC
    _SCANNER_COUNTERS: ClassVar[dict[str, str]] = {
        "file_count": "count_project_files",
        "function_count": "count_project_functions",
        "line_count": "count_project_lines",
    }
    def __init__(self,
                 project_path: str,
                 thresholds,
                 baseline_data: dict,
                 scanner,
                 quality_monitor=None,
                 function_mapping: dict | None = None):
        self.project_path = project_path
        self.thresholds = thresholds
        self.baseline_data = baseline_data
        self._scanner = scanner
        self.quality_monitor = quality_monitor
        self._count_errors: dict[str, Exception] = {}
        self.function_mapping = (
            function_mapping if isinstance(function_mapping, dict) else {})
    def gate_builders(self) -> tuple:
        return (
            self._gate_01_architecture_capacity,
            self._gate_02_function_completeness,
            self._gate_05_subsystem_presence,
        )
    @staticmethod
    def _skip_unavailable_counts(report: DeliveryGateReport,
                                 result: GateResult, subject: str) -> bool:
        if report.current_counts_available:
            return False
        _skip_neutral(result)
        result.recommendations.append(
            f"当前计数无采集通道（项目路径缺失或非目录，且未显式提供 current_*），无法评估{subject}")
        return True
    @staticmethod
    def _skip_missing_dim(report: DeliveryGateReport, result: GateResult,
                          dim: str, message: str) -> bool:
        if dim in report.current_count_dims:
            return False
        _skip_neutral(result)
        result.recommendations.append(message)
        return True
    def _gate_01_architecture_capacity(self, report: DeliveryGateReport) -> GateResult:
        result = GateResult(
            gate_id="GATE-01", gate_name="架构容量",
            description="检查文件数和行数是否低于基线阈值")
        bl_files = report.baseline_file_count
        bl_lines = report.baseline_line_count
        cur_files = report.current_file_count
        cur_lines = report.current_line_count
        if self._fail_count_errors(
                report, result, ("file_count", "line_count")):
            return result
        if self._skip_unavailable_counts(
                report, result, "容量缩减"):
            return result
        reductions = self._capacity_reductions(report, result)
        if reductions is None:
            if bl_files == 0 and bl_lines == 0:
                reason = ("基线未提供文件/行计数（baseline_file_count 与 "
                          "baseline_line_count 均为 0），无法评估容量缩减")
            else:
                reason = "基线文件/行计数与当前采集维度无交集，无法评估容量缩减"
            return _skip_with_reason(result, reason)
        file_reduction, line_reduction = reductions
        result.actual_value, result.threshold = self._dominant_reduction_evidence(
            file_reduction, line_reduction)
        self._apply_capacity_verdict(result, file_reduction, line_reduction)
        t = self.thresholds
        result.details = {
            "baseline_files": bl_files,
            "current_files": cur_files,
            "baseline_lines": bl_lines,
            "current_lines": cur_lines,
            "file_reduction_pct": (
                None if file_reduction is None else _round_evidence(
                    file_reduction * 100, t.ARCH_MAX_FILE_REDUCTION_PCT)),
            "line_reduction_pct": (
                None if line_reduction is None else _round_evidence(
                    line_reduction * 100, t.ARCH_MAX_LINE_REDUCTION_PCT)),
        }
        return result
    def _capacity_reductions(
            self, report: DeliveryGateReport,
            result: GateResult) -> tuple[float | None, float | None] | None:
        dims = report.current_count_dims
        file_reduction = self._dimension_reduction(
            report.baseline_file_count, report.current_file_count,
            "file_count", dims, "文件数", result)
        line_reduction = self._dimension_reduction(
            report.baseline_line_count, report.current_line_count,
            "line_count", dims, "行数", result)
        if file_reduction is None and line_reduction is None:
            return None
        return file_reduction, line_reduction
    @staticmethod
    def _dimension_reduction(baseline: int, current: int, dim: str,
                             dims: frozenset, label: str,
                             result: GateResult) -> float | None:
        evaluable = baseline > 0 and dim in dims
        if baseline > 0 and not evaluable:
            result.recommendations.append(
                f"{label}维度当前计数无采集通道（未显式提供），该维度不参与缩减评估")
        if not evaluable:
            return None
        return (baseline - current) / baseline
    def _apply_capacity_verdict(
            self, result: GateResult, file_reduction: float | None,
            line_reduction: float | None) -> None:
        t = self.thresholds
        file_over = (file_reduction is not None
                     and file_reduction > t.ARCH_MAX_FILE_REDUCTION_PCT / 100.0)
        line_over = (line_reduction is not None
                     and line_reduction > t.ARCH_MAX_LINE_REDUCTION_PCT / 100.0)
        if file_over:
            result.status = GateStatus.FAIL.value
            _file_pct = _round_evidence(
                file_reduction * 100, t.ARCH_MAX_FILE_REDUCTION_PCT)
            result.failure_reasons.append(
                f"文件数缩减 {_file_pct:.1f}% 超过阈值 {t.ARCH_MAX_FILE_REDUCTION_PCT}%"
            )
        if line_over:
            result.status = GateStatus.FAIL.value
            _line_pct = _round_evidence(
                line_reduction * 100, t.ARCH_MAX_LINE_REDUCTION_PCT)
            result.failure_reasons.append(
                f"行数缩减 {_line_pct:.1f}% 超过阈值 {t.ARCH_MAX_LINE_REDUCTION_PCT}%"
            )
        if file_over or line_over:
            result.score = _SCORE_ZERO if file_over else 30.0
            return
        result.status = GateStatus.PASS.value
        result.score = _SCORE_FULL
        if file_reduction is not None and file_reduction > 0:
            result.recommendations.append(
                f"文件数缩减 {file_reduction*100:.1f}%，在可接受范围内"
            )
    @staticmethod
    def _severity_ratio(reduction: float, max_ratio: float) -> float:
        if max_ratio > 0:
            return reduction / max_ratio
        return float("inf") if reduction > 0 else 0.0
    def _dominant_reduction_evidence(
            self, file_reduction: float | None,
            line_reduction: float | None) -> tuple[float, float]:
        t = self.thresholds
        max_reduction = t.ARCH_MAX_FILE_REDUCTION_PCT / 100.0
        max_line_reduction = t.ARCH_MAX_LINE_REDUCTION_PCT / 100.0
        candidates = []
        if file_reduction is not None:
            candidates.append((
                self._severity_ratio(file_reduction, max_reduction),
                _round_evidence(file_reduction * 100,
                                t.ARCH_MAX_FILE_REDUCTION_PCT),
                t.ARCH_MAX_FILE_REDUCTION_PCT,
            ))
        if line_reduction is not None:
            candidates.append((
                self._severity_ratio(line_reduction, max_line_reduction),
                _round_evidence(line_reduction * 100,
                                t.ARCH_MAX_LINE_REDUCTION_PCT),
                t.ARCH_MAX_LINE_REDUCTION_PCT,
            ))
        _severity, actual, threshold = max(candidates, key=lambda item: item[0])
        return actual, threshold
    def _gate_02_function_completeness(self, report: DeliveryGateReport) -> GateResult:
        result = GateResult(
            gate_id="GATE-02", gate_name="功能完整性",
            description="检查公开函数覆盖率和API表面积是否达标")
        monitor_block_reason, monitor_pending_reason = (
            self._attach_monitor_evidence(result))
        self._attach_mapping_evidence(result)
        coverage_pct = self._coverage_pct_or_none(report, result)
        if coverage_pct is not None:
            self._apply_coverage_verdict(result, coverage_pct)
            result.details.update({
                "baseline_functions": report.baseline_function_count,
                "current_functions": report.current_function_count,
                "coverage_pct": result.actual_value,
            })
        self._apply_monitor_block(result, monitor_block_reason)
        self._apply_monitor_pending(result, monitor_pending_reason)
        return result
    def _coverage_pct_or_none(self, report: DeliveryGateReport,
                              result: GateResult) -> float | None:
        bl_funcs = report.baseline_function_count
        if self._fail_count_errors(report, result, ("function_count",)):
            return None
        if self._skip_unavailable_counts(report, result, "功能覆盖率"):
            return None
        if bl_funcs == 0:
            _skip_with_reason(
                result,
                "基线未提供函数计数（baseline_function_count=0），无法评估功能覆盖率")
            return None
        if self._skip_missing_dim(
                report, result, "function_count",
                "当前函数计数无采集通道（未显式提供 current_function_count），"
                "无法评估功能覆盖率"):
            return None
        return report.current_function_count / bl_funcs * 100
    @staticmethod
    def _apply_monitor_block(result: GateResult, reason: str | None) -> None:
        if not reason:
            return
        result.status = GateStatus.FAIL.value
        result.score = _SCORE_ZERO
        result.failure_reasons.append(reason)
    def _apply_coverage_verdict(self, result: GateResult,
                                coverage_pct: float) -> None:
        t = self.thresholds
        _warn_ceiling = max(t.FUNC_MIN_API_SURFACE_PCT, t.FUNC_MIN_COVERAGE_PCT)
        _below_hard_floor = coverage_pct < t.FUNC_MIN_COVERAGE_PCT
        _threshold = (t.FUNC_MIN_COVERAGE_PCT if _below_hard_floor
                      else _warn_ceiling)
        _display_pct = _round_evidence(coverage_pct, _threshold)
        result.actual_value = _display_pct
        result.threshold = _threshold
        if _below_hard_floor:
            result.status = GateStatus.FAIL.value
            result.score = _bounded_score(_display_pct, _SCORE_ZERO)
            result.failure_reasons.append(
                f"函数覆盖率 {_display_pct:.1f}% 低于阈值 {t.FUNC_MIN_COVERAGE_PCT}%"
            )
        elif coverage_pct < _warn_ceiling:
            result.status = GateStatus.WARN.value
            result.score = _bounded_score(_display_pct, _SCORE_ZERO)
            result.recommendations.append(
                f"API表面积 {_display_pct:.1f}% 低于建议值 {_warn_ceiling:.0f}%"
            )
        else:
            result.status = GateStatus.PASS.value
            result.score = _SCORE_FULL
    @staticmethod
    def _monitor_block_note(blockers: list) -> str:
        if blockers:
            return ("批次质量监控判定 BLOCK："
                    + "；".join(str(b) for b in blockers[:3]))
        return "批次质量监控判定 BLOCK（监控器未提供具体阻断原因）"
    @staticmethod
    def _monitor_pending_note(blockers: list) -> str:
        detail = "；".join(str(b) for b in blockers[:3])
        return ("批次质量监控未能判定交付就绪（PENDING）："
                + (detail or "监控器未提供具体待补数据项"))
    @staticmethod
    def _apply_monitor_pending(result: GateResult, reason: str | None) -> None:
        if not reason:
            return
        result.recommendations.append(reason)
        if result.status != GateStatus.FAIL.value:
            result.status = GateStatus.WARN.value
    def _attach_monitor_evidence(
            self, result: GateResult) -> tuple[str | None, str | None]:
        monitor = self.quality_monitor
        if monitor is None:
            return None, None
        try:
            mon_report = getattr(monitor, "report", None)
            if mon_report is None:
                return None, None
            avg_cov = getattr(mon_report, "avg_function_coverage", None)
            verdict = getattr(mon_report, "final_verdict", "")
            blockers = _as_text_items(
                getattr(mon_report, "delivery_blockers", None))
        except Exception as e:  # noqa: BLE001 - 外部监控器异常必须转为门禁失败
            log_swallowed(
                __name__, e,
                context=('CountingGateEvaluator._attach_monitor_evidence'
                         f':{type(e).__name__}'))
            return f"批次质量监控证据读取异常，无法判定交付状态: {e}", None
        if _as_finite_float(avg_cov) is not None and avg_cov >= 0:
            result.details["monitor_avg_coverage"] = round(avg_cov, 1)
        if verdict == "BLOCK":
            return self._monitor_block_note(blockers), None
        if verdict == "PENDING":
            return None, self._monitor_pending_note(blockers)
        return None, None
    def _attach_mapping_evidence(self, result: GateResult) -> None:
        mapping = self.function_mapping
        if not isinstance(mapping, dict) or not mapping:
            return
        cov_rate = _as_finite_float(mapping.get("coverage_rate"))
        if cov_rate is not None and cov_rate >= 0:
            result.details["mapping_coverage_rate"] = round(cov_rate, 3)
        missing_count = _as_non_negative_int(mapping.get("missing_count"))
        if missing_count is not None:
            result.details["mapping_missing_count"] = missing_count
    def _gate_05_subsystem_presence(self, report: DeliveryGateReport) -> GateResult:
        t = self.thresholds
        result = GateResult(
            gate_id="GATE-05", gate_name="子系统存在性",
            description="检查子系统数量是否低于基线")
        bl_sub = report.baseline_subsystem_count
        cur_sub = report.current_subsystem_count
        if bl_sub == 0:
            return _skip_with_reason(
                result,
                "基线未提供子系统计数（baseline_subsystem_count=0），无法评估子系统保留率")
        if self._skip_missing_dim(
                report, result, "subsystem_count",
                "基线含子系统计数但当前值无采集通道（current_subsystem_count 未提供），"
                "无法评估保留率"):
            return result
        preserved_pct = cur_sub / bl_sub * 100
        _display_pct = _round_evidence(
            preserved_pct, t.SUBSYSTEM_MIN_PRESERVED_PCT)
        result.actual_value = _display_pct
        result.threshold = t.SUBSYSTEM_MIN_PRESERVED_PCT
        if preserved_pct < t.SUBSYSTEM_MIN_PRESERVED_PCT:
            result.status = GateStatus.FAIL.value
            result.score = _bounded_score(_display_pct, _SCORE_ZERO)
            result.failure_reasons.append(
                f"子系统保留率 {_display_pct:.1f}% 低于阈值 {t.SUBSYSTEM_MIN_PRESERVED_PCT}%"
            )
        else:
            result.status = GateStatus.PASS.value
            result.score = _SCORE_FULL
        result.details = {
            "baseline_subsystems": bl_sub,
            "current_subsystems": cur_sub,
            "preserved_pct": _display_pct,
        }
        return result
    def _fail_count_errors(self, report: DeliveryGateReport,
                           result: GateResult, dims: tuple[str, ...]) -> bool:
        failed = False
        for dim, baseline_field, _current_field in self._COUNT_DIMS:
            error = self._count_errors.get(dim)
            if (dim not in dims or error is None
                    or getattr(report, baseline_field) <= 0):
                continue
            _fail_component_error(result, f"{dim} 计数采集", error)
            failed = True
        return failed
    @staticmethod
    def _coerce_count(key: str, provided, dirty_as_none: bool = False):
        if provided is None:
            return None
        _reason = _count_invalid_reason(provided)
        if _reason is not None:
            _dirty_outcome = ("按未提供处理" if dirty_as_none
                              else "按 0 处理")
            _log.warning("[ConsolGate] 计数字段 %s %s（%r），%s",
                         key, _reason, provided, _dirty_outcome)
            return None if dirty_as_none else 0
        return int(provided)
    def populate_baseline(self, report: DeliveryGateReport) -> None:
        self._count_errors.clear()
        bl = self.baseline_data
        self._land_baseline_counts(report, bl)
        _explicit = self._explicit_current_counts(bl)
        _path_available = bool(self.project_path and os.path.isdir(self.project_path))
        self._land_current_counts(report, _explicit, _path_available)
    def _land_baseline_counts(self, report: DeliveryGateReport,
                              bl: dict) -> None:
        for key, baseline_field, _current_field in self._COUNT_DIMS:
            value = self._coerce_count(key, bl.get(key)) or 0
            setattr(report, baseline_field, value)
    def _explicit_current_counts(self, bl: dict) -> dict:
        return {
            current_field: self._coerce_count(
                current_field, bl.get(current_field), dirty_as_none=True)
            for _key, _baseline_field, current_field in self._COUNT_DIMS
        }
    def _land_current_counts(self, report: DeliveryGateReport,
                             _explicit: dict, _path_available: bool) -> None:
        dims: set[str] = set()
        for dim, _baseline_field, current_field in self._COUNT_DIMS:
            value = _explicit[current_field]
            if value is None and _path_available:
                counter = self._SCANNER_COUNTERS.get(dim)
                if counter:
                    value = self._count_from_scanner(dim, counter)
            if value is None:
                value = 0
            else:
                dims.add(dim)
            setattr(report, current_field, value)
        report.current_count_dims = frozenset(dims)
        report.current_counts_available = _counts_available(
            report.current_count_dims)
    def _count_from_scanner(self, dim: str, counter: str) -> int | None:
        try:
            raw = getattr(self._scanner, counter)()
        except Exception as e:
            self._count_errors[dim] = e
            log_swallowed(
                __name__, e,
                context=('CountingGateEvaluator._count_from_scanner'
                         f'[{counter}]:{type(e).__name__}'))
            return None
        value = _as_non_negative_int(raw)
        if value is None:
            self._count_errors[dim] = ValueError(
                f"{counter} 返回非法计数 {raw!r}")
            _log.warning(
                "[ConsolGate] 计数字段 %s 采集返回非法值 %r，按采集失败处理",
                dim, raw)
        return value
class _ImportEvidence(NamedTuple):
    targets: list
    pass_pct: float
    failed_names: list
    verify_mode: str
class ConsolScanGateEvaluator:
    def __init__(self,
                 project_path: str,
                 thresholds: GateThresholds,
                 scanner: GateProjectScanner,
                 import_verifier: GateImportVerifier,
                 function_mapping: dict | None = None):
        self.project_path = project_path
        self.thresholds = thresholds
        self._scanner = scanner
        self._import_verifier = import_verifier
        self.function_mapping = (
            function_mapping if isinstance(function_mapping, dict) else {})
    def gate_builders(self) -> tuple:
        return (
            self._gate_03_import_chain_integrity,
            self._gate_04_stub_ratio,
            self._gate_06_file_size,
            self._gate_07_full_import_integrity,
            self._gate_08_anti_fragment,
        )
    def _run_scanner_step(self, result: GateResult, component: str,
                          step, log_context: str,
                          parse=None) -> tuple[bool, Any]:
        try:
            value = step()
            return True, (parse(value) if parse is not None else value)
        except Exception as e:
            log_swallowed(__name__, e, context=log_context)
            _fail_component_error(result, component, e)
            return False, None
    @staticmethod
    def _skip_empty_scan(result: GateResult, total: int,
                         subject: str) -> bool:
        if total > 0:
            return False
        _skip_neutral(result)
        result.recommendations.append(
            f"未扫描到可评估的{subject}（空项目或无非 Python 源文件）")
        return True
    def _mapping_stub_rate_detail(self) -> float | None:
        mapping = self.function_mapping
        if not isinstance(mapping, dict) or not mapping:
            return None
        stub_rate = _as_finite_float(mapping.get("stub_rate"))
        if stub_rate is None or stub_rate < 0:
            return None
        return round(stub_rate * 100, 1)
    def _gate_import_evidence(self, result: GateResult, component: str):
        if _skip_if_no_project(result, self.project_path):
            return None
        try:
            targets = self._import_verifier.collect_import_targets(self.project_path)
            if not isinstance(targets, (list, tuple)):
                raise TypeError(
                    f"导入目标返回形态违约: {type(targets).__name__}（期望 list）")
            if not targets:
                _skip_neutral(result)
                result.recommendations.append("未找到可验证的导入目标")
                return None
            raw = self._import_verifier.verify_import_chain_subprocess(
                self.project_path, targets)
            pct, failed, mode = _normalize_import_result(raw)
            return _ImportEvidence(list(targets), pct, failed, mode)
        except Exception as e:
            log_swallowed(__name__, e, context='ConsolScanGateEvaluator._gate_import_evidence:Exc')
            _fail_component_error(result, component, e)
            return None
    @staticmethod
    def _apply_import_verdict(result: GateResult, pct: float, threshold: float,
                              failed_names: list, *, failure_label: str,
                              clean_recommendation) -> None:
        _display_pct = _round_evidence(pct, threshold)
        result.actual_value = _display_pct
        result.threshold = threshold
        if pct < threshold:
            result.status = GateStatus.FAIL.value
            result.score = _bounded_score(_display_pct, _SCORE_ZERO)
            if failed_names:
                result.failure_reasons.extend(
                    f"{failure_label}: {name}" for name in failed_names[:10])
            else:
                result.failure_reasons.append(
                    f"{failure_label}: 成功率 {_display_pct:.1f}% "
                    f"低于阈值 {threshold:.1f}%")
            return
        result.status = GateStatus.PASS.value
        result.score = _SCORE_FULL
        if failed_names:
            result.recommendations.append(clean_recommendation(len(failed_names)))
    def _gate_03_import_chain_integrity(self, report: DeliveryGateReport) -> GateResult:
        t = self.thresholds
        result = GateResult(
            gate_id="GATE-03", gate_name="导入链完整性",
            description="检查导入链是否完整、无断链")
        evidence = self._gate_import_evidence(result, "导入链验证")
        if evidence is None:
            return result
        targets, integrity_pct, broken, verify_mode = evidence
        self._apply_import_verdict(
            result, integrity_pct, t.IMPORT_MIN_INTEGRITY_PCT, broken,
            failure_label="断链",
            clean_recommendation=lambda n: f"有 {n} 处导入警告但不影响完整性",
        )
        result.details = {
            "total_targets": len(targets),
            "integrity_pct": result.actual_value,
            "broken_count": len(broken),
            "verify_mode": verify_mode,
        }
        return result
    def _gate_04_stub_ratio(self, report: DeliveryGateReport) -> GateResult:
        t = self.thresholds
        result = GateResult(
            gate_id="GATE-04", gate_name="空桩比率",
            description="检测桩函数(pass/ellipsis/空return)占比")
        if _skip_if_no_project(result, self.project_path):
            return result
        ok, counts = self._run_scanner_step(
            result, "空桩扫描", self._scanner.scan_stubs,
            'ConsolScanGateEvaluator._gate_04_stub_ratio:Exc',
            parse=_normalize_stub_counts)
        if not ok:
            return result
        stub_count, total_count = counts
        if self._skip_empty_scan(result, total_count, "函数"):
            return result
        ratio_pct = stub_count / total_count * 100
        _display_pct = _round_evidence(ratio_pct, t.STUB_MAX_RATIO_PCT)
        result.actual_value = _display_pct
        result.threshold = t.STUB_MAX_RATIO_PCT
        self._stub_ratio_verdict(
            result, stub_count, total_count, ratio_pct, _display_pct)
        result.details = {
            "stub_count": stub_count,
            "total_count": total_count,
            "ratio_pct": _display_pct,
        }
        mapping_stub_rate = self._mapping_stub_rate_detail()
        if mapping_stub_rate is not None:
            result.details["mapping_stub_rate_pct"] = mapping_stub_rate
        return result
    def _stub_ratio_verdict(self, result: GateResult, stub_count: int,
                            total_count: int, ratio_pct: float,
                            display_pct: float) -> None:
        t = self.thresholds
        ratio_fail = ratio_pct > t.STUB_MAX_RATIO_PCT
        abs_fail = (stub_count > t.STUB_MAX_ABSOLUTE
                    and total_count < t.STUB_ABSOLUTE_SCOPE_TOTAL)
        if ratio_fail or abs_fail:
            result.status = GateStatus.FAIL.value
            result.score = round(max(0.0, 100 - ratio_pct * 2), 1)
            if ratio_fail:
                result.failure_reasons.append(
                    f"空桩率 {display_pct:.1f}% (共{stub_count}个) 超过阈值 {t.STUB_MAX_RATIO_PCT}%"
                )
            else:
                result.actual_value = stub_count
                result.threshold = t.STUB_MAX_ABSOLUTE
                result.failure_reasons.append(
                    f"空桩数 {stub_count} 个超过绝对上限 {t.STUB_MAX_ABSOLUTE}"
                    f"（小样本 {total_count} 函数，比率 {display_pct:.1f}% 兜底触发）"
                )
            return
        result.status = GateStatus.PASS.value
        result.score = _SCORE_FULL
        if stub_count > 0:
            result.recommendations.append(
                f"存在 {stub_count} 个桩函数，占比 {display_pct:.1f}%")
    @staticmethod
    def _over_limit_ratio(values, limit: float) -> tuple[int, float]:
        sample = list(values)
        if not sample:
            return 0, 0.0
        over = sum(1 for value in sample if value > limit)
        return over, over / len(sample)
    def _check_large_file_ratio(self, size_data: dict) -> tuple:
        t = self.thresholds
        _count, ratio = self._over_limit_ratio(
            (size_data.get("file_sizes") or {}).values(), t.AVG_LINES_ALERT)
        return ratio, ratio > t.SIZE_LARGE_FILE_RATIO_MAX
    def _check_large_func_count(self, size_data: dict) -> tuple[int, float, bool]:
        t = self.thresholds
        count, ratio = self._over_limit_ratio(
            size_data.get("func_lines") or [], t.ARCH_MAX_FUNC_LINE)
        ratio_pct = ratio * 100
        return count, ratio_pct, ratio_pct > t.SIZE_LARGE_FUNC_RATIO_WARN * 100
    def _check_avg_file_lines(self, size_data: dict) -> tuple:
        t = self.thresholds
        total_lines = size_data.get("total_lines", 0)
        total_files = size_data.get("total_files", 0)
        if total_files == 0:
            return 0, False
        avg = total_lines / total_files
        return _round_evidence(avg, t.AVG_LINES_WARN), avg > t.AVG_LINES_WARN
    def _gate_06_file_size(self, report: DeliveryGateReport) -> GateResult:
        t = self.thresholds
        result = GateResult(
            gate_id="GATE-06", gate_name="文件大小",
            description="检查大文件比例和大函数数量")
        if _skip_if_no_project(result, self.project_path):
            return result
        ok, size_data = self._run_scanner_step(
            result, "大小数据收集", self._scanner.collect_size_data,
            'ConsolScanGateEvaluator._gate_06_file_size:Exc',
            parse=_normalize_size_data)
        if not ok:
            return result
        if self._skip_empty_scan(
                result, size_data["total_files"], "源文件"):
            return result
        large_ratio, ratio_fail = self._check_large_file_ratio(size_data)
        large_func_count, large_func_ratio, func_fail = (
            self._check_large_func_count(size_data))
        avg_lines, avg_warn = self._check_avg_file_lines(size_data)
        _file_threshold = t.SIZE_LARGE_FILE_RATIO_MAX * 100
        _func_threshold = t.SIZE_LARGE_FUNC_RATIO_WARN * 100
        _file_pct = _round_evidence(large_ratio * 100, _file_threshold)
        _func_pct = _round_evidence(large_func_ratio, _func_threshold)
        result.actual_value = _file_pct
        result.threshold = _file_threshold
        if avg_warn:
            result.recommendations.append(f"平均文件行数 {avg_lines} 超过预警值 {t.AVG_LINES_WARN}")
        self._size_verdict(result, large_func_count, _file_pct, _func_pct,
                           ratio_fail, func_fail)
        result.details = {
            "large_file_ratio": _file_pct,
            "large_func_count": large_func_count,
            "large_func_ratio": _func_pct,
            "avg_file_lines": avg_lines,
            "total_files": size_data["total_files"],
        }
        return result
    def _size_verdict(self, result: GateResult, large_func_count: int,
                      file_pct: float, func_pct: float,
                      ratio_fail: bool, func_fail: bool) -> None:
        t = self.thresholds
        if ratio_fail:
            result.status = GateStatus.FAIL.value
            result.score = _SCORE_ZERO
            result.failure_reasons.append(
                f"大文件比例 {file_pct:.1f}% 超过阈值 {t.SIZE_LARGE_FILE_RATIO_MAX*100:.1f}%"
            )
            return
        if func_fail:
            result.status = GateStatus.WARN.value
            result.score = 60.0
            _func_threshold = t.SIZE_LARGE_FUNC_RATIO_WARN * 100
            result.recommendations.append(
                f"存在 {large_func_count} 个超大函数(>{t.ARCH_MAX_FUNC_LINE}行),"
                f"占比 {func_pct:.1f}% 超过预警线 {_func_threshold:.0f}%")
            result.actual_value = func_pct
            result.threshold = _func_threshold
            return
        result.status = GateStatus.PASS.value
        result.score = _SCORE_FULL
    def _gate_07_full_import_integrity(self, report: DeliveryGateReport) -> GateResult:
        t = self.thresholds
        result = GateResult(
            gate_id="GATE-07", gate_name="完整导入验证",
            description="实际尝试导入所有模块，检查导入成功率")
        evidence = self._gate_import_evidence(result, "导入验证")
        if evidence is None:
            return result
        targets, pass_pct, failed_names, verify_mode = evidence
        self._apply_import_verdict(
            result, pass_pct, t.IMPORT_SUBPROCESS_MIN_PASS_PCT, failed_names,
            failure_label="导入失败",
            clean_recommendation=lambda n: f"有 {n} 个模块导入失败但不影响整体",
        )
        result.details = {
            "total_targets": len(targets),
            "passed": max(0, len(targets) - len(failed_names)),
            "failed": len(failed_names),
            "pass_pct": result.actual_value,
            "verify_mode": verify_mode,
        }
        return result
    def _compute_small_dir_ratios(self, small_files: list,
                                    file_sizes: dict) -> dict[str, float]:
        dir_small = Counter(os.path.dirname(path) for path in small_files)
        dir_total = Counter(os.path.dirname(path) for path in file_sizes)
        return {
            dir_path: small_count / dir_total[dir_path]
            for dir_path, small_count in dir_small.items()
            if dir_total[dir_path] >= self.thresholds.fragment_min_dir_files
        }
    def _apply_fragment_verdict(self, result: GateResult, small_files: list,
                                small_pct: float, dir_ratios: dict,
                                max_dir_ratio: float) -> None:
        t = self.thresholds
        if max_dir_ratio > t.fragment_block_dir_ratio and t.fragment_strict_mode:
            result.status = GateStatus.FAIL.value
            result.score = _SCORE_ZERO
            result.threshold = t.fragment_block_dir_ratio * 100
            _display_pct = _round_evidence(
                max_dir_ratio * 100, result.threshold)
            result.actual_value = _display_pct
            result.failure_reasons.append(
                f"目录 {_fragment_dir_label(dir_ratios)} 小文件占比 {_display_pct:.1f}% "
                f"超过阈值 {t.fragment_block_dir_ratio*100:.1f}%"
            )
        elif max_dir_ratio > t.fragment_warn_dir_ratio:
            result.status = GateStatus.WARN.value
            result.score = 50.0
            result.threshold = t.fragment_warn_dir_ratio * 100
            _display_pct = _round_evidence(
                max_dir_ratio * 100, result.threshold)
            result.actual_value = _display_pct
            result.recommendations.append(
                f"部分目录小文件占比 {_display_pct:.1f}% 超过预警 {t.fragment_warn_dir_ratio*100:.1f}%"
            )
        else:
            result.status = GateStatus.PASS.value
            result.score = _SCORE_FULL
            result.threshold = t.fragment_warn_dir_ratio * 100
            result.actual_value = _round_evidence(
                max_dir_ratio * 100, result.threshold)
            if small_files:
                result.recommendations.append(
                    f"存在 {len(small_files)} 个小文件(<{t.fragment_min_lines}行)，占比 {small_pct:.1f}%"
                )
    def _gate_08_anti_fragment(self, report: DeliveryGateReport) -> GateResult:
        t = self.thresholds
        result = GateResult(
            gate_id="GATE-08", gate_name="反碎片",
            description="检测过度拆分的小文件和碎片化模块")
        if _skip_if_no_project(result, self.project_path):
            return result
        ok, size_data = self._run_scanner_step(
            result, "碎片检查数据收集", self._scanner.collect_size_data,
            'ConsolScanGateEvaluator._gate_08_anti_fragment:Exc',
            parse=_normalize_size_data)
        if not ok:
            return result
        file_sizes = size_data["file_sizes"]
        if not file_sizes:
            self._skip_empty_scan(result, 0, "源文件")
            return result
        small_files = [path for path, lines in file_sizes.items()
                       if lines < t.fragment_min_lines]
        small_ratio = len(small_files) / len(file_sizes)
        small_pct = round(small_ratio * 100, 1)
        dir_ratios = self._compute_small_dir_ratios(small_files, file_sizes)
        max_dir_ratio = max(dir_ratios.values()) if dir_ratios else 0
        self._apply_fragment_verdict(
            result, small_files, small_pct, dir_ratios, max_dir_ratio)
        result.details = {
            "total_files": len(file_sizes),
            "small_files": len(small_files),
            "small_ratio": small_pct,
            "max_dir_ratio": result.actual_value,
        }
        return result
_OVERRIDABLE_THRESHOLD_KEYS = frozenset(GateThresholds.__dataclass_fields__)
_STATUS_FIELDS: dict[str, str] = {
    GateStatus.PASS.value: "passed_gates",
    GateStatus.FAIL.value: "failed_gates",
    GateStatus.WARN.value: "warn_gates",
    GateStatus.SKIP.value: "skipped_gates",
}
_GATE_STATUS_TEXTS = frozenset(s.value for s in GateStatus) | {"PENDING"}
_VERDICT_LABELS = {
    DeliveryVerdict.APPROVED.value: "通过",
    DeliveryVerdict.REJECTED.value: "拒绝",
    DeliveryVerdict.CONDITIONAL.value: "条件通过",
    DeliveryVerdict.PENDING.value: "待定",
}
_MAX_RENDERED_WARNINGS = 5
def _coerce_dict(value: object, field_name: str) -> dict:
    if value is None:
        return {}
    if not isinstance(value, dict):
        _log.warning("[ConsolGate] %s 类型非法（%s），按空处理",
                     field_name, type(value).__name__)
        return {}
    return value
class _ThresholdOverrides:
    def __init__(self, thresholds: GateThresholds) -> None:
        self._thresholds = thresholds
    def apply(self, overrides: dict | None) -> None:
        for key, val in _coerce_dict(overrides, "threshold_overrides").items():
            self._apply_one(key, val)
    def _apply_one(self, key: str, val: object) -> None:
        if key not in _OVERRIDABLE_THRESHOLD_KEYS:
            _log.warning(
                "[ConsolGate] 忽略未知阈值键 %s（合法键见 "
                "GateThresholds 字段面）", key)
            return
        current = getattr(self._thresholds, key)
        if self._value_ok(current, val):
            setattr(self._thresholds, key, val)
            return
        _log.warning(
            "[ConsolGate] 忽略阈值键 %s 的非法值 %r（类型 "
            "%s 不符字段类型 %s 或非有限数值），保持默认 %r",
            key, val, type(val).__name__, type(current).__name__, current)
    @staticmethod
    def _value_ok(current: object, val: object) -> bool:
        if isinstance(current, bool):
            return isinstance(val, bool)
        if isinstance(current, int):
            return isinstance(val, int) and not isinstance(val, bool) and val >= 0
        if isinstance(current, float):
            return _as_finite_float(val) is not None and val >= 0
        return isinstance(val, type(current))
def _as_text_items(value: object) -> list[str]:
    if value is None:
        return []
    if isinstance(value, str):
        return [value]
    if isinstance(value, (set, frozenset)):
        return [str(item) for item in sorted(value, key=str)]
    if isinstance(value, (list, tuple)):
        return [str(item) for item in value]
    return [str(value)]
def _as_count_text(value: object) -> str:
    if isinstance(value, bool) or not isinstance(value, int):
        return str(value)
    return f"{value:,}"
def _fragment_dir_label(dir_ratios: dict) -> str:
    if not dir_ratios:
        return "<项目根>"
    worst_dir = max(dir_ratios, key=dir_ratios.get)
    return os.path.basename(worst_dir) or worst_dir or "<项目根>"
class _GateReportRenderer:
    @classmethod
    def render(cls, report: DeliveryGateReport) -> str:
        lines = cls._render_header(report)
        lines += cls._render_verdict(report)
        lines += cls._render_gate_details(report)
        lines.append("")
        lines += cls._render_issues(report)
        lines.append(f"{'#'*70}")
        return '\n'.join(lines)
    @staticmethod
    def _render_header(report: DeliveryGateReport) -> list[str]:
        timestamp = _restore_timestamp(report.timestamp)
        return [
            f"\n{'#'*70}",
            "  交付验收报告",
            f"{'#'*70}",
            f"  项目: {report.project_name}",
            f"  路径: {report.project_path}",
            f"  时间: {time.strftime(FMT_DATETIME, time.localtime(timestamp))}",
            "",
            f"  基线: {report.baseline_file_count}文件 | {report.baseline_function_count}函数 | {_as_count_text(report.baseline_line_count)}行 | {report.baseline_subsystem_count}子系统",
            f"  当前: {report.current_file_count}文件 | {report.current_function_count}函数 | {_as_count_text(report.current_line_count)}行 | {report.current_subsystem_count}子系统",
            "",
        ]
    @staticmethod
    def _render_verdict(report: DeliveryGateReport) -> list[str]:
        verdict = (report.verdict if isinstance(report.verdict, str)
                   else DeliveryVerdict.PENDING.value)
        return [
            f"  最终判定: {_VERDICT_LABELS.get(verdict, verdict)}",
            f"  综合评分: {report.overall_score}/100",
            f"  交付签名: {report.delivery_hash}",
            "",
        ]
    @classmethod
    def _render_gate_details(cls, report: DeliveryGateReport) -> list[str]:
        gates = report.gates if isinstance(report.gates, dict) else {}
        lines: list[str] = []
        for gate_id in sorted(gates, key=str):
            lines += cls._render_gate_detail(gate_id, gates[gate_id])
        return lines
    @staticmethod
    def _render_gate_detail(gate_id: object, gate: object) -> list[str]:
        if not isinstance(gate, GateResult):
            degraded = (f"  [?] {gate_id}（记录形态违约："
                        f"{type(gate).__name__}，门禁明细无法渲染）")
            return [degraded]
        status = (gate.status if (isinstance(gate.status, str)
                                 and gate.status in _GATE_STATUS_TEXTS) else '?')
        lines = [
            f"  [{status}] {gate.gate_id} {gate.gate_name}",
            f"     阈值: {gate.threshold} | 实际: {gate.actual_value} | 评分: {gate.score}/100",
        ]
        lines.extend(f"     - {reason}" for reason in _as_text_items(gate.failure_reasons))
        lines.extend(f"     + {rec}" for rec in _as_text_items(gate.recommendations))
        return lines
    @classmethod
    def _render_issues(cls, report: DeliveryGateReport) -> list[str]:
        return cls._render_blocking(report) + cls._render_warnings(report)
    @staticmethod
    def _render_blocking(report: DeliveryGateReport) -> list[str]:
        issues = _as_text_items(report.blocking_issues)
        if not issues:
            return ["  阻断项: 无"]
        return ([
            f"  阻断项 ({len(issues)}):",
            *(f"    - {issue}" for issue in issues),
        ])
    @classmethod
    def _render_warnings(cls, report: DeliveryGateReport) -> list[str]:
        warnings = _as_text_items(report.warnings)
        if not warnings:
            return []
        lines = [f"  建议项 ({len(warnings)}):"]
        lines.extend(f"    + {w}" for w in warnings[:_MAX_RENDERED_WARNINGS])
        rest = len(warnings) - _MAX_RENDERED_WARNINGS
        if rest > 0:
            lines.append(f"    …（另有 {rest} 项）")
        return lines
_REPORT_FIELD_EXCLUSIONS: frozenset[str] = frozenset({
    "project_path", "project_name", "timestamp", "gates",
    "current_count_dims", "override_code",
})
_DELIVERY_REPORT_FIELDS: tuple[str, ...] = tuple(
    field_def.name for field_def in fields(DeliveryGateReport)
    if field_def.name not in _REPORT_FIELD_EXCLUSIONS
)
def _field_default(model: type, field_name: str) -> Any:
    field_def = model.__dataclass_fields__[field_name]
    if field_def.default is not MISSING:
        return field_def.default
    if field_def.default_factory is not MISSING:
        return field_def.default_factory()
    return None
_REPORT_INT_FIELDS: frozenset[str] = frozenset({
    "passed_gates", "failed_gates", "skipped_gates", "warn_gates",
    "baseline_file_count", "baseline_function_count", "baseline_line_count",
    "baseline_subsystem_count", "current_file_count", "current_function_count",
    "current_line_count", "current_subsystem_count",
})
_REPORT_TEXT_FIELDS: frozenset[str] = frozenset({
    "override_code", "override_reason", "delivery_hash",
})
_GATE_RESULT_FIELDS: frozenset[str] = frozenset(
    GateResult.__dataclass_fields__)
_GATE_TEXT_FIELDS: frozenset[str] = frozenset({
    "gate_id", "gate_name", "description",
})
_GATE_NON_NEGATIVE_FIELDS: frozenset[str] = frozenset({
    "threshold", "elapsed_ms",
})
_GATE_FINITE_FIELDS: frozenset[str] = frozenset({"actual_value"})
def _bounded_score(value: Any, default: float) -> float:
    normalized = _as_finite_float(value)
    if normalized is None or normalized < 0:
        return default
    return min(normalized, _SCORE_FULL)
def _normalize_report_field(field_name: str, value: Any) -> Any:
    default = _field_default(DeliveryGateReport, field_name)
    if field_name in _REPORT_INT_FIELDS:
        normalized = _as_non_negative_int(value)
        return default if normalized is None else normalized
    if field_name == "overall_score":
        return _bounded_score(value, default)
    if field_name == "current_counts_available":
        return value if isinstance(value, bool) else default
    if field_name in ("blocking_issues", "warnings"):
        return _as_text_items(value)
    if field_name == "verdict":
        return value if (isinstance(value, str)
                        and value in _VERDICT_LABELS) else default
    if field_name in _REPORT_TEXT_FIELDS:
        return value if isinstance(value, str) else default
    return default if value is None else value
def _restore_timestamp(raw: Any) -> float:
    if raw is None or isinstance(raw, bool):
        return 0.0
    try:
        timestamp = float(raw)
    except (TypeError, ValueError, OverflowError) as exc:
        log_swallowed(__name__, exc,
                      context=f'_restore_timestamp:{type(exc).__name__}')
        return 0.0
    if not is_real_number(timestamp):
        return 0.0
    try:
        time.localtime(timestamp)
    except (OverflowError, OSError, ValueError) as exc:
        log_swallowed(__name__, exc,
                      context=f'_restore_timestamp:{type(exc).__name__}')
        return 0.0
    return timestamp
def _normalize_gate_details(value: Any, default: dict) -> dict:
    if not isinstance(value, dict):
        return default
    try:
        json.dumps(value, ensure_ascii=False, allow_nan=False)
    except (TypeError, ValueError, RecursionError) as exc:
        _log.warning(
            "[ConsolGate] 门禁 details 不是合法 JSON（%s），按空处理", exc)
        return default
    return value
def _normalize_gate_field(field_name: str, value: Any) -> Any:
    default = _field_default(GateResult, field_name)
    if field_name in _GATE_TEXT_FIELDS:
        return value if isinstance(value, str) else default
    if field_name == "status":
        return (value if (isinstance(value, str)
                          and value in _GATE_STATUS_TEXTS) else default)
    if field_name in _GATE_NON_NEGATIVE_FIELDS:
        normalized = _as_finite_float(value)
        if normalized is not None and normalized >= 0:
            return normalized
        return default
    if field_name in _GATE_FINITE_FIELDS:
        normalized = _as_finite_float(value)
        return default if normalized is None else normalized
    if field_name == "score":
        return _bounded_score(value, default)
    if field_name in ("failure_reasons", "recommendations"):
        return _as_text_items(value)
    if field_name == "details":
        return _normalize_gate_details(value, default)
    return default if value is None else value
def _restore_gates(gates_data: Any) -> dict[str, Any]:
    if not isinstance(gates_data, dict):
        if gates_data is not None:
            _log.warning(
                "[ConsolGate] 门禁集形态违约（期望 dict，实际 %s），按空处理",
                type(gates_data).__name__)
        return {}
    restored: dict[str, Any] = {}
    for gid, gdata in gates_data.items():
        if not isinstance(gdata, dict):
            _log.warning(
                "[ConsolGate] 门禁记录 %r 形态违约（期望 dict，实际 %s），按原值保留",
                gid, type(gdata).__name__)
            restored[gid] = gdata
            continue
        payload = {k: _normalize_gate_field(k, v)
                   for k, v in gdata.items() if k in _GATE_RESULT_FIELDS}
        gate_id = payload.get("gate_id") or str(gid)
        payload["gate_id"] = gate_id
        restored[gid] = GateResult(**payload)
    return restored
def _coerce_count_dims(raw: Any) -> frozenset[str] | None:
    if not isinstance(raw, (list, set, tuple, frozenset)):
        return None
    return frozenset(
        item for item in raw
        if isinstance(item, str) and item in _COUNT_DIM_NAMES)
def restore_delivery_report(data: dict) -> DeliveryGateReport:
    if not isinstance(data, dict):
        _log.warning("[ConsolGate] 报告载荷顶层非 dict（%s），按空报告恢复",
                     type(data).__name__)
        return DeliveryGateReport(timestamp=0.0)
    raw_path = data.get("project_path")
    raw_name = data.get("project_name")
    report = DeliveryGateReport(
        project_path=raw_path if isinstance(raw_path, str) else "",
        project_name=raw_name if isinstance(raw_name, str) else "",
        timestamp=_restore_timestamp(data.get("timestamp")),
    )
    report.gates.update(_restore_gates(data.get("gates")))
    for field_name in _DELIVERY_REPORT_FIELDS:
        value = data.get(field_name)
        if value is not None:
            setattr(report, field_name,
                    _normalize_report_field(field_name, value))
    report.override_code = _normalize_report_field(
        "override_code", data.get("override_code"))
    dims = _coerce_count_dims(data.get("current_count_dims"))
    report.current_count_dims = frozenset() if dims is None else dims
    report.current_counts_available = _counts_available(
        report.current_count_dims)
    _raw_verdict = data.get("verdict")
    if _raw_verdict is not None and report.verdict != _raw_verdict:
        _log.warning(
            "[ConsolGate] 报告判定字段非法（%r），回落 %s",
            _raw_verdict, report.verdict)
    return report
def _gate_to_dict(g: Any) -> Any:
    if hasattr(g, "to_dict"):
        return g.to_dict()
    if isinstance(g, dict):
        return g
    if hasattr(g, "__dict__"):
        return {k: v for k, v in vars(g).items() if not k.startswith("_")}
    return str(g)
def _gates_payload(gates: Any) -> dict:
    if not isinstance(gates, dict):
        return {}
    raw_payload = {gid: _gate_to_dict(gate) for gid, gate in gates.items()}
    normalized = _restore_gates(raw_payload)
    return {gid: _gate_to_dict(gate) for gid, gate in normalized.items()}
def format_delivery_ci_output(report: Any) -> dict:
    if report is None:
        return {}
    _raw_path = getattr(report, "project_path", "")
    _raw_name = getattr(report, "project_name", "")
    _raw_ts = getattr(report, "timestamp", 0.0)
    _raw_code = getattr(report, "override_code", "")
    out: dict = {
        "project_path": _raw_path if isinstance(_raw_path, str) else "",
        "project_name": _raw_name if isinstance(_raw_name, str) else "",
        "timestamp": 0.0 if _raw_ts is None else _restore_timestamp(_raw_ts),
        "override_code": _raw_code if isinstance(_raw_code, str) else "",
    }
    for field_name in _DELIVERY_REPORT_FIELDS:
        out[field_name] = _normalize_report_field(
            field_name, getattr(report, field_name, None))
    dims = _coerce_count_dims(getattr(report, "current_count_dims", None))
    _dims = frozenset() if dims is None else dims
    out["current_count_dims"] = sorted(_dims)
    out["current_counts_available"] = _counts_available(_dims)
    out["gates"] = _gates_payload(getattr(report, "gates", None))
    return out
def _coerce_project_path(value: object) -> str:
    if isinstance(value, str):
        return value
    if value is None or isinstance(value, bool):
        return ""
    try:
        raw = os.fspath(value)
    except TypeError:
        raw = None
    if isinstance(raw, str):
        return raw
    _log.warning("[ConsolGate] project_path 类型非法（%s），按空路径处理",
                 type(value).__name__)
    return ""
def _project_name_from_path(project_path: str) -> str:
    if not project_path:
        return ""
    normalized = os.path.normpath(project_path)
    name = os.path.basename(normalized)
    return "" if name in ("", os.curdir, os.pardir) else name
def _coerce_function_mapping(function_mapping: object) -> dict:
    if function_mapping is None:
        return {}
    if isinstance(function_mapping, dict):
        return function_mapping
    _log.warning("[ConsolGate] function_mapping 类型非法（%s），按空处理",
                 type(function_mapping).__name__)
    return {}
def _gate_summary(gate: object) -> Any:
    if not isinstance(gate, GateResult):
        return str(gate)
    return [gate.status, gate.score, gate.actual_value, gate.threshold]
class PreDeliveryGate:
    def __init__(self,
                 project_path: str,
                 baseline_data: dict[str, Any] | None = None,
                 quality_monitor=None,
                 function_mapping: dict | None = None,
                 threshold_overrides: dict | None = None,
                 shared_cache=None):
        self.project_path = _coerce_project_path(project_path)
        self.project_name = _project_name_from_path(self.project_path)
        self.baseline_data = _coerce_dict(baseline_data, "baseline_data")
        self.quality_monitor = quality_monitor
        self.function_mapping = _coerce_function_mapping(function_mapping)
        self.thresholds = GateThresholds()
        self._scanner = GateProjectScanner(
            self.project_path, shared_cache=shared_cache)
        self._import_verifier = GateImportVerifier(
            self.project_path, self.thresholds, self._scanner)
        self._threshold_overrides = _ThresholdOverrides(self.thresholds)
        self._threshold_overrides.apply(threshold_overrides)
        self._report_store = DeliveryReportStore(self.project_name)
        self._scan_gates = ConsolScanGateEvaluator(
            self.project_path, self.thresholds, self._scanner,
            self._import_verifier, function_mapping=self.function_mapping)
        self._counting = CountingGateEvaluator(
            self.project_path, self.thresholds, self.baseline_data, self._scanner,
            quality_monitor=quality_monitor,
            function_mapping=self.function_mapping)
    def _compute_overall_score(self, gates: list[GateResult]) -> float:
        scores = [g.score for g in gates if g.status != GateStatus.SKIP.value]
        if not scores:
            return _SCORE_ZERO
        return round(sum(scores) / len(scores), 1)
    def _generate_hash(self, report: DeliveryGateReport) -> str:
        gates_digest = {
            str(gate_id): _gate_summary(gate)
            for gate_id, gate in sorted(
                (report.gates or {}).items(), key=lambda item: str(item[0]))
        }
        content = json.dumps({
            'project': report.project_path,
            'verdict': report.verdict,
            'passed': report.passed_gates,
            'failed': report.failed_gates,
            'warn': report.warn_gates,
            'skipped': report.skipped_gates,
            'score': report.overall_score,
            'override_code': report.override_code,
            'override_reason': report.override_reason,
            'gates': gates_digest,
        }, sort_keys=True, default=str)
        return hashlib.sha256(content.encode()).hexdigest()[:16]
    def execute(self, override_code: str = _DEFAULT_OVERRIDE_CODE,
                force: bool = _DEFAULT_FORCE) -> DeliveryGateReport:
        report = DeliveryGateReport(
            project_path=self.project_path,
            project_name=self.project_name,
        )
        self._scanner.reset()
        self._import_verifier.reset()
        self._counting.populate_baseline(report)
        gates = self._run_gates(report)
        self._register_gates(report, gates)
        self._finalize_report(report, gates, override_code, force)
        _log.info(
            "[delivery-gate] 判定完成: %s (评分 %.1f, PASS=%d FAIL=%d WARN=%d SKIP=%d)",
            report.verdict, report.overall_score,
            report.passed_gates, report.failed_gates,
            report.warn_gates, report.skipped_gates,
        )
        return report
    @staticmethod
    def _register_gates(report: DeliveryGateReport,
                        gates: list[GateResult]) -> None:
        for gate in gates:
            report.gates[gate.gate_id] = gate
    def _finalize_report(self, report: DeliveryGateReport,
                         gates: list[GateResult], override_code: str,
                         force: bool) -> None:
        self._apply_gate_statistics(report, gates)
        report.verdict = self._decide_verdict(report)
        self._collect_issues(report, gates)
        report.overall_score = self._compute_overall_score(gates)
        self._apply_override(report, override_code, force)
        report.delivery_hash = self._generate_hash(report)
    def _run_gates(self, report: DeliveryGateReport) -> list[GateResult]:
        gate_builders = (
            self._counting.gate_builders()
            + self._scan_gates.gate_builders()
        )
        gates: list[GateResult] = []
        for builder in gate_builders:
            start = time.perf_counter()
            gate = builder(report)
            gate.elapsed_ms = round((time.perf_counter() - start) * 1000, 1)
            gates.append(gate)
        return gates
    @classmethod
    def _apply_gate_statistics(cls, report: DeliveryGateReport,
                               gates: list[GateResult]) -> None:
        counts = Counter(gate.status for gate in gates)
        for status, field_name in _STATUS_FIELDS.items():
            setattr(report, field_name, counts.get(status, 0))
    @staticmethod
    def _decide_verdict(report: DeliveryGateReport) -> str:
        if report.failed_gates > 0:
            return DeliveryVerdict.REJECTED.value
        if report.warn_gates > 0:
            return DeliveryVerdict.CONDITIONAL.value
        if report.passed_gates > 0:
            return DeliveryVerdict.APPROVED.value
        return DeliveryVerdict.PENDING.value
    @staticmethod
    def _collect_issues(report: DeliveryGateReport,
                        gates: list[GateResult]) -> None:
        for gate in gates:
            if gate.status == GateStatus.FAIL.value:
                report.blocking_issues.extend(gate.failure_reasons)
                _log.warning(
                    "[delivery-gate] 门禁 FAIL %s: %s",
                    gate.gate_id,
                    "; ".join(gate.failure_reasons[:3]),
                )
            report.warnings.extend(gate.recommendations)
    @staticmethod
    def _apply_override(report: DeliveryGateReport, override_code: str,
                        force: bool) -> None:
        if override_code:
            if isinstance(override_code, str):
                report.override_code = override_code
            else:
                _log.warning(
                    "[delivery-gate] override_code 类型非法（%s），忽略",
                    type(override_code).__name__)
        if signal_bool(force):
            report.override_reason = "强制执行模式"
            report.verdict = DeliveryVerdict.APPROVED.value
    def save_report(self, report: DeliveryGateReport, output_dir: str | None = None) -> str:
        stamp_ms = int(_restore_timestamp(report.timestamp) * 1000)
        if output_dir is None and self.project_path:
            output_dir = default_reports_dir(os.path.abspath(self.project_path))
        return self._report_store.save(report.to_dict(), stamp_ms, output_dir)
def run_full_delivery_gate(project_path: str,
                           baseline: dict | None = None, *,
                           quality_monitor: Any = None,
                           function_mapping: dict | None = None,
                           override_code: str = _DEFAULT_OVERRIDE_CODE,
                           force: bool = _DEFAULT_FORCE) -> DeliveryGateReport:
    started = time.monotonic()
    gate = PreDeliveryGate(
        project_path,
        baseline_data=baseline,
        quality_monitor=quality_monitor,
        function_mapping=function_mapping,
    )
    result = gate.execute(override_code=override_code, force=force)
    verdict = str(getattr(result, "verdict", "") or "")
    trace_module_run("diag_delivery_gate", "run_full_delivery_gate", started,
                     outcome=verdict or "UNKNOWN", verdict=verdict)
    return result
_REPORTS_SUBDIR_NAME = "delivery_gates"
_DEFAULT_REPORT_FILE_PREFIX = "delivery_gate"
_REPORT_FILE_SUFFIX = ".json"
def default_reports_dir(skill_dir: str | None = None) -> str:
    if skill_dir:
        base = skill_dir
    else:
        candidate = resolve_search_root(os.getcwd())
        has_project_marker = (
            os.path.exists(os.path.join(candidate, "__init__.py"))
            or any(os.path.exists(os.path.join(candidate, marker))
                   for marker in PROJECT_ROOT_MARKERS)
        )
        base = (candidate if has_project_marker
                else os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(get_temp_base(base), _REPORTS_SUBDIR_NAME)
def _report_timestamp_ms(base: str, prefix: str, suffix: str) -> int | None:
    raw_stamp = base[len(prefix):-len(suffix)]
    if (not raw_stamp.isascii()
            or not raw_stamp.replace("_", "").isdigit()):
        return None
    try:
        stamp = int(raw_stamp)
    except ValueError as exc:
        log_swallowed(__name__, exc,
                      context=f'_report_timestamp_ms:{type(exc).__name__}')
        return None
    return stamp if stamp >= 0 else None
def _report_has_ambiguous_ownership(
        file_path: str, project_name: str,
        file_prefix: str = _DEFAULT_REPORT_FILE_PREFIX) -> bool:
    base = os.path.basename(file_path)
    prefix = f"{file_prefix}_{project_name}_"
    suffix = _REPORT_FILE_SUFFIX
    if not (base.startswith(prefix) and base.endswith(suffix)):
        return False
    return "_" in base[len(prefix):-len(suffix)]
def _delivery_report_entries(
        reports_dir: str, file_prefix: str,
        project_name: str) -> list[tuple[int, str]]:
    prefix = f"{file_prefix}_{project_name}_"
    suffix = _REPORT_FILE_SUFFIX
    entries: list[tuple[int, str]] = []
    for base in os.listdir(reports_dir):
        if not (base.startswith(prefix) and base.endswith(suffix)):
            continue
        timestamp_ms = _report_timestamp_ms(base, prefix, suffix)
        if timestamp_ms is None:
            continue
        file_path = os.path.join(reports_dir, base)
        if not os.path.isfile(file_path):
            continue
        entries.append((timestamp_ms, file_path))
    return entries
def delivery_report_candidates(project_name: str,
                               reports_dir: str | None = None,
                               file_prefix: str = _DEFAULT_REPORT_FILE_PREFIX) -> list[str]:
    reports_dir = reports_dir or default_reports_dir()
    try:
        candidates = _delivery_report_entries(
            reports_dir, file_prefix, project_name)
    except OSError as exc:
        log_swallowed(__name__, exc,
                      context='delivery_report_candidates:OSError')
        return []
    candidates.sort(key=lambda item: item[0], reverse=True)
    return [file_path for _timestamp_ms, file_path in candidates]
class DeliveryReportStore:
    def __init__(self, project_name: str, keep_reports: int = 3,
                 file_prefix: str = _DEFAULT_REPORT_FILE_PREFIX) -> None:
        self._project_name = project_name
        self._keep_reports = keep_reports
        self._file_prefix = file_prefix
    def save(self, payload: dict, stamp_ms: int,
             output_dir: str | None = None) -> str:
        _stamp = _as_non_negative_int(stamp_ms)
        if _stamp is None:
            _log.warning(
                "[delivery-gate] 报告毫秒戳非法（%r），按 0 落盘", stamp_ms)
            _stamp = 0
        stamp_ms = _stamp
        output_dir = output_dir or default_reports_dir()
        os.makedirs(output_dir, exist_ok=True)
        while True:
            filepath = os.path.join(
                output_dir, self._allocate_filename(output_dir, stamp_ms))
            try:
                with guarded_open(filepath, 'x', encoding='utf-8') as f:
                    json.dump(payload, f, indent=2, ensure_ascii=False, default=str)
                break
            except FileExistsError:
                continue
        _log.info("[delivery-gate] 报告写入: %s", filepath)
        self._rotate(output_dir, filepath)
        return filepath
    def _allocate_filename(self, output_dir: str, stamp_ms: int) -> str:
        stamp = stamp_ms
        while True:
            name = self._filename(stamp)
            if not os.path.exists(os.path.join(output_dir, name)):
                return name
            stamp += 1
    def _filename(self, stamp: int) -> str:
        return (f"{self._file_prefix}_{self._project_name}_{stamp}"
                f"{_REPORT_FILE_SUFFIX}")
    def _can_delete_report(self, file_path: str) -> bool:
        base = os.path.basename(file_path)
        prefix = f"{self._file_prefix}_{self._project_name}_"
        suffix = _REPORT_FILE_SUFFIX
        if not (base.startswith(prefix) and base.endswith(suffix)):
            return False
        raw_stamp = base[len(prefix):-len(suffix)]
        if "_" not in raw_stamp:
            return True
        try:
            with open(file_path, encoding="utf-8") as handle:
                payload = json.load(handle)
        except (OSError, ValueError, RecursionError) as exc:
            _log.warning(
                "[delivery-gate] 歧义报告不可读，跳过删除: %s: %s",
                file_path, exc)
            return False
        declared = payload.get("project_name") if isinstance(payload, dict) else None
        if (isinstance(declared, str) and declared
                and declared == self._project_name):
            return True
        _log.warning(
            "[delivery-gate] 文件名归属有歧义且内容未确认归属，跳过删除: %s",
            file_path)
        return False
    def _rotate(self, output_dir: str, current: str = "") -> None:
        lock_path = os.path.join(
            output_dir,
            f"{self._file_prefix}_{self._project_name}_rotation.lock")
        try:
            lock_fd = os.open(lock_path, os.O_CREAT | os.O_RDWR)
        except OSError as exc:
            _log.warning("[delivery-gate] 报告轮换锁创建失败（跳过清理）: %s", exc)
            return
        locked = False
        try:
            locked = lock_region_nonblocking(lock_fd)
            if not locked:
                _log.info("[delivery-gate] 另一写入者正在轮换（保留报告并跳过清理）")
                return
            if current and not os.path.isfile(current):
                _log.info("[delivery-gate] 当前报告已由前次轮换清理（跳过后续清理）")
                return
            try:
                stale_reports = self._stale_reports(output_dir, current)
            except OSError as exc:
                _log.warning("[delivery-gate] 清理超量历史报告失败: %s", exc)
                return
            for stale in stale_reports:
                if not self._can_delete_report(stale):
                    continue
                if safe_delete(stale):
                    _log.info("[delivery-gate] 清理超量历史报告: %s", stale)
                else:
                    _log.warning("[delivery-gate] 清理超量历史报告单条失败"
                                 "(跳过继续): %s", stale)
        finally:
            if locked:
                unlock_region(lock_fd)
            try:
                os.close(lock_fd)
            except OSError as exc:
                _log.warning("[delivery-gate] 报告轮换锁关闭失败: %s", exc)
    def _stale_reports(self, output_dir: str, current: str = "") -> list[str]:
        entries = _delivery_report_entries(
            output_dir, self._file_prefix, self._project_name)
        entries.sort(key=lambda item: (item[0], item[1]))
        reports = [file_path for _timestamp_ms, file_path in entries
                   if self._can_delete_report(file_path)]
        if not current:
            return reports[:max(len(reports) - self._keep_reports, 0)]
        current_key = os.path.normcase(os.path.abspath(current))
        others = [path for path in reports
                  if os.path.normcase(os.path.abspath(path)) != current_key]
        keep_others = max(self._keep_reports - 1, 0)
        return others[:max(len(others) - keep_others, 0)]
def load_last_delivery_report(project_name: str,
                               reports_dir: str | None = None) -> Any:
    files = delivery_report_candidates(project_name, reports_dir)
    for fp in files:
        try:
            with open(fp, encoding="utf-8") as f:
                loaded = json.load(f)
        except (OSError, ValueError, RecursionError) as e:
            _log.warning("[delivery] 报告不可读（回退更旧一份）: %s: %s", fp, e)
            continue
        if not isinstance(loaded, dict):
            _log.warning("[delivery] 报告顶层非 dict（回退更旧一份）: %s: %s",
                           fp, type(loaded).__name__)
            continue
        try:
            restored = restore_delivery_report(loaded)
        except (OSError, TypeError, ValueError, KeyError) as e:
            _log.warning("[delivery] 报告结构无效（回退更旧一份）: %s: %s", fp, e)
            continue
        declared = restored.project_name
        if declared and declared != project_name:
            _log.warning(
                "[delivery] 报告归属不符（请求 %r，声明 %r，回退更旧一份）: %s",
                project_name, declared, fp)
            continue
        if (not declared and _report_has_ambiguous_ownership(fp, project_name)):
            _log.warning(
                "[delivery] 歧义报告缺少项目归属声明（请求 %r，回退更旧一份）: %s",
                project_name, fp)
            continue
        return restored
    return None
__all__ = [
    'DeliveryGateReport',
    'DeliveryReportStore',
    'DeliveryVerdict',
    'GateResult',
    'GateStatus',
    'PreDeliveryGate',
    'default_reports_dir',
    'delivery_report_candidates',
    'format_delivery_ci_output',
    'load_last_delivery_report',
    'restore_delivery_report',
    'run_full_delivery_gate',
]

from __future__ import annotations

import copy
import hashlib
import itertools
import json
import logging
import math
import os
import re
import time
import uuid
from collections.abc import Callable, Mapping
from dataclasses import asdict, dataclass, field
from enum import Enum
from fractions import Fraction
from typing import Any, NamedTuple

from jwsgj.build_safe_rollback import (
    GATE_FAILURE_PREFIXES,
    FeedbackRollbackManager,
    VersionChain,
    VersionMeta,
    apply_regression_gate,
    get_rollback_audit,
    record_version_chain,
    regression_undecided,
    take_pre_snapshot,
    verify_applied_modification,
)
from jwsgj.code_feedback_cv_rules import (
    CV_RULE_TARGETS,
    CVRuleModifier,
    cv_rule_registry,
)
from jwsgj.code_feedback_thresholds import (
    THRESHOLD_TARGETS,
    ThresholdModifier,
    infer_threshold_from_entry,
    numeric_threshold_target,
    parse_threshold_value,
    threshold_direction_from_text,
    threshold_registry,
)
from jwsgj.code_level_feedback_l2 import (
    LogicInjector,
    SourceFixApplier,
    plan_l2_injection,
    resolve_injection_target,
)
from jwsgj.diag_guard_io import (
    atomic_write_text,
    path_identity,
)
from jwsgj.diag_guard_state import (
    read_json_artifact,
    serialize_json,
)
from jwsgj.diag_types_defs import (
    FeedbackBatchResult,
    FeedbackModification,
    build_failed_modification,
    str_field,
)
from jwsgj.diag_types_normalize import (
    cv_int,
    is_valid_fp_rate,
    parse_json_dict,
    safe_confidence,
    safe_float,
    safe_short_text,
    signal_bool,
)
from jwsgj.diag_types_vocab import (
    CONF_MEDIUM,
    DEFAULT_CONFIDENCE_FALLBACK,
    FIELD_CV_CONFIDENCE_THRESHOLDS,
    FIELD_FROZEN_ROUNDS_REMAINING,
    FIELD_METHOD_CONFIDENCE_MULTIPLIERS,
    FIELD_SUGGESTED_VALUE,
    FIELD_THRESHOLD_ADJUST,
    FMT_DATETIME,
    SEVERITY_RANK,
)
from jwsgj.fp_rules_judge import (
    SUPPRESSION_DEFAULT_MIN_SEVERITY,
    drop_fp_suppression_rule,
    normalize_suppression_rule,
)
from jwsgj.html_render_pipeline import emit_feedback_fix_report
from jwsgj.log_config import locked_artifact, log_swallowed
from jwsgj.retrospective_ledger import (
    enhancement_dict_items,
    read_enhancement_log,
)
from jwsgj.runtime_paths import (
    EVOLUTION_STATE_SECTIONS,
    evolution_state_path,
    feedback_enhancement_log_context,
    fp_suppression_path,
    get_jinhua_dir,
    read_evolution_section,
    read_evolution_state,
    update_evolution_section,
    write_evolution_section,
)
from jwsgj.runtime_scope import (
    normalize_skill_dir,
)
from jwsgj.xv_evidence_strength import (
    EVIDENCE_FAMILY_NAMES,
    family_reliability_base,
)

logger = logging.getLogger(__name__)
_AUDIT_RECORD_LIMIT = 200
_CONFLICT_RECORD_LIMIT = 100
_CONVERGING_RATIO = 0.7
_DIVERGING_RATIO = 1.3
CONSISTENCY_THRESHOLD = 3
OSCILLATION_WINDOW = 5
OSCILLATION_REVERSAL_LIMIT = 3
FREEZE_ROUNDS = 3
FREEZE_ROUNDS_MAX = 16
CONSISTENCY_THRESHOLD_MIN = 2
CONSISTENCY_THRESHOLD_MAX = 5
MAGNITUDE_HISTORY_SIZE = 5
_FIXER_SAFETY_OVERRIDES = "fixer_safety_overrides"
PARAMETER_MAPPING: dict[str, str] = {
    "SINGLE_SOURCE_CONFIRM_THRESHOLD": FIELD_CV_CONFIDENCE_THRESHOLDS,
    "COVERAGE_LOW_THRESHOLD": FIELD_CV_CONFIDENCE_THRESHOLDS,
    "_INITIAL_EVIDENCE_WEIGHTS": FIELD_CV_CONFIDENCE_THRESHOLDS,
    "RULE_FP_TRACKER": FIELD_CV_CONFIDENCE_THRESHOLDS,
    "CONFLICTING_PAIRS": FIELD_CV_CONFIDENCE_THRESHOLDS,
    "CONTRADICTION_SEVERITY_DECISION": FIELD_CV_CONFIDENCE_THRESHOLDS,
    "AUTO_SAFE_REGISTRY": _FIXER_SAFETY_OVERRIDES,
}
class Verdict(str, Enum):
    ALLOW = "allow"
    DEFER = "defer"
    FROZEN = "frozen"
    CONFLICT = "conflict"
@dataclass
class ParameterState:
    parameter: str = ""
    direction_history: list[int] = field(default_factory=list)
    runtime_direction_streak: int = 0
    runtime_last_direction: int = 0
    frozen_rounds_remaining: int = 0
    total_adjustments: int = 0
    total_conflicts: int = 0
    total_frozen: int = 0
    last_verdict: str = ""
    magnitude_history: list[float] = field(default_factory=list)
    oscillation_count: int = 0
    runtime_observed_snapshot: str = ""
    def to_dict(self) -> dict:
        return asdict(self)
@dataclass
class AdjustmentRecord:
    timestamp: str = ""
    parameter: str = ""
    direction: int = 0
    source: str = ""
    old_value: Any = None
    new_value: Any = None
    verdict: str = ""
    def to_dict(self) -> dict:
        return asdict(self)
@dataclass
class ConflictRecord:
    timestamp: str = ""
    parameter: str = ""
    runtime_direction: int = 0
    code_level_direction: int = 0
    runtime_value: Any = None
    code_level_value: Any = None
    message: str = ""
_PARAM_STATE_INT_FIELDS = (
    "runtime_direction_streak",
    "runtime_last_direction",
    FIELD_FROZEN_ROUNDS_REMAINING,
    "total_adjustments",
    "total_conflicts",
    "total_frozen",
    "oscillation_count",
)
def _is_plain_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)
def _is_finite_magnitude(value: Any) -> bool:
    return (isinstance(value, int) and not isinstance(value, bool)) or (
        isinstance(value, float) and math.isfinite(value))
def _is_direction_value(value: Any) -> bool:
    return _is_plain_int(value) and -1 <= value <= 1
def _is_non_negative_magnitude(value: Any) -> bool:
    return _is_finite_magnitude(value) and value >= 0
_NON_NEGATIVE_STATE_FIELDS = tuple(
    key for key in _PARAM_STATE_INT_FIELDS
    if key != "runtime_last_direction")
_HISTORY_FIELD_VALIDATORS = (
    ("direction_history", _is_direction_value, OSCILLATION_WINDOW),
    ("magnitude_history", _is_non_negative_magnitude, MAGNITUDE_HISTORY_SIZE),
)
def _normalize_param_state_fields(state: dict) -> None:
    for key, is_valid, limit in _HISTORY_FIELD_VALIDATORS:
        raw = state.get(key)
        valid = ([v for v in raw if is_valid(v)]
                 if isinstance(raw, list) else [])
        state[key] = valid[-limit:]
    for key in _PARAM_STATE_INT_FIELDS:
        value = state.get(key)
        floor = 0 if key in _NON_NEGATIVE_STATE_FIELDS else None
        if not _is_plain_int(value) or (floor is not None and value < floor):
            state[key] = 0
    if not _is_direction_value(state["runtime_last_direction"]):
        state["runtime_last_direction"] = 0
    if not isinstance(state.get("runtime_observed_snapshot"), str):
        state["runtime_observed_snapshot"] = ""
def frozen_remaining(state: dict) -> int:
    raw = state.get(FIELD_FROZEN_ROUNDS_REMAINING, 0)
    return max(0, raw) if _is_plain_int(raw) else 0
def section_size(section: Any) -> int:
    return len(section) if isinstance(section, dict) else 0
def new_runtime_snapshot_id() -> str:
    return uuid.uuid4().hex
def suggested_scalar(entry: dict) -> Any:
    raw = entry.get(FIELD_SUGGESTED_VALUE, "")
    return "" if isinstance(raw, bool) else raw
def _suggested_text(entry: dict, constant_name: str = "") -> str:
    raw = suggested_scalar(entry)
    if isinstance(raw, str):
        return raw
    if isinstance(raw, dict) and constant_name:
        raw = raw.get(constant_name)
        if isinstance(raw, str):
            return raw
    return str(raw) if _is_finite_magnitude(raw) else ""
def _infer_adjustment_magnitude(
    entry: dict,
    constant_name: str,
    targets: dict | None = None,
) -> float:
    target = numeric_threshold_target(constant_name, targets)
    if target is None:
        return 1.0
    default_val = safe_float(target.get("default", 0), None)
    suggested_val = safe_float(_suggested_text(entry, constant_name), None)
    if default_val is None or suggested_val is None:
        return 1.0
    base = abs(default_val) if default_val != 0 else 1.0
    magnitude = abs(suggested_val - default_val) / base
    return magnitude if math.isfinite(magnitude) else 1.0
def _looks_like_constant_target(target: Any) -> bool:
    if not isinstance(target, str) or not target.strip():
        return False
    tail = re.split(r"[./:]", target.strip())[-1]
    return bool(re.fullmatch(r"[A-Z][A-Z0-9_]*", tail)
                or re.fullmatch(r"[A-Za-z][A-Za-z0-9]*_[A-Za-z0-9_]+",
                                tail))
def _contains_identifier(text: Any, token: str) -> bool:
    if not isinstance(text, str) or not token:
        return False
    head = r"(?<![A-Za-z0-9_])"
    tail = (r"(?![A-Za-z0-9_])"
            if token[-1].isascii() and (token[-1].isalnum()
                                        or token[-1] == "_")
            else "")
    return re.search(f"{head}{re.escape(token)}{tail}", text,
                     re.IGNORECASE) is not None
class CoordinatorStateFiles:
    _STATE_SECTION = "coordinator_state"
    _ADJUSTMENTS_SECTION = "method_adjustments"
    def __init__(self, skill_dir: str):
        self.skill_dir = normalize_skill_dir(skill_dir)
        self.state_path = self._STATE_SECTION
        self.adjustments_path = self._ADJUSTMENTS_SECTION
        self.read_failures: dict[str, str] = {}
    def _read_section(self, section: str):
        state = read_evolution_state(self.skill_dir, for_update=True)
        data = (state[section] if section in state
                else read_evolution_section(self.skill_dir, section))
        if data is None:
            legacy_path = os.path.join(
                get_jinhua_dir(self.skill_dir), EVOLUTION_STATE_SECTIONS[section])
            if section in state or os.path.isfile(legacy_path):
                raise ValueError(f"状态 section 存在但不可读: {legacy_path}")
        return data
    def _load_section(self, section: str, log_tag: str,
                      read_failures: dict | None = None) -> dict | None:
        try:
            data = self._read_section(section)
        except (OSError, ValueError, TypeError) as e:
            log_swallowed(
                __name__, e,
                context=(f'CoordinatorStateFiles._load_section:'
                         f'{type(e).__name__}'))
            logger.warning(
                "[Coordinator] %s 读取故障，按初始状态继续且不覆盖既有状态: %s",
                log_tag, e)
            if read_failures is not None:
                read_failures[section] = str(e)
            return None
        if data is None:
            if read_failures is not None:
                read_failures.pop(section, None)
            return None
        if not isinstance(data, dict):
            logger.warning(
                "[Coordinator] %s 顶层非对象(%s)，使用初始状态",
                log_tag, type(data).__name__)
            if read_failures is not None:
                read_failures[section] = (
                    f"顶层非对象: {type(data).__name__}")
            return None
        if read_failures is not None:
            read_failures.pop(section, None)
        return data
    @staticmethod
    def _coerce_state_field(data: dict, key: str, expected: type, default: Any) -> None:
        if key not in data:
            data[key] = default
            return
        value = data[key]
        if not isinstance(value, expected) or (
                expected is int and isinstance(value, bool)):
            logger.warning(
                "[Coordinator] 状态 %s 类型异常(%s)，回落默认值",
                key, type(value).__name__)
            data[key] = default
    def load_state(self) -> dict[str, dict]:
        data = self._load_section(
            self._STATE_SECTION, "状态", self.read_failures)
        if data is not None:
            self._coerce_state_field(data, "parameters", dict, {})
            self._coerce_state_field(data, "conflicts", list, [])
            self._coerce_state_field(data, "session_count", int, 0)
            return data
        return {
            "version": "1.0",
            "parameters": {},
            "conflicts": [],
            "session_count": 0,
        }
    def load_runtime_adjustments(self) -> dict:
        data = self._load_section(
            self._ADJUSTMENTS_SECTION, "运行时调整", self.read_failures)
        if data is not None:
            return data
        return {
            "version": "1.0",
            FIELD_METHOD_CONFIDENCE_MULTIPLIERS: {},
            FIELD_CV_CONFIDENCE_THRESHOLDS: {},
            _FIXER_SAFETY_OVERRIDES: {},
            "last_updated": "",
        }
    def _overwrite_blocked(self) -> str | None:
        reason = self.read_failures.get(self._STATE_SECTION)
        if reason is None:
            return None
        try:
            data = self._read_section(self._STATE_SECTION)
        except (OSError, ValueError, TypeError) as e:
            return str(e)
        if data is None:
            self.read_failures.pop(self._STATE_SECTION, None)
            return None
        if isinstance(data, dict):
            return "状态 section 已恢复可读，需重新加载后才能保存"
        return f"状态 section 不可安全恢复: {type(data).__name__}"
    def persist(self, state: dict) -> bool:
        blocked = self._overwrite_blocked()
        if blocked is not None:
            logger.warning(
                "[Coordinator] 状态不可安全覆盖(%s)，跳过落盘以保留既有状态: %s",
                blocked, self.skill_dir)
            return False
        if not write_evolution_section(
                self.skill_dir, self._STATE_SECTION, state):
            logger.warning("[Coordinator] 状态保存失败: %s", self.skill_dir)
            return False
        return True
class ParameterLedger:
    def __init__(self, parameters: dict[str, dict],
                 threshold_targets: dict | None = None):
        self._parameters = parameters
        self._threshold_targets = threshold_targets
        self.records: list[AdjustmentRecord] = []
    def _registry(self) -> dict:
        return threshold_registry(self._threshold_targets)
    def get_or_create(self, param_name: str) -> dict:
        state = self._parameters.get(param_name)
        if isinstance(state, dict):
            _normalize_param_state_fields(state)
            return state
        if state is not None:
            logger.warning(
                "[Coordinator] 参数 %s 状态类型异常(%s)，重建默认状态",
                param_name, type(state).__name__)
        state = ParameterState(parameter=param_name).to_dict()
        self._parameters[param_name] = state
        return state
    def _known_constants(self) -> tuple[str, ...]:
        names = list(self._registry())
        if self._threshold_targets is None:
            names.extend(name for name in PARAMETER_MAPPING
                         if name not in names)
        return tuple(names)
    def _match_known_constant(self, text: str) -> str:
        names = (
            name for name in self._known_constants()
            if isinstance(name, str) and name.strip()
        )
        for const_name in sorted(names, key=len, reverse=True):
            if _contains_identifier(text, const_name):
                return const_name
        return ""
    def _fallback_registry(self) -> dict:
        if self._threshold_targets is None:
            return PARAMETER_MAPPING
        return self._registry()
    def _match_threshold_fallback(self, text: str) -> str:
        lowered = text.lower()
        if "threshold" not in lowered and "阈值" not in lowered:
            return ""
        candidates = tuple(
            name for name in self._fallback_registry()
            if isinstance(name, str) and "THRESHOLD" in name.upper())
        return candidates[0] if len(candidates) == 1 else ""
    def extract_constant_name(self, entry: dict) -> str:
        if not isinstance(entry, dict):
            entry = {}
        explicit_target = entry.get("target")
        if isinstance(explicit_target, str):
            registered_name = explicit_target.strip()
            if registered_name in self._known_constants():
                return registered_name
            for pattern, (_level, target_key) in TARGET_TO_LEVEL_MAP.items():
                is_alias = (registered_name.startswith(pattern)
                            if pattern.endswith("/") else
                            registered_name == pattern
                            or registered_name.startswith(pattern + "/"))
                if not is_alias:
                    continue
                if target_key in self._known_constants():
                    return target_key
                break
        if _looks_like_constant_target(explicit_target):
            return ""
        text = f"{entry.get('target') or ''} {entry.get('description') or ''}"
        matched = self._match_known_constant(text)
        if matched:
            return matched
        semantic = infer_threshold_from_entry(entry, self._registry())
        return semantic or self._match_threshold_fallback(text)
    def update_runtime_streak(
        self,
        direction: int,
        param_state: dict,
        snapshot_id: str | None = None,
    ) -> None:
        if (snapshot_id is not None
                and param_state.get("runtime_observed_snapshot") == snapshot_id):
            return
        if direction == 0:
            param_state["runtime_direction_streak"] = 0
            param_state["runtime_last_direction"] = 0
            if snapshot_id is not None:
                param_state["runtime_observed_snapshot"] = snapshot_id
            return
        streak = param_state.get("runtime_direction_streak", 0)
        param_state["runtime_direction_streak"] = (
            streak + 1
            if direction == param_state.get("runtime_last_direction", 0)
            else 1)
        param_state["runtime_last_direction"] = direction
        if snapshot_id is not None:
            param_state["runtime_observed_snapshot"] = snapshot_id
    def record(
        self,
        param_name: str,
        direction: int,
        verdict: str,
        entry: dict | None = None,
        record_direction: bool = True,
    ) -> None:
        state = self.get_or_create(param_name)
        self._append_audit(self._build_record(
            param_name, direction, verdict, entry,
            targets=self._threshold_targets))
        if record_direction and direction != 0:
            self._push_direction(state, direction)
        self._push_magnitude(state, entry, param_name)
        state["total_adjustments"] = state.get(
            "total_adjustments", 0) + 1
        state["last_verdict"] = verdict
        self._decrement_frozen(state)
    def _append_audit(self, record: AdjustmentRecord) -> None:
        self.records.append(record)
        if len(self.records) > _AUDIT_RECORD_LIMIT:
            del self.records[:-_AUDIT_RECORD_LIMIT]
    @staticmethod
    def _push_direction(state: dict, direction: int) -> None:
        history = state.get("direction_history", [])
        history.append(direction)
        state["direction_history"] = history[-OSCILLATION_WINDOW:]
    def _push_magnitude(self, state: dict, entry: dict | None,
                        param_name: str) -> None:
        magnitude = (1.0 if entry is None
                     else _infer_adjustment_magnitude(
                         entry, param_name, self._threshold_targets))
        history = state.get("magnitude_history", [])
        history.append(abs(magnitude))
        state["magnitude_history"] = history[-MAGNITUDE_HISTORY_SIZE:]
    @staticmethod
    def _decrement_frozen(state: dict) -> None:
        remaining = frozen_remaining(state)
        if remaining > 0:
            state[FIELD_FROZEN_ROUNDS_REMAINING] = remaining - 1
    @staticmethod
    def _build_record(param_name: str, direction: int, verdict: str,
                      entry: dict | None,
                      targets: dict | None = None) -> AdjustmentRecord:
        old_value = None
        new_value = None
        if entry is not None:
            new_value = suggested_scalar(entry)
            registry = threshold_registry(targets)
            target = registry.get(param_name) if isinstance(registry, dict) else None
            if isinstance(target, dict):
                old_value = target.get("default")
        return AdjustmentRecord(
            timestamp=time.strftime(FMT_DATETIME),
            parameter=param_name,
            direction=direction,
            source="code_level",
            old_value=old_value,
            new_value=new_value,
            verdict=verdict,
        )
    def history(self, parameter: str | None = None) -> list[dict]:
        records = self.records
        if parameter:
            records = [r for r in records if r.parameter == parameter]
        return [r.to_dict() for r in records]
    def adaptive_threshold(self, param_state: dict) -> int:
        ratio = self._magnitude_trend_ratio(
            param_state.get("magnitude_history", []))
        if ratio is None:
            return CONSISTENCY_THRESHOLD
        if ratio < _CONVERGING_RATIO:
            return CONSISTENCY_THRESHOLD_MIN
        if ratio > _DIVERGING_RATIO:
            return CONSISTENCY_THRESHOLD_MAX
        return CONSISTENCY_THRESHOLD
    @staticmethod
    def _magnitude_trend_ratio(magnitudes: list) -> Fraction | None:
        if len(magnitudes) < 2:
            return None
        mid = max(1, len(magnitudes) - 2)
        earlier = magnitudes[:mid]
        recent = magnitudes[mid:]
        earlier_total = sum(Fraction(value) for value in earlier)
        recent_total = sum(Fraction(value) for value in recent)
        avg_earlier = earlier_total / len(earlier)
        if avg_earlier == 0:
            return None
        return (recent_total / len(recent)) / avg_earlier
    def adaptive_freeze_rounds(self, param_state: dict) -> int:
        raw = (param_state.get("oscillation_count", 0)
               if isinstance(param_state, dict) else 0)
        if isinstance(raw, bool) or not isinstance(raw, int):
            raw = 0
        freeze = FREEZE_ROUNDS
        remaining = max(0, raw - 1)
        while remaining and freeze < FREEZE_ROUNDS_MAX:
            freeze *= 2
            remaining -= 1
        return min(freeze, FREEZE_ROUNDS_MAX)
    def detect_oscillation(self, history: list[int]) -> bool:
        if len(history) < OSCILLATION_REVERSAL_LIMIT + 1:
            return False
        window = history[-OSCILLATION_WINDOW:]
        reversals = sum(
            1 for prev, curr in itertools.pairwise(window)
            if prev and curr and prev != curr)
        return reversals >= OSCILLATION_REVERSAL_LIMIT
@dataclass
class CoordinatorReport:
    timestamp: str = ""
    total_evaluated: int = 0
    allowed: int = 0
    deferred: int = 0
    frozen: int = 0
    conflicts: int = 0
    parameter_states: dict[str, dict] = field(default_factory=dict)
    new_conflicts: list[dict] = field(default_factory=list)
    def to_dict(self) -> dict:
        return asdict(self)
def _runtime_section_key(param_name: str,
                         threshold_targets: dict | None = None
                         ) -> str | None:
    mapped = PARAMETER_MAPPING.get(param_name)
    if mapped:
        return mapped
    registry = threshold_registry(threshold_targets)
    target = registry.get(param_name) if isinstance(registry, dict) else None
    if isinstance(target, dict):
        return FIELD_CV_CONFIDENCE_THRESHOLDS
    return None
def _direction_from_safety_override(value: Any) -> int:
    if (isinstance(value, dict) and "auto_safe" in value
            and not signal_bool(value.get("auto_safe"))):
        return 1
    return 0
def _relative_direction(value: Any, pivot: float, *,
                        below: int, above: int) -> int:
    num = safe_float(value, None)
    if num is None or num == pivot:
        return 0
    return below if num < pivot else above
def _direction_from_confidence_multiplier(value: Any) -> int:
    return _relative_direction(value, 1.0, below=1, above=-1)
def _direction_from_cv_threshold(value: Any) -> int:
    return _relative_direction(value, CONF_MEDIUM, below=-1, above=1)
_RUNTIME_DIRECTION_RULES: dict[str, Callable[[Any], int]] = {
    _FIXER_SAFETY_OVERRIDES: _direction_from_safety_override,
    FIELD_METHOD_CONFIDENCE_MULTIPLIERS: _direction_from_confidence_multiplier,
    FIELD_CV_CONFIDENCE_THRESHOLDS: _direction_from_cv_threshold,
}
def infer_runtime_direction(
    adjustments: dict,
    param_key: str,
) -> int:
    section = _runtime_section(adjustments, param_key)
    if section is None:
        return 0
    infer_value_direction = _RUNTIME_DIRECTION_RULES.get(param_key)
    if infer_value_direction is None:
        return 0
    return _majority_direction(
        _section_direction_votes(section, infer_value_direction))
def _runtime_section(adjustments, param_key: str) -> dict | None:
    if not isinstance(adjustments, dict) or not adjustments:
        return None
    section = adjustments.get(param_key)
    if section is None:
        return None
    if not isinstance(section, dict):
        logger.warning(
            "[Coordinator] 运行时调整节 %s 类型异常(%s)，按空处理",
            param_key, type(section).__name__)
        return None
    return section or None
def _section_direction_votes(section: dict, infer_value_direction) -> list[int]:
    return [d for d in (infer_value_direction(v) for v in section.values()) if d]
def _majority_direction(directions: list[int]) -> int:
    if not directions:
        return 0
    avg = sum(directions) / len(directions)
    if avg > 0:
        return 1
    if avg < 0:
        return -1
    return 0
def infer_code_level_direction(
    entry: dict,
    constant_name: str,
    targets: dict | None = None,
) -> int:
    if not isinstance(entry, dict):
        entry = {}
    description = str(entry.get("description") or "").lower()
    suggested_direction = _direction_from_suggested_value(
        _suggested_text(entry, constant_name), constant_name, targets)
    if suggested_direction is not None:
        return suggested_direction
    return threshold_direction_from_text(description)
def _direction_from_suggested_value(suggested_raw: Any,
                                    constant_name: str,
                                    targets: dict | None = None) -> int | None:
    target = numeric_threshold_target(constant_name, targets)
    if target is None:
        return None
    try:
        default_val = float(target.get("default", 0))
        resolved_value = parse_threshold_value(
            str(suggested_raw), constant_name, targets)
        if resolved_value is None:
            return None
        suggested_val = float(resolved_value)
    except (ValueError, TypeError, OverflowError):
        logger.debug("[Coordinator] suggested_value 解析失败", exc_info=True)
        return None
    if not (math.isfinite(default_val) and math.isfinite(suggested_val)):
        return None
    if suggested_val > default_val:
        return 1
    if suggested_val < default_val:
        return -1
    return 0
class FeedbackRouteContext(NamedTuple):
    threshold_targets: dict | None = None
    cv_targets: dict | None = None
    injection_aliases: Mapping[str, str | None] | None = None
    @property
    def registries(self) -> dict:
        return {"threshold_targets": self.threshold_targets,
                "cv_targets": self.cv_targets}
@dataclass(frozen=True)
class _ArbitrationInput:
    param: str
    runtime_direction: int
    code_level_direction: int
    entry: dict
class FeedbackCoordinator:
    def __init__(self, skill_dir: str,
                 threshold_targets: dict | None = None):
        self.skill_dir = normalize_skill_dir(skill_dir)
        self._store = CoordinatorStateFiles(self.skill_dir)
        self._state: dict[str, dict] = self._store.load_state()
        self._runtime_adjustments: dict = self._store.load_runtime_adjustments()
        self._runtime_snapshot_id: str = new_runtime_snapshot_id()
        self._threshold_targets = threshold_targets
        self._ledger = ParameterLedger(
            self._state["parameters"], threshold_targets)
        self.version_chain = VersionChain(self.skill_dir)
        self._report = CoordinatorReport(
            timestamp=time.strftime(FMT_DATETIME),
        )
    def reload_runtime_adjustments(self) -> None:
        self._runtime_adjustments = self._store.load_runtime_adjustments()
        self._runtime_snapshot_id = new_runtime_snapshot_id()
        sizes = self._runtime_section_sizes()
        logger.debug("[Coordinator] 运行时调整已重载: %d 个方法乘数, %d 个CV阈值",
                      sizes["method_multipliers"], sizes["cv_thresholds"])
    def _runtime_section_sizes(self) -> dict[str, int]:
        return {
            "method_multipliers": section_size(
                self._runtime_adjustments.get(
                    FIELD_METHOD_CONFIDENCE_MULTIPLIERS, {})),
            "cv_thresholds": section_size(
                self._runtime_adjustments.get(
                    FIELD_CV_CONFIDENCE_THRESHOLDS, {})),
            "fixer_overrides": section_size(
                self._runtime_adjustments.get(
                    _FIXER_SAFETY_OVERRIDES, {})),
        }
    def _get_runtime_direction(self, param_name: str) -> int:
        runtime_key = _runtime_section_key(
            param_name, self._threshold_targets)
        if runtime_key is None:
            return 0
        return infer_runtime_direction(
            self._runtime_adjustments, runtime_key)
    def _get_runtime_value(self, param_name: str) -> Any:
        runtime_key = _runtime_section_key(
            param_name, self._threshold_targets)
        if runtime_key is None:
            return None
        section = self._runtime_adjustments.get(runtime_key)
        if not isinstance(section, dict) or not section:
            return None
        return section
    def evaluate(self, entry: dict) -> tuple[Verdict, str]:
        self._report.total_evaluated += 1
        if not isinstance(entry, dict):
            self._report.deferred += 1
            return (Verdict.DEFER,
                    f"条目不合法（{type(entry).__name__}），暂缓待裁决")
        if self._store.read_failures:
            self._report.deferred += 1
            sections = ", ".join(sorted(self._store.read_failures))
            return (Verdict.DEFER,
                    f"协调状态不可信（{sections}），暂缓代码级修改")
        constant_name = self._ledger.extract_constant_name(entry)
        if not constant_name:
            self._report.allowed += 1
            return Verdict.ALLOW, "无法识别目标参数，默认允许"
        param_state = self._ledger.get_or_create(constant_name)
        frozen = self._check_frozen(constant_name, param_state, entry)
        if frozen is not None:
            return frozen
        ctx = self._arbitration_input(entry, constant_name)
        self._ledger.update_runtime_streak(
            ctx.runtime_direction, param_state,
            snapshot_id=self._runtime_snapshot_id)
        oscillated = self._check_oscillation(ctx, param_state)
        if oscillated is not None:
            return oscillated
        return self._resolve_consistency(ctx, param_state)
    def _arbitration_input(self, entry: dict,
                           constant_name: str) -> _ArbitrationInput:
        return _ArbitrationInput(
            param=constant_name,
            runtime_direction=self._get_runtime_direction(constant_name),
            code_level_direction=infer_code_level_direction(
                entry, constant_name, self._threshold_targets),
            entry=entry,
        )
    def _finalize_frozen(self, param: str, direction: int, entry: dict,
                         reason: str) -> tuple[Verdict, str]:
        self._report.frozen += 1
        self._ledger.record(
            param, direction, Verdict.FROZEN.value,
            entry=entry, record_direction=False)
        self._store.persist(self._state)
        return Verdict.FROZEN, reason
    def _check_frozen(self, constant_name: str, param_state: dict,
                      entry: dict) -> tuple[Verdict, str] | None:
        remaining = frozen_remaining(param_state)
        if remaining <= 0:
            return None
        return self._finalize_frozen(
            constant_name, 0, entry,
            (f"参数 {constant_name} 被冻结（剩余 {remaining} 轮），"
             f"原因：振荡检测"))
    def _check_oscillation(self, ctx: _ArbitrationInput,
                           param_state: dict) -> tuple[Verdict, str] | None:
        direction_history = param_state.get("direction_history", [])
        if ctx.code_level_direction:
            direction_history = [
                *direction_history, ctx.code_level_direction]
        if not self._ledger.detect_oscillation(direction_history):
            return None
        param_state["oscillation_count"] = param_state.get(
            "oscillation_count", 0) + 1
        adaptive_freeze = self._ledger.adaptive_freeze_rounds(param_state)
        param_state[FIELD_FROZEN_ROUNDS_REMAINING] = adaptive_freeze
        param_state["total_frozen"] = param_state.get("total_frozen", 0) + 1
        param_state["direction_history"] = []
        return self._finalize_frozen(
            ctx.param, ctx.code_level_direction, ctx.entry,
            (f"参数 {ctx.param} 触发振荡检测"
             f"（{OSCILLATION_WINDOW} 次窗口内"
             f"{OSCILLATION_REVERSAL_LIMIT} 次反转），"
             f"冻结 {adaptive_freeze} 轮"
             f"（第{param_state['oscillation_count']}次振荡）"))
    def _resolve_consistency(self, ctx: _ArbitrationInput,
                             param_state: dict) -> tuple[Verdict, str]:
        runtime_streak = param_state.get("runtime_direction_streak", 0)
        adaptive_threshold = self._ledger.adaptive_threshold(param_state)
        if ctx.runtime_direction == 0:
            return self._defer(
                ctx, (f"运行时调整无方向信号（连续 {runtime_streak}/"
                      f"{adaptive_threshold}），暂缓代码级修改"))
        if ctx.code_level_direction == 0:
            return self._defer(ctx, "代码级调整无方向信号，暂缓代码级修改")
        if ctx.runtime_direction != ctx.code_level_direction:
            return self._conflict(ctx, param_state)
        if runtime_streak < adaptive_threshold:
            return self._defer(
                ctx, (f"方向一致但连续次数不足"
                      f"（{runtime_streak}/{adaptive_threshold}），暂缓"))
        self._report.allowed += 1
        self._ledger.record(
            ctx.param, ctx.code_level_direction, Verdict.ALLOW.value,
            entry=ctx.entry)
        return (Verdict.ALLOW,
                f"方向一致且稳定（连续 {runtime_streak} 次），允许执行")
    def _conflict_record(self, ctx: _ArbitrationInput) -> dict:
        return asdict(ConflictRecord(
            timestamp=time.strftime(FMT_DATETIME),
            parameter=ctx.param,
            runtime_direction=ctx.runtime_direction,
            code_level_direction=ctx.code_level_direction,
            runtime_value=self._get_runtime_value(ctx.param),
            code_level_value=suggested_scalar(ctx.entry),
            message=(f"运行时信号方向({ctx.runtime_direction})"
                     f"与代码级建议方向({ctx.code_level_direction})矛盾"),
        ))
    def _conflict(self, ctx: _ArbitrationInput,
                  param_state: dict) -> tuple[Verdict, str]:
        self._state["conflicts"].append(self._conflict_record(ctx))
        self._state["conflicts"] = (
            self._state["conflicts"][-_CONFLICT_RECORD_LIMIT:])
        param_state["total_conflicts"] = param_state.get(
            "total_conflicts", 0) + 1
        self._report.conflicts += 1
        self._report.new_conflicts.append({
            "parameter": ctx.param,
            "runtime_direction": ctx.runtime_direction,
            "code_level_direction": ctx.code_level_direction,
        })
        self._ledger.record(
            ctx.param, ctx.code_level_direction, Verdict.CONFLICT.value,
            entry=ctx.entry)
        self._store.persist(self._state)
        return (Verdict.CONFLICT,
                (f"方向矛盾：运行时={ctx.runtime_direction},"
                 f"代码级={ctx.code_level_direction}，挂起修改"))
    def _defer(self, ctx: _ArbitrationInput,
               reason: str) -> tuple[Verdict, str]:
        self._report.deferred += 1
        self._ledger.record(
            ctx.param, ctx.code_level_direction, Verdict.DEFER.value,
            entry=ctx.entry)
        return Verdict.DEFER, reason
    def save_state(self) -> None:
        self._state["session_count"] = self._state.get(
            "session_count", 0) + 1
        self._report.parameter_states = dict(self._state["parameters"].items())
        if self._store.persist(self._state):
            logger.info("[Coordinator] 状态已保存: %s (session #%d)",
                        self._store.state_path,
                        self._state["session_count"])
    def get_report(self) -> CoordinatorReport:
        return self._report
    def get_adjustment_history(self, parameter: str | None = None) -> list[dict]:
        return self._ledger.history(parameter)
    def record_modification(self, filepath: str, pre_hash: str,
                            post_hash: str, meta: VersionMeta) -> Any:
        node = self.version_chain.add_version(
            filepath=filepath, pre_hash=pre_hash, post_hash=post_hash,
            meta=meta,
        )
        logger.debug("[Coordinator] 版本记录: %s level=%s file=%s",
                     node.node_id, meta.get("level", ""),
                     os.path.basename(filepath))
        return node
    def get_status(self) -> dict:
        params = self._state.get("parameters", {})
        frozen_params = [
            name for name, state in params.items()
            if isinstance(state, dict) and frozen_remaining(state) > 0
        ]
        return {
            "session_count": self._state.get("session_count", 0),
            "total_parameters_tracked": len(params),
            "frozen_parameters": frozen_params,
            "total_conflicts": len(self._state.get("conflicts", [])),
            "runtime_adjustments_loaded": self._runtime_section_sizes(),
            "version_chain": self.version_chain.get_stats(),
        }
def _entry_sort_key(entry: dict) -> tuple[int, float]:
    level = entry.get("level")
    if not isinstance(level, str) or not level:
        level = "L1"
    return (_LEVEL_PRIORITY.get(level, 1), -entry_confidence(entry))
def coordinate_feedback(skill_dir: str,
                        threshold_targets: dict | None = None
                        ) -> CoordinatorReport:
    coordinator = FeedbackCoordinator(skill_dir, threshold_targets)
    pending = load_pending_entries(skill_dir)
    pending.sort(key=_entry_sort_key)
    for entry in pending:
        verdict, reason = coordinator.evaluate(entry)
        logger.debug("[Coordinator] [%s] %s → %s: %s",
                      entry.get("level", "?"),
                      entry.get("target", "unknown"),
                      verdict.value, reason)
    coordinator.save_state()
    return coordinator.get_report()
def get_coordinator_status(skill_dir: str) -> dict:
    coordinator = FeedbackCoordinator(skill_dir)
    return coordinator.get_status()
def load_pending_entries(skill_dir: str) -> list[dict]:
    data, _readable = read_enhancement_log(skill_dir, label="CodeFeedback")
    if data is None:
        return []
    return [entry for entry in enhancement_dict_items(data)
            if entry.get("status") == "pending"]
def entry_confidence(entry: dict,
                     default: float = DEFAULT_CONFIDENCE_FALLBACK) -> float:
    if not isinstance(entry, dict):
        return default
    raw = entry.get("confidence")
    if isinstance(raw, bool) or not isinstance(raw, (int, float)):
        return default
    return safe_confidence(raw, default)
MAX_FEEDBACK_BATCHES = 50
_LATEST_HISTORY_BY_SKILL: dict[str, dict] = {}
# 良性跳过标记：幂等重放/重复注入/重复追加/无需撤销等「本就不需要改」的销项结论
_BENIGN_SKIP_MARKERS: tuple[str, ...] = (
    "幂等", "already applied", "already fixed", "already exists",
    "idempotent", "no change", "unchanged",
    "跳过重复", "相似逻辑已存在于", "无需撤销",
    # L3 dict_merge 待合键全部已存在：与「重复追加/重复注入」同为无需改动，
    # 真实失败「幂等守卫失效」由 _BENIGN_SKIP_BLOCKERS 先行拦截
    "全部已存在",
)
# 含「幂等」却属真实失败的短语：幂等守卫被击穿不得归为良性跳过
_BENIGN_SKIP_BLOCKERS: tuple[str, ...] = ("守卫失效",)
_OUTCOME_BUCKETS: tuple[str, ...] = ("applied", "failed", "skipped")
_STATS_COUNTER_KEYS: tuple[str, ...] = (
    "total_l1", "total_l2", "total_l3", "total_l4",
    "total_applied", "total_failed", "total_skipped",
)
_FEEDBACK_LEVELS: tuple[str, ...] = ("L1", "L2", "L3", "L4")
_LEVEL_PRIORITY: dict[str, int] = {
    level: index for index, level in enumerate(_FEEDBACK_LEVELS)}
_APPLIED_FIELD_BY_LEVEL: dict[str, str] = {
    lvl: f"{lvl.lower()}_applied" for lvl in _FEEDBACK_LEVELS}
_BATCH_COUNTER_FIELDS: tuple[str, ...] = (
    *_APPLIED_FIELD_BY_LEVEL.values(), "skipped", "failed")
_STAT_KEY_BY_COUNTER: dict[str, str] = {
    **{field: f"total_{lvl.lower()}"
       for lvl, field in _APPLIED_FIELD_BY_LEVEL.items()},
    "applied": "total_applied",
    "failed": "total_failed",
    "skipped": "total_skipped",
}
def open_feedback_rollback(skill_dir: str):
    try:
        return FeedbackRollbackManager(skill_dir)
    except Exception as e:  # noqa: BLE001
        logger.warning("[FixSafety] FeedbackRollbackManager init failed: %s", e)
        return None
def _read_feedback_log(skill_dir: str, label: str) -> dict | None:
    try:
        data = read_evolution_section(skill_dir, "code_feedback_log")
    except (OSError, ValueError, TypeError) as error:
        logger.warning("%s: 历史 section 不可读: %s", label, error)
        return None
    if data is None:
        return None
    if not isinstance(data, dict):
        logger.warning("%s: 历史顶层非对象(%s)，已重置", label,
                       type(data).__name__)
        return None
    return data
def _zero_stats() -> dict[str, int]:
    return dict.fromkeys(_STATS_COUNTER_KEYS, 0)
def _empty_history() -> dict:
    return {"batches": [], "stats": _zero_stats()}
def _normalize_stats_values(stats: dict) -> dict:
    for key in _STATS_COUNTER_KEYS:
        val = stats.get(key)
        if not isinstance(val, int) or isinstance(val, bool) or val < 0:
            stats[key] = 0
    return stats
def _normalized_history(data: object, source: str) -> dict:
    if not isinstance(data, dict):
        logger.warning("%s: 历史顶层非 dict(%s)，重置为空结构",
                       source, type(data).__name__)
        return _empty_history()
    if not isinstance(data.get("batches"), list):
        logger.warning("%s: batches 非法类型(%s)，已重置为空列表",
                       source, type(data.get("batches")).__name__)
        data["batches"] = []
    else:
        batches = data["batches"]
        valid_batches = [b for b in batches if isinstance(b, dict)]
        if len(valid_batches) != len(batches):
            logger.warning("%s: batches 含 %d 条非对象元素，已剔除",
                           source, len(batches) - len(valid_batches))
            data["batches"] = valid_batches
    if not isinstance(data.get("stats"), dict):
        logger.warning("%s: stats 非法类型(%s)，已重置为默认统计",
                       source, type(data.get("stats")).__name__)
        data["stats"] = _zero_stats()
    _normalize_stats_values(data["stats"])
    observed = _observed_history_stats(data["batches"])
    for key in _STATS_COUNTER_KEYS:
        data["stats"][key] = max(data["stats"][key], observed[key])
    return data
def classify_modification_outcome(mod) -> str:
    if getattr(mod, "applied", False):
        return "applied"
    msg = getattr(mod, "error_message", "")
    msg = msg if isinstance(msg, str) else ""
    msg_folded = msg.casefold()
    if (msg.startswith(GATE_FAILURE_PREFIXES)
            or any(blocker in msg for blocker in _BENIGN_SKIP_BLOCKERS)):
        return "failed"
    if not msg_folded or any(
            marker.casefold() in msg_folded
            for marker in _BENIGN_SKIP_MARKERS):
        return "skipped"
    return "failed"
def _outcome_counters(result: str, level: str) -> dict[str, int]:
    if result not in _OUTCOME_BUCKETS:
        logger.warning("[FixSafety] 未识别销项结论 %r，按 failed 归档", result)
        result = "failed"
    if level not in _FEEDBACK_LEVELS:
        logger.warning("[FixSafety] 未识别修改层级 %r，层级计数按零归档", level)
    applied = 1 if result == "applied" else 0
    counters = {field: applied if level == lvl else 0
                for lvl, field in _APPLIED_FIELD_BY_LEVEL.items()}
    counters["applied"] = applied
    counters["failed"] = 1 if result == "failed" else 0
    counters["skipped"] = 1 if result == "skipped" else 0
    return counters
def _safe_confidence(mod) -> float:
    raw = getattr(mod, "confidence", 0.0)
    if isinstance(raw, bool) or not isinstance(raw, (int, float)):
        return 0.0
    return safe_confidence(raw, 0.0)
def _compose_modification_summary(mod) -> str:
    status = "已应用" if mod.applied else "未应用"
    reason = f"（{mod.error_message}）" if mod.error_message else ""
    return (f"[{mod.level}] {mod.action_type} @ {mod.target_name} "
            f"({mod.target_file or '运行时配置'}): {status}{reason} "
            f"置信度={_safe_confidence(mod):.2f}")
def load_feedback_history(skill_dir: str) -> dict:
    data = _read_feedback_log(skill_dir, "[FixSafety] 修改历史")
    if data is None:
        return _empty_history()
    return _normalized_history(data, "[FixSafety] 修改历史")
def _batch_identity(entry: Any) -> tuple[str, str, str] | None:
    if not isinstance(entry, dict):
        return None
    identity = (str(entry.get("batch_id") or ""),
                str(entry.get("timestamp") or ""),
                str(entry.get("summary") or ""))
    return identity if any(part.strip() for part in identity) else None
def _batch_count(batch: dict, key: str) -> int:
    value = batch.get(key, 0)
    return value if _is_plain_int(value) and value > 0 else 0
def _observed_history_stats(batches: list) -> dict[str, int]:
    observed = _zero_stats()
    for batch in batches:
        if not isinstance(batch, dict):
            continue
        level_applied = 0
        for level in _FEEDBACK_LEVELS:
            count = _batch_count(batch, _APPLIED_FIELD_BY_LEVEL[level])
            observed[f"total_{level.lower()}"] += count
            level_applied += count
        failed = _batch_count(batch, "failed")
        skipped = _batch_count(batch, "skipped")
        processed = _batch_count(batch, "total_processed")
        observed["total_failed"] += failed
        observed["total_skipped"] += skipped
        observed["total_applied"] += max(
            level_applied, processed - failed - skipped)
    return observed
def _merge_feedback_histories(base: dict, incoming: dict) -> dict:
    base = _normalized_history(base, "[FixSafety] 修改历史")
    incoming = _normalized_history(incoming, "[FixSafety] 修改历史")
    seen = {ident for ident in map(_batch_identity, base["batches"])
            if ident is not None}
    unidentified = [
        batch for batch in base["batches"]
        if _batch_identity(batch) is None]
    for batch in incoming["batches"]:
        ident = _batch_identity(batch)
        if ident is not None:
            if ident in seen:
                continue
            seen.add(ident)
        elif batch in unidentified:
            continue
        base["batches"].append(batch)
        if ident is None:
            unidentified.append(batch)
    observed = _observed_history_stats(base["batches"])
    prune_feedback_history(base)
    for key in _STATS_COUNTER_KEYS:
        base["stats"][key] = max(base["stats"].get(key, 0),
                                 incoming["stats"].get(key, 0),
                                 observed[key])
    return base
def prune_feedback_history(history: dict) -> None:
    if not isinstance(history, dict):
        logger.warning("[FixSafety] 修改历史容器非法(%s)，跳过裁剪",
                       type(history).__name__)
        return
    batches = history.get("batches")
    if not isinstance(batches, list):
        logger.warning("[FixSafety] 修改历史 batches 非法类型(%s)，重置为空列表",
                       type(batches).__name__)
        history["batches"] = []
        return
    if len(batches) > MAX_FEEDBACK_BATCHES:
        history["batches"] = (batches[-MAX_FEEDBACK_BATCHES:]
                              if MAX_FEEDBACK_BATCHES > 0 else [])
def register_feedback_history(skill_dir: str, history: dict) -> dict:
    if not isinstance(history, dict):
        logger.warning("[FixSafety] 历史注册拒绝非 dict(%s)",
                       type(history).__name__)
        return _empty_history()
    try:
        key = path_identity(skill_dir)
    except (OSError, ValueError) as _e:
        log_swallowed(
            __name__, _e,
            context=f'register_feedback_history:{type(_e).__name__}')
        return history
    existing = _LATEST_HISTORY_BY_SKILL.get(key)
    if isinstance(existing, dict) and existing is not history:
        history = _merge_feedback_histories(existing, history)
    _LATEST_HISTORY_BY_SKILL[key] = history
    return history
def record_feedback_batch(history: dict, mod,
                          outcome: str | None = None) -> None:
    try:
        if not isinstance(history, dict):
            logger.warning("[FixSafety] 修改历史容器非法(%s)，跳过记录: %s",
                           type(history).__name__,
                           getattr(mod, "modification_id", ""))
            return
        history = _normalized_history(history, "[FixSafety] 修改历史")
        result = outcome if outcome is not None else classify_modification_outcome(mod)
        counters = _outcome_counters(result, mod.level)
        entry = FeedbackBatchResult(
            batch_id=mod.modification_id or "MOD-UNKNOWN",
            timestamp=mod.timestamp or time.strftime(FMT_DATETIME),
            total_pending=1,
            total_processed=1,
            **{field: counters[field] for field in _BATCH_COUNTER_FIELDS},
            modifications=[mod],
            summary=_compose_modification_summary(mod),
        ).to_dict()
        history["batches"].append(entry)
        stats = history["stats"]
        for counter_key, stat_key in _STAT_KEY_BY_COUNTER.items():
            stats[stat_key] = stats.get(stat_key, 0) + counters[counter_key]
        prune_feedback_history(history)
        logger.info("[FixSafety] 修改销项: %s %s -> %s",
                    mod.level, mod.modification_id, result)
    except Exception as e:  # noqa: BLE001
        logger.warning("[FixSafety] 修改历史记录失败: %s", e)
@dataclass
class ApprovalGate:
    skill_dir: str
    rollback_mgr: Any
    coordinator: Any
    history: dict
    update_status: Callable[[dict, str], None]
    def run(self, entry: dict, route: dict, target_file: str,
            dispatch: Callable[[dict, dict, str], Any]) -> FeedbackModification:
        level = str_field(route, "level")
        if level != "L4" and target_file and not self.rollback_mgr:
            mod = _failed_mod(
                "MOD-GATE-SKIP", level, str_field(entry, "target"),
                str_field(entry, "action_type"), entry,
                "回滚管理器不可用，拒绝执行缺少写后校验与回滚能力的代码修改")
            self._settle(entry, mod, "failed")
            return mod
        snapshot = take_pre_snapshot(
            self.skill_dir, self.rollback_mgr, entry, target_file, level)
        if level != "L4" and target_file and snapshot is None:
            mod = _failed_mod(
                "MOD-SNAPSHOT-SKIP", level, str_field(entry, "target"),
                str_field(entry, "action_type"), entry,
                "无法创建修改前快照，拒绝执行缺少基线校验与回滚能力的代码修改")
            self._settle(entry, mod, "failed")
            return mod
        mod = dispatch(entry, route, level)
        if mod is None:
            mod = build_failed_modification(
                "MOD-NONE", level, str_field(entry, "target"),
                str_field(entry, "action_type"),
                "处理链未产出修改结果（内部跳过）", 0)
        if mod.applied:
            verify_applied_modification(
                self.skill_dir, self.rollback_mgr, mod, target_file,
                level, snapshot)
            if mod.applied:
                apply_regression_gate(
                    self.skill_dir, self.rollback_mgr, mod)
            self._settle_gated(entry, mod)
        else:
            self._settle(entry, mod, classify_modification_outcome(mod))
        return mod
    def _settle_gated(self, entry: dict, mod: FeedbackModification) -> None:
        if regression_undecided(mod):
            record_feedback_batch(self.history, mod, outcome="applied")
            _persist_feedback_history(self.skill_dir, self.history)
            logger.warning(
                "[Router] 定向回归未定论，保留待审条目交 AI 裁决: %s %s",
                mod.level, mod.modification_id)
            return
        outcome = "applied" if mod.applied else "failed"
        self._settle(entry, mod, outcome)
        if mod.applied and self.coordinator and mod.target_file:
            record_version_chain(self.skill_dir, self.coordinator, mod)
    def _settle(self, entry: dict, mod: FeedbackModification,
                outcome: str) -> None:
        self.update_status(entry, outcome)
        record_feedback_batch(self.history, mod, outcome=outcome)
        _persist_feedback_history(self.skill_dir, self.history)
def _history_base_for_merge(current: Any) -> dict:
    if current is None:
        return _empty_history()
    if not isinstance(current, dict):
        raise TypeError(
            f"历史 section 顶层非对象({type(current).__name__})，拒绝覆盖")
    batches = current.get("batches", [])
    if (not isinstance(batches, list)
            or any(not isinstance(batch, dict) for batch in batches)):
        raise TypeError("历史 batches 结构损坏，拒绝覆盖原始证据")
    stats = current.get("stats", {})
    if not isinstance(stats, dict):
        raise TypeError("历史 stats 结构损坏，拒绝覆盖原始证据")
    for key in _STATS_COUNTER_KEYS:
        if key in stats and not _is_plain_int(stats[key]):
            raise TypeError(f"历史统计 {key} 类型损坏，拒绝覆盖原始证据")
        if key in stats and stats[key] < 0:
            raise ValueError(f"历史统计 {key} 为负数，拒绝覆盖原始证据")
    return current
def _persist_feedback_history(skill_dir: str, history: dict) -> bool:
    if not isinstance(history, dict):
        logger.warning("[FixSafety] 修改历史非 dict(%s)，跳过落盘",
                       type(history).__name__)
        return False
    def merge_current(current):
        return _merge_feedback_histories(
            _history_base_for_merge(current), history)
    try:
        persisted, merged = update_evolution_section(
            skill_dir, "code_feedback_log", merge_current)
    except (OSError, RuntimeError, ValueError, TypeError, RecursionError) as e:
        logger.warning("[FixSafety] 修改历史合并落盘失败: %s", e)
        return False
    if not persisted:
        logger.warning("[FixSafety] 修改历史落盘失败: %s", skill_dir)
        return False
    if isinstance(merged, dict) and merged is not history:
        history.clear()
        history.update(merged)
    return True
def get_code_feedback_history(skill_dir: str) -> dict:
    skill_dir = normalize_skill_dir(skill_dir)
    key = None
    try:
        key = path_identity(skill_dir)
        _reg = _LATEST_HISTORY_BY_SKILL.get(key)
    except (OSError, ValueError) as _e:
        log_swallowed(
            __name__, _e,
            context=f'get_code_feedback_history:{type(_e).__name__}')
        _reg = None
    history = _read_legacy_feedback_log(skill_dir)
    if isinstance(_reg, dict):
        history = _merge_feedback_histories(history, _reg)
    history = _normalized_history(history, "get_code_feedback_history")
    if key is not None:
        _LATEST_HISTORY_BY_SKILL[key] = history
    history = copy.deepcopy(history)
    history["rollback_audit"] = get_rollback_audit(skill_dir)
    return history
def _read_legacy_feedback_log(skill_dir: str) -> dict:
    data = _read_feedback_log(skill_dir, "get_code_feedback_history")
    return data if data is not None else _empty_history()
_REVIEW_CARRYOVER_KEYS: tuple[tuple[str, int], ...] = (
    ("ai_review_verdict", 0),
    ("ai_review_rationale", 800),
    ("ai_review_assessment", 0),
)
TARGET_TO_LEVEL_MAP: dict[str, tuple[str, str]] = {
    "SINGLE_SOURCE_CONFIRM_THRESHOLD": ("L1", "SINGLE_SOURCE_CONFIRM_THRESHOLD"),
    "COVERAGE_LOW_THRESHOLD": ("L1", "COVERAGE_LOW_THRESHOLD"),
    "contradiction_resolution": ("L3", "CONFLICTING_PAIRS"),
    "CONTRADICTION_SEVERITY_DECISION": ("L3", "CONTRADICTION_SEVERITY_DECISION"),
    "evidence_weights": ("L3", "_INITIAL_EVIDENCE_WEIGHTS"),
    "fp_tracker": ("L3", "RULE_FP_TRACKER"),
    "fp_suppression/": ("L4", "_fp_suppression"),
    "source_fix/": ("L2", "source_fix"),
}
FUZZY_LEVEL_RULES: list[dict[str, Any]] = [
    {"keywords": ["阈值", "threshold", "confidence_multiplier"],
     "level": "L1", "target_key": None,
     "description": "阈值调整类建议 → L1"},
    {"keywords": ["CV 规则", "CV规则", "xv_rules", "xv_core",
                  "xv_threshold_learning", "xv_conclusion_engine",
                  "交叉验证规则", "cv_rule", "confirmation_threshold",
                  "contradiction", "evidence_weight", "fp_rate"],
     "level": "L3", "target_key": None,
     "description": "交叉验证规则相关建议 → L3"},
    {"keywords": ["逻辑增强", "logic_enhance", "路径规范化", "描述",
                  "回滚率", "行号", "副作用", "new_check"],
     "level": "L2", "target_key": None,
     "description": "逻辑增强/新检查相关建议 → L2"},
    {"keywords": ["fp_suppression", "fp_pattern", "detector_improvement",
                  "抑制规则", "误报模式", "improvement_suggestion"],
     "level": "L4", "target_key": "_fp_suppression",
     "description": "FP抑制规则类建议 → L4"},
]
_ACTION_TYPE_ROUTES: dict[str, tuple[str, str | None]] = {
    FIELD_THRESHOLD_ADJUST: ("L1", None),
    "logic_enhance": ("L2", None),
    "rule_modify": ("L3", None),
    "fp_suppression": ("L4", "_fp_suppression"),
}
_ROUTABLE_ACTION_TYPES = frozenset(
    ("source_fix", "logic_enhance", *_ACTION_TYPE_ROUTES))
_INFER_ACTION_TYPES = frozenset({"", "improvement_suggestion"})
def _failed_mod(modification_id: str, level: str, target_name: str,
                action_type: str, entry: dict, error_message: str,
                confidence: float | None = None) -> FeedbackModification:
    if confidence is None:
        confidence = entry_confidence(entry)
    else:
        confidence = safe_confidence(confidence, 0.0)
    return build_failed_modification(
        modification_id, level, target_name, action_type, error_message,
        confidence)
class CodeLevelFeedbackRouter:
    def __init__(self, skill_dir: str, coordinator: Any = None,
                 threshold_targets: dict | None = None,
                 cv_targets: dict | None = None,
                 injection_aliases: Mapping[str, str | None] | None = None,
                 ) -> None:
        self.skill_dir, _ = feedback_enhancement_log_context(skill_dir)
        self._threshold_targets = threshold_targets
        self._cv_targets = cv_targets
        self._injection_aliases = _injection_aliases_for_project(
            self.skill_dir, injection_aliases)
        self.l1 = ThresholdModifier(self.skill_dir, targets=threshold_targets)
        self.l2 = LogicInjector(self.skill_dir)
        self.l3 = CVRuleModifier(self.skill_dir, targets=cv_targets)
        self.source_fix = SourceFixApplier(self.skill_dir)
        self._rollback_mgr = open_feedback_rollback(self.skill_dir)
        self._coordinator = coordinator
        self._feedback_log_path = "code_feedback_log"
        self._modification_history = register_feedback_history(
            self.skill_dir, load_feedback_history(self.skill_dir))
    def apply_approved_fix(self, plan: dict) -> FeedbackModification:
        entry, route = _normalize_plan(plan)
        if not str_field(entry, "level"):
            route_level = str_field(route, "level")
            if route_level:
                entry = {**entry, "level": route_level}
        target_file = resolve_target_file(
            entry, route, threshold_targets=self._threshold_targets,
            cv_targets=self._cv_targets,
            injection_aliases=self._injection_aliases)
        gate = ApprovalGate(
            self.skill_dir, self._rollback_mgr, self._coordinator,
            self._modification_history, self.update_entry_status)
        return gate.run(entry, route, target_file, self._dispatch_process)
    def _process_l3(self, entry: dict, route: dict) -> FeedbackModification | None:
        target_key = l3_target_key(entry, route, self.l3.targets)
        if not target_key:
            return _failed_mod(
                "MOD-L3-SKIP", "L3", str_field(entry, "target"),
                "rule_modify", entry,
                f"无法推断CV规则目标: {str_field(entry, 'target')}")
        modification, skip_reason = build_l3_modification(
            entry, target_key, self.l3.targets)
        if skip_reason:
            return _failed_mod(
                "MOD-L3-SKIP", "L3", target_key, "rule_modify", entry,
                skip_reason)
        return self.l3.modify(
            target_name=target_key,
            modification=modification,
            source_enhancement_id=str_field(entry, "target"),
            confidence=entry_confidence(entry),
        )
    def _dispatch_process(self, entry: dict, route: dict,
                          level: str) -> FeedbackModification | None:
        try:
            if level == "L1":
                return self._process_l1(entry, route)
            if level == "L2":
                return self._process_l2(entry, route)
            if level == "L3":
                return self._process_l3(entry, route)
            if level == "L4":
                return FpSuppressionWriter(self.skill_dir).process(entry)
            return _failed_mod(
                "MOD-SKIP", level, str_field(entry, "target"),
                str_field(entry, "action_type"), entry,
                f"未识别级别: {level}", 0)
        except Exception as e:
            logger.exception("[Router] 审批执行失败 %s",
                             entry.get("target", "unknown"))
            return _failed_mod(
                "MOD-ERR", level, str_field(entry, "target"),
                str_field(entry, "action_type"), entry,
                f"执行异常: {e}", 0)
    def update_entry_status(self, entry: dict, new_status: str,
                             from_status: str = "pending") -> None:
        with locked_artifact(evolution_state_path(self.skill_dir)) as locked:
            if not locked:
                logger.warning(
                    "[Router] enhancement_log 锁不可用，拒绝无锁销项: %s",
                    self.skill_dir)
                return
            raw = read_evolution_section(
                self.skill_dir, "enhancement_log", None)
            if raw is None:
                return
            entries = enhancement_dict_items(raw)
            marked = _mark_matching_entries(
                entries, entry, new_status, from_status)
            if not marked:
                return
            try:
                if not write_evolution_section(
                        self.skill_dir, "enhancement_log", raw):
                    logger.warning("[Router] 更新状态失败: %s", self.skill_dir)
                    return
            except (OSError, ValueError, TypeError) as e:
                logger.warning("[Router] 更新状态失败: %s", e)
                return
            logger.info("[Router] 销项 %d 条 enhancement_log 条目 -> %s",
                        marked, new_status)
    def _process_l1(self, entry: dict, route: dict) -> FeedbackModification | None:
        target_key = _l1_target_key(
            entry, route, threshold_targets=self._threshold_targets)
        if not target_key:
            return _failed_mod(
                "MOD-L1-SKIP", "L1", str_field(entry, "target"),
                FIELD_THRESHOLD_ADJUST, entry, "无法推断阈值目标")
        suggested = _suggested_text(entry, target_key)
        new_value = parse_threshold_value(
            suggested, target_key, self._threshold_targets)
        if new_value is None:
            return _failed_mod(
                "MOD-L1-SKIP", "L1", target_key, FIELD_THRESHOLD_ADJUST,
                entry, f"无法解析阈值新值: {suggested}")
        return self.l1.modify(
            constant_name=target_key,
            new_value=new_value,
            source_enhancement_id=str_field(entry, "target"),
            confidence=entry_confidence(entry),
        )
    def _process_l2(self, entry: dict, route: dict) -> FeedbackModification | None:
        if entry.get("action_type") == "source_fix":
            return self._process_source_fix(entry, route)
        plan = plan_l2_injection(entry, self._injection_aliases)
        target = str_field(entry, "target")
        if plan.skip_reason:
            return _failed_mod(
                "MOD-L2-SKIP", "L2", target, "logic_inject", entry,
                plan.skip_reason)
        return self.l2.inject(
            target_file=plan.target_file,
            target_function=plan.target_function,
            template_name=plan.template_name,
            source_enhancement_id=target,
            confidence=entry_confidence(entry),
        )
    def _process_source_fix(self, entry: dict, route: dict) -> FeedbackModification | None:
        fixed_source = entry.get("fixed_source")
        if isinstance(fixed_source, str) and fixed_source.strip():
            return self._apply_fixed_source(entry, route, fixed_source)
        sv, sv_parsed = parse_json_dict(entry.get(FIELD_SUGGESTED_VALUE))
        if not sv_parsed:
            return _failed_mod(
                "MOD-L2-SRC-SKIP", "L2", str_field(entry, "target"),
                "source_fix", entry, "suggested_value 无法解析")
        target_file = source_fix_target_file(entry, route)
        fix_specs = sv.get("fix_specs") or []
        if not target_file or not fix_specs:
            return _failed_mod(
                "MOD-L2-SRC-SKIP", "L2", str_field(entry, "target"),
                "source_fix", entry, "缺少 target_file/fix_specs")
        return self.source_fix.apply(
            target_file=target_file,
            fix_specs=fix_specs,
            source_enhancement_id=str_field(entry, "target"),
            confidence=entry_confidence(entry),
        )
    def _apply_fixed_source(self, entry: dict, route: dict,
                            fixed_source: str) -> FeedbackModification:
        target_file = source_fix_target_file(entry, route)
        if not target_file:
            return _failed_mod(
                "MOD-L2-SRC-SKIP", "L2", str_field(entry, "target"),
                "source_fix", entry,
                "fixed_source 缺少 target_file，无法应用")
        return self.source_fix.apply_full_source(
            target_file=target_file,
            fixed_source=fixed_source,
            source_enhancement_id=str_field(entry, "target"),
            confidence=entry_confidence(entry),
        )
def _carry_review_fields(target_entry: dict, source_entry: dict) -> None:
    for key, limit in _REVIEW_CARRYOVER_KEYS:
        value = source_entry.get(key)
        if isinstance(value, str) and value:
            target_entry[key] = value[:limit] if limit else value
        elif isinstance(value, dict) and value:
            target_entry[key] = value
_L3_KEYWORD_ROUTES: tuple[tuple[tuple[str, ...], tuple[str, ...], str], ...] = (
    (("evidence_weight",), ("权重",), "_INITIAL_EVIDENCE_WEIGHTS"),
    (("severity_decision", "严重度决策"),
     ("severity_decision", "严重度决策"), "CONTRADICTION_SEVERITY_DECISION"),
    (("contradiction",), ("矛盾",), "CONFLICTING_PAIRS"),
    (("fp_tracker",), ("fp_rate",), "RULE_FP_TRACKER"),
)
def _l3_keyword_target(target_l: str, description_l: str) -> str | None:
    for target_keys, desc_keys, key in _L3_KEYWORD_ROUTES:
        if any(_contains_identifier(target_l, k) for k in target_keys):
            return key
        if any(k in description_l for k in desc_keys):
            return key
    return None
def _registered_l3_target(entry: dict, registry: dict) -> str | None:
    combined = (f"{str_field(entry, 'target')} "
                f"{str_field(entry, 'description')}").lower()
    for name, config in registry.items():
        if not isinstance(name, str) or not name.strip():
            continue
        keywords = config.get("keywords", ()) if isinstance(config, dict) else ()
        candidates = (name, *(keywords
                              if isinstance(keywords, (tuple, list)) else ()))
        if any(isinstance(keyword, str) and keyword.strip()
               and _contains_identifier(combined, keyword.strip())
               for keyword in candidates):
            return name
    return None
def l3_target_key(entry: dict, route: dict,
                  cv_targets: dict | None = None) -> str | None:
    target_key = route.get("target_key")
    if target_key:
        return target_key
    registry = cv_rule_registry(cv_targets)
    if not isinstance(registry, dict):
        return None
    keyword_target = _l3_keyword_target(
        str_field(entry, "target").lower(),
        str_field(entry, "description").lower())
    if keyword_target in registry:
        return keyword_target
    return _registered_l3_target(entry, registry)
def _normalize_fp_counts(fp_raw: Any, total_raw: Any) -> tuple[Any, Any]:
    fp = max(0, cv_int(fp_raw))
    total = max(0, cv_int(total_raw))
    return fp, max(total, fp)
def _fp_payload(fp_rate: Any, fp_raw: Any = 0,
                total_raw: Any = 0) -> dict:
    fp_count, total = _normalize_fp_counts(fp_raw, total_raw)
    return {"fp_rate": fp_rate, "total": total, "fp": fp_count}
def _fp_payload_from_json(suggested: Any) -> dict | None:
    if isinstance(suggested, dict):
        fp_data = suggested
    else:
        try:
            fp_data = json.loads(suggested) if suggested else {}
        except (json.JSONDecodeError, TypeError, RecursionError) as e:
            logger.warning("解析 fp_data 失败，回退从 entry 读取: %s", e)
            return None
    if not isinstance(fp_data, dict) or "fp_rate" not in fp_data:
        return None
    fp_rate = fp_data["fp_rate"]
    if not is_valid_fp_rate(fp_rate):
        logger.warning(
            "fp_data 中 fp_rate 为脏值(%r)，不透传，回退从 entry 读取", fp_rate)
        return None
    return _fp_payload(fp_rate, fp_data.get("fp", 0), fp_data.get("total", 0))
def _parse_fp_tracker_modification(entry: dict, suggested: Any) -> dict | None:
    payload = _fp_payload_from_json(suggested)
    if payload is not None:
        return payload
    fp_rate = entry.get("fp_rate")
    if entry.get("fp_pattern") and is_valid_fp_rate(fp_rate):
        return _fp_payload(fp_rate, entry.get("fp_count"), entry.get("total"))
    if suggested is not None and (
            not isinstance(suggested, str) or suggested.strip()):
        return None
    logger.warning(
        "[Router] fp_tracker 缺少 fp_rate 证据（suggested_value 为空且无有效 "
        "fp_pattern/fp_rate），拒绝生成无证据修改: %s",
        entry.get("target", ""))
    return None
_EVIDENCE_RAISE_WORDS: tuple[str, ...] = (
    "提高", "增强", "提升", "increase", "raise", "boost", "strengthen")
_EVIDENCE_LOWER_WORDS: tuple[str, ...] = (
    "降低", "减少", "降权", "decrease", "reduce", "lower", "weaken")
_EVIDENCE_WEIGHT_FACTORS: tuple[tuple[tuple[str, ...], float], ...] = (
    (_EVIDENCE_RAISE_WORDS, 1.25),
    (_EVIDENCE_LOWER_WORDS, 0.80),
)
_EVIDENCE_WEIGHT_DEFAULT_FACTOR = 1.10
def _parse_evidence_weight_modification(
        combined: str) -> tuple[str | None, float | None]:
    lowered = combined.lower()
    families = [family for family in EVIDENCE_FAMILY_NAMES
                if family.lower() in lowered]
    if not families:
        return None, None
    if len(families) > 1:
        logger.warning(
            "[Router] 证据权重目标歧义，拒绝自动修改: families=%s", families)
        return None, None
    family = families[0]
    factors = [
        factor for words, factor in _EVIDENCE_WEIGHT_FACTORS
        if any(word in lowered for word in words)]
    if len(factors) > 1:
        logger.warning(
            "[Router] 证据权重方向冲突，拒绝自动修改: family=%s", family)
        return None, None
    factor = factors[0] if factors else _EVIDENCE_WEIGHT_DEFAULT_FACTOR
    return family, _scaled_evidence_weight(family, factor)
def _scaled_evidence_weight(family: str, factor: float) -> float | None:
    """把相对系数落成绝对权重: L3 dict_modify 写入的是值本身."""
    current = safe_float(family_reliability_base(family), None)
    if current is None or not current > 0:
        logger.warning(
            "[Router] 证据家族 %s 当前权重缺失或非正，拒绝按系数换算", family)
        return None
    scaled = round(current * factor, 2)
    if not math.isfinite(scaled) or scaled <= 0:
        logger.warning(
            "[Router] 证据家族 %s 权重换算结果非法(%r)，拒绝自动修改",
            family, scaled)
        return None
    return scaled
def parse_cv_dict_modification(entry: dict,
                               target_key: str) -> tuple[str | None, Any]:
    if not isinstance(entry, dict) or not isinstance(target_key, str):
        return None, None
    if target_key not in ("_INITIAL_EVIDENCE_WEIGHTS", "RULE_FP_TRACKER"):
        return None, None
    desc = str_field(entry, "description")
    suggested = entry.get(FIELD_SUGGESTED_VALUE)
    target = str_field(entry, "target")
    combined = f"{desc} {_suggested_text(entry)} {target}"
    if target_key == "_INITIAL_EVIDENCE_WEIGHTS":
        return _parse_evidence_weight_modification(combined)
    parts = target.split("/")
    rule_family = parts[-1].strip() if len(parts) >= 2 else ""
    if not rule_family:
        return None, None
    return rule_family, _parse_fp_tracker_modification(entry, suggested)
def build_l3_modification(entry: dict, target_key: str,
                          cv_rule_targets: dict) -> tuple[dict, str | None]:
    target_config = cv_rule_targets.get(target_key, {})
    mod_type = target_config.get("type", "dict_modify")
    if mod_type == "dict_modify":
        key, value = parse_cv_dict_modification(entry, target_key)
        if key and value is not None:
            return {"key": key, "new_value": value}, None
        return {}, f"无法解析CV修改参数: {str_field(entry, 'description')}"
    if mod_type == "list_append":
        entry_text = _suggested_text(entry)
        if not entry_text.strip():
            return {}, ("无法解析CV列表追加参数: suggested_value 必须为"
                        "非空 Python 表达式字符串")
        return {"entry": entry_text}, None
    if mod_type == "dict_merge":
        raw_value = entry.get(FIELD_SUGGESTED_VALUE)
        entries, parsed = parse_json_dict(raw_value)
        if not parsed and raw_value is not None and (
                not isinstance(raw_value, str) or raw_value.strip()):
            return {}, "无法解析CV合并参数: suggested_value 必须是 JSON 对象"
        return {"entries": entries}, None
    return {}, f"未知CV规则修改类型: {mod_type}（目标 {target_key}）"
def _l1_target_key(entry: dict, route: dict, *,
                   threshold_targets: dict | None = None) -> str | None:
    target_key = route.get("target_key")
    if not target_key:
        explicit_target = (entry.get("target")
                           if isinstance(entry, dict) else None)
        registry = threshold_registry(threshold_targets)
        if isinstance(explicit_target, str):
            registered_name = explicit_target.strip()
            if registered_name in registry:
                return registered_name
        if _looks_like_constant_target(explicit_target):
            return None
        target_key = infer_threshold_from_entry(entry, threshold_targets)
    return target_key
def _registry_target_file(registry: Any, target_key: Any) -> str:
    if not isinstance(registry, dict) or not isinstance(target_key, str):
        return ""
    target = registry.get(target_key)
    if not isinstance(target, dict):
        return ""
    target_file = target.get("file", "")
    return target_file if isinstance(target_file, str) else ""
def resolve_target_file(entry: dict, route: dict, *,
                        threshold_targets: dict | None = None,
                        cv_targets: dict | None = None,
                        injection_aliases: Mapping[str, str | None] | None = None,
                        ) -> str:
    level = route.get("level", "")
    target_file: Any = ""
    if level == "L2":
        target_file = resolve_l2_target_file(
            entry, route, injection_aliases)
    elif level in ("L1", "L3"):
        target_key = level_target_key(
            entry, route, threshold_targets=threshold_targets,
            cv_targets=cv_targets)
        if level == "L1":
            registry = threshold_registry(threshold_targets)
        else:
            registry = cv_rule_registry(cv_targets)
        target_file = _registry_target_file(registry, target_key)
    return target_file if isinstance(target_file, str) else ""
def level_target_key(entry: dict, route: dict, *,
                     threshold_targets: dict | None = None,
                     cv_targets: dict | None = None) -> str | None:
    level = route.get("level", "")
    if level == "L1":
        return _l1_target_key(
            entry, route, threshold_targets=threshold_targets)
    if level == "L3":
        return l3_target_key(entry, route, cv_targets)
    return route.get("target_key")
def _normalize_plan(plan: Any) -> tuple[dict, dict]:
    plan = plan if isinstance(plan, dict) else {}
    raw_entry = plan.get("entry")
    entry = raw_entry if isinstance(raw_entry, dict) else {}
    raw_route = plan.get("route")
    if (isinstance(raw_route, dict) and isinstance(raw_route.get("level"), str)
            and raw_route.get("level")):
        return entry, raw_route
    return entry, route_entry(entry)
def _has_entry_identity(entry: dict) -> bool:
    return any(str_field(entry, key).strip()
               for key in ("target", "description"))
def _effective_entry_level(entry: dict) -> str:
    level = entry.get("level")
    if isinstance(level, str) and level:
        return level
    route_level = route_entry(entry).get("level")
    return route_level if isinstance(route_level, str) else ""
def _mark_matching_entries(entries: list, entry: dict, new_status: str,
                           from_status: str) -> int:
    if not _has_entry_identity(entry):
        logger.warning(
            "[Router] 销项缺少身份键(target/description 双空)，"
            "拒绝按空键批量销项: status=%s", new_status)
        return 0
    target_desc = str_field(entry, "description")
    target_target = str_field(entry, "target")
    target_level = _effective_entry_level(entry)
    marked = 0
    for e in entries:
        if not isinstance(e, dict):
            continue
        if (str_field(e, "description") != target_desc
                or str_field(e, "target") != target_target
                or e.get("status") != from_status):
            continue
        if target_level and _effective_entry_level(e) != target_level:
            continue
        e["status"] = new_status
        e["modified_at"] = time.strftime(FMT_DATETIME)
        _carry_review_fields(e, entry)
        marked += 1
    return marked
def apply_approved_fix(plan: dict, skill_dir: str) -> Any:
    plan = plan if isinstance(plan, dict) else {}
    mod = CodeLevelFeedbackRouter(skill_dir).apply_approved_fix(plan)
    emit_feedback_fix_report(mod, plan, skill_dir)
    return mod
def _route_target_file(target: str, target_key: str) -> str:
    if target_key == "source_fix":
        parts = target.split("/")
        return "/".join(parts[1:]) if len(parts) >= 2 else ""
    return (_registry_target_file(THRESHOLD_TARGETS, target_key)
            or _registry_target_file(CV_RULE_TARGETS, target_key))
def _make_route(level: str, target_key: str | None, file: str,
                action_type: str) -> dict:
    return {"level": level, "target_key": target_key, "file": file,
            "action_type": action_type}
def _exact_route(text: str, target: str, action_type: str) -> dict | None:
    for pattern_key, (level, target_key) in TARGET_TO_LEVEL_MAP.items():
        if _contains_identifier(text, pattern_key):
            return _make_route(level, target_key,
                               _route_target_file(target, target_key),
                               action_type)
    return None
def _fuzzy_route(target: str, description: str, suggested_value: str,
                 action_type: str) -> dict | None:
    combined = f"{target} {description} {suggested_value}".lower()
    _best_rule: dict[str, Any] | None = None
    _best_rank: tuple[int, int] = (0, 0)
    for rule in FUZZY_LEVEL_RULES:
        _hits = [kw for kw in rule["keywords"] if kw.lower() in combined]
        if not _hits:
            continue
        _rank = (len(_hits), max(len(kw) for kw in _hits))
        if _rank > _best_rank:
            _best_rank = _rank
            _best_rule = rule
    if _best_rule is None:
        return None
    return _make_route(_best_rule["level"], _best_rule.get("target_key"),
                       "", action_type)
def _action_route(action_type: str, target: str) -> dict:
    if action_type == "source_fix":
        return _make_route("L2", "source_fix",
                           _route_target_file(target, "source_fix"),
                           action_type)
    route = _ACTION_TYPE_ROUTES.get(action_type)
    if route is None:
        return _make_route("", None, "", action_type)
    level, target_key = route
    return _make_route(level, target_key, "", action_type)
def route_entry(entry: dict) -> dict:
    target = str_field(entry, "target")
    action_type = str_field(entry, "action_type")
    description = str_field(entry, "description")
    suggested_value = str_field(entry, FIELD_SUGGESTED_VALUE)
    if (action_type not in _ROUTABLE_ACTION_TYPES
            and action_type not in _INFER_ACTION_TYPES):
        return _action_route(action_type, target)
    if action_type in ("source_fix", "logic_enhance"):
        return _action_route(action_type, target)
    action_route = (_action_route(action_type, target)
                    if action_type in _ACTION_TYPE_ROUTES else None)
    for text in (target, description):
        route = _exact_route(text, target, action_type)
        if route is None:
            continue
        if (action_route is not None
                and route["level"] != action_route["level"]):
            return action_route
        return route
    if action_route is not None:
        return action_route
    route = _fuzzy_route(target, description, suggested_value, action_type)
    if route is not None:
        return route
    return _action_route(action_type, target)
def source_fix_target_file(entry: dict, route: dict) -> str:
    sv, _sv_parsed = parse_json_dict(entry.get(FIELD_SUGGESTED_VALUE))
    explicit = sv.get("target_file")
    if isinstance(explicit, str) and explicit.strip():
        return explicit.strip()
    fallback = route.get("file", "")
    return fallback if isinstance(fallback, str) else ""
_L2_INJECTION_TARGET_ALIASES: dict[str, str | None] = {
    "xv_core": "xv_confidence_review.py",
    "xv_rules": "xv_confidence_review.py",
    "treatment": "treatment_experience.py",
    "feedback_mechanism": "treatment_feedback.py",
    "detector": None,
}
def _injection_aliases_for_project(
        skill_dir: str,
        aliases: Mapping[str, str | None] | None,
) -> Mapping[str, str | None]:
    if aliases is not None:
        return aliases
    return {
        alias: target_file
        for alias, target_file in _L2_INJECTION_TARGET_ALIASES.items()
        if target_file is None or os.path.isfile(
            os.path.join(skill_dir, target_file))
    }
def resolve_l2_target_file(
        entry: dict, route: dict,
        aliases: Mapping[str, str | None] | None = None) -> str:
    if entry.get("action_type") == "source_fix":
        return source_fix_target_file(entry, route)
    return resolve_injection_target(entry, aliases or {})[0]
def _as_patterns(value: Any, field_name: str) -> list[str]:
    if value is None:
        return []
    if (not isinstance(value, list)
            or any(not isinstance(pattern, str) for pattern in value)):
        raise TypeError(f"{field_name} 必须为字符串列表")
    if any(not pattern.strip() for pattern in value):
        raise ValueError(f"{field_name} 含空模式")
    return list(value)
def _as_severity(value: Any) -> str:
    if value is None:
        return SUPPRESSION_DEFAULT_MIN_SEVERITY
    if isinstance(value, str):
        normalized = value.upper().strip()
        if normalized in SEVERITY_RANK:
            return normalized
    raise ValueError(f"min_severity_to_suppress 严重度非法: {value!r}")
def _l4_fail(mod_id: str, target_name: str, confidence: float,
             error_message: str) -> FeedbackModification:
    if not isinstance(target_name, str):
        target_name = safe_short_text(target_name)
    return FeedbackModification(
        modification_id=mod_id,
        level="L4", target_name=target_name,
        action_type="fp_suppression",
        applied=False,
        confidence=confidence,
        error_message=error_message,
    )
@dataclass(frozen=True)
class _L4Payload:
    confidence: float
    suppression_rule: Any
    rid_raw: Any
def _skill_relative_path(skill_dir: str, path: str) -> str:
    try:
        rel = os.path.relpath(path, skill_dir)
    except ValueError as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc, context='_skill_relative_path:ValueError')
        return path
    if rel == os.pardir or rel.startswith(os.pardir + os.sep):
        return path
    return rel.replace(os.sep, "/")
def _l4_success(rid: str, final_rule: dict,
                confidence: float, target_file: str) -> FeedbackModification:
    fp_rate = float(final_rule["fp_rate"])
    fp_count = int(final_rule["fp_count"])
    logger.info("[L4] FP抑制规则写入: rule=%s, min_sev=%s, fp_rate=%.2f, fp_count=%d",
                rid, final_rule["min_severity_to_suppress"], fp_rate, fp_count)
    rid_digest = hashlib.md5(
        str(rid).encode(), usedforsecurity=False).hexdigest()[:8].upper()
    return FeedbackModification(
        modification_id=(
            f"MOD-L4-{rid_digest}-{uuid.uuid4().hex[:8].upper()}"),
        level="L4", target_name=rid,
        target_file=target_file,
        action_type="fp_suppression",
        applied=True,
        timestamp=time.strftime(FMT_DATETIME),
        confidence=confidence,
        error_message="",
        backup_path="",
        new_value=(f"FP抑制规则: {rid} (fp_rate={fp_rate:.2f}, "
                   f"min_sev={final_rule['min_severity_to_suppress']})"),
    )
def _parse_suggested_rule(entry: dict, confidence: float) -> tuple:
    suggested = entry.get(FIELD_SUGGESTED_VALUE, "")
    if not suggested:
        return _l4_fail("MOD-L4-SKIP", entry.get("target", ""),
                        confidence, "suggested_value为空"), None
    if isinstance(suggested, dict):
        return None, suggested
    try:
        parsed = json.loads(suggested)
    except (json.JSONDecodeError, TypeError, RecursionError) as e:
        log_swallowed(
            __name__, e,
            context=f'_parse_suggested_rule:{type(e).__name__}')
        return _l4_fail("MOD-L4-SKIP", entry.get("target", ""),
                        confidence, f"解析suggested_value失败: {e}"), None
    if not isinstance(parsed, dict):
        return _l4_fail("MOD-L4-SKIP", entry.get("target", ""),
                        confidence,
                        f"suggested_value 解析结果须为 JSON 对象: "
                        f"{type(parsed).__name__}"), None
    return None, parsed
def _extract_rule_list(data: Any, sp_path: str) -> list:
    if isinstance(data, list):
        rules = data
    elif isinstance(data, dict) and isinstance(data.get("rules"), list):
        rules = data["rules"]
    else:
        raise TypeError(f"抑制规则文件结构非法，须为规则列表或包含 rules 列表的对象: {sp_path}")
    for index, rule in enumerate(rules):
        if not isinstance(rule, dict):
            raise TypeError(
                f"抑制规则文件第 {index} 项类型非法，须为对象: {sp_path}")
    return rules
def _load_existing_suppression_rules(sp_path: str) -> list:
    if not os.path.isfile(sp_path):
        return []
    try:
        data, status, error = read_json_artifact(sp_path)
        if status != "ok":
            raise ValueError(error or "未知读取错误")
        return _extract_rule_list(data, sp_path)
    except Exception as e:
        raise ValueError(f"无法安全读取既有抑制规则: {e}") from e
def _build_final_rule(rid: str, suppression_rule: dict) -> dict:
    fp_rate = suppression_rule.get("fp_rate", 0.0)
    line_zero_ratio = suppression_rule.get("line_zero_ratio", 0.0)
    fp_count = suppression_rule.get("fp_count", 0)
    for field_name, value in (
            ("fp_rate", fp_rate), ("line_zero_ratio", line_zero_ratio)):
        if not is_valid_fp_rate(value):
            raise ValueError(f"{field_name} 必须为 [0,1] 有限数值")
    if not _is_plain_int(fp_count) or fp_count < 0:
        raise ValueError("fp_count 必须为非负整数")
    return {
        "rule_id": rid,
        "min_severity_to_suppress": _as_severity(
            suppression_rule.get("min_severity_to_suppress")),
        "message_patterns": _as_patterns(
            suppression_rule.get("message_patterns"), "message_patterns"),
        "file_patterns": _as_patterns(
            suppression_rule.get("file_patterns"), "file_patterns"),
        "fp_rate": float(fp_rate),
        "fp_count": fp_count,
        "line_zero_ratio": float(line_zero_ratio),
        "observation_mode": bool(suppression_rule.get("observation_mode")),
        "source": "fp_evolution_l4",
        "created_at": time.strftime(FMT_DATETIME),
    }
def _rule_id_identity(value: Any) -> str:
    if isinstance(value, str):
        return value.strip()
    if isinstance(value, float) and value.is_integer():
        return str(int(value))
    return str(value)
_REVOKE_TARGET_PREFIX = "fp_suppression/"
def _revoke_rule_id_of(entry: dict) -> str:
    """从过度抑制反馈中解析待撤销的抑制规则号。

    假阴性/过度抑制反馈的 target 形如 `fp_suppression/{rule_id}`，
    与 `TARGET_TO_LEVEL_MAP` 的前缀路由一一对应。
    """
    if str_field(entry, "feedback_type").strip() != "over_suppression":
        return ""
    target = str_field(entry, "target").strip()
    if not target.startswith(_REVOKE_TARGET_PREFIX):
        return ""
    return target[len(_REVOKE_TARGET_PREFIX):].strip()
class FpSuppressionWriter:
    def __init__(self, skill_dir: str):
        self.skill_dir = normalize_skill_dir(skill_dir)
    def process(self, entry: dict) -> FeedbackModification:
        _revoke_rid = _revoke_rule_id_of(entry)
        if _revoke_rid:
            return self._revoke_rule(_revoke_rid, entry_confidence(entry))
        fail_mod, payload = self._resolve_fp_suppression_payload(entry)
        if fail_mod is not None:
            return fail_mod
        fail_mod, rid = self._normalize_rule_id(
            payload.rid_raw, entry.get("target", ""), payload.confidence)
        if fail_mod is not None:
            return fail_mod
        fail_mod, final_rule, target_file = self._persist_rule(
            rid, payload.suppression_rule, payload.confidence)
        if fail_mod is not None:
            return fail_mod
        return _l4_success(rid, final_rule, payload.confidence, target_file)
    def _revoke_rule(self, rid: str,
                     confidence: float) -> FeedbackModification:
        if not drop_fp_suppression_rule(self.skill_dir, rid):
            return _l4_fail(
                "MOD-L4-NOOP", rid, confidence,
                "抑制规则不存在或已失效，无需撤销")
        rid_digest = hashlib.md5(
            str(rid).encode(), usedforsecurity=False).hexdigest()[:8].upper()
        return FeedbackModification(
            modification_id=(
                f"MOD-L4-RVK-{rid_digest}-{uuid.uuid4().hex[:8].upper()}"),
            level="L4", target_name=rid,
            target_file=_skill_relative_path(
                self.skill_dir, fp_suppression_path(self.skill_dir)),
            action_type="fp_suppression",
            applied=True,
            timestamp=time.strftime(FMT_DATETIME),
            confidence=confidence,
            error_message="",
            backup_path="",
            new_value=f"撤销过度抑制规则: {rid}",
        )
    def _persist_rule(self, rid: str, suppression_rule: dict,
                      confidence: float) -> tuple:
        sp_path = fp_suppression_path(self.skill_dir)
        try:
            final_rule = _build_final_rule(rid, suppression_rule)
        except (TypeError, ValueError) as e:
            logger.warning("[L4] 抑制规则字段非法，拒绝写入: %s", e)
            return (_l4_fail(
                "MOD-L4-SKIP", rid, confidence, str(e)), None, "")
        final_rule = normalize_suppression_rule(final_rule)
        if final_rule is None:
            logger.warning("[L4] 抑制规则未通过加载契约，拒绝写入: %s", rid)
            return (_l4_fail(
                "MOD-L4-SKIP", rid, confidence,
                "规则未通过加载契约（rule_id/证据/严重度）"), None, "")
        try:
            with locked_artifact(sp_path) as locked:
                if not locked:
                    raise RuntimeError("抑制规则读改写锁不可用，拒绝无锁覆盖")
                try:
                    existing_rules = [
                        r for r in _load_existing_suppression_rules(sp_path)
                        if _rule_id_identity(r.get("rule_id", "")) != rid
                    ]
                except ValueError as e:
                    logger.warning(
                        "[CodeFeedback] 既有抑制规则不可用，拒绝写入并保留原文件: %s: %s",
                        sp_path, e)
                    return (_l4_fail(
                        "MOD-L4-FAIL", rid, confidence,
                        f"读取fp_suppression.json失败，已保留原文件: {e}"), None, "")
                existing_rules.append(final_rule)
                _sp_dir = os.path.dirname(sp_path)
                if _sp_dir:
                    os.makedirs(_sp_dir, exist_ok=True)
                atomic_write_text(
                    sp_path,
                    serialize_json({"rules": existing_rules}, indent=2),
                    "L4-fp-suppression", newline="")
        except (OSError, RuntimeError, ValueError, RecursionError) as e:
            log_swallowed(
                __name__, e,
                context=f'FpSuppressionWriter._persist_rule:{type(e).__name__}')
            return (_l4_fail("MOD-L4-FAIL", rid, confidence,
                             f"写入fp_suppression.json失败: {e}"), None, "")
        return None, final_rule, _skill_relative_path(self.skill_dir, sp_path)
    @staticmethod
    def _resolve_fp_suppression_payload(entry) -> tuple:
        confidence = entry_confidence(entry)
        if not isinstance(entry, dict):
            return _l4_fail(
                "MOD-L4-SKIP", safe_short_text(entry), confidence,
                f"entry 类型错误: 期望 dict，实际 {type(entry).__name__}"), None
        fail_mod, suppression_rule = _parse_suggested_rule(entry, confidence)
        if fail_mod is not None:
            return fail_mod, None
        rid_raw = (suppression_rule.get("rule_id")
                   if isinstance(suppression_rule, dict) else None)
        if rid_raw is None or rid_raw == "":
            return _l4_fail("MOD-L4-SKIP", entry.get("target", ""),
                            confidence, "抑制规则缺少rule_id"), None
        return None, _L4Payload(confidence, suppression_rule, rid_raw)
    @staticmethod
    def _normalize_rule_id(rid_raw, entry_target: str,
                           confidence: float) -> tuple:
        rid = rid_raw
        if isinstance(rid, str):
            stripped = rid.strip()
            if not stripped:
                return _l4_fail("MOD-L4-SKIP", entry_target,
                                confidence, "rule_id 为空"), ""
            return None, stripped
        bad_shape = (isinstance(rid, bool) or not isinstance(rid, (int, float))
                     or (isinstance(rid, float) and not math.isfinite(rid)))
        if bad_shape:
            return _l4_fail("MOD-L4-SKIP", entry_target,
                            confidence, f"rule_id 形态非法: {type(rid).__name__}"), ""
        try:
            normalized = _rule_id_identity(rid)
        except (ValueError, TypeError, RecursionError) as exc:
            log_swallowed(
                __name__, exc,
                context=f'_normalize_rule_id:{type(exc).__name__}')
            return _l4_fail("MOD-L4-SKIP", entry_target, confidence,
                            f"rule_id 无法规范化: {exc}"), ""
        return None, normalized
__all__ = [
    "CONSISTENCY_THRESHOLD",
    "CONSISTENCY_THRESHOLD_MAX",
    "CONSISTENCY_THRESHOLD_MIN",
    "FREEZE_ROUNDS",
    "FREEZE_ROUNDS_MAX",
    "MAGNITUDE_HISTORY_SIZE",
    "OSCILLATION_REVERSAL_LIMIT",
    "OSCILLATION_WINDOW",
    "PARAMETER_MAPPING",
    "AdjustmentRecord",
    "ApprovalGate",
    "CodeLevelFeedbackRouter",
    "ConflictRecord",
    "CoordinatorReport",
    "CoordinatorStateFiles",
    "FeedbackCoordinator",
    "FeedbackRouteContext",
    "FpSuppressionWriter",
    "ParameterLedger",
    "ParameterState",
    "Verdict",
    "apply_approved_fix",
    "classify_modification_outcome",
    "coordinate_feedback",
    "entry_confidence",
    "frozen_remaining",
    "get_code_feedback_history",
    "get_coordinator_status",
    "infer_code_level_direction",
    "infer_runtime_direction",
    "level_target_key",
    "load_feedback_history",
    "load_pending_entries",
    "new_runtime_snapshot_id",
    "open_feedback_rollback",
    "parse_cv_dict_modification",
    "read_enhancement_log",
    "record_feedback_batch",
    "register_feedback_history",
    "resolve_target_file",
    "route_entry",
    "section_size",
    "suggested_scalar",
]
logger.info("feedback_coordinator 反馈裁决域已加载: %d 项导出", len(__all__))

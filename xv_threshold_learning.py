from __future__ import annotations

import json
import logging
import os
import threading
import time
from dataclasses import (
    dataclass,
)
from typing import Any

from jwsgj.diag_guard_state import (
    read_json_artifact,
    read_review_queue_entries,
    write_json_artifact,
)
from jwsgj.diag_types_normalize import (
    env_number,
    is_real_number,
    safe_confidence,
    safe_float,
    safe_isfinite,
    signal_bool,
)
from jwsgj.diag_types_vocab import (
    CONF_BOOST_SMALL,
    CONF_CAP,
    CONF_FLOOR,
    CONF_HIGH,
    CONF_LOW,
    FIELD_CV_CONFIDENCE_THRESHOLDS,
    FIELD_METHOD_CONFIDENCE_MULTIPLIERS,
)
from jwsgj.log_config import (
    locked_artifact,
    log_swallowed,
)
from jwsgj.memory_bridge import (
    CATEGORY_CV_TUNING,
    TP_CONFIDENCE_MULTIPLIER,
    TP_THRESHOLD_ADJUSTMENT,
    DiagnosticMemoryContext,
    collect_ctx_evidence,
    normalize_rule_id,
)
from jwsgj.runtime_paths import (
    cv_uncertain_path,
    fp_tracker_path,
    read_evolution_section,
    skill_dir_or_fallback,
    threshold_history_path,
)
from jwsgj.treatment_state import (
    canonical_locator_key,
    get_treatment_state_path,
    open_confirm_store,
    parse_locator_rule_family,
    save_treatment_state,
)

logger = logging.getLogger(__name__)
__all__ = [
    "COVERAGE_LOW_THRESHOLD",
    "PRECISE_SMOKE_FAMILIES",
    "RULE_FP_TRACKER",
    "RULE_SPECIFIC_THRESHOLDS",
    "SINGLE_SOURCE_CONFIRM_THRESHOLD",
    "CVRuleTuning",
    "apply_cv_threshold_adjustments",
    "apply_cv_tunings_to_config",
    "apply_feedback_thresholds",
    "build_fp_tracker_state",
    "calibrate_and_persist_fp_tracker",
    "calibrate_confidence",
    "calibrate_fp_tracker_from_xv_results",
    "calibrate_from_treatment_outcomes",
    "feed_channel_signals_to_fp_tracker",
    "fp_tuning_params",
    "generate_cv_tunings",
    "get_adaptive_threshold",
    "get_approved_rule_threshold",
    "get_rule_threshold",
    "get_rule_weight",
    "is_rule_retired",
    "learning_dir_request",
    "load_feedback_adjustments",
    "load_fp_tracker_persisted",
    "persist_fp_channel_stats",
    "record_threshold_outcome",
    "resolve_threshold",
    "retired_rule_ids",
    "rule_retirement_state",
    "save_fp_tracker_persisted",
    "set_approved_rule_thresholds",
    "set_threshold_learning_dir",
    "update_rule_fp_tracker",
]
COVERAGE_LOW_THRESHOLD: int = env_number(
    "JWSGJ_COVERAGE_LOW_THRESHOLD", 40, int
)
SINGLE_SOURCE_CONFIRM_THRESHOLD: float = env_number(
    "JWSGJ_SINGLE_SOURCE_CONFIRM_THRESHOLD", 0.50, float
)
def _finite_number(raw: Any) -> tuple[float | None, str]:
    if isinstance(raw, bool):
        return None, "bool"
    try:
        num = float(raw)
    except (TypeError, ValueError, OverflowError):
        return None, "type"
    if not safe_isfinite(num):
        return None, "nonfinite"
    return num, ""
def _parse_clamped_adjustment_map(raw: dict, cap: float | None, kind: str,
                                  floor: float | None = None) -> dict[str, float]:
    valid: dict[str, float] = {}
    for k, v in raw.items():
        num, reason = _finite_number(v)
        if reason == "bool":
            logger.warning("[CV] 反馈调整%s为 bool 值（会被误钳为生效阈值），跳过: %s=%r", kind, k, v)
            continue
        if reason == "type":
            logger.debug("[CV] 反馈调整%s格式解析失败（跳过条目）: %s=%r", kind, k, v)
            continue
        if reason == "nonfinite":
            logger.warning("[CV] 反馈调整%s非有限值，跳过: %s=%r", kind, k, v)
            continue
        valid[k] = _clamp_threshold(num, cap, floor)
    return valid
_FEEDBACK_STATE_ATTRS: tuple[str, ...] = (
    "_method_confidence_multipliers",
    "_cv_confidence_thresholds",
    "_feedback_adjustments",
)
_FEEDBACK_GLOBAL_BASELINE_ATTR = "_feedback_global_baseline"
_FEEDBACK_GLOBAL_MISSING = object()
# 管线注入的调整（approved_adjustments + 记忆驱动 CV 调优）必须跨开轮重载保留：
# validate() 开轮按演化节重建反馈状态，重载后依据此记录重新套用。
_PIPELINE_ADJUSTMENTS_ATTR = "_pipeline_adjustments"
def _set_cv_state(cv, attr_name: str, value) -> bool:
    try:
        setattr(cv, attr_name, value)
        return True
    except (AttributeError, TypeError) as e:
        logger.warning("[CV] 调用位不可写 %s(%s)，本次反馈状态跳过: %s",
                       attr_name, type(cv).__name__, e)
        return False
def _delete_cv_state(cv, attr_name: str) -> bool:
    try:
        delattr(cv, attr_name)
        return True
    except (AttributeError, TypeError) as e:
        if isinstance(e, AttributeError) and not hasattr(cv, attr_name):
            return True
        logger.warning("[CV] 调用位不可删除 %s(%s)，反馈状态恢复失败: %s",
                       attr_name, type(cv).__name__, e)
        return False
def _ensure_feedback_global_baseline(cv) -> None:
    if isinstance(getattr(cv, _FEEDBACK_GLOBAL_BASELINE_ATTR, None), dict):
        return
    baseline = {}
    for target, _new_key, _old_key in _GLOBAL_THRESHOLD_ALIASES:
        baseline[target] = getattr(cv, target, _FEEDBACK_GLOBAL_MISSING)
    _set_cv_state(cv, _FEEDBACK_GLOBAL_BASELINE_ATTR, baseline)
def _restore_feedback_global_thresholds(cv) -> bool:
    baseline = getattr(cv, _FEEDBACK_GLOBAL_BASELINE_ATTR, None)
    if not isinstance(baseline, dict):
        return True
    restored = True
    for target, value in baseline.items():
        if value is _FEEDBACK_GLOBAL_MISSING:
            succeeded = _delete_cv_state(cv, target)
        else:
            succeeded = _set_cv_state(cv, target, value)
        if not succeeded:
            restored = False
    return restored
def _clear_feedback_state(cv) -> bool:
    _ensure_feedback_global_baseline(cv)
    cleared = _restore_feedback_global_thresholds(cv)
    for _attr_name in _FEEDBACK_STATE_ATTRS:
        if not _set_cv_state(cv, _attr_name, {}):
            cleared = False
    set_approved_rule_thresholds(None)
    return cleared
def _load_adjustment_field(cv, adjustments: dict, field_key: str,
                           attr_name: str, cap: float | None,
                           floor: float | None, kind: str) -> None:
    raw = adjustments.get(field_key, {})
    if not isinstance(raw, dict):
        logger.warning("[CV] 反馈调整 %s 字段非 dict(实际 %s)，已清空旧值",
                       field_key, type(raw).__name__)
        _set_cv_state(cv, attr_name, {})
        return
    _set_cv_state(
        cv, attr_name, _parse_clamped_adjustment_map(raw, cap, kind, floor))
_MULTIPLIER_FLOOR: float = 0.5
_MULTIPLIER_CAP: float = 1.5
_FEEDBACK_FIELD_SPECS = (
    (FIELD_METHOD_CONFIDENCE_MULTIPLIERS,
     "_method_confidence_multipliers", _MULTIPLIER_CAP,
     _MULTIPLIER_FLOOR, "乘数"),
    (FIELD_CV_CONFIDENCE_THRESHOLDS,
     "_cv_confidence_thresholds", None, None, "阈值"),
)
def load_feedback_adjustments(cv) -> None:
    try:
        skill_dir = skill_dir_or_fallback(cv)
        if not skill_dir:
            logger.debug("[CV] skill_dir 不可推导，反馈调整跳过加载（回退默认阈值）")
            _clear_feedback_state(cv)
            return
        try:
            adjustments = read_evolution_section(
                skill_dir, "approved_adjustments")
        except (OSError, ValueError, TypeError) as err:
            logger.warning("[CV] 反馈配置加载失败，已清空旧调整: %s", err)
            _clear_feedback_state(cv)
            return
        if adjustments is None:
            _clear_feedback_state(cv)
            return
        if not isinstance(adjustments, dict):
            logger.warning("[CV] 反馈调整文件顶层非 dict(实际 %s)，已清空旧值",
                           type(adjustments).__name__)
            _clear_feedback_state(cv)
            return
        for field_key, attr_name, cap, floor, kind in _FEEDBACK_FIELD_SPECS:
            _load_adjustment_field(
                cv, adjustments, field_key, attr_name, cap, floor, kind)
        _set_cv_state(cv, "_feedback_adjustments", adjustments)
    except (json.JSONDecodeError, OSError, KeyError, TypeError, ValueError,
            AttributeError, RuntimeError):
        _clear_feedback_state(cv)
        logger.warning("[CV] 反馈配置加载失败，已清空旧调整", exc_info=True)
def _valid_threshold_num(raw: Any, label: str, key: Any) -> float | None:
    num, reason = _finite_number(raw)
    if reason == "bool":
        logger.warning("[CV] %s阈值为 bool 值（会被误钳为生效阈值），跳过: %s=%r", label, key, raw)
    elif reason == "type":
        logger.warning("[CV] %s阈值非数值，跳过: %s=%r", label, key, raw)
    elif reason == "nonfinite":
        logger.warning("[CV] %s阈值非有限值，跳过: %s=%r", label, key, raw)
    return num
def _clamp_threshold(num: float, cap: float | None = None,
                     floor: float | None = None) -> float:
    _cap = CONF_CAP if cap is None else cap
    _floor = CONF_FLOOR if floor is None else floor
    return max(_floor, min(_cap, num))
_RULE_THRESHOLD_KEY_PREFIXES = ("CV-CONFIDENCE-", "CONFIDENCE_")
def _split_rule_key(key: Any) -> tuple[str, str]:
    text = key if isinstance(key, str) else str(key)
    for prefix in _RULE_THRESHOLD_KEY_PREFIXES:
        if text.startswith(prefix):
            return prefix, text[len(prefix):].strip()
    return "", text.strip()
def _canonical_rule_id(rule_id: Any) -> str:
    return normalize_rule_id(_split_rule_key(rule_id)[1]) or ""
def _collect_rule_overrides(cvt: dict) -> dict[str, float]:
    rule_overrides: dict[str, float] = {}
    for k, v in cvt.items():
        prefix, rid = _split_rule_key(k)
        if not prefix:
            continue
        if not rid:
            logger.warning("[CV] 规则级阈值键rule_id为空，跳过: %r", k)
            continue
        rule_id = _canonical_rule_id(rid)
        _num = _valid_threshold_num(v, "规则级", k)
        if rule_id and _num is not None:
            rule_overrides[rule_id] = _num
    return rule_overrides
_GLOBAL_THRESHOLD_ALIASES = (
    ("AUTO_CONFIRM_THRESHOLD", "global_confirm", "CONFIRM_THRESHOLD"),
    ("AUTO_STRENGTH_THRESHOLD", "global_strength", "STRENGTH_THRESHOLD"),
    ("AUTO_MIN_ADJUSTED", "global_min_adjusted", "MIN_ADJUSTED"),
)
def _cv_dict_state(cv, attr_name: str, label: str) -> dict | None:
    state = getattr(cv, attr_name, None)
    if isinstance(state, dict):
        return state
    if state:
        logger.warning("[CV] %s非 dict(实际 %s)，按空容器重建",
                       label, type(state).__name__)
    rebuilt: dict = {}
    return rebuilt if _set_cv_state(cv, attr_name, rebuilt) else None
def apply_feedback_thresholds(cv) -> None:
    _ensure_feedback_global_baseline(cv)
    _restore_feedback_global_thresholds(cv)
    cvt = _cv_dict_state(cv, "_cv_confidence_thresholds", "反馈阈值状态")
    effective = cvt if cvt is not None else {}
    set_approved_rule_thresholds(_collect_rule_overrides(effective) or None)
    if not effective:
        return
    _apply_global_thresholds(cv, effective)
def _apply_global_thresholds(cv, cvt: dict) -> None:
    for target, new_key, old_key in _GLOBAL_THRESHOLD_ALIASES:
        # 显式哨兵代替 for/else：可读性更好，也不依赖隐式控制流。
        _num = None
        for src_key in (new_key, old_key):
            raw = cvt.get(src_key)
            if raw is None:
                continue
            _num = _valid_threshold_num(raw, "全局", src_key)
            if _num is not None:
                break
        if _num is None:
            continue
        v = _clamp_threshold(_num)
        if not _set_cv_state(cv, target, v):
            continue
        logger.info("[CV] AI已批准全局阈值生效: %s = %.3f", target, v)
_SMALL_SAMPLE_LIMIT = 20
_MIN_DECISION_SAMPLE = 10
_HALF_DECAY_INTERVAL = 200
_CALIBRATION_BOOST_RATE = 0.25
_CALIBRATION_COMPRESS_RATE = 0.6
_HISTORY_RECORD_DEFAULTS: dict[str, int] = {
    "hits": 0, "fp": 0, "confirmed": 0, "last_update": 0}
_CALIBRATION_PARTIAL_ERROR: dict[str, bool] = {
    "_error": True, "_partial": True}
_OUTCOME_TRUE_TEXT = frozenset({"1", "true", "yes", "on"})
_OUTCOME_FALSE_TEXT = frozenset({"0", "false", "no", "off"})
def _outcome_flag(value: Any, *, label: str, rule_id: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        text = value.strip().lower()
        if text in _OUTCOME_TRUE_TEXT:
            return True
        if text in _OUTCOME_FALSE_TEXT:
            return False
    elif is_real_number(value) and value in (0, 1):
        return bool(value)
    logger.warning(
        "[XV_Threshold] 规则 %r 的%s标志非法(%r)，本次学习结果丢弃",
        rule_id, label, value)
    return None
RULE_SPECIFIC_THRESHOLDS: dict[str, float] = {
    "规则2":  0.85,
    "规则12": 0.85,
    "规则22": 0.85,
    "规则6":  0.60,
    "规则13": 0.55,
    "规则1":  0.75,
    "规则20": 0.80,
    "规则42": 0.75,
    "规则43": 0.80,
    "规则44": 0.75,
    "规则45": 0.70,
    "规则46": 0.65,
    "规则47": 0.85,
    "规则48": 0.75,
    "规则52": 0.65,
    "规则53": 0.70,
    "规则54": 0.60,
    "规则50": 0.60,
    "规则55": 0.70,
    "规则56": 0.60,
    "规则57": 0.55,
    "规则15": 0.50,
    "default": 0.70,
}
def _rule_base_threshold(rule_id: Any) -> float:
    rid = normalize_rule_id(rule_id)
    return RULE_SPECIFIC_THRESHOLDS.get(
        rid, RULE_SPECIFIC_THRESHOLDS.get("default", CONF_HIGH))
_THRESHOLD_HISTORY_PATH: str = ""
_THRESHOLD_HISTORY: dict[str, dict[str, Any]] = {}
_THRESHOLD_HISTORY_LOCK = threading.Lock()
_THRESHOLD_LOADED: bool = False
_THRESHOLD_HISTORY_LOAD_FAILED: bool = False
def learning_dir_request(skill_dir: Any) -> tuple[str, bool]:
    try:
        raw_truthy = bool(skill_dir)
    except Exception as _bool_err:  # noqa: BLE001
        logger.warning(
            "[XV_Threshold] 学习目录布尔判值失败(实际 %s)，进入纯内存模式: %s",
            type(skill_dir).__name__, _bool_err)
        return "", True
    if isinstance(skill_dir, (str, os.PathLike)):
        try:
            path = os.fspath(skill_dir)
        except (TypeError, ValueError) as _swallow_e:
            log_swallowed(__name__, _swallow_e, context='learning_dir_request:TypeError+')
            return "", raw_truthy
        return (path if isinstance(path, str) else ""), raw_truthy
    if raw_truthy:
        logger.warning(
            "[XV_Threshold] 学习目录入参非路径类型(实际 %s)，按无效目录进入纯内存模式",
            type(skill_dir).__name__)
    return "", raw_truthy
def set_threshold_learning_dir(skill_dir: str) -> None:
    global _THRESHOLD_HISTORY_PATH, _THRESHOLD_LOADED
    global _THRESHOLD_HISTORY_LOAD_FAILED
    skill_dir, _raw_truthy = learning_dir_request(skill_dir)
    try:
        with _THRESHOLD_HISTORY_LOCK:
            previous_path = _THRESHOLD_HISTORY_PATH
            previous_history = dict(_THRESHOLD_HISTORY)
            previous_loaded = _THRESHOLD_LOADED
            previous_failed = _THRESHOLD_HISTORY_LOAD_FAILED
            try:
                if skill_dir and os.path.isdir(skill_dir):
                    _THRESHOLD_HISTORY_PATH = threshold_history_path(skill_dir)
                    os.makedirs(
                        os.path.dirname(_THRESHOLD_HISTORY_PATH), exist_ok=True)
                elif _raw_truthy:
                    logger.warning(
                        "[XV_Threshold] 学习目录无效或不存在(%r)，进入纯内存模式",
                        skill_dir or type(skill_dir).__name__)
                    _THRESHOLD_HISTORY_PATH = ""
                else:
                    _THRESHOLD_HISTORY_PATH = ""
                _THRESHOLD_HISTORY.clear()
                _THRESHOLD_LOADED = False
                _load_threshold_history()
            except Exception:
                _THRESHOLD_HISTORY_PATH = previous_path
                _THRESHOLD_HISTORY.clear()
                _THRESHOLD_HISTORY.update(previous_history)
                _THRESHOLD_LOADED = previous_loaded
                _THRESHOLD_HISTORY_LOAD_FAILED = previous_failed
                raise
    except (OSError, PermissionError, RuntimeError) as e:
        logger.warning("[XV_Threshold] set_threshold_learning_dir 失败，保持原路径: %s", e)
def _load_threshold_history() -> None:
    global _THRESHOLD_LOADED, _THRESHOLD_HISTORY_LOAD_FAILED
    _THRESHOLD_HISTORY_LOAD_FAILED = False
    _history_path = _THRESHOLD_HISTORY_PATH
    _THRESHOLD_HISTORY.clear()
    if _history_path:
        data, kind, err = read_json_artifact(_history_path)
        if kind == "ok":
            if not isinstance(data, dict):
                logger.warning("[XV_Threshold] 阈值历史顶层非 dict(实际 %s),置空", type(data).__name__)
                _THRESHOLD_HISTORY_LOAD_FAILED = True
            else:
                _THRESHOLD_HISTORY.update(data)
        elif kind == "parse_error":
            logger.warning("[XV_Threshold] 加载阈值历史失败,置空: %s", err)
            _THRESHOLD_HISTORY_LOAD_FAILED = True
    _THRESHOLD_LOADED = True
def _load_history_if_needed_locked() -> None:
    if not _THRESHOLD_LOADED:
        _load_threshold_history()
def _history_count(value) -> int:
    if isinstance(value, bool) or not isinstance(value, (int, float, str)):
        return 0
    number, reason = _finite_number(value)
    if reason or not number.is_integer():
        return 0
    return max(0, int(number))
def _history_counts(rec: dict) -> tuple[int, int, int]:
    return (
        _history_count(rec.get("hits", 0)),
        _history_count(rec.get("confirmed", 0)),
        _history_count(rec.get("fp", 0)),
    )

def _history_record_for_read_locked(rule_id: Any) -> tuple[str, Any, str | None]:
    rid = normalize_rule_id(rule_id) or ""
    if not rid:
        return "", None, None
    rec = _THRESHOLD_HISTORY.get(rid)
    if rec is not None:
        return rid, rec, None
    for key, candidate in _THRESHOLD_HISTORY.items():
        if (normalize_rule_id(key) or "") == rid:
            return rid, candidate, key
    return rid, None, None
def _read_record_fields(rule_id: str) -> tuple[int, int, int]:
    with _THRESHOLD_HISTORY_LOCK:
        _load_history_if_needed_locked()
        _rid, rec, _legacy_key = _history_record_for_read_locked(rule_id)
        if not _rid or not isinstance(rec, dict):
            return (0, 0, 0)
        hits, confirmed, fp = _history_counts(rec)
        if confirmed + fp > hits:
            logger.warning(
                "[XV_Threshold] 规则 %s 历史计数不变量非法"
                "(hits=%d, confirmed=%d, fp=%d)，按未度量处理",
                _rid, hits, confirmed, fp)
            return (0, 0, 0)
    return (hits, confirmed, fp)
def _small_sample_damping(hits: int) -> float:
    if hits < _MIN_DECISION_SAMPLE:
        return 0.5
    if hits < _SMALL_SAMPLE_LIMIT:
        return 0.5 + 0.5 * (hits - _MIN_DECISION_SAMPLE) / (
            _SMALL_SAMPLE_LIMIT - _MIN_DECISION_SAMPLE)
    return 1.0
def _save_threshold_history() -> None:
    _history_path = _THRESHOLD_HISTORY_PATH
    if not _history_path:
        return
    if _THRESHOLD_HISTORY_LOAD_FAILED:
        logger.warning(
            "[XV_Threshold] 历史文件未能读取，跳过本次落盘以免覆盖历史: %s",
            _history_path)
        return
    try:
        write_json_artifact(_history_path, _THRESHOLD_HISTORY, indent=2)
    except (OSError, TypeError, ValueError, OverflowError, RuntimeError):
        logger.warning("[XV_Threshold] _save_threshold_history failed", exc_info=True)
def _fp_rate_adjustment(fp_rate: float) -> float:
    if fp_rate < 0.12:
        return -CONF_BOOST_SMALL
    if fp_rate < 0.18:
        t = (fp_rate - 0.12) / 0.06
        return -CONF_BOOST_SMALL + 0.025 * t
    if fp_rate < 0.27:
        center = 0.225
        deviation = (fp_rate - center) / 0.045
        return round(0.025 * deviation, 4)
    if fp_rate < 0.33:
        t = (fp_rate - 0.27) / 0.06
        return 0.025 + 0.025 * t
    return +CONF_BOOST_SMALL
def _decision_sample(hits: int, confirmed: int, fp: int) -> int:
    decisions = max(0, confirmed) + max(0, fp)
    return min(decisions, max(hits, 0))
def _decision_fp_rate(hits: int, confirmed: int, fp: int) -> float | None:
    sample = _decision_sample(hits, confirmed, fp)
    if sample <= 0:
        return None
    return min(1.0, max(0.0, max(0, fp) / sample))
def get_adaptive_threshold(rule_id: str, base_threshold: float) -> float:
    base = safe_confidence(base_threshold, _rule_base_threshold(rule_id))
    try:
        hits, confirmed, fp = _read_record_fields(rule_id)
        if fp <= 0 and confirmed <= 0:
            # 既无正也无负样本时不做阈值调整：未复核的自动抑制只记中性
            # hit，fp_rate=0 不能推出“规则精确”，只说明“还没测到”。
            # 否则只学中性 hit 会让阈值单调下降（越来越敏感、误报上升）。
            # 有 confirmed 样本时仍按旧口径降阈值（高精度规则提高召回），
            # 负样本由复核通过的 fixate_fp_rules 回写。
            return base
        sample = _decision_sample(hits, confirmed, fp)
        if sample < _MIN_DECISION_SAMPLE:
            return base
        fp_rate = _decision_fp_rate(hits, confirmed, fp)
        if fp_rate is None:
            return base
        sample_factor = _small_sample_damping(sample)
        adjustment = _fp_rate_adjustment(fp_rate) * sample_factor
        adjusted = _clamp_threshold(base + adjustment)
        return round(adjusted, 3)
    except Exception:
        logger.exception("[get_adaptive_threshold] 异常降级")
        return base
def _history_record_locked(rule_id: str) -> tuple[str, dict]:
    rid, rec, legacy_key = _history_record_for_read_locked(rule_id)
    if not rid:
        return rid, dict(_HISTORY_RECORD_DEFAULTS)
    if not isinstance(rec, dict):
        if rec is not None:
            logger.warning(
                "[XV_Threshold] 规则 %s 历史记录非 dict(实际 %s)，从干净基线重启学习",
                rid, type(rec).__name__)
        rec = dict(_HISTORY_RECORD_DEFAULTS)
    else:
        hits, confirmed, fp = _history_counts(rec)
        if confirmed + fp > hits:
            logger.warning(
                "[XV_Threshold] 规则 %s 历史计数不变量非法"
                "(hits=%d, confirmed=%d, fp=%d)，从干净基线重启学习",
                rid, hits, confirmed, fp)
            rec = dict(_HISTORY_RECORD_DEFAULTS)
    if legacy_key is not None:
        _THRESHOLD_HISTORY.pop(legacy_key, None)
    _THRESHOLD_HISTORY[rid] = rec
    return rid, rec
def _decayed_history_counts(rec: dict, rid: str) -> tuple[int, int, int]:
    hits, confirmed_count, fp = _history_counts(rec)
    if hits >= _HALF_DECAY_INTERVAL:
        _raw_hits = hits
        hits //= 2
        fp //= 2
        confirmed_count //= 2
        logger.debug("[XV_Threshold] 规则 %s 历史数据半衰减重置 (hits=%d -> %d)",
                     rid, _raw_hits, hits)
    return hits, fp, confirmed_count
def record_threshold_outcome(rule_id: str, confirmed: bool, was_false_positive: bool = False) -> None:
    try:
        _confirmed = _outcome_flag(
            confirmed, label="confirmed", rule_id=rule_id)
        _was_fp = _outcome_flag(
            was_false_positive, label="was_false_positive", rule_id=rule_id)
        if _confirmed is None or _was_fp is None:
            return
        with _THRESHOLD_HISTORY_LOCK:
            _load_history_if_needed_locked()
            rid, rec = _history_record_locked(rule_id)
            if not rid:
                logger.warning("[XV_Threshold] 规则号无效(%r)，本次学习结果丢弃", rule_id)
                return
            hits, fp, confirmed_count = _decayed_history_counts(rec, rid)
            if _confirmed and _was_fp:
                logger.warning(
                    "[XV_Threshold] 规则 %s 同时标记 confirmed 与误报，按误报记（confirmed 不计）",
                    rid)
                _confirmed = False
            rec["hits"] = hits + 1
            rec["confirmed"] = confirmed_count + _confirmed
            rec["fp"] = fp + _was_fp
            rec["last_update"] = int(time.time())
            _save_threshold_history()
    except Exception:
        logger.exception("[record_threshold_outcome] 异常降级")
_APPROVED_RULE_THRESHOLDS: dict[str, float] = {}
_APPROVED_RULE_LOCK = threading.Lock()
def set_approved_rule_thresholds(mapping: dict | None) -> None:
    if not isinstance(mapping, dict):
        if mapping:
            logger.warning("[XV_Threshold] 已批准规则阈值入参非 dict(实际 %s)，按空处理清空",
                           type(mapping).__name__)
        mapping = {}
    valid = _validated_rule_thresholds(mapping)
    with _APPROVED_RULE_LOCK:
        _APPROVED_RULE_THRESHOLDS.clear()
        if not valid:
            return
        _APPROVED_RULE_THRESHOLDS.update(valid)
        logger.info("[XV_Threshold] AI已批准规则级确认阈值生效: %d 条", len(valid))
def _validated_rule_thresholds(mapping: dict) -> dict[str, float]:
    valid: dict[str, float] = {}
    for rid, val in mapping.items():
        rid_s = _canonical_rule_id(rid)
        if not rid_s:
            logger.warning("[XV_Threshold] 已批准规则阈值为空rule_id，跳过: %r", rid)
            continue
        num = _valid_threshold_num(val, "已批准规则", rid_s)
        if num is not None:
            valid[rid_s] = _clamp_threshold(num)
    return valid
def get_approved_rule_threshold(rule_id: str) -> float | None:
    with _APPROVED_RULE_LOCK:
        return _APPROVED_RULE_THRESHOLDS.get(_canonical_rule_id(rule_id))
def get_rule_threshold(rule_id: str) -> float:
    _rid = _canonical_rule_id(rule_id)
    base = _rule_base_threshold(_rid)
    try:
        adjusted = get_adaptive_threshold(_rid, base)
        approved = get_approved_rule_threshold(_rid)
        if approved is not None:
            return round(approved, 3)
        return adjusted
    except Exception:
        logger.exception("[get_rule_threshold] 异常降级")
        return base
def _confirmed_precision_rate(hits: int, confirmed: int, fp: int) -> float | None:
    sample = _decision_sample(hits, confirmed, fp)
    if sample < _MIN_DECISION_SAMPLE:
        return None
    return min(1.0, max(0.0, max(0, confirmed) / sample))
_RULE_WEIGHT_ANCHORS: tuple[tuple[float, float], ...] = (
    (0.0, 0.5), (CONF_LOW, 0.8), (CONF_HIGH, 1.0), (0.90, 1.0), (1.0, 1.5))
def _interpolate_anchors(anchors, x: float) -> float:
    if x <= anchors[0][0]:
        return anchors[0][1]
    prev = anchors[0]
    for cur in anchors[1:]:
        if x <= cur[0]:
            return prev[1] + (cur[1] - prev[1]) * (x - prev[0]) / (cur[0] - prev[0])
        prev = cur
    return anchors[-1][1]
def _learning_context(rule_id: str) -> tuple[float | None, float]:
    hits, confirmed, fp = _read_record_fields(rule_id)
    rate = _confirmed_precision_rate(hits, confirmed, fp)
    if rate is None:
        return None, 1.0
    return rate, _small_sample_damping(_decision_sample(hits, confirmed, fp))
def get_rule_weight(rule_id: str) -> float:
    try:
        confirmed_rate, sample_factor = _learning_context(rule_id)
        if confirmed_rate is None:
            return 1.0
        raw_weight = _interpolate_anchors(_RULE_WEIGHT_ANCHORS, confirmed_rate)
        weight = 1.0 + (raw_weight - 1.0) * sample_factor
        return round(weight, 3)
    except Exception:
        logger.exception("[get_rule_weight] 异常降级")
        return 1.0
def calibrate_confidence(rule_id: str, raw_confidence: float) -> float:
    base_confidence = safe_confidence(raw_confidence, 0.0)
    try:
        confirmed_rate, sample_factor = _learning_context(rule_id)
        if confirmed_rate is None:
            return base_confidence
        if confirmed_rate > 0.80:
            calibrated = base_confidence * (1.0 + (confirmed_rate - 0.80) * _CALIBRATION_BOOST_RATE * sample_factor)
        elif confirmed_rate < 0.50:
            calibrated = base_confidence * (1.0 - (0.50 - confirmed_rate) * _CALIBRATION_COMPRESS_RATE * sample_factor)
        else:
            return base_confidence
        return round(max(0.0, min(1.0, calibrated)), 3)
    except Exception:
        logger.exception("[calibrate_confidence] 异常降级")
        return base_confidence
_RETIRE_MIN_SAMPLE = 50
_RETIRE_FP_RATE = 0.6
_RETIRE_CONFIRM_RATIO = 0.2
def rule_retirement_state(rule_id: str) -> dict:
    """规则退休判定：样本充足且误报压倒性时降级为观察态。

    退休不是删除：规则仍执行，但 ``confirmed`` 降级为 ``suggestion``（不可
    作为交付终态），并在报告里显式列出。这样既不交付噪声，也不把真问题从
    视野里抹掉——真问题回潮时 confirmed 样本占比回升，判定会自动解除。
    """
    rid = _canonical_rule_id(rule_id)
    try:
        with _THRESHOLD_HISTORY_LOCK:
            _load_history_if_needed_locked()
            _rid, rec, _legacy_key = _history_record_for_read_locked(rid)
            if not _rid or not isinstance(rec, dict):
                return {"retired": False, "sample": 0, "fp_rate": 0.0,
                        "confirmed_ratio": 0.0, "reason": "no_sample"}
            _hits, confirmed, fp = _history_counts(rec)
            if confirmed + fp > _hits:
                logger.warning(
                    "[XV_Threshold] 规则 %s 历史计数不变量非法，禁止退休判定"
                    "(hits=%d, confirmed=%d, fp=%d)",
                    _rid, _hits, confirmed, fp)
                return {"retired": False, "sample": 0, "fp_rate": 0.0,
                        "confirmed_ratio": 0.0, "reason": "invalid_counts"}
    except Exception:
        logger.exception("[rule_retirement_state] 异常降级")
        return {"retired": False, "sample": 0, "fp_rate": 0.0,
                "confirmed_ratio": 0.0, "reason": "read_failed"}
    decisions = max(0, confirmed) + max(0, fp)
    if decisions < _RETIRE_MIN_SAMPLE:
        return {"retired": False, "sample": decisions, "fp_rate": 0.0,
                "confirmed_ratio": 0.0, "reason": "insufficient_sample"}
    fp_rate = fp / decisions
    confirmed_ratio = confirmed / decisions
    retired = (fp_rate >= _RETIRE_FP_RATE
               and confirmed_ratio < _RETIRE_CONFIRM_RATIO)
    return {
        "retired": retired,
        "sample": decisions,
        "fp_rate": round(fp_rate, 3),
        "confirmed_ratio": round(confirmed_ratio, 3),
        "reason": "fp_dominant" if retired else "healthy",
    }
def is_rule_retired(rule_id: str) -> bool:
    try:
        return bool(rule_retirement_state(rule_id).get("retired"))
    except Exception:
        logger.exception("[is_rule_retired] 异常降级")
        return False
def retired_rule_ids() -> list[str]:
    """当前处于退休态的规则清单（报告与门禁可见性用）。

    读取与判定均不报错：``rule_retirement_state`` 自身已降级为
    ``retired=False``，清单只做纯内存遍历。
    """
    with _THRESHOLD_HISTORY_LOCK:
        _load_history_if_needed_locked()
        rule_ids = [str(rid) for rid in _THRESHOLD_HISTORY]
    return sorted(
        rid for rid in rule_ids
        if rule_retirement_state(rid).get("retired"))
def fp_tuning_params(fp_rate: float) -> tuple[float, float]:
    rate = safe_confidence(fp_rate, 0.0)
    return (min(0.2, round(rate * 0.3, 2)),
            max(0.7, round(1.0 - rate * 0.3, 2)))
@dataclass
class CVRuleTuning:
    rule_id: str
    threshold_adjustment: float
    confidence_multiplier: float
    reason: str
    evidence_count: int = 0
    category: str = CATEGORY_CV_TUNING
def _dampen_toward_neutral(adjustment: float,
                           multiplier: float) -> tuple[float, float]:
    return (round(adjustment / 2, 3),
            round(1.0 + (multiplier - 1.0) / 2, 3))
def _dampen_on_repeat(ev: dict, direction: int, adjustment: float,
                      multiplier: float,
                      reason: str) -> tuple[float, float, str]:
    hist_adj = ev.get("historical_adjustment", 0.0)
    if hist_adj * direction <= 0:
        return adjustment, multiplier, reason
    adjustment, multiplier = _dampen_toward_neutral(adjustment, multiplier)
    label = "收紧" if direction > 0 else "放宽"
    return (adjustment, multiplier,
            f"{reason}；历史已{label}{hist_adj:+.2f}，防振荡削减幅度至{adjustment:+.2f}")
def _fp_rate_tuning(rid: str, ev: dict, fp_rate: float,
                   total: int) -> CVRuleTuning:
    adjustment, multiplier = fp_tuning_params(fp_rate)
    reason = f"历史FP率{fp_rate:.0%}({ev['fp_count']}/{total})，需提高阈值"
    if ev.get("fp_reasons"):
        reason += f": {'; '.join(ev['fp_reasons'][:2])}"
    adjustment, multiplier, reason = _dampen_on_repeat(
        ev, 1, adjustment, multiplier, reason)
    return CVRuleTuning(
        rule_id=rid, threshold_adjustment=adjustment,
        confidence_multiplier=multiplier, reason=reason,
        evidence_count=total)
def _tp_rate_tuning(rid: str, ev: dict, fp_rate: float,
                   total: int) -> CVRuleTuning:
    reason = f"历史TP率{1-fp_rate:.0%}({ev['tp_count']}/{total})，可提升置信度"
    adjustment, multiplier, reason = _dampen_on_repeat(
        ev, -1, TP_THRESHOLD_ADJUSTMENT, TP_CONFIDENCE_MULTIPLIER, reason)
    return CVRuleTuning(
        rule_id=rid, threshold_adjustment=adjustment,
        confidence_multiplier=multiplier, reason=reason,
        evidence_count=total)
def _rule_tuning_for_evidence(rid: str, ev: dict) -> CVRuleTuning | None:
    total = ev["fp_count"] + ev["tp_count"]
    if total < 2:
        return None
    fp_rate = ev["fp_count"] / total
    if fp_rate > 0.6:
        return _fp_rate_tuning(rid, ev, fp_rate, total)
    if fp_rate < 0.15 and ev["tp_count"] >= 3:
        return _tp_rate_tuning(rid, ev, fp_rate, total)
    return None
def generate_cv_tunings(
    ctx: DiagnosticMemoryContext,
) -> list[CVRuleTuning]:
    tunings: list[CVRuleTuning] = []
    rule_evidence = collect_ctx_evidence(ctx)
    for rid, ev in rule_evidence.items():
        tuning = _rule_tuning_for_evidence(rid, ev)
        if tuning is not None:
            tunings.append(tuning)
    logger.info("[MemoryBridge] CV调优生成: %d条规则调整建议", len(tunings))
    return tunings
def _threshold_config_key(rid: Any) -> str:
    _prefix, bare_rid = _split_rule_key(rid)
    return (f"{_RULE_THRESHOLD_KEY_PREFIXES[0]}{bare_rid}" if bare_rid else "")
def _apply_single_tuning(tuning: CVRuleTuning, thresholds: dict,
                         multipliers: dict) -> None:
    rid = normalize_rule_id(tuning.rule_id) or ""
    if not rid:
        logger.warning("[MemoryBridge] 跳过脏 rule_id 调优项: %r", tuning.rule_id)
        return
    key = _threshold_config_key(rid)
    if not key:
        logger.warning("[MemoryBridge] 跳过空规则号调优项: %r", tuning.rule_id)
        return
    bare_rid = _split_rule_key(key)[1]
    storage_keys = tuple(
        f"{prefix}{bare_rid}" for prefix in _RULE_THRESHOLD_KEY_PREFIXES
    ) + (bare_rid,)
    old_threshold = get_rule_threshold(rid)
    for storage_key in storage_keys:
        candidate = safe_float(thresholds.get(storage_key), None)
        if candidate is not None:
            old_threshold = candidate
            break
    new_threshold = _clamp_threshold(
        old_threshold + safe_float(tuning.threshold_adjustment))
    thresholds[key] = round(new_threshold, 3)
    for storage_key in storage_keys:
        if storage_key != key:
            thresholds.pop(storage_key, None)
    old_mult = safe_float(multipliers.get(rid), 1.0)
    new_mult = max(_MULTIPLIER_FLOOR, min(
        _MULTIPLIER_CAP,
        old_mult * safe_float(tuning.confidence_multiplier, 1.0)))
    multipliers[rid] = round(new_mult, 3)
def _config_section(config: dict, key: str) -> dict:
    value = config.get(key)
    if isinstance(value, dict):
        return dict(value)
    if value:
        logger.warning("[MemoryBridge] 配置段 %s 非 dict(实际 %s)，按空段重建",
                       key, type(value).__name__)
    return {}
def apply_cv_tunings_to_config(
    config: dict,
    tunings: list[CVRuleTuning],
) -> dict:
    if not isinstance(config, dict):
        config = {}
    if not tunings:
        return config
    adjusted = dict(config)
    thresholds = _config_section(adjusted, FIELD_CV_CONFIDENCE_THRESHOLDS)
    multipliers = _config_section(adjusted, FIELD_METHOD_CONFIDENCE_MULTIPLIERS)
    for tuning in tunings:
        _apply_single_tuning(tuning, thresholds, multipliers)
    adjusted[FIELD_CV_CONFIDENCE_THRESHOLDS] = thresholds
    adjusted[FIELD_METHOD_CONFIDENCE_MULTIPLIERS] = multipliers
    return adjusted
def _apply_cv_threshold_section(adjustments: dict, cv) -> None:
    cv_thresholds = adjustments.get(FIELD_CV_CONFIDENCE_THRESHOLDS, {})
    if cv_thresholds and not isinstance(cv_thresholds, dict):
        logger.warning("[Stage2b] CV阈值调整非 dict 形态，忽略: %s",
                      type(cv_thresholds).__name__)
        return
    if not cv_thresholds:
        return
    logger.info("[Stage2b] 应用反馈调整: %d 个CV规则置信度阈值", len(cv_thresholds))
    cvt = _cv_dict_state(cv, "_cv_confidence_thresholds", "CV阈值容器")
    if cvt is None:
        return
    cvt.update(cv_thresholds)
    apply_feedback_thresholds(cv)
def _apply_method_multiplier_section(adjustments: dict, cv) -> None:
    method_mults = adjustments.get(FIELD_METHOD_CONFIDENCE_MULTIPLIERS, {})
    if method_mults and not isinstance(method_mults, dict):
        logger.warning("[Stage2b] 方法乘数调整非 dict 形态，忽略: %s",
                       type(method_mults).__name__)
        return
    if not method_mults:
        return
    clamped = _parse_clamped_adjustment_map(
        method_mults, _MULTIPLIER_CAP, "乘数", _MULTIPLIER_FLOOR)
    if not clamped:
        return
    logger.info("[Stage2b] 应用反馈调整: %d 个方法置信度乘数", len(clamped))
    mcm = _cv_dict_state(cv, "_method_confidence_multipliers", "方法乘数容器")
    if mcm is None:
        return
    mcm.update(clamped)
def apply_cv_threshold_adjustments(adjustments: dict, cv) -> None:
    if not isinstance(adjustments, dict):
        logger.warning("[Stage2b] 反馈调整入参非 dict(实际 %s)，按空调整处理",
                       type(adjustments).__name__)
        adjustments = {}
    _apply_cv_threshold_section(adjustments, cv)
    _apply_method_multiplier_section(adjustments, cv)
    if adjustments:
        _set_cv_state(cv, _PIPELINE_ADJUSTMENTS_ATTR, dict(adjustments))
def resolve_threshold(override: float | None, env_name: str, default: float) -> float:
    value = (override if override is not None
             else env_number(env_name, default, float))
    return safe_confidence(value, default)
def _fp_entry(fp_rate: float) -> dict:
    return {"total": 0, "fp": 0, "fp_rate": fp_rate}
RULE_FP_TRACKER: dict[str, dict] = {  # jwsgj:suppress TP-07
    "code_smell":             _fp_entry(0.30),
    "none_comparison":        _fp_entry(0.30),
    "shadowing_builtin":      _fp_entry(0.30),
    "missing_docstring":      _fp_entry(0.30),
    "todo_marker":            _fp_entry(0.30),
    "high_complexity":        _fp_entry(0.15),
    "long_function":          _fp_entry(0.15),
    "deep_nesting":           _fp_entry(0.15),
    "duplicate_code":         _fp_entry(0.15),
    "god_file":               _fp_entry(0.15),
    "high_coupling":          _fp_entry(0.15),
    "sql_injection":          _fp_entry(0.05),
    "path_traversal":         _fp_entry(0.05),
    "hardcoded_credential":   _fp_entry(0.05),
    "syntax_error":           _fp_entry(0.08),
    "broad_except":           _fp_entry(0.10),
    "dead_code":              _fp_entry(0.12),
    "circular_dep":           _fp_entry(0.10),
    "unbounded_recursion":    _fp_entry(0.15),
    "broken_call":            _fp_entry(0.10),
    "mutable_global":         _fp_entry(0.15),
}
PRECISE_SMOKE_FAMILIES: tuple = (
    "syntax_error", "import_error", "broken_import",
    "undefined_name", "broken_call",
)
_FP_TRACKER_BASELINE: dict[str, dict] = {
    family: dict(entry) for family, entry in RULE_FP_TRACKER.items()
}
def _accumulate_fp_entry(data: dict, fam: str, cnt: int) -> None:
    entry = data.setdefault(fam, {"total": 0, "fp": 0, "fp_rate": 0.0})
    if not isinstance(entry, dict):
        entry = {"total": 0, "fp": 0, "fp_rate": 0.0}
        data[fam] = entry
    entry.update(_build_tracker_entry(
        entry.get("total"), entry.get("fp"),
        total_delta=cnt, fp_delta=cnt))
def _normalize_family_key(value: Any) -> str:
    return value.strip() if isinstance(value, str) else ""
def _normalized_channel_stats(stats: Any) -> dict[str, int]:
    if not isinstance(stats, dict):
        if stats:
            logger.warning("[ChannelLoopC] 通道统计入参非 dict(实际 %s)，跳过固化",
                           type(stats).__name__)
        return {}
    normalized: dict[str, int] = {}
    for fam, raw in stats.items():
        family = _normalize_family_key(fam)
        if not family:
            logger.debug("[ChannelLoopC] 规则族名为空(%r)，跳过", fam)
            continue
        count = _to_tracker_count(raw)
        if count <= 0:
            logger.debug("[ChannelLoopC] 规则族 %s 计数无效(%r)，跳过", family, raw)
            continue
        if raw != count:
            logger.debug("[ChannelLoopC] 规则族 %s 计数非整数(%r)，按 %d 计",
                         family, raw, count)
        normalized[family] = normalized.get(family, 0) + count
    return normalized
def _read_tracker_for_update(path: str, *, propagate_io: bool = False) -> dict | None:
    data, kind, err = read_json_artifact(path, propagate_io=propagate_io)
    if kind == "missing":
        return {}
    if kind != "ok":
        logger.warning("[XV] FP tracker 既有内容不可读，禁止覆盖: %s", err)
        return None
    if not isinstance(data, dict):
        logger.warning("[XV] FP tracker 顶层非 dict(实际 %s)，禁止覆盖",
                       type(data).__name__)
        return None
    return data
def persist_fp_channel_stats(skill_dir: str, stats: dict) -> int:
    stats = _normalized_channel_stats(stats)
    if not stats:
        return 0
    try:
        path = fp_tracker_path(skill_dir)
    except (RuntimeError, OSError, TypeError, ValueError) as _pe:
        logger.warning("[ChannelLoopC] fp_tracker 路径不可用，本轮固化跳过: %s", _pe)
        return 0
    with locked_artifact(path) as locked:
        if not locked:
            logger.warning("[ChannelLoopC] fp_tracker 锁不可用，保留原统计: %s", path)
            return 0
        try:
            data = _read_tracker_for_update(path, propagate_io=True)
        except OSError as _re:
            logger.warning("[ChannelLoopC] fp_tracker 读取 I/O 失败，保留原统计: %s", _re)
            return 0
        if data is None:
            return 0
        for fam, cnt in stats.items():
            _accumulate_fp_entry(data, fam, cnt)
        try:
            write_json_artifact(path, data, indent=2)
        except (OSError, ValueError, TypeError) as e:
            logger.warning("[ChannelLoopC] fp_tracker 写入失败: %s", e)
            return 0
    with RULE_FP_TRACKER_LOCK:
        for fam, cnt in stats.items():
            entry = RULE_FP_TRACKER.get(fam)
            if not isinstance(entry, dict):
                entry = _build_tracker_entry(0, 0)
                RULE_FP_TRACKER[fam] = entry
            _accumulate_tracker(entry, total_delta=cnt, fp_delta=cnt)
    logger.info("[ChannelLoopC] 通道信号→FP固化: %d 个 rule_family 并入 fp_tracker", len(stats))
    return len(stats)
def _has_reliable_negative_evidence(xvr: dict) -> bool:
    _inner = xvr.get("findings")
    if not isinstance(_inner, list):
        return False
    return any(isinstance(f, dict) and _finding_has_negative_evidence(f)
               for f in _inner)
def _finding_has_negative_evidence(finding: dict) -> bool:
    if signal_bool(finding.get("_counter_evidence")):
        return True
    return bool(
        signal_bool(finding.get("_test_triage_smoke_pass"))
        and str(finding.get("rule_family", "")) in PRECISE_SMOKE_FAMILIES
    )
def _ai_confirmed_locator(ai_store, locator: str,
                          rule_id: str | None = None) -> bool | None:
    if ai_store is None:
        return False
    try:
        if rule_id is None or not rule_id.strip():
            _m = ai_store.fuzzy_match(locator)
        else:
            _m = ai_store.fuzzy_match(locator, rule_id=rule_id)
    except Exception as _fe:  # noqa: BLE001
        log_swallowed(__name__, _fe,
                      context='feed_channel_signals:ai_confirm_lookup')
        return None
    return _m is not None and _m.verdict == "confirmed"
def _fp_signal_family(xvr: dict, censored_locs: frozenset,
                      ai_store) -> str | None:
    if str(xvr.get("conclusion", "")) != "suppressed":
        return None
    _fam = xvr.get("rule_family")
    if not isinstance(_fam, str) or not _fam:
        return None
    fam = _fam
    locator = str(xvr.get("locator", "") or "")
    if canonical_locator_key(locator) in censored_locs:
        return None
    if not _has_reliable_negative_evidence(xvr):
        return None
    ai_confirmed = _ai_confirmed_locator(
        ai_store, locator, str(xvr.get("rule_id", "") or ""))
    if ai_confirmed is not False:
        return None
    return fam
def _collect_fp_channel_stats(xv_findings: list, censored_locs: frozenset, ai_store,
                              contributing_samples: list | None = None) -> dict:
    stats: dict = {}
    for xvr in xv_findings or []:
        if not isinstance(xvr, dict):
            continue
        fam = _fp_signal_family(xvr, censored_locs, ai_store)
        if fam:
            stats[fam] = stats.get(fam, 0) + 1
            if contributing_samples is not None:
                contributing_samples.append(xvr)
    return stats
def _pending_review_locators(skill_dir: str) -> frozenset | None:
    if not skill_dir:
        return frozenset()
    path = cv_uncertain_path(skill_dir)
    try:
        entries = read_review_queue_entries(path)
    except Exception as _qe:  # noqa: BLE001
        logger.warning("[ChannelLoopC] 复核队列读取失败，本轮FP学习跳过: %s", _qe)
        return None
    if entries is None:
        _payload, kind, _err = read_json_artifact(path)
        if kind == "missing":
            return frozenset()
        logger.warning(
            "[ChannelLoopC] 复核队列存在但不可解析(kind=%s)，待审定位不可确认，"
            "本轮FP学习跳过", kind)
        return None
    return frozenset(
        canonical_locator_key(entry.get("locator"))
        for entry in entries
        if isinstance(entry, dict) and entry.get("status") == "pending_review"
    )
_FP_CHANNEL_CALIBRATED = "_fp_channel_calibrated"
def feed_channel_signals_to_fp_tracker(skill_dir: str, xv_findings: list | None) -> int:
    _ai_store = open_confirm_store(skill_dir)
    _censored_locs = _pending_review_locators(skill_dir)
    if _censored_locs is None:
        return 0
    contributing_samples: list[dict] = []
    stats = _collect_fp_channel_stats(
        xv_findings, _censored_locs, _ai_store, contributing_samples)
    if not stats or not skill_dir:
        return 0
    persisted = persist_fp_channel_stats(skill_dir, stats)
    if persisted:
        for sample in contributing_samples:
            sample[_FP_CHANNEL_CALIBRATED] = True
    return persisted
RULE_FP_TRACKER_LOCK = threading.RLock()
def _build_tracker_entry(total: Any, fp: Any, *, total_delta: int = 0,
                         fp_delta: int = 0, rate_digits: int = 3) -> dict:
    normalized_total = _to_tracker_count(total) + total_delta
    normalized_fp = min(_to_tracker_count(fp) + fp_delta, normalized_total)
    return {
        "total": normalized_total,
        "fp": normalized_fp,
        "fp_rate": round(
            normalized_fp / max(normalized_total, 1), rate_digits),
    }
def _accumulate_tracker(tracker: dict, *, total_delta: int = 1,
                        fp_delta: int = 0) -> None:
    tracker.update(_build_tracker_entry(
        tracker.get("total", 0), tracker.get("fp", 0),
        total_delta=total_delta, fp_delta=fp_delta))
def update_rule_fp_tracker(rule_family: str, is_false_positive: bool) -> bool:
    try:
        family = _normalize_family_key(rule_family)
        if not family:
            return False
        normalized = _outcome_flag(
            is_false_positive, label="is_false_positive", rule_id=family)
        if normalized is None:
            return False
        with RULE_FP_TRACKER_LOCK:
            tracker = RULE_FP_TRACKER.get(family)
            if isinstance(tracker, dict):
                _accumulate_tracker(tracker, fp_delta=int(normalized))
            else:
                RULE_FP_TRACKER[family] = _build_tracker_entry(
                    0, 0, total_delta=1,
                    fp_delta=int(normalized))
        return True
    except Exception as e:  # noqa: BLE001
        logger.warning("[XV] FP追踪器更新失败 in update_rule_fp_tracker(): %s", e)
        return False
def _calibration_sample(xvf, censored: dict) -> tuple[str, bool] | None:
    if not isinstance(xvf, dict):
        return None
    if signal_bool(xvf.get(_FP_CHANNEL_CALIBRATED)):
        return None
    conclusion = xvf.get("conclusion", "")
    if conclusion not in ("confirmed", "suppressed"):
        return None
    rf = _normalize_family_key(xvf.get("rule_family"))
    if not rf:
        return None
    if rf in censored:
        return None
    return rf, conclusion == "suppressed"
def calibrate_fp_tracker_from_xv_results(xv_results: dict) -> dict:
    try:
        updated_families, total_updates = _calibration_counts(xv_results)
        return {
            "updated_families": len(updated_families),
            "total_updates": total_updates,
        }
    except Exception as e:  # noqa: BLE001
        logger.warning("[XV] FP追踪器校准失败 in calibrate_fp_tracker_from_xv_results(): %s", e)
        return dict(_CALIBRATION_PARTIAL_ERROR)
_CENSORED_CONTAINER_TYPES = (dict, list, tuple, set, frozenset)
def _censored_family_set(raw: Any) -> frozenset[str]:
    if not raw:
        return frozenset()
    if not isinstance(raw, _CENSORED_CONTAINER_TYPES):
        logger.warning(
            "[XV] _fp_censored_families 载体非映射/序列(实际 %s)，按空集处理",
            type(raw).__name__)
        return frozenset()
    items = ((family for family, count in raw.items()
              if _to_tracker_count(count) > 0)
             if isinstance(raw, dict) else raw)
    families = {_normalize_family_key(item) for item in items}
    families.discard("")
    return frozenset(families)
def _calibration_samples(xv_results: dict) -> list:
    raw = xv_results.get("findings_index")
    if raw is None:
        return []
    if not isinstance(raw, list):
        logger.warning("[XV] findings_index 载体非 list(实际 %s)，本轮校准跳过",
                       type(raw).__name__)
        return []
    return raw
def _calibration_counts(xv_results: dict) -> tuple[set, int]:
    updated_families: set = set()
    total_updates = 0
    _censored = _censored_family_set(
        xv_results.get("_fp_censored_families"))
    for xvf in _calibration_samples(xv_results):
        sample = _calibration_sample(xvf, _censored)
        if sample is None:
            continue
        rf, is_fp = sample
        if not update_rule_fp_tracker(rf, is_fp):
            continue
        updated_families.add(rf)
        total_updates += 1
    return updated_families, total_updates
def _calibrate_from_xv_results(result: dict) -> None:
    try:
        _calibration = calibrate_fp_tracker_from_xv_results(result)
        result["fp_tracker_calibration"] = _calibration
        logger.info("[CV] FP tracker calibrate: %d families, %d updates",
                    _calibration.get("updated_families", 0),
                    _calibration.get("total_updates", 0))
    except Exception as e:
        logger.warning("[CV] FP tracker calibrate error: %s", e, exc_info=True)
def _calibrate_from_treatment_feedback(cv, result: dict) -> None:
    try:
        _skill_dir = skill_dir_or_fallback(cv) or ""
        if not (_skill_dir and os.path.isdir(_skill_dir)):
            return
        result["treatment_feedback_calibration"] = calibrate_from_treatment_outcomes(
            cv, _skill_dir,
            tracker_persist=lambda: save_fp_tracker_persisted(
                cv, return_status=True))
    except Exception as _tf_exc:  # noqa: BLE001
        logger.warning("[CV] treatment feedback calibration failed: %s", _tf_exc)
def calibrate_and_persist_fp_tracker(cv, result: dict) -> None:
    _calibrate_from_xv_results(result)
    _calibrate_from_treatment_feedback(cv, result)
    try:
        save_fp_tracker_persisted(cv)
    except (AttributeError, OSError, TypeError, ValueError) as e:
        logger.warning("[CV] FP tracker persist save failed: %s", e)
def _treatment_item_outcome(item: Any) -> tuple[str, bool, dict] | None:
    if not isinstance(item, dict):
        return None
    status = item.get("status", "")
    if status not in ("ai_fixed", "fixed", "succeeded", "fp_confirmed"):
        return None
    result = item.get("result", {})
    if not isinstance(result, dict):
        logger.warning(
            "[CV-TreatmentFeedback] 治疗结果字段非 dict(实际 %s)，保留原值并跳过样本",
            type(result).__name__)
        return None
    calibrated = _outcome_flag(
        result.get("cv_calibrated", False), label="cv_calibrated",
        rule_id=item.get("locator", ""))
    if calibrated is not False:
        return None
    rf = parse_locator_rule_family(item.get("locator", ""))
    if not rf:
        return None
    return rf, status == "fp_confirmed", result
def _treatment_outcome_items(t_state: dict) -> list | None:
    items = t_state.get("items") or []
    if not isinstance(items, list):
        return None
    return items
def _persist_calibration_marks(skill_dir: str, t_state: dict) -> bool:
    try:
        save_treatment_state(skill_dir, t_state)
    except Exception as _e:  # noqa: BLE001
        logger.warning("[CV-TreatmentFeedback] 校准标记回写失败，内存增量将回滚: %s", _e)
        return False
    return True
def _read_treatment_state(skill_dir: str) -> tuple[dict | None, str]:
    state_path = get_treatment_state_path(skill_dir)
    if not os.path.isfile(state_path):
        return None, "no_treatment_state"
    t_state, kind, err = read_json_artifact(state_path)
    if kind == "missing":
        return None, "no_treatment_state"
    if kind != "ok":
        logger.warning("[CV-TreatmentFeedback] 治疗状态文件加载失败，按无样本脏数据处理: %s", err)
        return None, "invalid_state"
    if not isinstance(t_state, dict):
        return None, "invalid_state"
    return t_state, ""
def _apply_treatment_calibration(items: list) -> tuple[set[str], int]:
    calibrated_families: set[str] = set()
    samples = 0
    for item in items:
        outcome = _treatment_item_outcome(item)
        if outcome is None:
            continue
        rf, is_fp, result = outcome
        if not update_rule_fp_tracker(rf, is_fp):
            continue
        result["cv_calibrated"] = True
        item["result"] = result
        calibrated_families.add(rf)
        samples += 1
    return calibrated_families, samples
def _snapshot_item_results(items: list) -> list[tuple[dict, bool, Any]]:
    snapshot: list[tuple[dict, bool, Any]] = []
    for item in items:
        if not isinstance(item, dict):
            continue
        previous = item.get("result")
        snapshot.append((
            item, "result" in item,
            dict(previous) if isinstance(previous, dict) else previous))
    return snapshot
def _restore_item_results(snapshot: list[tuple[dict, bool, Any]]) -> None:
    for item, present, previous in snapshot:
        if present:
            item["result"] = previous
        else:
            item.pop("result", None)
def _restore_tracker_snapshot(snapshot: dict) -> None:
    RULE_FP_TRACKER.clear()
    RULE_FP_TRACKER.update(snapshot)
def _apply_treatment_calibration_transaction(
        skill_dir: str, t_state: dict, items: list,
        tracker_persist=None) -> tuple[set[str], int, bool, str]:
    with RULE_FP_TRACKER_LOCK:
        tracker_snapshot = {
            key: dict(value) if isinstance(value, dict) else value
            for key, value in RULE_FP_TRACKER.items()
        }
        item_snapshot = _snapshot_item_results(items)
        try:
            calibrated, samples = _apply_treatment_calibration(items)
            if samples and not _persist_calibration_marks(skill_dir, t_state):
                _restore_tracker_snapshot(tracker_snapshot)
                _restore_item_results(item_snapshot)
                return calibrated, samples, False, "calibration_mark_write_failed"
            if (samples and tracker_persist is not None
                    and not tracker_persist()):
                _restore_tracker_snapshot(tracker_snapshot)
                _restore_item_results(item_snapshot)
                rollback_saved = _persist_calibration_marks(skill_dir, t_state)
                reason = "tracker_persist_failed"
                if not rollback_saved:
                    reason += "_and_calibration_rollback_failed"
                    logger.error(
                        "[CV-TreatmentFeedback] tracker 落盘失败后，校准标记回滚也失败；"
                        "下轮可能漏学，请人工核对治疗状态与 FP tracker")
                return calibrated, samples, False, reason
            return calibrated, samples, True, ""
        except Exception:
            _restore_tracker_snapshot(tracker_snapshot)
            _restore_item_results(item_snapshot)
            raise
def calibrate_from_treatment_outcomes(
        _cv, skill_dir: str, tracker_persist=None) -> dict:
    try:
        t_state, reason = _read_treatment_state(skill_dir)
        if t_state is None:
            return {"calibrated_families": 0, "ground_truth_samples": 0,
                    "reason": reason}
        items = _treatment_outcome_items(t_state)
        if items is None:
            return {"calibrated_families": 0, "ground_truth_samples": 0,
                    "reason": "invalid_items"}
        if not items:
            return {"calibrated_families": 0, "ground_truth_samples": 0, "reason": "no_items"}
        calibrated_families, samples, committed, reason = (
            _apply_treatment_calibration_transaction(
                skill_dir, t_state, items, tracker_persist=tracker_persist))
        if not committed:
            return {"calibrated_families": 0, "ground_truth_samples": 0,
                    "reason": reason,
                    "_error": True, "_partial": True}
        if samples:
            logger.info("[CV-TreatmentFeedback] 治疗结果回流校准: %d 样本, %d 族",
                        samples, len(calibrated_families))
        return {"calibrated_families": len(calibrated_families), "ground_truth_samples": samples}
    except Exception as e:  # noqa: BLE001
        logger.warning("[CV-TreatmentFeedback] 治疗结果回流校准降级: %s", e)
        return dict(_CALIBRATION_PARTIAL_ERROR)
def _strict_tracker_count(value: Any) -> int | None:
    if not is_real_number(value):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if value < 0 or not value.is_integer():
        return None
    return int(value)
def _to_tracker_count(v: Any) -> int:
    normalized = _strict_tracker_count(v)
    return normalized if normalized is not None else 0
def _normalized_fp_rate(tr: dict) -> float:
    rate, _reason = _finite_number(tr.get("fp_rate", 0.0))
    if rate is None:
        return 0.0
    return max(0.0, min(1.0, rate))
def build_fp_tracker_state() -> dict:
    rules: dict[str, dict] = {}
    with RULE_FP_TRACKER_LOCK:
        for rf, tr in (RULE_FP_TRACKER or {}).items():
            if not isinstance(tr, dict):
                continue
            family = _normalize_family_key(rf)
            if not family:
                logger.debug("[CV] FP tracker 规则族名非法(%r)，报告跳过", rf)
                continue
            entry = rules.setdefault(
                family, {"total": 0, "fp": 0, "fp_rate": 0.0})
            entry["total"] += _to_tracker_count(tr.get("total", 0))
            entry["fp"] = min(
                entry["fp"] + _to_tracker_count(tr.get("fp", 0)),
                entry["total"])
            entry["fp_rate"] = (
                round(entry["fp"] / entry["total"], 3)
                if entry["total"] else round(_normalized_fp_rate(tr), 3))
    high = sorted(family for family, entry in rules.items()
                  if entry["fp_rate"] > 0.5)
    return {"rules": rules, "high_fp_rules": high,
            "high_fp_count": len(high)}
def _merge_persisted_fp_entry(rule_family: str, tracker_data: Any) -> bool:
    rule_family = _normalize_family_key(rule_family)
    if not rule_family:
        logger.debug("[CV] FP tracker 规则族为空(%r)，按脏数据跳过", rule_family)
        return False
    if not isinstance(tracker_data, dict):
        return False
    total = _strict_tracker_count(tracker_data.get("total", 0))
    fp = _strict_tracker_count(tracker_data.get("fp", 0))
    if total is None or total < 1 or fp is None or fp > total:
        logger.debug("[CV] FP tracker 条目计数或不变量非法，按脏数据跳过: %s=%r",
                     rule_family, tracker_data)
        return False
    with RULE_FP_TRACKER_LOCK:
        existing = RULE_FP_TRACKER.get(rule_family)
        existing_total = (_strict_tracker_count(existing.get("total", 0))
                          if isinstance(existing, dict) else 0)
        existing_fp = (_strict_tracker_count(existing.get("fp", 0))
                       if isinstance(existing, dict) else 0)
        if (existing_total is None or existing_fp is None
                or existing_fp > existing_total):
            existing_total, existing_fp = 0, 0
        RULE_FP_TRACKER[rule_family] = _build_tracker_entry(
            existing_total, existing_fp,
            total_delta=total, fp_delta=fp)
    return True
def _read_persisted_tracker(fp_path: str) -> dict | None:
    saved, kind, err = read_json_artifact(fp_path)
    if kind == "missing":
        return None
    if kind != "ok":
        logger.warning("[CV] FP tracker load failed: %s", err)
        return None
    if not isinstance(saved, dict):
        logger.warning("[CV] FP tracker 顶层非 dict(实际 %s)，跳过加载",
                       type(saved).__name__)
        return None
    return saved
def _merge_persisted_entries(saved: dict) -> int:
    loaded = 0
    for rule_family, tracker_data in saved.items():
        if _merge_persisted_fp_entry(rule_family, tracker_data):
            loaded += 1
    return loaded
def _replace_tracker_with_persisted(saved: dict | None) -> int:
    with RULE_FP_TRACKER_LOCK:
        RULE_FP_TRACKER.clear()
        RULE_FP_TRACKER.update(
            {fam: dict(entry) for fam, entry in _FP_TRACKER_BASELINE.items()})
        return _merge_persisted_entries(saved) if saved else 0
def load_fp_tracker_persisted(cv) -> None:
    try:
        skill_dir = skill_dir_or_fallback(cv)
        if not skill_dir:
            logger.debug("[CV] skill_dir 不可推导，清空 FP tracker 防止跨项目残留")
            _replace_tracker_with_persisted(None)
            return
        fp_path = fp_tracker_path(skill_dir)
        # 读取器负责规范路径与旧布局候选，不能用新路径 isfile 提前短路。
        saved = _read_persisted_tracker(fp_path)
        if saved is None:
            _replace_tracker_with_persisted(None)
            return
        loaded = _replace_tracker_with_persisted(saved)
        logger.info("[CV] FP tracker loaded from disk: %d/%d families",
                    loaded, len(saved))
    except (OSError, TypeError, ValueError, OverflowError, RuntimeError):
        logger.warning("[CV] FP tracker load failed", exc_info=True)
        _replace_tracker_with_persisted(None)
def _snapshot_tracker_for_save() -> dict:
    snapshot: dict[str, dict] = {}
    with RULE_FP_TRACKER_LOCK:
        for family, tracker in RULE_FP_TRACKER.items():
            if not isinstance(tracker, dict):
                continue
            normalized_family = _normalize_family_key(family)
            if not normalized_family:
                logger.warning("[CV] FP tracker 规则族名为空，跳过持久化: %r", family)
                continue
            total = _strict_tracker_count(tracker.get("total", 0))
            fp = _strict_tracker_count(tracker.get("fp", 0))
            if total == 0 and fp == 0:
                continue
            if (total is None or total < 1 or fp is None or fp > total):
                logger.warning(
                    "[CV] FP tracker 条目计数或不变量非法，跳过持久化: %s=%r",
                    family, tracker)
                continue
            entry = _build_tracker_entry(total, fp)
            previous = snapshot.get(normalized_family)
            if previous is not None:
                entry = _build_tracker_entry(
                    previous["total"], previous["fp"],
                    total_delta=total, fp_delta=fp)
            snapshot[normalized_family] = entry
    return snapshot
def save_fp_tracker_persisted(cv, *, return_status: bool = False) -> bool | None:
    succeeded = False
    to_save: dict | None = None
    try:
        skill_dir = skill_dir_or_fallback(cv)
        if not skill_dir:
            logger.debug("[CV] skill_dir 不可推导，跳过 FP tracker 持久化")
        else:
            fp_path = fp_tracker_path(skill_dir)
            os.makedirs(os.path.dirname(fp_path), exist_ok=True)
            with locked_artifact(fp_path) as locked:
                if not locked:
                    logger.warning("[CV] FP tracker 锁不可用，跳过持久化: %s", fp_path)
                elif _read_tracker_for_update(fp_path) is not None:
                    to_save = _snapshot_tracker_for_save()
                    write_json_artifact(fp_path, to_save, indent=2)
                    succeeded = True
            if succeeded and to_save is not None:
                logger.info("[CV] FP tracker persisted: %d families", len(to_save))
    except (OSError, TypeError, ValueError, OverflowError, RuntimeError):
        logger.warning("[CV] FP tracker persist failed", exc_info=True)
    return succeeded if return_status else None

from __future__ import annotations

import datetime
import logging
import math
import os
import re
from collections.abc import Callable, Iterator, Mapping
from dataclasses import dataclass, field
from itertools import combinations
from typing import Any, Self

from jwsgj.build_matching_diagnoser import (
    CaptureRuleDiagnoser,
    MatchingRuleDiagnoser,
    diag_skill_full_pipeline,
)
from jwsgj.build_text_document import (
    contains_term,
    normalize_str_list,
    normalize_text,
)
from jwsgj.build_text_scoring import (
    generate_trigger_examples,
    keyword_matches,
    normalize_keywords,
    probe_pipeline_trigger,
    stem_matches,
)

logger = logging.getLogger(__name__)
__all__ = [
    'KEYWORD_GOOD_COUNT',
    'KEYWORD_TARGET_COUNT',
    'MIN_KEYWORD_COUNT',
    'ActivationDecision',
    'AutoDisclosureOptimizer',
    'CalibratedScore',
    'CalibrationProfile',
    'ConfidenceCalibrator',
    'MatchRecord',
    'SkillActivationRouter',
    'SkillRoutingInfo',
    'TriggerFeedback',
    'TriggerFeedbackLoop',
    'distinct_keywords',
    'evaluate_trigger_coverage',
    'evaluate_trigger_feedback',
    'get_calibrator',
    'kw_language_flags',
    'quick_route',
    'recommend_cold_start',
    'score_triggers',
    'trigger_feedback_message',
]
@dataclass
class MatchRecord:
    skill_name: str
    user_query: str
    raw_score: float
    triggered: bool
    match_features: dict[str, float] = field(default_factory=dict)
    timestamp: str = ""
    source: str = "simulation"
@dataclass
class CalibratedScore:
    skill_name: str = ""
    raw_score: float = 0.0
    calibrated_score: float = 0.0
    confidence_level: str = "unknown"
    calibration_records: int = 0
    feature_breakdown: dict[str, float] = field(default_factory=dict)
    reason: str = ""
@dataclass
class CalibrationProfile:
    skill_name: str = ""
    total_records: int = 0
    feature_hit_rates: dict[str, float] = field(default_factory=dict)
    feature_counts: dict[str, int] = field(default_factory=dict)
    avg_raw_score: float = 0.0
    avg_trigger_rate: float = 0.0
    bias: float = 0.0
_HIGH_CONFIDENCE_MIN_SAMPLES = 50
_DEFAULT_MIN_SAMPLES = 5
_SCORE_MIN = 0.0
_SCORE_MAX = 1.0
_RAW_SCORE_WEIGHT = 0.7
_FEATURE_MEAN_WEIGHT = 0.3
_BIAS_WEIGHT = 0.5
_DEFAULT_FEATURE_HIT_RATE = 0.5
_FEATURE_HIT_THRESHOLD = 0.5
def _clamp_score(value: float) -> float:
    return max(_SCORE_MIN, min(_SCORE_MAX, value))
def _incremental_mean(old_mean: float, value: float, count: int) -> float:
    return (old_mean * (count - 1) + value) / count
def _mean(values: list[float]) -> float:
    if not values:
        return 0.0
    return sum(values) / len(values)
def _coerce_min_samples(value: Any) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        logger.warning(
            "ConfidenceCalibrator min_samples 非负整数校验失败: %r，回落 %d",
            value, _DEFAULT_MIN_SAMPLES)
        return _DEFAULT_MIN_SAMPLES
    return value
class ConfidenceCalibrator:
    def __init__(self: Self, min_samples: int = _DEFAULT_MIN_SAMPLES) -> None:
        self._profiles: dict[str, CalibrationProfile] = {}
        self._min_samples = _coerce_min_samples(min_samples)
    def record_match(self: Self, record: MatchRecord) -> None:
        if not isinstance(record, MatchRecord):
            logger.warning("record_match 拒绝非 MatchRecord 入参: %r", record)
            return
        self._update_profile(record)
    def record_from_test(self: Self, skill_name: str,
                         test_results: list[tuple[str, float, bool]]) -> None:
        for query, score, triggered in self._iter_test_records(test_results):
            self.record_match(MatchRecord(
                skill_name=skill_name,
                user_query=query,
                raw_score=score,
                triggered=triggered,
                timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                source="test",
            ))
    @staticmethod
    def _iter_test_records(test_results: Any) -> Iterator[tuple[Any, Any, Any]]:
        if not isinstance(test_results, (list, tuple)):
            logger.warning("record_from_test test_results 非列表形态: %s，按空处理",
                           type(test_results).__name__)
            return
        for item in test_results:
            if not (isinstance(item, (list, tuple)) and len(item) == 3):
                logger.warning("record_from_test 记录非三元组形态，跳过: %r", item)
                continue
            yield tuple(item)
    def calibrate(self: Self, skill_name: str, raw_score: float,
                   features: dict[str, float] | None = None) -> CalibratedScore:
        skill_name = normalize_text(skill_name).strip()
        norm_score = self._norm_score_value(raw_score)
        profile = self._profiles.get(skill_name)
        if norm_score is None:
            logger.warning("calibrate raw_score 非数值形态: %r，按 0 分校准",
                            raw_score)
            return self._invalid_score_result(skill_name, profile)
        features = self._normalize_feature_map(features, label="calibrate")
        if not profile or profile.total_records < self._min_samples:
            return self._insufficient_samples_result(
                skill_name, norm_score, profile)
        calibrated, feature_breakdown = self._calibrate_features(
            norm_score, features, profile)
        calibrated = _clamp_score(calibrated - profile.bias * _BIAS_WEIGHT)
        return self._calibrated_result(
            skill_name, norm_score, calibrated, feature_breakdown, profile)
    @staticmethod
    def _normalize_feature_map(features: Any, *, label: str) -> dict[str, Any]:
        if features is None:
            return {}
        if not isinstance(features, dict):
            logger.warning("%s 特征载荷非 dict 形态: %s，按空特征处理",
                           label, type(features).__name__)
            return {}
        normalized: dict[str, Any] = {}
        for key, value in features.items():
            name = normalize_text(key).strip()
            if not name:
                logger.warning("%s 特征名为空/非法，跳过该特征: %r", label, key)
                continue
            normalized[name] = value
        return normalized
    @staticmethod
    def _invalid_score_result(skill_name: str,
                              profile: CalibrationProfile | None) -> CalibratedScore:
        return CalibratedScore(
            skill_name=skill_name,
            raw_score=0.0,
            calibrated_score=0.0,
            confidence_level="low",
            reason="invalid_raw_score",
            calibration_records=profile.total_records if profile else 0,
        )
    @staticmethod
    def _insufficient_samples_result(skill_name: str, norm_score: float,
                                      profile: CalibrationProfile | None) -> CalibratedScore:
        return CalibratedScore(
            skill_name=skill_name,
            raw_score=norm_score,
            calibrated_score=norm_score,
            confidence_level="low",
            reason="insufficient_samples",
            calibration_records=profile.total_records if profile else 0,
        )
    @staticmethod
    def _calibrated_result(skill_name: str, norm_score: float, calibrated: float,
                            feature_breakdown: dict[str, float],
                            profile: CalibrationProfile) -> CalibratedScore:
        return CalibratedScore(
            skill_name=skill_name,
            raw_score=norm_score,
            calibrated_score=calibrated,
            confidence_level=(
                "high" if profile.total_records >= _HIGH_CONFIDENCE_MIN_SAMPLES
                else "medium"),
            reason="calibrated",
            calibration_records=profile.total_records,
            feature_breakdown=feature_breakdown,
        )
    def _calibrate_features(self: Self, norm_score: float,
                             features: dict[str, float] | None,
                             profile: CalibrationProfile) -> tuple[float, dict[str, float]]:
        feature_breakdown: dict[str, float] = {}
        if not features:
            return norm_score, feature_breakdown
        feat_calibrated_values = []
        for feat_name, feat_value in features.items():
            feat_calibrated = self._calibrate_feature_value(
                profile, feat_name, feat_value)
            if feat_calibrated is None:
                continue
            feature_breakdown[feat_name] = feat_calibrated
            feat_calibrated_values.append(feat_calibrated)
        if not feat_calibrated_values:
            return norm_score, feature_breakdown
        calibrated = (norm_score * _RAW_SCORE_WEIGHT
                      + _mean(feat_calibrated_values) * _FEATURE_MEAN_WEIGHT)
        return calibrated, feature_breakdown
    def _calibrate_feature_value(self: Self, profile: CalibrationProfile,
                                 feat_name: str, feat_value: Any) -> float | None:
        norm_value = self._norm_feat_value(feat_value)
        if norm_value is None:
            logger.warning(
                "calibrate 特征值非数值形态: %s=%r，跳过该特征",
                feat_name, feat_value)
            return None
        hit_rate = profile.feature_hit_rates.get(
            feat_name, _DEFAULT_FEATURE_HIT_RATE)
        return _clamp_score(norm_value) * hit_rate
    @staticmethod
    def _norm_feat_value(value: Any) -> float | None:
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            return None
        try:
            normalized = float(value)
        except OverflowError:
            return None
        return normalized if math.isfinite(normalized) else None
    @staticmethod
    def _norm_score_value(value: Any) -> float | None:
        norm = ConfidenceCalibrator._norm_feat_value(value)
        if norm is None:
            return None
        return _clamp_score(norm)
    def _update_profile(self: Self, record: MatchRecord) -> None:
        normalized = self._normalize_record(record)
        if normalized is None:
            return
        skill_name, norm_score = normalized
        profile = self._ensure_profile(skill_name)
        profile.total_records += 1
        n = profile.total_records
        profile.avg_raw_score = _incremental_mean(
            profile.avg_raw_score, norm_score, n)
        triggered_int = 1.0 if _flag_true(record.triggered) else 0.0
        profile.avg_trigger_rate = _incremental_mean(
            profile.avg_trigger_rate, triggered_int, n)
        self._update_feature_stats(profile, record)
        profile.bias = profile.avg_raw_score - profile.avg_trigger_rate
    def _normalize_record(self: Self, record: MatchRecord) -> tuple[str, float] | None:
        skill_name = normalize_text(record.skill_name).strip()
        if not skill_name:
            logger.warning("_update_profile skill_name 归一后为空，记录跳过: %r",
                           record.skill_name)
            return None
        norm_score = self._norm_score_value(record.raw_score)
        if norm_score is None:
            logger.warning("_update_profile raw_score 非数值形态，记录跳过（不更新画像）: %r",
                           record.raw_score)
            return None
        return skill_name, norm_score
    def _ensure_profile(self: Self, skill_name: str) -> CalibrationProfile:
        profile = self._profiles.get(skill_name)
        if profile is None:
            profile = CalibrationProfile(skill_name=skill_name)
            self._profiles[skill_name] = profile
        return profile
    def _update_feature_stats(self: Self, profile: CalibrationProfile,
                              record: MatchRecord) -> None:
        features = self._normalize_feature_map(
            record.match_features, label="_update_profile")
        for feat_name, feat_value in features.items():
            norm_value = self._norm_feat_value(feat_value)
            if norm_value is None:
                logger.warning(
                    "_update_profile 特征值非数值形态: %s=%r，跳过该特征",
                    feat_name, feat_value)
                continue
            self._record_feature(
                profile, feat_name, _flag_true(record.triggered), norm_value)
    @staticmethod
    def _record_feature(profile: CalibrationProfile, feat_name: str,
                        triggered: bool, norm_value: float) -> None:
        if feat_name not in profile.feature_counts:
            profile.feature_counts[feat_name] = 0
            profile.feature_hit_rates[feat_name] = _DEFAULT_FEATURE_HIT_RATE
        count = profile.feature_counts[feat_name]
        new_hit = 1.0 if (
            triggered and norm_value > _FEATURE_HIT_THRESHOLD) else 0.0
        profile.feature_hit_rates[feat_name] = _incremental_mean(
            profile.feature_hit_rates[feat_name], new_hit, count + 1)
        profile.feature_counts[feat_name] += 1
_TRUE_FLAG_TEXTS: frozenset[str] = frozenset({"true", "1", "yes", "y", "on"})
def _flag_true(value: Any) -> bool:
    if isinstance(value, str):
        return value.strip().lower() in _TRUE_FLAG_TEXTS
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        return value != 0
    if isinstance(value, float):
        return math.isfinite(value) and value != 0
    return bool(value)
_global_calibrator: ConfidenceCalibrator = ConfidenceCalibrator()
def get_calibrator() -> ConfidenceCalibrator:
    return _global_calibrator
def _iter_corpus_items(items: Any, label: str) -> Iterator[dict]:
    if items is None:
        return
    if not isinstance(items, (list, tuple)):
        logger.warning("trigger 语料 %s 非列表形态: %s，按空处理",
                       label, type(items).__name__)
        return
    for item in items:
        if isinstance(item, dict):
            yield item
        else:
            logger.warning("trigger 语料 %s 项非 dict，跳过: %r", label, item)
def _probe_corpus_item(
    item: dict,
    strong_matcher,
    trigger_probe: Callable[..., Mapping[str, Any]] | None = None,
) -> tuple[str, str, list[str]]:
    text = normalize_text(item.get("text", ""))
    hits = strong_matcher(text)
    probe = probe_pipeline_trigger if trigger_probe is None else trigger_probe
    decision = probe(text, strong_hits=hits)["decision"]
    return text, decision, hits
def _positive_passed(level: str, decision: str) -> bool:
    if level == "hit":
        return decision == "hit"
    if level == "soft":
        return decision in ("hit", "soft")
    return False
def evaluate_trigger_coverage(
    positives: list[dict],
    negatives: list[dict],
    strong_matcher,
    trigger_probe: Callable[..., Mapping[str, Any]] | None = None,
) -> dict:
    if not callable(strong_matcher):
        raise TypeError(
            "evaluate_trigger_coverage: strong_matcher 必须可调用（提供强词匹配）")
    positives = list(_iter_corpus_items(positives, "positives"))
    negatives = list(_iter_corpus_items(negatives, "negatives"))
    pos_passed = 0
    missed: list[dict] = []
    for item in positives:
        text, decision, _hits = _probe_corpus_item(
            item, strong_matcher, trigger_probe=trigger_probe)
        level = normalize_text(item.get("level", "hit")).strip().lower() or "hit"
        if _positive_passed(level, decision):
            pos_passed += 1
        else:
            missed.append({"text": text, "level": level,
                           "decision": decision})
    strong_fp: list[str] = []
    soft_hits: list[str] = []
    for item in negatives:
        text, decision, _hits = _probe_corpus_item(
            item, strong_matcher, trigger_probe=trigger_probe)
        if decision == "hit":
            strong_fp.append(text)
        if decision == "soft":
            soft_hits.append(text)
    neg_total = len(negatives)
    return {
        "positives": {"total": len(positives), "passed": pos_passed,
                      "missed": missed},
        "negatives": {"total": neg_total,
                      "strong_false_positives": strong_fp,
                      "soft_hits": soft_hits,
                      "soft_rate": (len(soft_hits) / neg_total) if neg_total else 0.0},
    }
_LATIN_LETTER_RE = re.compile(r"[A-Za-z\u00c0-\u024f]")
_NON_LATIN_SCRIPT_RE = re.compile(
    r"[\u0370-\u03ff\u0400-\u04ff\u0600-\u06ff\u0e00-\u0e7f"
    r"\u3040-\u30ff\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff"
    r"\uac00-\ud7af]")
_WORD_RE = re.compile(r"[^\W\d_]+", re.UNICODE)
_LATIN_RUN_RE = re.compile(r"[A-Za-z\u00c0-\u024f]+")
_CJK_SEGMENT_RE = re.compile(
    r"[\u3040-\u30ff\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff"
    r"\uac00-\ud7af]+")
_STOPWORDS: frozenset[str] = frozenset({
    "the", "an", "is", "are", "was", "were", "be",
    "been", "being", "have", "has", "had", "do", "does",
    "did", "of", "and", "or", "but", "if", "than", "then",
    "so", "as", "in", "on", "at", "to", "for", "with",
    "by", "from", "into", "about", "over", "under",
    "up", "down", "out", "off", "not", "no", "nor",
    "too", "very", "this", "that", "these", "those",
    "it", "its", "they", "them", "their", "we", "our",
    "you", "your", "he", "she", "his", "her", "who",
    "whom", "whose", "which", "what", "when", "where",
    "why", "how", "will", "would", "can", "could",
    "should", "may", "might", "must", "shall",
    "there", "here", "such", "own", "same",
})
_CN_FUNCTION_CHARS: frozenset[str] = frozenset(
    "的是在和了有这那与为等及或对中从到用被不")
_CN_STOP_BIGRAMS: frozenset[str] = frozenset(
    a + b for a in _CN_FUNCTION_CHARS for b in _CN_FUNCTION_CHARS)
_DEFAULT_ACTIVATION_THRESHOLD = 0.35
_DEFAULT_MULTI_SKILL_THRESHOLD = 0.25
_DEFAULT_MAX_ACTIVE_SKILLS = 5
_W_KEYWORD = 0.4
_W_DESCRIPTION = 0.3
_W_CATEGORY = 0.15
_W_NAME = 0.15
_CONFLICT_PENALTY = 0.2
_CONFLICT_OVERLAP_THRESHOLD = 0.6
_SCORE_POOL_FLOOR = 10
@dataclass
class ActivationDecision:
    activated_skills: list[str] = field(default_factory=list)
    confidence_scores: dict[str, float] = field(default_factory=dict)
    rejected_skills: list[str] = field(default_factory=list)
    rejection_reasons: dict[str, str] = field(default_factory=dict)
    conflict_warnings: list[str] = field(default_factory=list)
    cascade_dependencies: list[str] = field(default_factory=list)
@dataclass
class SkillRoutingInfo:
    name: str = ""
    description: str = ""
    keywords: list[str] = field(default_factory=list)
    category: str = ""
    depends_on: list[str] = field(default_factory=list)
    anti_patterns: list[str] = field(default_factory=list)
    skill_md_path: str = ""
_FIELD_CAPTURE_DIAG = "capture_diag"
_FIELD_FULL_PIPELINE = "full_pipeline"
@dataclass(frozen=True)
class _EnhancementChannel:
    field: str
    stage: str
    tag: str
    payload_fn: Callable[[SkillRoutingInfo], dict[str, Any]]
def _apply_diag_enhancement(
    skills: dict[str, SkillRoutingInfo], reports: list[dict[str, Any]],
    channel: _EnhancementChannel) -> None:
    for r in reports:
        raw_name = r.get("skill_name", "")
        name = raw_name if isinstance(raw_name, str) else str(raw_name)
        info = skills.get(name)
        if not (info and info.skill_md_path):
            continue
        try:
            r[channel.field] = channel.payload_fn(info)
        except Exception:
            logger.warning(
                "diag_matching_quality: %s（技能 %s，%s）",
                channel.stage, name, channel.tag, exc_info=True)
def _matching_report_entry(name: str, report: Any) -> dict[str, Any]:
    return {
        "skill_name": name,
        "score": report.overall_score,
        "grade": report.grade,
        "violations": len(report.violations),
        "critical": report.critical_count,
        "high": report.high_count,
        "medium": report.medium_count,
        "details": [
            {"rule": v.rule_id, "severity": v.severity,
             "description": v.description}
            for v in report.violations
        ],
        _FIELD_CAPTURE_DIAG: None,
        _FIELD_FULL_PIPELINE: None,
    }
def _capture_diag_payload(
        info: SkillRoutingInfo,
        diagnoser_box: dict[str, CaptureRuleDiagnoser]) -> dict[str, Any]:
    if "diagnoser" not in diagnoser_box:
        diagnoser_box["diagnoser"] = CaptureRuleDiagnoser()
    cap_report = diagnoser_box["diagnoser"].diag(
        info.skill_md_path, description=info.description)
    return {
        "score": cap_report.overall_score,
        "grade": cap_report.grade,
        "violations": len(cap_report.violations),
        "critical": cap_report.critical_count,
    }
def _full_pipeline_payload(info: SkillRoutingInfo) -> dict[str, Any]:
    full_result = diag_skill_full_pipeline(info.skill_md_path)
    return {
        "overall_score": full_result.overall_score,
        "overall_grade": full_result.overall_grade,
        "matching_score": full_result.phase_scores.get("matching", 0),
        "capture_score": full_result.phase_scores.get("capture", 0),
    }
class SkillActivationRouter:
    @staticmethod
    def _norm_threshold(value: Any, field: str) -> float:
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            raise TypeError(
                f"{field} 必须为 int/float，实际 {type(value).__name__}")
        try:
            normalized = float(value)
        except OverflowError:
            raise ValueError(
                f"{field} 必须为有限值，实际 {value!r}") from None
        if not math.isfinite(normalized):
            raise ValueError(f"{field} 必须为有限值，实际 {value!r}")
        if not _SCORE_MIN <= normalized <= _SCORE_MAX:
            raise ValueError(
                f"{field} 必须位于 0~1，实际 {normalized}")
        return normalized
    def __init__(self: Self, activation_threshold: float = _DEFAULT_ACTIVATION_THRESHOLD,
                 multi_skill_threshold: float = _DEFAULT_MULTI_SKILL_THRESHOLD,
                 max_active: int = _DEFAULT_MAX_ACTIVE_SKILLS) -> None:
        if isinstance(max_active, bool) or not isinstance(max_active, int):
            raise TypeError(
                f"max_active 必须为 int，实际 {type(max_active).__name__}")
        if max_active < 0:
            raise ValueError(
                f"max_active 不得为负（负值令 decide 截断切片语义反转），"
                f"实际 {max_active}")
        self.activation_threshold = self._norm_threshold(
            activation_threshold, "activation_threshold")
        self.multi_skill_threshold = self._norm_threshold(
            multi_skill_threshold, "multi_skill_threshold")
        self.max_active = max_active
        self._skills: dict[str, SkillRoutingInfo] = {}
    @staticmethod
    def _as_str(value: str | Any | None) -> str:
        return value if isinstance(value, str) else ""
    @staticmethod
    def _as_path_text(value: Any) -> str:
        if isinstance(value, os.PathLike):
            try:
                path = os.fspath(value)
            except TypeError:
                return ""
            return path if isinstance(path, str) else ""
        return value if isinstance(value, str) else ""
    def register(self: Self, name: str, description: str, keywords: list[str],
                 category: str = "", depends_on: list[str] | None = None,
                 anti_patterns: list[str] | None = None,
                 skill_md_path: str = "") -> None:
        if not isinstance(name, str) or not name.strip():
            logger.warning(
                "SkillActivationRouter.register: 无效技能名 %r（空/非字符串），跳过注册", name)
            return
        name = name.strip()
        self._skills[name] = SkillRoutingInfo(
            name=name,
            description=self._as_str(description),
            keywords=distinct_keywords(normalize_str_list(keywords)),
            category=self._as_str(category),
            depends_on=normalize_str_list(depends_on),
            anti_patterns=normalize_str_list(anti_patterns),
            skill_md_path=self._as_path_text(skill_md_path),
        )
    def register_from_metadata(self: Self, skills_metadata: dict[str, dict]) -> None:
        if not isinstance(skills_metadata, dict):
            logger.warning(
                "SkillActivationRouter.register_from_metadata: 元数据非 dict"
                "（实际 %s），跳过批量注册",
                type(skills_metadata).__name__)
            return
        for name, meta in skills_metadata.items():
            if not isinstance(meta, dict):
                logger.warning(
                    "SkillActivationRouter.register_from_metadata: 技能 %r"
                    "元数据非 dict（实际 %s），跳过该条", name,
                    type(meta).__name__)
                continue
            self.register(
                name,
                meta.get("description", ""),
                meta.get("keywords", []),
                category=meta.get("category", ""),
                depends_on=meta.get("depends_on"),
                anti_patterns=meta.get("anti_patterns"),
                skill_md_path=meta.get("skill_md_path", ""),
            )
    def route(self: Self, intent: str) -> list[tuple[str, float]]:
        if not isinstance(intent, str):
            intent = ""
        intent_lower = intent.lower()
        intent_keywords = self._intent_keywords(intent)
        scored: list[tuple[str, float]] = []
        for name, info in self._skills.items():
            score = self._calculate_match_score(intent_lower, intent_keywords, info)
            if score > 0:
                scored.append((name, score))
        scored.sort(key=lambda x: (-x[1], x[0]))
        scored = self._penalize_conflicts(scored)
        return scored[:self._score_pool_limit()]
    def _score_pool_limit(self: Self) -> int:
        return max(_SCORE_POOL_FLOOR, self.max_active)
    @staticmethod
    def _penalty_map(
            conflicts: list[tuple[str, str, float]]) -> dict[str, float]:
        penalty_map: dict[str, float] = {}
        for s1, s2, overlap in conflicts:
            penalty = overlap * _CONFLICT_PENALTY
            penalty_map[s1] = max(penalty_map.get(s1, 0.0), penalty)
            penalty_map[s2] = max(penalty_map.get(s2, 0.0), penalty)
        return penalty_map
    def _penalize_conflicts(
            self: Self,
            scored: list[tuple[str, float]]) -> list[tuple[str, float]]:
        conflicts = self._detect_conflicts([s[0] for s in scored])
        if not conflicts:
            return scored
        penalty_map = self._penalty_map(conflicts)
        penalized = [
            (name, round(score * (1.0 - penalty_map.get(name, 0.0)), 3))
            for name, score in scored
        ]
        penalized.sort(key=lambda x: (-x[1], x[0]))
        return penalized
    def decide(self: Self, intent: str) -> ActivationDecision:
        scored = self.route(intent)
        decision = ActivationDecision()
        if not scored:
            return decision
        top_name, top_score = scored[0]
        if top_score < self.activation_threshold:
            self._reject_all(decision, scored, "below_threshold")
            return decision
        for name, score in scored:
            self._classify_candidate(decision, name, score, top_name, top_score)
        self._trim_overflow(decision)
        self._collect_cascade_dependencies(decision)
        self._append_conflict_warnings(decision)
        return decision
    @staticmethod
    def _reject_all(decision: ActivationDecision,
                    scored: list[tuple[str, float]], reason: str) -> None:
        for name, _score in scored:
            decision.rejected_skills.append(name)
            decision.rejection_reasons[name] = reason
    def _classify_candidate(self: Self, decision: ActivationDecision, name: str,
                            score: float, top_name: str, top_score: float) -> None:
        if name == top_name:
            decision.activated_skills.append(name)
            decision.confidence_scores[name] = score
        elif score < self.activation_threshold:
            decision.rejected_skills.append(name)
            decision.rejection_reasons[name] = "below_threshold"
        elif top_score - score > self.multi_skill_threshold:
            decision.rejected_skills.append(name)
            decision.rejection_reasons[name] = "below_multi_skill_band"
        else:
            decision.activated_skills.append(name)
            decision.confidence_scores[name] = score
    def _trim_overflow(self: Self, decision: ActivationDecision) -> None:
        overflow = decision.activated_skills[self.max_active:]
        if not overflow:
            return
        for name in overflow:
            decision.confidence_scores.pop(name, None)
            decision.rejection_reasons[name] = "exceeds_max_active"
        decision.rejected_skills.extend(overflow)
        decision.activated_skills = decision.activated_skills[: self.max_active]
    def _collect_cascade_dependencies(self: Self, decision: ActivationDecision) -> None:
        skipped = set(decision.activated_skills)
        queue = list(decision.activated_skills)
        while queue:
            info = self._skills.get(queue.pop(0))
            if info is None:
                continue
            for dep in info.depends_on:
                if dep in self._skills and dep not in skipped:
                    decision.cascade_dependencies.append(dep)
                    skipped.add(dep)
                    queue.append(dep)
        cascade = set(decision.cascade_dependencies)
        decision.rejected_skills = [
            name for name in decision.rejected_skills if name not in cascade]
        for name in cascade:
            decision.rejection_reasons.pop(name, None)
    def _append_conflict_warnings(self: Self, decision: ActivationDecision) -> None:
        for s1, s2, overlap in self._detect_conflicts(list(decision.activated_skills)):
            decision.conflict_warnings.append(
                f"{s1} 与 {s2} 功能重叠 {overlap:.0%}（已施加惩罚）"
            )
    @staticmethod
    def _clamped_ratio(hits: int, total: int) -> float:
        return min(hits / total, 1.0) if total else 0.0
    def _calculate_match_score(self: Self, intent_lower: str, intent_keywords: list[str],
                               info: SkillRoutingInfo) -> float:
        for anti in info.anti_patterns:
            if contains_term(anti, intent_lower):
                return 0.0
        score = 0.0
        intent_keyword_set = set(intent_keywords)
        keyword_hits = sum(
            1 for kw in info.keywords if contains_term(kw, intent_lower))
        score += self._clamped_ratio(keyword_hits, len(info.keywords)) * _W_KEYWORD
        desc_keywords = self._intent_keywords(info.description)
        overlap = len(set(desc_keywords) & intent_keyword_set)
        score += self._clamped_ratio(overlap, len(intent_keyword_set)) * _W_DESCRIPTION
        if info.category and contains_term(info.category, intent_lower):
            score += _W_CATEGORY
        name_words = self._intent_keywords(info.name)
        name_overlap = len(set(name_words) & intent_keyword_set)
        score += self._clamped_ratio(name_overlap, len(set(name_words))) * _W_NAME
        return round(min(score, 1.0), 3)
    @staticmethod
    def _intent_keywords(text: str) -> list[str]:
        text_lower = text.lower()
        words: list[str] = []
        for token in _WORD_RE.findall(text_lower):
            if _CJK_SEGMENT_RE.search(token):
                words.extend(_LATIN_RUN_RE.findall(token))
            else:
                words.append(token)
        cjk_segments = _CJK_SEGMENT_RE.findall(text_lower)
        cjk_bigrams = [seg[i] + seg[i + 1]
                       for seg in cjk_segments
                       for i in range(len(seg) - 1)]
        tokens = words + cjk_bigrams
        return [w for w in tokens
                if len(w) > 1
                and w not in _STOPWORDS
                and w not in _CN_STOP_BIGRAMS]
    def _detect_conflicts(self: Self, skill_names: list[str]) -> list[tuple[str, str, float]]:
        conflicts: list[tuple[str, str, float]] = []
        for s1, s2 in combinations(skill_names, 2):
            if s1 not in self._skills or s2 not in self._skills:
                continue
            overlap = self._calculate_overlap(s1, s2)
            if overlap > _CONFLICT_OVERLAP_THRESHOLD:
                conflicts.append((s1, s2, overlap))
        return conflicts
    def _calculate_overlap(self: Self, name1: str, name2: str) -> float:
        info1 = self._skills.get(name1)
        info2 = self._skills.get(name2)
        if info1 is None or info2 is None:
            logger.warning(
                "_calculate_overlap 未注册技能 %r/%r，重叠度按 0 处理",
                name1, name2)
            return 0.0
        kw1 = {k.lower() for k in info1.keywords}
        kw2 = {k.lower() for k in info2.keywords}
        desc1 = set(self._intent_keywords(info1.description))
        desc2 = set(self._intent_keywords(info2.description))
        overlaps: list[float] = []
        if kw1 or kw2:
            overlaps.append(self._clamped_ratio(
                len(kw1 & kw2), len(kw1 | kw2)))
        if desc1 or desc2:
            overlaps.append(self._clamped_ratio(
                len(desc1 & desc2), len(desc1 | desc2)))
        return _mean(overlaps)
    def diag_matching_quality(self: Self, skill_name: str = "") -> dict[str, Any]:
        targets, missing_requested = self._resolve_diag_targets(skill_name)
        reports = self._build_matching_reports(targets)
        self._run_diag_enhancements(reports)
        return self._summarize_diag_reports(reports, missing_requested)
    def _resolve_diag_targets(
            self: Self, skill_name: str,
    ) -> tuple[list[tuple[str, SkillRoutingInfo]], list[str]]:
        if not isinstance(skill_name, str):
            skill_name = str(skill_name) if skill_name else ""
        skill_name = skill_name.strip()
        if not skill_name:
            return list(self._skills.items()), []
        info = self._skills.get(skill_name)
        if info is None:
            return [], [skill_name]
        return [(skill_name, info)], []
    @staticmethod
    def _build_matching_reports(
            targets: list[tuple[str, SkillRoutingInfo]]) -> list[dict[str, Any]]:
        diagnoser = MatchingRuleDiagnoser()
        return [
            _matching_report_entry(
                name, diagnoser.diag(name, info.description, info.keywords))
            for name, info in targets
        ]
    def _run_diag_enhancements(self: Self,
                               reports: list[dict[str, Any]]) -> None:
        capture_box: dict[str, CaptureRuleDiagnoser] = {}
        _apply_diag_enhancement(self._skills, reports, _EnhancementChannel(
            _FIELD_CAPTURE_DIAG, "捕捉阶段诊断降级", "CaptureRuleDiagnoser",
            lambda info: _capture_diag_payload(info, capture_box)))
        _apply_diag_enhancement(self._skills, reports, _EnhancementChannel(
            _FIELD_FULL_PIPELINE, "全链路诊断降级",
            "diag_skill_full_pipeline", _full_pipeline_payload))
    @staticmethod
    def _summarize_diag_reports(
            reports: list[dict[str, Any]],
            missing_requested: list[str]) -> dict[str, Any]:
        return {
            "total": len(reports),
            "avg_score": round(
                sum(r["score"] for r in reports) / max(len(reports), 1), 1),
            "reports": reports,
            "requested_missing": missing_requested,
        }
def quick_route(user_intent: str, skills_metadata: dict[str, dict],
                threshold: float = _DEFAULT_ACTIVATION_THRESHOLD) -> ActivationDecision:
    router = SkillActivationRouter(activation_threshold=threshold)
    router.register_from_metadata(skills_metadata)
    return router.decide(user_intent)
def _feedback_field(tf: Any, key: str, default: Any = None) -> Any:
    if isinstance(tf, Mapping):
        return tf.get(key, default)
    return getattr(tf, key, default)
def trigger_feedback_message(tf: Any) -> str | None:
    recommendation = _feedback_field(tf, "recommendation")
    trigger_word = _feedback_field(tf, "trigger_word", "")
    precision = _feedback_field(tf, "precision", 0.0)
    recall = _feedback_field(tf, "recall", 0.0)
    if recommendation == "remove":
        return f"触发词 '{trigger_word}' 误报率高(precision={precision})，建议移除"
    if recommendation == "reduce":
        return (f"触发词 '{trigger_word}' 精度偏低(precision={precision})，"
                "建议收窄使用范围")
    if recommendation == "boost":
        return (f"触发词 '{trigger_word}' 漏触发多(recall={recall})，"
                "建议增强覆盖/添加同义词")
    return None
@dataclass
class TriggerFeedback:
    trigger_word: str = ""
    total_activations: int = 0
    correct_activations: int = 0
    false_positives: int = 0
    missed_activations: int = 0
    precision: float = 0.0
    recall: float = 0.0
    f1_score: float = 0.0
    recommendation: str = "keep"
    def to_dict(self) -> dict[str, Any]:
        return {
            "trigger_word": self.trigger_word,
            "total_activations": self.total_activations,
            "correct_activations": self.correct_activations,
            "false_positives": self.false_positives,
            "missed_activations": self.missed_activations,
            "precision": self.precision,
            "recall": self.recall,
            "f1_score": self.f1_score,
            "recommendation": self.recommendation,
        }
def _recommend_from_metrics(total: int, evaluations: int, missed: int,
                           precision: float, recall: float) -> str:
    if total == 0 and missed == 0:
        return "keep"
    if evaluations == 0:
        return "boost"
    if precision < 0.3:
        return "remove"
    if precision < 0.5:
        return "reduce"
    if recall < 0.3:
        return "boost"
    return "keep"
def _new_trigger_stats() -> dict[str, int]:
    return {
        "total": 0,
        "correct": 0,
        "false_positive": 0,
        "missed": 0,
    }
class TriggerFeedbackLoop:
    def __init__(self) -> None:
        self._trigger_stats: dict[str, dict[str, int]] = {}
    @staticmethod
    def _norm_trigger(trigger_word: Any) -> str:
        return trigger_word.strip() if isinstance(trigger_word, str) else ""
    def _stats(self, trigger_word: str) -> dict[str, int]:
        stats = self._trigger_stats.get(trigger_word)
        if stats is None:
            stats = _new_trigger_stats()
            self._trigger_stats[trigger_word] = stats
        return stats
    def record_trigger(self, trigger_word: str, *, outcome: str = "correct") -> None:
        trigger_word = self._norm_trigger(trigger_word)
        if not trigger_word:
            return
        if outcome not in ("correct", "false_positive", "missed"):
            logger.warning(
                "record_trigger 拒绝未知结果 %r（触发词 %r）", outcome, trigger_word)
            return
        stats = self._stats(trigger_word)
        if outcome != "missed":
            stats["total"] += 1
        stats[outcome] += 1
    def compute_feedback(self, trigger_word: str) -> TriggerFeedback:
        trigger_word = self._norm_trigger(trigger_word)
        stats = self._trigger_stats.get(trigger_word)
        if stats is None:
            stats = _new_trigger_stats()
        total = stats["total"]
        correct = stats["correct"]
        fp = stats["false_positive"]
        missed = stats["missed"]
        raw_precision = correct / (correct + fp) if (correct + fp) > 0 else 0.0
        raw_recall = correct / (correct + missed) if (correct + missed) > 0 else 0.0
        precision = round(raw_precision, 3)
        recall = round(raw_recall, 3)
        f1 = round((2 * raw_precision * raw_recall / (raw_precision + raw_recall)
                    if (raw_precision + raw_recall) > 0 else 0.0), 3)
        recommendation = _recommend_from_metrics(
            total, correct + fp, missed, raw_precision, raw_recall)
        return TriggerFeedback(
            trigger_word=trigger_word,
            total_activations=total,
            correct_activations=correct,
            false_positives=fp,
            missed_activations=missed,
            precision=precision,
            recall=recall,
            f1_score=f1,
            recommendation=recommendation,
        )
    def get_recommendations(self) -> list[TriggerFeedback]:
        return [self.compute_feedback(tw) for tw in self._trigger_stats]
def evaluate_trigger_feedback(
    skill_name: str,
    description: str,
    keywords: list[str] | None = None,
) -> TriggerFeedbackLoop:
    keywords = distinct_keywords(keywords)
    loop = TriggerFeedbackLoop()
    if not keywords:
        return loop
    examples = list(_iter_corpus_items(
        generate_trigger_examples(
            skill_name, description, keywords, num_positive=len(keywords)),
        "feedback"))
    for example in examples:
        _record_example_hits(loop, keywords, example)
    return loop
def _record_example_hits(
    loop: TriggerFeedbackLoop,
    keywords: list[str],
    example: dict[str, Any],
) -> None:
    query = normalize_text(example.get("query", "")).lower()
    should_trigger = _flag_true(example.get("should_trigger", ""))
    matched = {kw for kw in keywords if keyword_matches(kw, query)}
    for kw in keywords:
        if kw in matched:
            loop.record_trigger(
                kw, outcome="correct" if should_trigger else "false_positive")
        elif should_trigger:
            loop.record_trigger(kw, outcome="missed")
_TRIGGER_GUIDE_STEMS = ('trigger', 'when', 'activate')
_TRIGGER_GUIDE_WORDS = ('use this skill', '当用户', '时触发', '使用本技能', '触发条件')
_NEGATIVE_DEFENSE_WORDS = (
    'not for', "don't use", 'do not use', 'never use', 'avoid',
    '不适用', '不用于', '不要用于', '禁止', '请勿',
    '不负责', '不处理', '仅限于', '仅用于', '除非', '除外',
)
_WEAK_ACTION_STEMS = ('create', 'edit', 'generate', 'analyze', 'build',
                      'search', 'convert', 'extract', 'read', 'write', 'process')
_WEAK_ACTION_WORDS = ('创建', '新建', '编辑', '修改', '生成', '分析', '构建',
                      '搜索', '检索', '转换', '提取', '读取', '写入', '处理',
                      '诊断', '审查', '优化', '合并', '校验', '验证')
_EXAMPLE_STEMS = ('example',)
_EXAMPLE_WORDS = ('e.g.', 'such as', 'like', '例如', '比如', '口语化触发', '用户说')
MIN_KEYWORD_COUNT = 5
KEYWORD_GOOD_COUNT = 10
KEYWORD_TARGET_COUNT = 15
def distinct_keywords(keywords: list[str] | None) -> list[str]:
    seen: set[str] = set()
    distinct: list[str] = []
    for kw in normalize_keywords(keywords):
        key = kw.casefold()
        if key in seen:
            continue
        seen.add(key)
        distinct.append(kw)
    return distinct
def _text_hits(text_lower: str, stems: tuple[str, ...] = (),
               words: tuple[str, ...] = ()) -> bool:
    return (any(stem_matches(s, text_lower) for s in stems)
            or any(keyword_matches(w, text_lower) for w in words))
def _trigger_kw_count_score(keywords: list[str]) -> int:
    count = len(distinct_keywords(keywords))
    if count >= KEYWORD_TARGET_COUNT:
        return 30
    if count >= KEYWORD_GOOD_COUNT:
        return 25
    if count >= MIN_KEYWORD_COUNT:
        return 15
    return 10 if count >= 3 else 0
def kw_language_flags(keywords: list[str]) -> tuple[bool, bool]:
    keywords = normalize_keywords(keywords)
    has_local = any(_NON_LATIN_SCRIPT_RE.search(kw)
                    for kw in keywords if isinstance(kw, str))
    has_latin = any(_LATIN_LETTER_RE.search(kw)
                    for kw in keywords if isinstance(kw, str))
    return has_local, has_latin
def _keyword_coverage_score(keywords: list[str]) -> float:
    score = float(_trigger_kw_count_score(keywords))
    has_cn, has_en = kw_language_flags(keywords)
    if has_cn and has_en:
        return score + 20
    if has_cn or has_en:
        return score + 10
    return score
def _description_framing_score(desc_lower: str) -> float:
    score = 0.0
    if _text_hits(desc_lower, _TRIGGER_GUIDE_STEMS, _TRIGGER_GUIDE_WORDS):
        score += 20
    if _text_hits(desc_lower, (), _NEGATIVE_DEFENSE_WORDS):
        score += 15
    return score
def _name_quality_score(name: str) -> float:
    return 15.0 if len(name) >= 5 and ("-" in name or "_" in name) else 0.0
def score_triggers(description: str, keywords: list[str], name: str) -> float:
    keywords = normalize_keywords(keywords)
    description = normalize_text(description)
    name = normalize_text(name)
    return min(
        _keyword_coverage_score(keywords)
        + _description_framing_score(description.lower())
        + _name_quality_score(name),
        100,
    )
class AutoDisclosureOptimizer:
    @staticmethod
    def _check_missing_trigger_guide(description: str) -> str | None:
        if not _text_hits(description,
                          _TRIGGER_GUIDE_STEMS, _TRIGGER_GUIDE_WORDS):
            return "描述缺少触发引导词（trigger/when/activate），建议添加"
        return None
    @staticmethod
    def _check_missing_negative_defense(description: str) -> str | None:
        if not _text_hits(description, (), _NEGATIVE_DEFENSE_WORDS):
            return "描述缺少反向排除（NOT for/不适用），建议添加负面边界"
        return None
    @staticmethod
    def _check_weak_action_verbs(description: str) -> str | None:
        if not _text_hits(description,
                          _WEAK_ACTION_STEMS, _WEAK_ACTION_WORDS):
            return "描述缺少强动作动词（create/edit/generate等），建议添加"
        return None
    @staticmethod
    def _check_no_example(description: str) -> str | None:
        if not _text_hits(description,
                          _EXAMPLE_STEMS, _EXAMPLE_WORDS):
            return "描述缺少示例（example/例如），建议添加使用示例"
        return None
    def analyze(self: Self, description: str, keywords: list[str]) -> list[str]:
        description = normalize_text(description).lower()
        keywords = normalize_keywords(keywords)
        suggestions: list[str] = []
        content_results = [
            c(description) for c in
            (self._check_missing_trigger_guide,
             self._check_missing_negative_defense,
             self._check_weak_action_verbs,
             self._check_no_example)
        ]
        suggestions.extend(r for r in content_results if r)
        distinct_count = len(distinct_keywords(keywords))
        if distinct_count < MIN_KEYWORD_COUNT:
            suggestions.append(
                f"关键词数量不足({distinct_count}<{MIN_KEYWORD_COUNT})，"
                f"建议补充至少{MIN_KEYWORD_COUNT}个关键词")
        has_cn, has_en = kw_language_flags(keywords)
        if not has_cn:
            suggestions.append(
                "关键词缺少本地语言（中文/日/韩等非拉丁文字）覆盖，建议添加对应触发词")
        if not has_en:
            suggestions.append("关键词缺少英文覆盖，建议添加英文触发词")
        return suggestions
_GENERIC_TOKENS = frozenset({
    "analysis", "code", "create", "build", "generate", "process",
    "convert", "extract", "search", "read", "write", "edit",
    "doc", "docs", "web", "api", "tool", "tools", "data", "auto",
    "skill", "skills",
})
def _normalize_coexisting_skills(existing_skills: Any) -> list:
    if existing_skills is None:
        return []
    if isinstance(existing_skills, str):
        return [existing_skills] if existing_skills.strip() else []
    if isinstance(existing_skills, dict):
        if "name" in existing_skills:
            return [existing_skills]
        return [{"name": str(key)} for key in existing_skills
                if str(key).strip()]
    if isinstance(existing_skills, (set, frozenset)):
        return sorted(existing_skills, key=_coexisting_skill_name)
    if isinstance(existing_skills, (list, tuple)):
        return list(existing_skills)
    return []
def _coexisting_skill_name(other: object) -> str:
    if isinstance(other, str):
        return other
    if isinstance(other, dict):
        other_name = other.get("name", "")
        if not isinstance(other_name, str):
            return "" if other_name is None else str(other_name)
        return other_name
    return ""
def _coexisting_related(other_name: str, hay: str) -> bool:
    normalized_name = other_name.strip().lower()
    if not normalized_name:
        return False
    if contains_term(normalized_name, hay):
        return True
    if len(normalized_name) < 3:
        return False
    parts = [t.lower() for t in re.split(r"[-_\s]+", normalized_name) if t]
    meaningful = [
        part for part in parts
        if len(part) >= 3 and part not in _GENERIC_TOKENS
    ]
    return any(contains_term(part, hay) for part in meaningful)
def _suggest_differentiation(skill_name: str, description: str,
                             keywords: list[str], existing_skills: list) -> list[str]:
    suggestions: list[str] = []
    hay = f"{skill_name} {description} {' '.join(keywords)}".lower()
    skill_key = skill_name.casefold()
    for other in existing_skills:
        other_name = _coexisting_skill_name(other).strip()
        if not other_name or other_name.casefold() == skill_key:
            continue
        if not _coexisting_related(other_name, hay):
            continue
        if other_name.lower() in description.lower():
            continue
        suggestions.append(
            f"与已有技能 '{other_name}' 同目录共存，建议在 description/keywords 中明确差异化定位")
    return suggestions
def _keyword_volume_advice(keywords: list[str]) -> list[str]:
    distinct_count = len(distinct_keywords(keywords))
    if distinct_count < MIN_KEYWORD_COUNT:
        return [
            (f"关键词数量偏少({distinct_count}个)，"
             f"建议至少{MIN_KEYWORD_COUNT}个覆盖核心场景"),
        ]
    return []
def _primary_trigger_advice(skill_name: str, keywords: list[str]) -> list[str]:
    if skill_name and skill_name.casefold() not in {
            kw.casefold() for kw in keywords}:
        return [f"建议添加技能名 '{skill_name}' 作为主干触发词"]
    return []
def _description_heat_advice(description: str) -> list[str]:
    if not description or len(description) < 30:
        return ["description 过短，建议补充触发场景描述以提升被 Agent 识别概率"]
    return []
def _has_negative_declaration(description: str, keywords: list[str]) -> bool:
    if any(keyword_matches(marker, kw.lower()) for kw in keywords
           for marker in _NEGATIVE_DEFENSE_WORDS):
        return True
    desc_lower = description.lower()
    return any(keyword_matches(marker, desc_lower)
               for marker in _NEGATIVE_DEFENSE_WORDS)
def _negative_exclusion_advice(description: str, keywords: list[str]) -> list[str]:
    if _has_negative_declaration(description, keywords):
        return []
    return ["建议添加反向排除关键词（如'不适用场景'）以降低误触发率"]
def recommend_cold_start(skill_name: str, description: str = "",
                         keywords: list[str] | None = None,
                         existing_skills: list[Any] | None = None) -> list[str]:
    skill_name = normalize_text(skill_name)
    description = normalize_text(description)
    existing_skills = _normalize_coexisting_skills(existing_skills)
    keywords = normalize_keywords(keywords)
    recommendations = _suggest_differentiation(
        skill_name, description, keywords, existing_skills)
    recommendations += _keyword_volume_advice(keywords)
    recommendations += _primary_trigger_advice(skill_name, keywords)
    recommendations += _description_heat_advice(description)
    recommendations += _negative_exclusion_advice(description, keywords)
    return list(dict.fromkeys(recommendations))

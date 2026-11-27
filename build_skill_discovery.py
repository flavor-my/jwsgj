from __future__ import annotations

import json
import logging
import math
import os
import threading
import time
from collections import Counter, defaultdict
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Any

import yaml

from jwsgj.build_discover_sixdim import (
    clamp_description_to_hard_limit,
    enhance_skill_discoverability,
)
from jwsgj.build_matching_diagnoser import (
    CaptureRuleDiagnoser,
    diag_skill_full_pipeline,
    get_diagnoser,
)
from jwsgj.build_skill_consistency import (
    MatchingConflictDetector,
    MetadataOptimizationResult,
    SkillMetadataOptimizer,
    assess_description_generation,
)
from jwsgj.build_text_document import (
    ENTRY_DOC_NAME,
    is_skill_dir,
    normalize_text,
    resolve_entry_document,
    safe_is_dir,
)
from jwsgj.build_text_frontmatter import (
    INLINE_KEYWORDS_MAX,
    frontmatter_keywords,
    is_frontmatter_fence,
    locate_frontmatter_body_start,
    normalize_description_field,
    purify_skill_md,
    read_meta_degraded,
    read_skill_md,
    update_frontmatter_desc_keywords,
)
from jwsgj.build_text_scoring import (
    DESC_MIN_LENGTH,
    LOW_TRIGGER_SCORE,
    NEGATIVE_COMMANDS,
    TRIGGER_COMMANDS,
    detect_vague_words,
    keyword_matches,
    normalize_keywords,
)
from jwsgj.build_trigger_activation import (
    KEYWORD_GOOD_COUNT,
    KEYWORD_TARGET_COUNT,
    MIN_KEYWORD_COUNT,
    AutoDisclosureOptimizer,
    TriggerFeedback,
    distinct_keywords,
    evaluate_trigger_feedback,
    kw_language_flags,
    recommend_cold_start,
    score_triggers,
    trigger_feedback_message,
)
from jwsgj.diag_types_vocab import (
    DESC_MAX,
    FIELD_DISCOVERABILITY_INDEX,
    FIELD_EXPECTED_IMPACT,
    FIELD_OPTIMIZED_DESCRIPTION,
    FIELD_RECOMMENDATIONS,
)
from jwsgj.engine_a4_doc_code import DocCodeConsistencyAnalyzer
from jwsgj.log_config import (
    STATE_FILE_SKILL_HOTNESS,
    get_log_dir,
    locked_artifact,
    log_swallowed,
    write_module_run,
)
from jwsgj.shared_cache import CacheNotWarmedError, require_warmed

_log = logging.getLogger(__name__)
__all__ = [
    'DiscoverabilityDiagnoser',
    'DiscoverabilitySkillHealth',
    'DocQualityEngine',
    'HotnessTracker',
    'SkillHotness',
    'analyze_skill_discoverability',
    'apply_full_discoverability',
    'average_overall_score',
    'default_hotness_store',
    'evaluate_skill_hotness',
    'evaluate_skill_hotness_for_dir',
    'optimize_creation_discoverability',
    'quick_diag_skill_dir',
    'resolve_analyze_input',
    'run_c2_doc_quality_engine',
    'run_dimension_diagnostics',
    'safe_hotness_section',
]
def _path_arg(value: Any) -> Path | None:
    if isinstance(value, os.PathLike):
        try:
            value = os.fspath(value)
        except TypeError:
            return None
    if not isinstance(value, str):
        return None
    text = value.strip()
    return Path(text) if text else None
def _path_text(value: Any) -> str:
    path = _path_arg(value)
    return "" if path is None else str(path)
def _violation_rows(report: Any, message_limit: int | None = None,
                    with_rule_name: bool = False) -> list[dict]:
    rows = []
    for violation in report.violations:
        message = normalize_text(getattr(violation, "description", ""))
        if message_limit is not None:
            message = message[:message_limit]
        row = {
            "rule": normalize_text(getattr(violation, "rule_id", "")),
            "severity": normalize_text(getattr(violation, "severity", "")),
        }
        if with_rule_name:
            row["name"] = normalize_text(getattr(violation, "rule_name", ""))
        rows.append({**row, "message": message})
    return rows
def _report_diag_block(
        report: Any, prefix: str, message_limit: int | None = None,
        with_rule_name: bool = False, include_failed: bool = True,
        extra: dict | None = None, quality_checks: dict | None = None,
        check_prefix: str | None = None) -> dict:
    block = {
        f"{prefix}_score": report.overall_score,
        f"{prefix}_grade": report.grade,
        f"{prefix}_violations": _violation_rows(
            report, message_limit=message_limit, with_rule_name=with_rule_name),
        f"{prefix}_passed": report.passed_rules,
    }
    if include_failed:
        block[f"{prefix}_failed"] = report.failed_rules
    if extra:
        block.update(extra)
    if isinstance(quality_checks, dict) and check_prefix:
        quality_checks[f"{check_prefix}_score"] = report.overall_score
        quality_checks[f"{check_prefix}_grade"] = report.grade
        if report.critical_count > 0:
            quality_checks[f"{check_prefix}_critical"] = report.critical_count
    return block
def _run_matching_diag(
        name: str, enhanced_desc: str, expanded_kw: list,
        quality_checks: dict) -> dict:
    matching_diag = {}
    try:
        matching_report = get_diagnoser().diag(name, enhanced_desc, expanded_kw)
        matching_diag = _report_diag_block(
            matching_report, "matching", quality_checks=quality_checks,
            check_prefix="matching_rules")
        _log.info("[init] 匹配规则诊断: score=%.0f, grade=%s, violations=%d",
                  matching_report.overall_score, matching_report.grade,
                  len(matching_report.violations))
    except Exception as e:  # noqa: BLE001
        _log.warning("[init] 匹配规则诊断失败，跳过: %s: %s",
                     type(e).__name__, e)
    return matching_diag
def _run_capture_diag(
        target_dir: str, enhanced_desc: str, quality_checks: dict) -> dict:
    capture_diag = {}
    raw_target_dir = target_dir
    target_dir = _path_text(target_dir)
    if not target_dir:
        _log.warning("[init] 捕捉规则诊断跳过：target_dir 非法: %r",
                     raw_target_dir)
        return capture_diag
    try:
        entry = resolve_entry_document(target_dir)
        skill_md_for_capture = (os.fspath(entry) if entry is not None
                                else str(Path(target_dir) / ENTRY_DOC_NAME))
        if os.path.exists(skill_md_for_capture):
            capture_report = CaptureRuleDiagnoser().diag(
                skill_md_for_capture, description=enhanced_desc)
            capture_diag = _report_diag_block(
                capture_report, "capture", message_limit=120,
                with_rule_name=True,
                extra={"capture_body_lines": capture_report.body_lines},
                quality_checks=quality_checks,
                check_prefix="capture_rules")
            _log.info(
                "[init] 捕捉规则诊断: score=%.0f, grade=%s, violations=%d",
                capture_report.overall_score, capture_report.grade,
                len(capture_report.violations),
            )
    except Exception as e:  # noqa: BLE001
        _log.warning("[init] 捕捉规则诊断失败，跳过: %s: %s",
                     type(e).__name__, e)
    return capture_diag
def _run_description_diag(
        name: str, expanded_kw: list, quality_checks: dict) -> dict:
    description_optimization = {}
    try:
        gen_result = assess_description_generation(
            name, expanded_kw)["generation"]
        description_optimization = {
            "generated_description": gen_result["template"].generated_description,
            **_report_diag_block(
                gen_result["diag"], "gen_diag", message_limit=120,
                include_failed=False, quality_checks=quality_checks,
                check_prefix="description_gen"),
        }
        _log.info(
            "[init] description 生成诊断: score=%.0f, grade=%s",
            gen_result["diag"].overall_score, gen_result["diag"].grade,
        )
    except Exception as e:  # noqa: BLE001
        _log.warning("[init] description 生成诊断失败，跳过: %s: %s",
                     type(e).__name__, e)
    return description_optimization
def run_dimension_diagnostics(
    *,
    name: str,
    description: str,
    keywords: list,
    target_dir: str,
    quality_checks: dict | None = None,
) -> dict[str, dict]:
    checks = quality_checks if isinstance(quality_checks, dict) else {}
    name = normalize_text(name)
    description = normalize_text(description)
    keywords = normalize_keywords(keywords)
    target_dir = _path_text(target_dir)
    return {
        "matching_diag": _run_matching_diag(
            name, description, keywords, checks),
        "capture_diag": _run_capture_diag(target_dir, description, checks),
        "description_optimization": _run_description_diag(
            name, keywords, checks),
    }
@dataclass(frozen=True)
class _DiscoverabilityView:
    description: str
    keywords: list
    index: Any
    dimensions: dict[str, float]
def _quality_dimensions(disc_result: dict) -> dict[str, float]:
    details = disc_result.get("quality_details")
    dimensions = details.get("dimensions") if isinstance(details, dict) else None
    if not isinstance(dimensions, dict):
        return {}
    result: dict[str, float] = {}
    for key, value in dimensions.items():
        if (not isinstance(key, str) or isinstance(value, bool)
                or not isinstance(value, (int, float))):
            continue
        try:
            numeric = float(value)
        except (OverflowError, ValueError) as _swallowed_exc:
            log_swallowed(
                __name__, _swallowed_exc,
                context=f'_quality_dimensions:{type(_swallowed_exc).__name__}')
            continue
        if math.isfinite(numeric):
            result[key] = numeric
    return result
def _clamp_view_description(view: _DiscoverabilityView) -> _DiscoverabilityView:
    clamped = clamp_description_to_hard_limit(view.description)
    if clamped == view.description:
        return view
    return replace(view, description=clamped)
def _normalize_disc_result(
        disc_result: dict, description: str,
        keywords: list) -> _DiscoverabilityView:
    if not isinstance(disc_result, dict):
        disc_result = {}
    index = disc_result.get(FIELD_DISCOVERABILITY_INDEX)
    if index is None:
        index = disc_result.get("quality_score")
    if index is None:
        index = 0
    index = min(max(_sanitize_metric(index), 0.0), 100.0)
    optimized = disc_result.get(FIELD_OPTIMIZED_DESCRIPTION)
    if not isinstance(optimized, str) or not optimized.strip():
        optimized = normalize_text(description)
    return _DiscoverabilityView(
        description=optimized,
        keywords=(normalize_keywords(disc_result.get("keywords"))
                  or normalize_keywords(keywords)),
        index=index,
        dimensions=_quality_dimensions(disc_result),
    )
_QUALITY_DIM_PASS = 0.5
def _dimension_passed(dimensions: dict[str, float],
                      *keys: str) -> bool | None:
    for key in keys:
        value = dimensions.get(key)
        if value is not None:
            return value >= _QUALITY_DIM_PASS
    return None
def _keywords_embedded_in(description: str, keywords: list) -> bool:
    unique_kws: dict[str, str] = {}
    for kw in keywords:
        text = normalize_text(kw)
        if text:
            unique_kws.setdefault(text.casefold(), text)
    top_kws = list(unique_kws.values())[:INLINE_KEYWORDS_MAX]
    if not top_kws:
        return False
    desc_lower = description.lower()
    hits = sum(1 for kw in top_kws if keyword_matches(kw, desc_lower))
    return hits / len(top_kws) >= _QUALITY_DIM_PASS
def _build_quality_checks(view: _DiscoverabilityView) -> dict:
    dimensions = view.dimensions
    has_trigger = _dimension_passed(dimensions, "has_trigger_command")
    if has_trigger is None:
        has_trigger = any(
            keyword_matches(cmd, view.description.lower())
            for cmd in TRIGGER_COMMANDS)
    has_negative = _dimension_passed(dimensions, "has_negative_rule")
    if has_negative is None:
        desc_lower = view.description.lower()
        has_negative = any(
            keyword_matches(cmd, desc_lower) for cmd in NEGATIVE_COMMANDS)
    has_embedded = _dimension_passed(
        dimensions, "has_keywords_coverage", "has_keywords_embedded")
    if has_embedded is None:
        has_embedded = _keywords_embedded_in(view.description, view.keywords)
    return {
        "has_trigger_command": has_trigger,
        "has_negative_rule": has_negative,
        "has_keywords_embedded": has_embedded,
        "length_optimal": DESC_MIN_LENGTH <= len(view.description) <= DESC_MAX,
        "vague_words_clean": not detect_vague_words(view.description),
        FIELD_DISCOVERABILITY_INDEX: view.index,
    }
def apply_full_discoverability(
        target_dir: str,
        name: str,
        description: str,
        skill_type: str,
        keywords: list) -> dict:
    name = normalize_text(name)
    description = normalize_text(description)
    target_dir = _path_text(target_dir)
    if not target_dir or not Path(target_dir).is_dir():
        _log.warning("[init] apply_full_discoverability: target_dir 非法: %r",
                     target_dir)
        return {
            "skill_name": name,
            "enhanced_description": description,
            "expanded_keywords": normalize_keywords(keywords),
            FIELD_DISCOVERABILITY_INDEX: 0,
            "quality_checks": {}, "matching_diag": {}, "capture_diag": {},
            "description_optimization": {},
            "frontmatter_written": False,
            "error": "target_dir 必须为已存在的目录",
        }
    keywords = normalize_keywords(keywords)
    _t0 = time.monotonic()
    disc_result = enhance_skill_discoverability(
        skill_name=name,
        description=description,
        keywords=keywords,
        skill_type=skill_type,
    )
    view = _clamp_view_description(
        _normalize_disc_result(disc_result, description, keywords))
    quality_checks = _build_quality_checks(view)
    _log.info("[init] 六域可发现性优化: index=%s", view.index)
    diag_blocks = run_dimension_diagnostics(
        name=name,
        description=view.description,
        keywords=view.keywords,
        target_dir=target_dir,
        quality_checks=quality_checks,
    )
    write_error: str | None = None
    frontmatter_written = False
    entry = resolve_entry_document(target_dir)
    if entry is None:
        write_error = "未找到入口文档，frontmatter 未写入"
        _log.warning("[init] %s: %s", write_error, target_dir)
    else:
        skill_md_path = os.fspath(entry)
        frontmatter_written = update_frontmatter_desc_keywords(
            skill_md_path, view.description, view.keywords)
        if frontmatter_written:
            _log.info("[init] %s frontmatter 已更新", entry.name)
            purify_skill_md(skill_md_path)
        else:
            write_error = "frontmatter 写回失败（缺锚点或落盘失败）"
            _log.warning(
                "[init] %s frontmatter 未写入（缺锚点或落盘失败）: %s",
                entry.name, skill_md_path)
    write_module_run(
        "build_skill_discovery", "apply_full_discoverability",
        outcome="ok" if frontmatter_written else "fail",
        duration_ms=(time.monotonic() - _t0) * 1000.0,
        skill=name, index=view.index,
        frontmatter_written=frontmatter_written,
        matching_diag=bool(diag_blocks["matching_diag"]),
        capture_diag=bool(diag_blocks["capture_diag"]),
        desc_gen=bool(diag_blocks["description_optimization"]))
    result = {
        "skill_name": name,
        "enhanced_description": view.description,
        "expanded_keywords": view.keywords,
        FIELD_DISCOVERABILITY_INDEX: view.index,
        "quality_checks": quality_checks,
        "frontmatter_written": frontmatter_written,
        **diag_blocks,
    }
    if write_error is not None:
        result["error"] = write_error
    return result
def optimize_creation_discoverability(
    skill_name: str, description: str, skill_type: str,
    user_keywords: list[str] | None = None,
    existing_descriptions: list[str] | None = None,
) -> tuple[MetadataOptimizationResult, dict]:
    opt_result = SkillMetadataOptimizer().optimize(
        skill_name=skill_name,
        description=description,
        skill_type=skill_type,
        user_keywords=user_keywords,
    )
    discoverability_result = enhance_skill_discoverability(
        skill_name=skill_name,
        description=opt_result.optimized_description,
        keywords=opt_result.optimized_keywords,
        skill_type=skill_type,
        existing_descs=existing_descriptions or [],
    )
    return opt_result, discoverability_result
def average_overall_score(reports: list) -> float:
    items = reports if isinstance(reports, (list, tuple)) else []
    scores = [_sanitize_metric(getattr(r, "overall_score", 0.0))
              for r in items if r is not None]
    return round(sum(scores) / len(scores), 1) if scores else 0.0
_DEFAULT_ACTIVATION_SUCCESS = True
def evaluate_skill_hotness(
    skill_name: str,
    description: str = "",
    keywords: list[str] | None = None,
    store_path: str | Path | None = None,
    record: bool = True,
    success: bool = _DEFAULT_ACTIVATION_SUCCESS,
) -> tuple[HotnessTracker, SkillHotness]:
    tracker = HotnessTracker(
        store_path=store_path if store_path is not None else default_hotness_store()
    )
    if record:
        tracker.record_activation(
            skill_name, success=_coerce_success(success))
    return tracker, tracker.compute_hotness(skill_name)
def evaluate_skill_hotness_for_dir(skill_dir: str, *,
                                   record: bool = False) -> dict:
    path = _path_arg(skill_dir)
    if path is None or not is_skill_dir(path):
        _log.warning("evaluate_skill_hotness_for_dir: 技能目录无效: %r",
                     skill_dir)
        return {"skill_name": "", "error": f"技能目录无效: {skill_dir!r}"}
    meta = read_meta_degraded(path, "evaluate_skill_hotness_for_dir")
    _tracker, hotness = evaluate_skill_hotness(
        skill_name=meta["name"], record=record)
    return hotness.to_dict()
def _is_low_frequency_activation(hotness: SkillHotness) -> bool:
    return hotness.activation_count_30d == 0 and hotness.activation_count_total >= 1
def safe_hotness_section(
    name: str,
    description: str,
    keywords: list[str],
    record_activation: bool,
    hotness_store: str | Path | None,
) -> tuple[dict[str, Any], list[str]]:
    try:
        _, hotness = evaluate_skill_hotness(
            name,
            record=record_activation,
            store_path=hotness_store,
        )
        messages: list[str] = []
        if hotness.trend == "declining":
            messages.append(
                f"技能热度呈下降趋势(近7天{hotness.activation_count_7d}次激活)，建议扩充触发词与多场景示例"
            )
        if _is_low_frequency_activation(hotness):
            messages.append(
                "技能近30天激活极少，建议扩充关键词/触发示例提升被 Agent 调用概率"
            )
        return hotness.to_dict(), messages
    except (OSError, RuntimeError, ValueError, TypeError) as exc:
        _log.warning("热度评估失败: %s", exc)
        return {}, [f"热度评估失败，已跳过（{type(exc).__name__}）"]
@dataclass
class _HealthSignals:
    issues: list[str] = field(default_factory=list)
    optimizations: list[str] = field(default_factory=list)
    def merge(self, other: _HealthSignals) -> None:
        self.issues.extend(other.issues)
        self.optimizations.extend(other.optimizations)
def _violation_issues(report: Any, *, label: str, prefix: str = "",
                     desc_limit: int | None = None) -> list[str]:
    issues: list[str] = []
    if report.critical_count > 0:
        issues.append(f"{label}严重违规({report.critical_count}项)")
    for v in report.violations:
        severity = normalize_text(getattr(v, "severity", ""))
        if severity not in ("critical", "high"):
            continue
        desc = normalize_text(getattr(v, "description", ""))
        if desc_limit is not None:
            desc = desc[:desc_limit]
        rule_id = normalize_text(getattr(v, "rule_id", ""))
        issues.append(f"[{prefix}{rule_id}] {desc}")
    return issues
def _score_matching_dimension(
    name: str, description: str, keywords: list[str],
) -> tuple[float | None, _HealthSignals]:
    signals = _HealthSignals()
    matching_score: float | None = None
    try:
        matching_report = get_diagnoser().diag(name, description, keywords)
        matching_score = matching_report.overall_score
        signals.issues.extend(
            _violation_issues(matching_report, label="匹配规则"))
    except (AttributeError, RuntimeError, ValueError, TypeError) as exc:
        _log.warning("diag_skill_directory: 匹配规则诊断失败 %s: %s", name, exc)
    return matching_score, signals
def _score_capture_dimension(
    name: str, description: str, md_file: Path,
) -> tuple[float | None, _HealthSignals]:
    signals = _HealthSignals()
    capture_score: float | None = None
    try:
        capture_report = CaptureRuleDiagnoser().diag(
            str(md_file), description=description
        )
        capture_score = capture_report.overall_score
        signals.issues.extend(_violation_issues(
            capture_report, label="捕捉规则", desc_limit=80))
    except (AttributeError, RuntimeError, ValueError, TypeError, OSError) as exc:
        _log.warning("diag_skill_directory: 捕捉规则诊断失败 %s: %s", name, exc)
    return capture_score, signals
def _score_trigger_dimension(
    name: str, description: str, keywords: list[str],
) -> tuple[float, _HealthSignals]:
    signals = _HealthSignals()
    trigger_score = 0.0
    try:
        trigger_score = score_triggers(description, keywords, name)
        signals.optimizations.extend(AutoDisclosureOptimizer().analyze(
            description, keywords))
    except (AttributeError, RuntimeError, ValueError, TypeError) as exc:
        _log.warning("diag_skill_directory: 触发维评分失败 %s: %s", name, exc)
    return trigger_score, signals
def _score_gen_dimension(
    name: str, keywords: list[str], matching_score: float | None,
) -> tuple[float | None, _HealthSignals]:
    signals = _HealthSignals()
    gen_score: float | None = None
    try:
        assessment = assess_description_generation(
            name, keywords, matching_score)
        gen_score = assessment["score"]
        signals.issues.extend(assessment["issues"])
        signals.optimizations.extend(assessment["optimizations"])
    except (AttributeError, RuntimeError, ValueError, TypeError, KeyError) as exc:
        _log.warning("diag_skill_directory: 生成描述校验失败 %s: %s", name, exc)
    return gen_score, signals
@dataclass(frozen=True)
class _DimensionScores:
    trigger_score: float
    matching_score: float | None
    capture_score: float | None
    gen_score: float | None
    def fused(self) -> float:
        fused = self.trigger_score
        if self.matching_score is not None:
            fused = fused * 0.8 + self.matching_score * 0.2
        if self.capture_score is not None:
            fused = fused * 0.9 + self.capture_score * 0.1
        return fused
def _map_score_signals(
    scores: _DimensionScores,
    keywords: list[str], description: str,
) -> _HealthSignals:
    signals = _HealthSignals()
    signals.issues.extend(_score_issue_signals(scores, keywords, description))
    signals.optimizations.extend(_score_optimization_signals(scores))
    return signals
def _score_issue_signals(
    scores: _DimensionScores, keywords: list[str], description: str,
) -> list[str]:
    issues: list[str] = []
    if scores.trigger_score < 50:
        issues.append(f"触发词评分偏低({scores.trigger_score:.0f}/100)")
    keyword_count = len(distinct_keywords(keywords))
    if keyword_count < MIN_KEYWORD_COUNT:
        issues.append(
            f"关键词数量不足({keyword_count}<{MIN_KEYWORD_COUNT})")
    if not description:
        issues.append("description 为空")
    return issues
def _score_optimization_signals(scores: _DimensionScores) -> list[str]:
    optimizations: list[str] = []
    if scores.trigger_score < 70:
        optimizations.append("建议优化触发词覆盖度")
    if scores.matching_score is not None and scores.matching_score < 50:
        optimizations.append(
            f"匹配规则评分偏低({scores.matching_score:.0f}/100)，"
            "建议优化 description 触发覆盖"
        )
    if scores.capture_score is not None and scores.capture_score < 50:
        optimizations.append(
            f"捕捉规则评分偏低({scores.capture_score:.0f}/100)，"
            "建议优化 SKILL.md 正文结构"
        )
    if scores.gen_score is not None and scores.gen_score < 50:
        optimizations.append(
            f"生成的 description 评分偏低({scores.gen_score:.0f}/100)，"
            "当前领域模板可能不适合此技能"
        )
    return optimizations
def _collect_trigger_feedback(
    name: str, description: str, keywords: list[str],
) -> tuple[list[dict[str, Any]], _HealthSignals]:
    signals = _HealthSignals()
    trigger_feedback: list[dict[str, Any]] = []
    try:
        fb_loop = evaluate_trigger_feedback(name, description, keywords)
        for tf in fb_loop.get_recommendations():
            trigger_feedback.append(tf.to_dict())
            msg = trigger_feedback_message(tf)
            if not msg:
                continue
            if tf.recommendation == "boost":
                signals.optimizations.append(msg)
            else:
                signals.issues.append(msg)
    except (AttributeError, RuntimeError, ValueError, TypeError) as exc:
        _log.warning("diag_skill_directory: 触发反馈评估失败 %s: %s", name, exc)
    return trigger_feedback, signals
def _collect_hotness(
    name: str,
) -> tuple[dict[str, Any], _HealthSignals]:
    signals = _HealthSignals()
    hotness_dict: dict[str, Any] = {}
    try:
        _, _hot = evaluate_skill_hotness(name, record=False)
        hotness_dict = _hot.to_dict()
        if _hot.trend == "declining" and _hot.activation_count_30d > 0:
            signals.issues.append(
                "技能热度呈下降趋势"
                f"(近7天{_hot.activation_count_7d}次/"
                f"近30天{_hot.activation_count_30d}次激活)"
            )
        if _is_low_frequency_activation(_hot):
            signals.optimizations.append(
                "近30天零激活记录，建议扩充触发词覆盖并在真实使用中积累激活"
            )
    except (AttributeError, OSError, RuntimeError, ValueError, TypeError) as exc:
        _log.warning("diag_skill_directory: 热度评估失败 %s: %s", name, exc)
    return hotness_dict, signals
def _resolve_health_meta(
    skill_path: Path, meta: dict[str, Any] | None
) -> tuple[str, str, list[str]]:
    if not isinstance(meta, dict):
        meta = read_meta_degraded(skill_path, "diag_skill_directory")
    name = meta.get("name")
    if not isinstance(name, str) or not name:
        name = skill_path.name
    description = normalize_description_field(meta.get("description"))
    keywords = frontmatter_keywords(meta.get("keywords"))
    return name, description, keywords
def _meta_view(meta: dict[str, Any]) -> dict[str, Any]:
    return {
        "name": meta["name"],
        "description": meta["description"],
        "keywords": meta["keywords"],
    }
def _priority_of(fused_score: float) -> str:
    if fused_score < 30:
        return "critical"
    if fused_score < 60:
        return "high"
    return "normal"
@dataclass(frozen=True)
class _HealthBundle:
    scores: _DimensionScores
    signals: _HealthSignals
    trigger_feedback: list[dict[str, Any]]
    hotness: dict[str, Any]
def _collect_health_bundle(
    name: str, description: str, keywords: list[str], md_file: Path,
) -> _HealthBundle:
    signals = _HealthSignals()
    matching_score, part = _score_matching_dimension(
        name, description, keywords)
    signals.merge(part)
    capture_score, part = _score_capture_dimension(name, description, md_file)
    signals.merge(part)
    gen_score, part = _score_gen_dimension(name, keywords, matching_score)
    signals.merge(part)
    trigger_score, part = _score_trigger_dimension(
        name, description, keywords)
    signals.merge(part)
    scores = _DimensionScores(
        trigger_score, matching_score, capture_score, gen_score)
    signals.merge(_map_score_signals(scores, keywords, description))
    trigger_feedback, part = _collect_trigger_feedback(
        name, description, keywords)
    signals.merge(part)
    hotness_dict, part = _collect_hotness(name)
    signals.merge(part)
    return _HealthBundle(
        scores=scores, signals=signals,
        trigger_feedback=trigger_feedback, hotness=hotness_dict)
@dataclass
class DiscoverabilitySkillHealth:
    skill_name: str = ""
    overall_score: float = 0.0
    trigger_score: float = 0.0
    matching_score: float = 0.0
    capture_score: float = 0.0
    metadata_score: float = 0.0
    matching_measured: bool = False
    capture_measured: bool = False
    gen_measured: bool = False
    priority: str = "normal"
    issues: list[str] = field(default_factory=list)
    optimizations: list[str] = field(default_factory=list)
    trigger_feedback: list[dict[str, Any]] = field(default_factory=list)
    hotness: dict[str, Any] = field(default_factory=dict)
    def to_dict(self) -> dict[str, Any]:
        return {
            "skill_name": self.skill_name,
            "overall_score": self.overall_score,
            "trigger_score": self.trigger_score,
            "matching_score": self.matching_score,
            "capture_score": self.capture_score,
            "metadata_score": self.metadata_score,
            "matching_measured": self.matching_measured,
            "capture_measured": self.capture_measured,
            "gen_measured": self.gen_measured,
            "priority": self.priority,
            "issues": list(self.issues),
            "optimizations": list(self.optimizations),
            "trigger_feedback": [dict(fb) for fb in self.trigger_feedback],
            "hotness": dict(self.hotness),
        }
class DiscoverabilityDiagnoser:
    def __init__(self, skills_root: str | Path) -> None:
        self.skills_root = _path_arg(skills_root)
    def diag_skill_directory(
        self, skill_dir: str | Path, meta: dict[str, Any] | None = None
    ) -> DiscoverabilitySkillHealth | None:
        skill_path = _path_arg(skill_dir)
        if skill_path is None:
            _log.warning(
                "diag_skill_directory: 技能目录为空/非法，跳过: %r", skill_dir)
            return None
        entry = resolve_entry_document(skill_path)
        if entry is None:
            return None
        md_file = entry
        name, description, keywords = _resolve_health_meta(skill_path, meta)
        bundle = _collect_health_bundle(name, description, keywords, md_file)
        fused = bundle.scores.fused()
        return DiscoverabilitySkillHealth(
            skill_name=name,
            overall_score=round(fused, 1),
            trigger_score=round(bundle.scores.trigger_score, 1),
            matching_score=(round(bundle.scores.matching_score, 1)
                            if bundle.scores.matching_score is not None else 0.0),
            capture_score=(round(bundle.scores.capture_score, 1)
                           if bundle.scores.capture_score is not None else 0.0),
            metadata_score=min(100.0, len(distinct_keywords(keywords)) * 5),
            matching_measured=bundle.scores.matching_score is not None,
            capture_measured=bundle.scores.capture_score is not None,
            gen_measured=bundle.scores.gen_score is not None,
            priority=_priority_of(fused),
            issues=bundle.signals.issues,
            optimizations=bundle.signals.optimizations,
            trigger_feedback=bundle.trigger_feedback,
            hotness=bundle.hotness,
        )
    def diag(self) -> dict[str, Any]:
        if self.skills_root is None:
            return {"total": 0, "message": "skills_root 必须为非空路径"}
        if not safe_is_dir(self.skills_root):
            return {"total": 0, "message": f"skills_root 不存在: {self.skills_root}"}
        reports: list[DiscoverabilitySkillHealth] = []
        skill_meta: list[dict[str, Any]] = []
        failed: list[dict[str, str]] = []
        try:
            _entries = sorted(self.skills_root.iterdir())
        except OSError as exc:
            _log.warning("diag: skills_root 不可读 %s: %s", self.skills_root, exc)
            return {"total": 0, "message": f"skills_root 不可读: {self.skills_root}"}
        for d in _entries:
            if not is_skill_dir(d):
                continue
            report, meta, error = self._diagnose_entry(d)
            if error is not None:
                failed.append({"skill_dir": str(d), "error": error})
            if meta is None:
                continue
            skill_meta.append(meta)
            if report is not None:
                reports.append(report)
        result = self._compile_report(reports, skill_meta, failed)
        if failed:
            result["failed_skills"] = failed
        return result
    def _diagnose_entry(
        self, skill_dir: Path,
    ) -> tuple[DiscoverabilitySkillHealth | None, dict[str, Any] | None, str | None]:
        try:
            meta = read_skill_md(skill_dir)
        except (OSError, UnicodeDecodeError) as exc:
            _log.warning("diag: 读取 %s 入口文档失败，跳过: %s", skill_dir, exc)
            return None, None, str(exc)[:200]
        try:
            report = self.diag_skill_directory(skill_dir, meta=meta)
        except Exception as exc:  # noqa: BLE001
            _log.warning("diag: 体检 %s 异常，跳过: %s: %s",
                         skill_dir, type(exc).__name__, exc)
            return None, _meta_view(meta), str(exc)[:200]
        if report is None:
            error = "入口文档不可用，未生成可发现性健康报告"
            _log.warning("diag: %s %s", skill_dir, error)
            return None, _meta_view(meta), error
        return report, _meta_view(meta), None
    def _compile_report(
        self,
        reports: list[DiscoverabilitySkillHealth],
        skill_meta: list[dict[str, Any]],
        failed: list[dict[str, str]],
    ) -> dict[str, Any]:
        total = len(reports) + len(failed)
        if total == 0:
            return {"total": 0, "message": "No skills found"}
        priorities = Counter(r.priority for r in reports)
        result = {
            "total": total,
            "reported": len(reports),
            "failed_count": len(failed),
            "avg_score": average_overall_score(reports),
            "critical_count": priorities["critical"],
            "high_count": priorities["high"],
            "todos": self._build_todos(reports),
            "conflict_detection": self._detect_conflicts(skill_meta),
            "skills": [r.to_dict() for r in reports],
        }
        if not reports:
            result["message"] = "全部技能读取失败，未产出可发现性报告"
        return result
    @staticmethod
    def _build_todos(
        reports: list[DiscoverabilitySkillHealth],
    ) -> list[dict[str, Any]]:
        return [
            {
                "skill": report.skill_name,
                "priority": report.priority,
                "action": optimization,
                FIELD_EXPECTED_IMPACT: "提升触发识别率",
            }
            for report in reports
            for optimization in report.optimizations
        ]
    @staticmethod
    def _detect_conflicts(skill_meta: list[dict[str, Any]]) -> dict[str, Any]:
        if len(skill_meta) < 2:
            return {}
        try:
            return MatchingConflictDetector().detect(skill_meta)
        except (RuntimeError, ValueError, TypeError) as exc:
            _log.warning("_compile_report: 冲突检测失败: %s", exc)
            return {}
def quick_diag_skill_dir(
    skill_dir: str | Path,
) -> DiscoverabilitySkillHealth | None:
    path = _path_arg(skill_dir)
    if path is None:
        _log.warning("quick_diag_skill_dir: 技能目录为空/非法，跳过: %r",
                     skill_dir)
        return None
    if not is_skill_dir(path):
        _log.warning("quick_diag_skill_dir: 非技能目录，跳过: %s", path)
        return None
    return DiscoverabilityDiagnoser(path.parent).diag_skill_directory(path)
_TREND_WINDOW_DAYS = 30
_TREND_RECENT_DAYS = 7
_TREND_REST_DAYS = _TREND_WINDOW_DAYS - _TREND_RECENT_DAYS
_TREND_RISING_RATIO = 2.0
_TREND_DECLINING_RATIO = 0.5
_TRUE_SUCCESS_TOKENS = frozenset({"true", "1", "yes", "y", "on"})
_FALSE_SUCCESS_TOKENS = frozenset({"false", "0", "no", "n", "off", ""})
_HOTNESS_TOTAL_RECORD_TYPE = "hotness_totals"
_HOTNESS_ARCHIVED_TOTAL = "_archived_total"
def _sanitize_metric(value: Any, default: float = 0.0) -> float:
    if isinstance(value, bool):
        return default
    try:
        v = float(value)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_sanitize_metric:{type(_e).__name__}')
        return default
    return v if math.isfinite(v) else default
def _clamp_satisfaction(value: Any) -> float:
    v = _sanitize_metric(value)
    return min(max(v, 0.0), 1.0)
def _positive_values(entries: list[dict[str, Any]], key: str) -> list[float]:
    values: list[float] = []
    for entry in entries:
        value = _sanitize_metric(entry.get(key, 0.0))
        if value > 0:
            values.append(value)
    return values
def _parse_event_line(
    raw_line: str, line_no: int,
) -> tuple[str, dict[str, Any]] | None:
    line = raw_line.strip()
    if not line:
        return None
    try:
        event = json.loads(line)
    except (ValueError, TypeError, RecursionError) as exc:
        _log.warning("HotnessTracker._load 第 %d 行解析失败: %s", line_no, exc)
        return None
    return _parse_loaded_event(event, line_no)
def _archived_total_payload(
    event: dict[str, Any], line_no: int,
) -> dict[str, int] | None:
    raw_total = event.get("activation_count_total")
    total = _sanitize_metric(raw_total, default=-1.0)
    if total < 0 or not total.is_integer():
        _log.warning(
            "HotnessTracker._load 第 %d 行历史汇总计数非法（%r），跳过",
            line_no, raw_total)
        return None
    return {_HOTNESS_ARCHIVED_TOTAL: int(total)}
def _parse_loaded_event(
    event: Any, line_no: int,
) -> tuple[str, dict[str, Any]] | None:
    if not isinstance(event, dict):
        _log.warning("HotnessTracker._load 第 %d 行非 JSON 对象，跳过", line_no)
        return None
    raw_name = event.get("skill_name")
    if not isinstance(raw_name, str):
        _log.warning(
            "HotnessTracker._load 第 %d 行 skill_name 非字符串（%s），跳过",
            line_no, type(raw_name).__name__)
        return None
    name = normalize_text(raw_name).strip()
    if not name:
        return None
    if event.get("record_type") == _HOTNESS_TOTAL_RECORD_TYPE:
        payload = _archived_total_payload(event, line_no)
        return (name, payload) if payload is not None else None
    return name, _event_payload(
        timestamp=event.get("timestamp", 0.0),
        success=event.get("success", True),
        response_time_ms=event.get("response_time_ms", 0.0),
        user_satisfaction=event.get("user_satisfaction", 0.0),
    )
def _coerce_success(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return _sanitize_metric(value) != 0
    if isinstance(value, str):
        token = value.strip().lower()
        if token in _TRUE_SUCCESS_TOKENS:
            return True
        if token in _FALSE_SUCCESS_TOKENS:
            return False
    return False
def _event_payload(*, timestamp: Any, success: Any, response_time_ms: Any,
                   user_satisfaction: Any) -> dict[str, Any]:
    return {
        "timestamp": _sanitize_metric(timestamp),
        "success": _coerce_success(success),
        "response_time_ms": _sanitize_metric(response_time_ms),
        "user_satisfaction": _clamp_satisfaction(user_satisfaction),
    }
@dataclass
class SkillHotness:
    skill_name: str = ""
    activation_count_7d: int = 0
    activation_count_30d: int = 0
    activation_count_total: int = 0
    success_rate: float = 0.0
    avg_response_time_ms: float = 0.0
    user_satisfaction: float = 0.0
    hotness_score: float = 0.0
    trend: str = "stable"
    def to_dict(self) -> dict[str, Any]:
        return {
            "skill_name": self.skill_name,
            "activation_count_7d": self.activation_count_7d,
            "activation_count_30d": self.activation_count_30d,
            "activation_count_total": self.activation_count_total,
            "success_rate": round(self.success_rate, 3),
            "avg_response_time_ms": round(self.avg_response_time_ms, 1),
            "user_satisfaction": round(self.user_satisfaction, 3),
            "hotness_score": self.hotness_score,
            "trend": self.trend,
        }
class HotnessTracker:
    PRUNE_MAX_AGE_DAYS = 35
    PRUNE_MAX_LINES = 5000
    def __init__(self, store_path: str | Path | None = None) -> None:
        self.store_path = _path_arg(store_path)
        if store_path is not None and self.store_path is None:
            _log.warning("HotnessTracker: store_path 为空/非法，禁用持久化: %r",
                         store_path)
        if self.store_path is not None and self.store_path.is_dir():
            _log.warning("HotnessTracker: store_path 指向目录，禁用持久化: %s",
                         self.store_path)
            self.store_path = None
        self._archived_counts: Counter[str] = Counter()
        self._usage_log: dict[str, list[dict[str, Any]]] = defaultdict(list)
        self._io_lock = threading.Lock()
        if self.store_path is not None and self.store_path.exists():
            self._load()
    @contextmanager
    def _store_lock(self) -> Iterator[bool]:
        with self._io_lock:
            if self.store_path is None:
                yield True
                return
            with locked_artifact(str(self.store_path)) as locked:
                yield locked
    def _load(self) -> None:
        store_path = self.store_path
        if store_path is None:
            return
        try:
            text = store_path.read_text(encoding="utf-8-sig")
        except (OSError, ValueError) as exc:
            _log.warning("HotnessTracker._load 读取失败: %s", exc)
            return
        for line_no, raw_line in enumerate(text.splitlines(), start=1):
            parsed = _parse_event_line(raw_line, line_no)
            if parsed is not None:
                name, payload = parsed
                archived = payload.get(_HOTNESS_ARCHIVED_TOTAL)
                if archived is not None:
                    self._archived_counts[name] += archived
                else:
                    self._usage_log[name].append(payload)
    def record_activation(
        self,
        skill_name: str,
        *,
        success: bool = _DEFAULT_ACTIVATION_SUCCESS,
        response_time_ms: float = 0.0,
        user_satisfaction: float = 0.0,
        persist: bool | None = None,
    ) -> None:
        skill_name = normalize_text(skill_name).strip()
        if not skill_name:
            return
        event = _event_payload(
            timestamp=time.time(),
            success=success,
            response_time_ms=response_time_ms,
            user_satisfaction=user_satisfaction,
        )
        self._usage_log[skill_name].append(event)
        should_persist = persist if persist is not None else self.store_path is not None
        if should_persist and self.store_path is not None:
            self._persist_event({"skill_name": skill_name, **event})
    def _persist_event(self, record: dict[str, Any]) -> None:
        store_path = self.store_path
        if store_path is None:
            return
        try:
            store_path.parent.mkdir(parents=True, exist_ok=True)
            with self._store_lock() as locked:
                if not locked:
                    _log.warning(
                        "HotnessTracker.record_activation 锁不可用，跳过本次落盘: %s",
                        store_path)
                    return
                with store_path.open("a", encoding="utf-8") as fh:
                    fh.write(json.dumps(record, ensure_ascii=False, default=str) + "\n")
                try:
                    self._prune_store_locked()
                except (OSError, ValueError, TypeError) as exc:
                    _log.warning("HotnessTracker._prune_store 裁剪失败: %s", exc)
        except (OSError, ValueError, TypeError) as exc:
            _log.warning("HotnessTracker.record_activation 落盘失败: %s", exc)
    def _prune_store(self) -> None:
        if self.store_path is None:
            return
        try:
            with self._store_lock() as locked:
                if not locked:
                    _log.warning(
                        "HotnessTracker._prune_store 锁不可用，跳过重写裁剪: %s",
                        self.store_path)
                    return
                self._prune_store_locked()
        except (OSError, ValueError, TypeError) as exc:
            _log.warning("HotnessTracker._prune_store 裁剪失败: %s", exc)
    def _prune_store_locked(self) -> None:
        if self.store_path is None:
            return
        now = time.time()
        cutoff = now - self.PRUNE_MAX_AGE_DAYS * 86400
        kept, archived, removed = self._read_prune_entries(cutoff)
        line_limit = max(self.PRUNE_MAX_LINES, 0)
        if len(kept) > line_limit:
            overflow_count = len(kept) - line_limit
            metric_cutoff = now - _TREND_WINDOW_DAYS * 86400
            prunable = sorted(
                (entry for entry in enumerate(kept)
                 if entry[1][2]["timestamp"] < metric_cutoff),
                key=lambda entry: (entry[1][2]["timestamp"], entry[0]),
            )
            overflow = prunable[:overflow_count]
            overflow_indexes = {index for index, _entry in overflow}
            for _index, (_raw, name, _payload) in overflow:
                archived[name] += 1
            kept = [entry for index, entry in enumerate(kept)
                    if index not in overflow_indexes]
            removed += len(overflow)
        if removed == 0:
            return
        total_lines = [
            json.dumps({
                "record_type": _HOTNESS_TOTAL_RECORD_TYPE,
                "skill_name": name,
                "activation_count_total": count,
            }, ensure_ascii=False)
            for name, count in sorted(archived.items()) if count > 0
        ]
        self._replace_store(total_lines + [raw for raw, _name, _payload in kept])
        _log.info(
            "HotnessTracker._prune_store 裁剪 %d 行"
            "（保留 %d 事件行、%d 汇总行）",
            removed, len(kept), len(total_lines))
    def _read_prune_entries(
        self, cutoff: float,
    ) -> tuple[list[tuple[str, str, dict[str, Any]]], Counter[str], int]:
        store_path = self.store_path
        if store_path is None:
            return [], Counter(), 0
        kept: list[tuple[str, str, dict[str, Any]]] = []
        archived: Counter[str] = Counter()
        removed = 0
        with store_path.open("r", encoding="utf-8-sig") as fh:
            for line_no, line in enumerate(fh, start=1):
                stripped = line.strip()
                if not stripped:
                    removed += 1
                    continue
                parsed = _parse_event_line(stripped, line_no)
                if parsed is None:
                    removed += 1
                    continue
                name, payload = parsed
                archived_total = payload.get(_HOTNESS_ARCHIVED_TOTAL)
                if archived_total is not None:
                    archived[name] += archived_total
                elif payload["timestamp"] >= cutoff:
                    kept.append((stripped, name, payload))
                else:
                    archived[name] += 1
                    removed += 1
        return kept, archived, removed
    def _replace_store(self, kept: list[str]) -> None:
        store_path = self.store_path
        if store_path is None:
            return
        tmp_path = store_path.with_name(store_path.name + ".tmp")
        with tmp_path.open("w", encoding="utf-8") as fh:
            fh.write("\n".join(kept) + ("\n" if kept else ""))
        os.replace(tmp_path, store_path)
    @staticmethod
    def _aggregate_recent_metrics(
        recent_30d: list[dict[str, Any]]
    ) -> tuple[float, float, float]:
        if not recent_30d:
            return 0.0, 0.0, 0.0
        successes = sum(1 for entry in recent_30d if entry["success"])
        success_rate = successes / len(recent_30d)
        times = _positive_values(recent_30d, "response_time_ms")
        avg_response_time_ms = sum(times) / len(times) if times else 0.0
        sats = _positive_values(recent_30d, "user_satisfaction")
        user_satisfaction = sum(sats) / len(sats) if sats else 0.0
        return success_rate, avg_response_time_ms, user_satisfaction
    @staticmethod
    def _detect_trend(
        recent_7d: list[dict[str, Any]], recent_30d: list[dict[str, Any]]
    ) -> tuple[str, float]:
        if not recent_30d:
            return "stable", 5
        rest_count = len(recent_30d) - len(recent_7d)
        if rest_count <= 0:
            return "rising", 10
        week_ratio = ((len(recent_7d) / _TREND_RECENT_DAYS)
                      / (rest_count / _TREND_REST_DAYS))
        if week_ratio > _TREND_RISING_RATIO:
            return "rising", 10
        if week_ratio < _TREND_DECLINING_RATIO:
            return "declining", 2
        return "stable", 5
    def compute_hotness(self, skill_name: str) -> SkillHotness:
        skill_name = normalize_text(skill_name).strip()
        logs = self._usage_log.get(skill_name, [])
        now = time.time()
        week_ago = now - 7 * 86400
        month_ago = now - 30 * 86400
        happened = [entry for entry in logs if entry["timestamp"] <= now]
        recent_7d = [entry for entry in happened if entry["timestamp"] >= week_ago]
        recent_30d = [entry for entry in happened if entry["timestamp"] >= month_ago]
        hotness = SkillHotness(skill_name=skill_name)
        hotness.activation_count_7d = len(recent_7d)
        hotness.activation_count_30d = len(recent_30d)
        hotness.activation_count_total = (
            self._archived_counts.get(skill_name, 0) + len(happened))
        if recent_30d:
            (hotness.success_rate, hotness.avg_response_time_ms,
             hotness.user_satisfaction) = self._aggregate_recent_metrics(recent_30d)
        freq_score = min(hotness.activation_count_7d / 10, 1.0) * 40
        success_score = hotness.success_rate * 30
        sat_score = hotness.user_satisfaction * 20
        hotness.trend, trend_score = self._detect_trend(recent_7d, recent_30d)
        hotness.hotness_score = round(
            freq_score + success_score + sat_score + trend_score, 1
        )
        return hotness
def default_hotness_store() -> Path | None:
    _dir = get_log_dir()
    return Path(_dir) / STATE_FILE_SKILL_HOTNESS if _dir else None
def resolve_analyze_input(
    skill_dir_or_name: Any, description: str, keywords: list[str]
) -> tuple[Path | None, str, str, list[str]]:
    path = _path_arg(skill_dir_or_name)
    if path is not None and safe_is_dir(path):
        meta = read_meta_degraded(path, "resolve_analyze_input")
        resolved_description = (
            description if normalize_text(description) else meta["description"])
        resolved_keywords = keywords if keywords else meta["keywords"]
        return path, meta["name"], resolved_description, resolved_keywords
    name = "" if skill_dir_or_name is None else str(skill_dir_or_name)
    return None, name, description, keywords
def _sibling_skill_names(skill_dir: Path | None) -> list[str]:
    if skill_dir is None:
        return []
    resolved_dir = skill_dir.resolve()
    return [
        p.name for p in resolved_dir.parent.iterdir()
        if p.name != resolved_dir.name and is_skill_dir(p)
    ]
def _safe_disclosure_cold_start(
    name: str, description: str, keywords: list[str], skill_dir: Path | None
) -> tuple[list, list]:
    try:
        disclosure_optimizer = AutoDisclosureOptimizer()
        disclosure_suggestions = disclosure_optimizer.analyze(description, keywords)
    except (RuntimeError, ValueError, TypeError) as exc:
        _log.warning("披露建议生成失败: %s", exc)
        disclosure_suggestions = []
    try:
        cold_start_recommendations = recommend_cold_start(
            name, description, keywords, _sibling_skill_names(skill_dir)
        )
    except (RuntimeError, ValueError, TypeError, OSError) as exc:
        _log.warning("冷启动推荐生成失败: %s", exc)
        cold_start_recommendations = []
    return disclosure_suggestions, cold_start_recommendations
def _safe_trigger_feedback(
    name: str, description: str, keywords: list[str]
) -> list[TriggerFeedback]:
    try:
        feedback_loop = evaluate_trigger_feedback(name, description, keywords)
        return feedback_loop.get_recommendations()
    except (RuntimeError, ValueError, TypeError) as exc:
        _log.warning("触发反馈评估失败: %s", exc)
        return []
def _feedback_recommendations(
    feedback: list[TriggerFeedback],
) -> list[str]:
    messages: list[str] = []
    for tf in feedback:
        msg = trigger_feedback_message(tf)
        if msg:
            messages.append(msg)
    return messages
def _base_rule_recommendations(trigger_score: float, keywords: list[str],
                              has_cn: bool, has_en: bool) -> list[str]:
    messages: list[str] = []
    if trigger_score < LOW_TRIGGER_SCORE:
        messages.append(f"触发评分较低 ({trigger_score})，建议优化 description 和 keywords")
    keyword_count = len(distinct_keywords(keywords))
    if keyword_count < MIN_KEYWORD_COUNT:
        messages.append(
            f"关键词数量不足 ({keyword_count}<{MIN_KEYWORD_COUNT})，"
            f"建议扩展至 {KEYWORD_TARGET_COUNT}+ 个")
    elif keyword_count < KEYWORD_GOOD_COUNT:
        messages.append(f"关键词数量偏少 ({keyword_count})，"
                        f"建议扩展至 {KEYWORD_TARGET_COUNT}+ 个")
    if not has_cn or not has_en:
        messages.append("建议同时覆盖本地语言与英文关键词")
    return messages
def analyze_skill_discoverability(
    name: str,
    description: str,
    keywords: list[str] | None = None,
    *,
    skill_dir: Path | None = None,
    record_activation: bool = False,
    hotness_store: str | Path | None = None,
) -> dict[str, Any]:
    keywords = normalize_keywords(keywords)
    trigger_score = score_triggers(description, keywords, name)
    has_cn, has_en = kw_language_flags(keywords)
    report = {
        "skill_name": name,
        "trigger_score": trigger_score,
        "keyword_count": len(distinct_keywords(keywords)),
        "has_cn_keywords": has_cn,
        "has_en_keywords": has_en,
        FIELD_RECOMMENDATIONS: [],
    }
    recommendations = _base_rule_recommendations(
        trigger_score, keywords, has_cn, has_en
    )
    disclosure_suggestions, cold_start_recommendations = (
        _safe_disclosure_cold_start(name, description, keywords, skill_dir)
    )
    report["disclosure_suggestions"] = disclosure_suggestions
    report["cold_start_recommendations"] = cold_start_recommendations
    recommendations.extend(disclosure_suggestions)
    recommendations.extend(cold_start_recommendations)
    trigger_feedback = _safe_trigger_feedback(name, description, keywords)
    report["trigger_feedback"] = [tf.to_dict() for tf in trigger_feedback]
    recommendations.extend(_feedback_recommendations(trigger_feedback))
    hotness_dict, hotness_messages = safe_hotness_section(
        name, description, keywords, record_activation, hotness_store
    )
    report["hotness"] = hotness_dict
    recommendations.extend(hotness_messages)
    report[FIELD_RECOMMENDATIONS] = recommendations
    report["overall_score"] = min(trigger_score, 100)
    return report
def _frontmatter_struct_error(loaded: Any) -> str | None:
    if loaded is None:
        return (
            "frontmatter 为空：'---' 与闭合 '---' 之间无 YAML"
            " 内容，name/description 已按空处理"
        )
    return (
        f"frontmatter 顶层结构非映射（实际得到 "
        f"{type(loaded).__name__}），name/description 已按空处理"
    )
def _read_text_lines(path: str) -> list[str]:
    with open(path, encoding="utf-8-sig") as f:
        return f.read().split("\n")
def _yaml_struct_error(frontmatter_lines: list[str]) -> str | None:
    loaded = yaml.safe_load("\n".join(frontmatter_lines))
    if not isinstance(loaded, dict):
        return _frontmatter_struct_error(loaded)
    return None
def _findings_status(findings: list) -> str:
    return "warn" if findings else "pass"
def _c2_error_envelope(summary: str) -> dict:
    return {
        "status": "error",
        "findings_count": 0,
        "summary": summary,
        "findings": [],
        "payload": {},
    }
class DocQualityEngine:
    def __init__(self, skill_dir: str, cache: Any = None):
        self.skill_dir = skill_dir
        self.cache = cache
        path = _path_arg(skill_dir)
        entry = resolve_entry_document(path) if path is not None else None
        self.skill_md_path = (
            os.fspath(entry) if entry is not None
            else os.path.join(os.fspath(path), ENTRY_DOC_NAME)
            if path is not None else ""
        )
    @property
    def _entry_name(self) -> str:
        return os.path.basename(self.skill_md_path) or ENTRY_DOC_NAME
    def run_matching_rules(self) -> dict:
        if not os.path.isfile(self.skill_md_path):
            return _c2_error_envelope(f"{self._entry_name} not found")
        try:
            full_result = diag_skill_full_pipeline(self.skill_md_path)
            return self._matching_success_envelope(
                full_result, self._matching_findings(full_result))
        except CacheNotWarmedError:
            raise
        except Exception as e:  # noqa: BLE001
            _log.warning("[DocQualityEngine] matching_rules failed: %s: %s",
                         type(e).__name__, e, exc_info=True)
            return _c2_error_envelope(f"matching diag error: {str(e)[:200]}")
    @staticmethod
    def _matching_success_envelope(full_result, findings: list[dict]) -> dict:
        _scores = getattr(full_result, "phase_scores", {}) or {}
        _match_score = _sanitize_metric(_scores.get("matching"))
        _capture_score = _sanitize_metric(_scores.get("capture"))
        _overall_score = _sanitize_metric(
            getattr(full_result, "overall_score", 0.0))
        _grade = normalize_text(getattr(full_result, "overall_grade", "")) or "?"
        return {
            "status": _findings_status(findings),
            "findings_count": len(findings),
            "summary": (
                f"matching_rules: match={_match_score:.0f}"
                f", capture={_capture_score:.0f}"
                f", overall={_overall_score:.0f}/{_grade}"
                f", findings={len(findings)}"
            ),
            "findings": findings,
            "matching_score": _match_score,
            "capture_score": _capture_score,
            "overall_score": _overall_score,
            "overall_grade": _grade,
        }
    def _matching_findings(self, full_result) -> list[dict]:
        findings: list[dict] = []
        _fm_finding = self._frontmatter_parse_finding()
        if _fm_finding:
            findings.append(_fm_finding)
        findings.extend(self._phase_finding_dicts(
            full_result.matching_report, "matching"))
        findings.extend(self._phase_finding_dicts(
            full_result.capture_report, "capture"))
        return findings
    def _phase_finding_dicts(self, report, phase: str) -> list[dict]:
        if not report:
            return []
        return [{
            "rule_id": v.rule_id,
            "phase": phase,
            "severity": v.severity,
            "description": v.description,
            "message": v.description,
            "file": self._entry_name,
            "line": 0,
            "source": "C2",
        } for v in report.violations]
    def _frontmatter_parse_finding(self) -> dict | None:
        fm_err = self._frontmatter_parse_error()
        if not fm_err:
            return None
        _fm_msg = (
            f"{self._entry_name} frontmatter 不可用（{fm_err}）。"
            f"name/description/keywords 已按空处理——本轮 DR 系"
            f"违规可能全部由此引起，请先修复 frontmatter 语法，"
            f"而非按 DR 违规逐条改写 description 内容"
        )
        return {
            "rule_id": "FM-PARSE",
            "phase": "matching",
            "severity": "critical",
            "description": _fm_msg,
            "message": _fm_msg,
            "file": self._entry_name,
            "line": 1,
            "source": "C2",
        }
    def _frontmatter_parse_error(self) -> str | None:
        try:
            lines = _read_text_lines(self.skill_md_path)
            if not lines:
                return None
            first = 0
            while first < len(lines) and not str(lines[first]).strip():
                first += 1
            if first >= len(lines):
                return None
            opening = str(lines[first]).lstrip("\ufeff").rstrip("\r")
            if first > 0 and opening.strip() == "---":
                return ("frontmatter 起始围栏必须位于文件第一行"
                        "（检测到前置空行）")
            body_start = locate_frontmatter_body_start(lines)
            if body_start:
                return _yaml_struct_error(lines[first + 1:body_start - 1])
            if is_frontmatter_fence(opening):
                return "frontmatter 未闭合：'---' 后无闭合分隔符"
            if opening.strip() == "---":
                return ("frontmatter 起始围栏必须位于行首"
                        "（检测到缩进或前置不可见字符）")
            return None
        except Exception as e:  # noqa: BLE001
            log_swallowed(
                __name__, e,
                context=(
                    'DocQualityEngine._frontmatter_parse_error:'
                    f'{type(e).__name__}'))
            return f"{type(e).__name__}: {str(e)[:150]}"
    def run_doc_consistency(self) -> dict:
        if not os.path.isfile(self.skill_md_path):
            return _c2_error_envelope(f"{self._entry_name} not found")
        try:
            analyzer = DocCodeConsistencyAnalyzer(self.skill_dir, cache=self.cache)
            raw_findings = analyzer.analyze()
            _src_err = self._doc_source_error(analyzer)
            if _src_err is not None:
                return _src_err
            return self._consistency_success_envelope(
                analyzer, self._consistency_findings(raw_findings))
        except CacheNotWarmedError:
            raise
        except Exception as e:  # noqa: BLE001
            _log.warning("[DocQualityEngine] doc_consistency failed: %s: %s",
                         type(e).__name__, e, exc_info=True)
            return _c2_error_envelope(f"文档-代码一致性诊断异常: {e}")
    def _doc_source_error(self, analyzer) -> dict | None:
        if analyzer.doc_source_status == "missing":
            return _c2_error_envelope(f"{self._entry_name} not found")
        if analyzer.doc_source_status == "read_error":
            return _c2_error_envelope(
                f"{self._entry_name} 读取失败（IO 降级空文档），一致性对比不可信")
        return None
    def _consistency_success_envelope(self, analyzer,
                                      findings: list[dict]) -> dict:
        n = len(findings)
        return {
            "status": _findings_status(findings),
            "findings_count": n,
            "summary": self._consistency_summary_notes(analyzer, n),
            "findings": findings,
            "filtered_orphans": list(analyzer.filtered_orphans),
            "rule_id_disposition": analyzer.rule_id_disposition,
        }
    def _consistency_findings(self, raw_findings) -> list[dict]:
        findings: list[dict] = []
        for rf in raw_findings:
            raw_extra = getattr(rf, "extra", None)
            extra = raw_extra if isinstance(raw_extra, dict) else {}
            findings.append({
                "rule_id": normalize_text(getattr(rf, "rule_id", "")),
                "severity": normalize_text(getattr(rf, "severity", "")),
                "confidence": _sanitize_metric(
                    getattr(rf, "confidence", 0.0)),
                "message": normalize_text(getattr(rf, "message", "")),
                "file": normalize_text(getattr(rf, "file", "")),
                "line": getattr(rf, "line", 0),
                "source": "C2",
                "doc_type": normalize_text(extra.get("type", "")),
                "name": normalize_text(extra.get("name", "")),
            })
        return findings
    def _consistency_summary_notes(self, analyzer, n: int) -> str:
        summary = f"文档-代码一致性: {n}个不一致"
        if analyzer.api_face_total > 0:
            summary += (
                f" (公开可调用API {analyzer.api_face_total} 个, 文档提及 "
                f"{analyzer.api_face_covered}, 覆盖率 "
                f"{analyzer.api_face_covered / analyzer.api_face_total:.0%})"
            )
        return summary + self._strip_audit_notes(analyzer)
    @staticmethod
    def _strip_audit_notes(analyzer) -> str:
        notes = ""
        _filtered = analyzer.filtered_orphans
        if _filtered:
            notes += f", 低置信孤儿过滤{len(_filtered)}条"
        _rid = analyzer.rule_id_disposition
        _stripped = _rid.get("registered_stripped", [])
        _ghosts = _rid.get("ghost_elevated", [])
        if _stripped or _ghosts:
            notes += (f", 规则ID域剥离{len(_stripped)}条"
                      f"/幽灵升级{len(_ghosts)}条")
        for values, label in (
            (analyzer.host_var_stripped, "变量绑定剥离"),
            (analyzer.local_def_stripped, "本地定义剥离"),
            (analyzer.out_of_scope_import_stripped, "范围外导入剥离"),
        ):
            if values:
                notes += f", {label}{len(values)}条"
        return notes
    def analyze(self) -> dict:
        matching_result = self.run_matching_rules()
        consistency_result = self.run_doc_consistency()
        return {
            "skill_dir": self.skill_dir,
            "status": _combined_status(matching_result, consistency_result),
            "matching_rules": matching_result,
            "doc_consistency": consistency_result,
            "findings": (
                matching_result.get("findings", [])
                + consistency_result.get("findings", [])
            ),
        }
_C2_STATUS_ORDER = {"pass": 0, "skip": 1, "warn": 2, "error": 3}
def _combined_status(*results: dict) -> str:
    combined = "pass"
    for raw_status in (r.get("status", "skip") for r in results):
        status = raw_status if raw_status in _C2_STATUS_ORDER else "skip"
        if _C2_STATUS_ORDER[status] > _C2_STATUS_ORDER[combined]:
            combined = status
    return combined
def _c2_quality_envelope(merged: dict) -> dict:
    consistency_result = merged["doc_consistency"]
    matching_result = merged["matching_rules"]
    c_findings = consistency_result.get("findings", [])
    m_findings = matching_result.get("findings", [])
    all_findings = m_findings + c_findings
    summary = (
        f"文档质量引擎: {len(c_findings)}个一致性问题, "
        f"{len(m_findings)}个匹配规则问题"
    )
    for _sub in (consistency_result.get("summary", ""),
                 matching_result.get("summary", "")):
        if _sub:
            summary += f" | {_sub}"
    return {
        "status": merged["status"],
        "findings_count": len(all_findings),
        "summary": summary,
        "findings": all_findings,
        "payload": {
            "consistency": consistency_result,
            "matching_rules": matching_result,
        },
    }
def run_c2_doc_quality_engine(skill_dir: str, cache=None) -> dict:
    require_warmed(cache, "C2 文档质量引擎")
    try:
        return _c2_quality_envelope(
            DocQualityEngine(skill_dir, cache).analyze())
    except CacheNotWarmedError:
        raise
    except Exception as e:  # noqa: BLE001
        _log.warning("[C2] 文档质量引擎异常: %s: %s",
                     type(e).__name__, e, exc_info=True)
        return _c2_error_envelope(f"文档质量引擎错误: {e}")

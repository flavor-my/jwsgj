from __future__ import annotations

import math
import re
from collections.abc import Callable, Iterable, Iterator, Mapping
from dataclasses import dataclass, field
from datetime import UTC, datetime
from functools import partial
from typing import Any

from jwsgj.diag_types_normalize import (
    as_list,
    count_tasks,
    dict_or_empty,
    is_finite_num,
    normalize_success_rate,
    safe_float,
    safe_str,
)
from jwsgj.diag_types_normalize import (
    unwrap_cv_results as _unwrap_cv_results,
)
from jwsgj.diag_types_vocab import (
    DIAGNOSE_TO_P,
    FIELD_RECOMMENDATIONS,
    SEVERITY_RANK,
    TX_FAILED_STATUSES,
    TX_FIXED_STATUSES,
    TX_ROLLED_BACK_STATUSES,
    diag_severity_to_p,
    register_review_provider,
)
from jwsgj.log_config import get_module_logger, log_swallowed

__all__ = [
    "CATEGORY_CROSS_SESSION_LESSON",
    "CATEGORY_CV_TUNING",
    "CATEGORY_DIAGNOSTIC_SUMMARY",
    "CATEGORY_ENHANCEMENT_IMPACT",
    "CATEGORY_FIXER_PERF_SYNC",
    "CATEGORY_FIX_LEARNING",
    "CATEGORY_FIX_RESULT",
    "CATEGORY_FP_PATTERN",
    "CATEGORY_OSCILLATION",
    "CATEGORY_PDCA_TRACKING",
    "CATEGORY_REGRESSION",
    "CATEGORY_RULE_EVOLUTION",
    "CATEGORY_TP_PATTERN",
    "JACCARD_THRESHOLD",
    "MIN_QUALITY_SCORE",
    "RULE_ID_BARE_RE",
    "TP_CONFIDENCE_MULTIPLIER",
    "TP_THRESHOLD_ADJUSTMENT",
    "TREATMENT_ITEM_KEYS",
    "WIKI_CONCEPTS_PREFIX",
    "WIKI_LESSONS_PREFIX",
    "WIKI_PROJECTS_PREFIX",
    "DiagnosticMemoryContext",
    "DiagnosticMemoryOperation",
    "TreatmentMemoryEnhancement",
    "baseline_count",
    "collect_ctx_evidence",
    "compute_enhancement_impact",
    "compute_information_density",
    "cv_confirmed_signal",
    "cv_fp_count_signal",
    "detect_diagnostic_regression",
    "enhance_fupan_with_memory",
    "enhance_pre_creation_with_memory",
    "enhance_retrospective_with_memory",
    "enhance_review_with_memory",
    "evaluate_memory_density",
    "extract_bare_rule_id",
    "extract_fixer_name",
    "extract_path_ts",
    "first_valid_count_signal",
    "fix_failed",
    "fix_succeeded",
    "format_memory_trend_score",
    "get_memory_search_queries",
    "get_pre_creation_search_queries",
    "get_rule_severity_calibrations",
    "has_total_findings",
    "infer_memory_category",
    "is_newer",
    "is_valid_count_form",
    "is_valid_memory_score",
    "iter_rule_findings",
    "last_summary_dict",
    "materialize_existing_memories",
    "md_cell",
    "memory_date_stamp",
    "memory_raw_text",
    "memory_text_tokens",
    "normalize_mem_entry",
    "normalize_rule_id",
    "now_str",
    "parse_cv_tuning_memory",
    "parse_diagnostic_summary",
    "parse_fix_result_memory",
    "parse_nonneg_count_str",
    "parse_oscillation_memory",
    "parse_pattern_memory",
    "path_segment",
    "pattern_rule_ids",
    "pick_first",
    "pick_text",
    "pipeline_stage_views",
    "prepare_diagnostic_context",
    "rules_triggered_count",
    "rules_triggered_signal",
    "safe_int",
    "str_memory_paths",
    "total_findings_count",
    "total_findings_signal",
    "treatment_counts",
    "treatment_items",
    "ts_no_older",
    "validate_memory_context",
]
logger = get_module_logger(__name__, __file__)
logger.info("memory_bridge 已加载: %d 项导出", len(__all__))
CATEGORY_FP_PATTERN = "fp_pattern"
CATEGORY_TP_PATTERN = "tp_pattern"
CATEGORY_FIX_RESULT = "fix_result"
FIX_RESULT_UPDATE_HEADING = "## 修复结果更新"
CATEGORY_OSCILLATION = "oscillation"
CATEGORY_DIAGNOSTIC_SUMMARY = "diag_summary"
CATEGORY_CV_TUNING = "cv_tuning"
CATEGORY_ENHANCEMENT_IMPACT = "enhancement_impact"
CATEGORY_REGRESSION = "regression"
CATEGORY_RULE_EVOLUTION = "rule_evolution"
CATEGORY_FIX_LEARNING = "fix_learning"
CATEGORY_FIXER_PERF_SYNC = "fixer_perf_sync"
CATEGORY_PDCA_TRACKING = "pdca_tracking"
CATEGORY_CROSS_SESSION_LESSON = "cross_session_lesson"
WIKI_CONCEPTS_PREFIX = "wiki/concepts"
WIKI_LESSONS_PREFIX = "wiki/lessons"
WIKI_PROJECTS_PREFIX = "wiki/projects"
MIN_QUALITY_SCORE = 4.0
JACCARD_THRESHOLD = 0.7
TP_THRESHOLD_ADJUSTMENT = -0.05
TP_CONFIDENCE_MULTIPLIER = 1.05
TREATMENT_ITEM_KEYS = ("items", "treatment_items", "details", "fix_details")
_CJK_RUN_RE = re.compile(r"[\u4e00-\u9fff]+")
_EN_MEMORY_TOKEN_RE = re.compile(r"[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*")
def memory_text_tokens(text: Any) -> set[str]:
    if not isinstance(text, str) or not text:
        return set()
    tokens = {
        match.group(0).lower() for match in _EN_MEMORY_TOKEN_RE.finditer(text)
        if len(match.group(0)) >= 2
    }
    for chunk in _CJK_RUN_RE.findall(text):
        tokens.update(chunk[index:index + 2]
                      for index in range(len(chunk) - 1))
    return tokens
@dataclass
class DiagnosticMemoryContext:
    known_fp_patterns: list[dict] = field(default_factory=list)
    known_tp_patterns: list[dict] = field(default_factory=list)
    historical_fix_rates: dict[str, list[dict]] = field(default_factory=dict)
    oscillation_params: dict[str, dict] = field(default_factory=dict)
    last_diagnosis_summary: dict | None = None
    cv_tuning_history: list[dict] = field(default_factory=list)
    raw_memory_paths: list[str] = field(default_factory=list)
    raw_search_results: list[dict] = field(default_factory=list)
    source: str = "memory_system"
    loaded_at: str = ""
    fixer_performance: dict[str, dict] = field(default_factory=dict)
    fix_patterns: list[dict] = field(default_factory=list)
    pdca_history: list[dict] = field(default_factory=list)
    regression_history: list[dict] = field(default_factory=list)
    rule_evolution: list[dict] = field(default_factory=list)
    enhancement_impact_history: list[dict] = field(default_factory=list)
    cross_session_lessons: list[dict] = field(default_factory=list)
@dataclass
class TreatmentMemoryEnhancement:
    rule_id: str
    preferred_fixer: str | None
    skip_fixers: list[str]
    success_rate: float
    total_attempts: int
    fixer_ranking: list = field(default_factory=list)
    category: str = CATEGORY_FIXER_PERF_SYNC
@dataclass
class DiagnosticMemoryOperation:
    operation: str
    path: str
    content: str = ""
    old_text: str = ""
    category: str = ""
    quality_score: float = 0.0
    reason: str = ""
    rule_id: str = ""
    confidence: float = 0.0
    tags: list[str] = field(default_factory=list)
_CONTEXT_FIELD_NAMES = frozenset(DiagnosticMemoryContext.__dataclass_fields__)
def _coerce_diagnostic_context(ctx: Any) -> Any:
    if isinstance(ctx, DiagnosticMemoryContext):
        return ctx
    if not isinstance(ctx, Mapping):
        return None
    return DiagnosticMemoryContext(**{
        name: ctx[name] for name in _CONTEXT_FIELD_NAMES if name in ctx})
def now_str() -> str:
    return datetime.now(UTC).astimezone().strftime("%Y%m%d%H%M%S")
def memory_date_stamp() -> str:
    return now_str()[:8]
_SUCCESS_TRUE_TEXT = frozenset({
    "true", "1", "yes", "on", "ok", "success", "succeeded",
    "successful", "是", "真",
})
_SUCCESS_FALSE_TEXT = frozenset({
    "false", "0", "no", "off", "failed", "failure", "否", "假", "失败",
})
def _success_marker(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        text = value.strip().lower()
        if text in _SUCCESS_TRUE_TEXT:
            return True
        if text in _SUCCESS_FALSE_TEXT:
            return False
        return None
    if isinstance(value, (int, float)):
        try:
            if not math.isfinite(value):
                return None
        except OverflowError:
            return None
        if value == 1:
            return True
        if value == 0:
            return False
    return None
def fix_succeeded(f: dict) -> bool:
    if not isinstance(f, dict):
        return False
    success = _success_marker(f.get("success"))
    return (success is not False
            and (f.get("status") in TX_FIXED_STATUSES or success is True))
def fix_failed(f: dict) -> bool:
    if not isinstance(f, dict):
        return False
    success = _success_marker(f.get("success"))
    if success is True:
        return False
    if success is False:
        return True
    status = f.get("status")
    return (status in TX_FAILED_STATUSES
            or status in TX_ROLLED_BACK_STATUSES)
def normalize_rule_id(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    text = value.strip()
    return text or None
def treatment_items(tx: dict) -> list:
    if not isinstance(tx, dict):
        return []
    for key in TREATMENT_ITEM_KEYS:
        value = tx.get(key)
        if isinstance(value, list) and value:
            return value
    return []
def pipeline_stage_views(pipeline_result: dict) -> tuple[dict, dict, dict, dict]:
    pipeline_result = dict_or_empty(pipeline_result)
    diag = dict_or_empty(pipeline_result.get("stage1_diagnosis"))
    cv = _unwrap_cv_results(pipeline_result.get("stage2_cross_validation"))
    tx = dict_or_empty(pipeline_result.get("stage4_treatment_execution"))
    review = dict_or_empty(pipeline_result.get("stage5_review"))
    return diag, cv, tx, review
def _tx_pick_count(tx: dict, *keys: str) -> tuple[int, bool]:
    for k in keys:
        v = tx.get(k)
        if is_valid_count_form(v):
            return safe_int(v), True
    return 0, False
_TX_APPLIED_ALIAS_KEYS = ("succeeded", "fixed", "fixes_applied", "fixed_count")
_TX_AI_APPLIED_KEYS = ("ai_fixed",)
_TX_FAILED_ALIAS_KEYS = ("failed", "failed_count", "error")
_TX_ROLLED_BACK_KEYS = ("rolled_back",)
def _tx_sum_counts(tx: dict,
                   groups: tuple[tuple[str, ...], ...]) -> tuple[int, bool]:
    total = 0
    found_any = False
    for keys in groups:
        value, found = _tx_pick_count(tx, *keys)
        if found:
            total += value
            found_any = True
    return total, found_any
def _tx_count_by_status(items: list) -> tuple[int, int]:
    n_fixed = sum(1 for t in items if fix_succeeded(t))
    n_failed = sum(1 for t in items if fix_failed(t))
    return n_fixed, n_failed
def _tx_executed_authoritative_only(executed: int, has_executed: bool,
                                    has_fixed: bool, has_failed: bool,
                                    items: list) -> bool:
    return (has_executed and executed > 0
            and not has_fixed and not has_failed and bool(items))
def _tx_fill_from_items(counts: dict[str, tuple[int, bool]],
                        item_fixed: int, item_failed: int) -> tuple[int, int]:
    executed, has_executed = counts["executed"]
    fixed, has_fixed = counts["fixed"]
    failed, has_failed = counts["failed"]
    if not (has_executed and executed > 0):
        has_fixed = has_fixed and fixed > 0
        has_failed = has_failed and failed > 0
    if not has_fixed:
        fixed = item_fixed
    if not has_failed:
        failed = item_failed
    return fixed, failed
def _tx_resolve_executed(counts: dict[str, tuple[int, bool]], items: list,
                         item_fixed: int, item_failed: int,
                         fixed: int, failed: int) -> tuple[int, int, int]:
    executed, has_executed = counts["executed"]
    _, has_fixed = counts["fixed"]
    _, has_failed = counts["failed"]
    if not (has_executed or has_fixed or has_failed):
        executed = len(items) if items else executed
    elif _tx_executed_authoritative_only(
            executed, has_executed, has_fixed, has_failed, items):
        fixed, failed = item_fixed, item_failed
    elif not has_executed and (has_fixed or has_failed):
        executed = fixed + failed
    return max(executed, fixed + failed), fixed, failed
def _tx_fallback_counts(counts: dict[str, tuple[int, bool]],
                        items: list) -> tuple[int, int, int]:
    item_fixed, item_failed = _tx_count_by_status(items) if items else (0, 0)
    fixed, failed = _tx_fill_from_items(counts, item_fixed, item_failed)
    return _tx_resolve_executed(counts, items, item_fixed, item_failed,
                               fixed, failed)
def treatment_counts(tx: dict) -> dict:
    if not isinstance(tx, dict):
        return {"executed": 0, "fixed": 0, "failed": 0}
    counts = {
        "executed": _tx_pick_count(tx, "executed"),
        "fixed": _tx_sum_counts(
            tx, (_TX_APPLIED_ALIAS_KEYS, _TX_AI_APPLIED_KEYS)),
        "failed": _tx_sum_counts(
            tx, (_TX_FAILED_ALIAS_KEYS, _TX_ROLLED_BACK_KEYS)),
    }
    executed, fixed, failed = _tx_fallback_counts(
        counts, treatment_items(tx))
    return {"executed": executed, "fixed": fixed, "failed": failed}
def str_memory_paths(ctx: DiagnosticMemoryContext | None) -> set[str]:
    ctx = _coerce_diagnostic_context(ctx)
    if not ctx:
        return set()
    return {p for p in as_list(ctx.raw_memory_paths) if isinstance(p, str)}
def pick_first(source: Mapping, keys: tuple[str, ...], default: Any = None) -> Any:
    if not isinstance(source, Mapping):
        return default
    for key in keys:
        if key in source and source[key] is not None:
            return source[key]
    return default
def pick_text(source: dict, keys: tuple[str, ...], default: str = "") -> str:
    value = pick_first(source, keys, default)
    return value if isinstance(value, str) else str(value)
def md_cell(value: Any) -> str:
    return (str(value).replace("|", "\\|")
            .replace("\r", " ").replace("\n", " "))
_PATH_SEGMENT_STRIP_RE = re.compile(r'[\\/:*?"<>|\x00-\x1f]')
def path_segment(value: Any) -> str:
    if value is None:
        return ""
    text = _PATH_SEGMENT_STRIP_RE.sub("_", str(value).strip())
    text = text.replace("..", "_")
    return text.strip(" .") or ""
def safe_int(value: Any, default: int = 0) -> int:
    if isinstance(value, int) and not isinstance(value, bool):
        return max(0, value)
    parsed = count_tasks(value)
    return default if parsed is None else parsed
def parse_nonneg_count_str(value: str) -> bool:
    try:
        parsed = float(value)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e,
                      context=f'parse_nonneg_count_str:{type(_e).__name__}')
        return False
    return math.isfinite(parsed) and parsed >= 0 and parsed.is_integer()
def is_valid_count_form(value: Any) -> bool:
    if isinstance(value, int) and not isinstance(value, bool):
        return value >= 0
    if is_finite_num(value):
        return value >= 0 and value.is_integer()
    if isinstance(value, str):
        return parse_nonneg_count_str(value)
    return False
def is_valid_memory_score(value: Any) -> bool:
    return is_finite_num(value) and 0 <= value <= 100
def total_findings_count(diag: dict) -> int:
    if not isinstance(diag, dict):
        return 0
    raw = diag.get("total_findings")
    if raw is not None and is_valid_count_form(raw):
        return safe_int(raw)
    findings = diag.get("findings")
    return len(findings) if isinstance(findings, list) else 0
def has_total_findings(diag: dict) -> bool:
    if not isinstance(diag, dict) or not diag:
        return False
    raw = diag.get("total_findings")
    if raw is not None and is_valid_count_form(raw):
        return True
    return isinstance(diag.get("findings"), list)
def total_findings_signal(diag: dict) -> int | None:
    return total_findings_count(diag) if has_total_findings(diag) else None
def _pick_valid_count(source: dict, keys: tuple[str, ...]) -> tuple[int, bool]:
    for key in keys:
        value = source.get(key)
        if value is not None and is_valid_count_form(value):
            return safe_int(value), True
    return 0, False
_CV_FP_COUNT_KEYS = ("fp_filtered_count", "false_positive_count",
                     "fp_count", "degraded_count")
_CV_FP_SUPPRESSED_KEYS = ("findings_suppressed", "suppressed")
_CV_CONFIRMED_KEYS = ("confirmed", "confirmed_count")
def first_valid_count_signal(source: dict,
                             keys: tuple[str, ...]) -> int | None:
    if not isinstance(source, dict):
        return None
    explicit, found = _pick_valid_count(source, keys)
    return explicit if found else None
def rules_triggered_signal(cv_results: dict) -> int | None:
    return first_valid_count_signal(
        cv_results, ("rules_triggered", "rules_applied_count"))
def rules_triggered_count(cv_results: dict) -> int:
    signal = rules_triggered_signal(cv_results)
    return 0 if signal is None else signal
def cv_fp_count_signal(cv_results: dict) -> int | None:
    if not isinstance(cv_results, dict) or not cv_results:
        return None
    signal = first_valid_count_signal(cv_results, _CV_FP_COUNT_KEYS)
    if signal is not None:
        return signal
    degraded = cv_results.get("degraded_findings")
    if isinstance(degraded, list) and degraded:
        return len(degraded)
    signal = first_valid_count_signal(cv_results, _CV_FP_SUPPRESSED_KEYS)
    if signal is not None:
        return signal
    return 0 if isinstance(degraded, list) else None
def cv_confirmed_signal(cv_results: dict) -> int | None:
    if not isinstance(cv_results, dict) or not cv_results:
        return None
    signal = first_valid_count_signal(cv_results, _CV_CONFIRMED_KEYS)
    if signal is not None:
        return signal
    confirmed = cv_results.get("confirmed_findings")
    return len(confirmed) if isinstance(confirmed, list) else None
def iter_rule_findings(findings) -> Iterator[tuple[str, dict]]:
    for finding in findings if isinstance(findings, list) else ():
        if not isinstance(finding, dict):
            continue
        rid = normalize_rule_id(finding.get("rule_id"))
        if rid:
            yield rid, finding
def pattern_rule_ids(patterns: Any) -> set[str]:
    return {rid for rid, _pattern in iter_rule_findings(patterns)}
def last_summary_dict(ctx: DiagnosticMemoryContext | None) -> dict | None:
    ctx = _coerce_diagnostic_context(ctx)
    summary = ctx.last_diagnosis_summary if ctx is not None else None
    return summary if isinstance(summary, dict) and summary else None
_SUCCESS_RATE_RE = re.compile(
    r"(?:成功率|success[_ -]rate)[:：\s]*([\d.]+%?)", re.IGNORECASE)
RULE_ID_BARE_RE = re.compile(
    r"((?<![A-Za-z0-9_])[A-Z]+-?\d+(?![A-Za-z0-9_])"
    r"|(?<![A-Za-z0-9_])(?:[a-z]+-\d+|[a-z]{1,4}\d+)(?![A-Za-z0-9_]))")
_SEVERITY_TOKEN_RE = re.compile(r"P\d")
def _is_rule_token(token: str) -> bool:
    return _SEVERITY_TOKEN_RE.fullmatch(token.upper()) is None
_SUCCESS_NEG_CONTEXT_RE = re.compile(
    r"unsucce"
    r"|(?<![a-z0-9])(?:no|not|never|without|cannot)\s+(?:a\s+|any\s+)?succe"
    r"|(?<![a-z0-9])succe[a-z]*\s+"
    r"(?:(?:was|were|is|did|does|could|would|has|have|had)\s+)?"
    r"(?:not|never)\b"
    r"|未成功|不成功|没有成功|无成功",
    re.IGNORECASE)
_SUCCESS_KW_RE = re.compile(
    r"(?<![a-z])(?:succe(?!(?:ss[_ -]?rate))|成功(?!率))", re.IGNORECASE)
_SUCCESS_LABELED_VALUE_RE = re.compile(
    r"(?<![a-z0-9])(?:success|成功)\s*(?:[:：=]|为|是)\s*([\w./-]+%?)",
    re.IGNORECASE)
_FIX_WORD_RE = re.compile(r"(?<![a-z0-9])fix")
_PERF_WORD_RE = re.compile(r"(?<![a-z0-9])perf(?![a-z])")
_FP_WORD_RE = re.compile(r"(?<![a-z0-9])fp")
_TP_WORD_RE = re.compile(r"(?<![a-z0-9])tp")
_SUMMARY_PLACEHOLDER_CAP = 1000
def _parse_count(match: re.Match | None) -> int:
    return safe_int(match.group(1)) if match else 0
def _extract_rule_id(content: str, path: str) -> str:
    rule_match = re.search(r"(?:rule_id|规则(?:ID)?)[:：\s|]*([A-Z]+-?\d+)",
                           content, re.IGNORECASE)
    if rule_match:
        labeled = rule_match.group(1).upper()
        if _is_rule_token(labeled):
            return labeled
    return extract_bare_rule_id(path)
def extract_bare_rule_id(content: str) -> str:
    for match in RULE_ID_BARE_RE.finditer(content or ""):
        token = match.group(1).upper()
        if _is_rule_token(token):
            return token
    return ""
def _explicit_rate_value(raw: Any) -> float | None:
    text = raw.strip() if isinstance(raw, str) else raw
    has_percent = isinstance(text, str) and text.endswith("%")
    numeric = safe_float(text[:-1] if has_percent else text, None)
    if not is_finite_num(numeric) or not 0.0 <= numeric <= 100.0:
        return None
    return numeric / 100.0 if has_percent else normalize_success_rate(numeric)
def _success_rate_from_content(content: str) -> float | None:
    match = _SUCCESS_RATE_RE.search(content)
    return _explicit_rate_value(match.group(1)) if match is not None else None
_FIXER_TABLE_CELL = r"((?:\\.|[^|\r\n])+?)"
_FIXER_NAME_ROW_RE = re.compile(
    rf"\|\s*{_FIXER_TABLE_CELL}\s*\|\s*\d+\s*/\s*\d+\s*\|")
def _fixer_cell_text(value: str) -> str:
    return value.replace("\\|", "|").strip()
def extract_fixer_name(content: str) -> str:
    match = re.search(r"修复器[:：\s]*(.+?)(?:性能快照|处理规则)", content)
    if match:
        return match.group(1).strip()
    match = re.search(r"修复模式[:：\s]+([\w.-]+)", content)
    if match:
        return match.group(1)
    match = re.search(
        r"(?:(?<![A-Za-z0-9_])fixer|修复器)[:：\s]+([\w.-]+)", content, re.IGNORECASE
    )
    if match:
        return match.group(1)
    match = re.search(r"(?:^|\n)\s*(?:summary[:：]\s*)?([\w.-]+)[:：]\s*成功率", content)
    if match:
        return match.group(1)
    match = _FIXER_NAME_ROW_RE.search(content)
    if match:
        return _fixer_cell_text(match.group(1))
    return ""
def _extract_reason(content: str) -> str:
    match = re.search(r"(?:reason|原因|因为)(?![A-Za-z0-9_])[:：\s]*(.+?)(?:\n|$)",
                      content, re.IGNORECASE)
    return match.group(1).strip() if match else ""
def _explicit_success_rate(content: str) -> float | None:
    rate_match = _SUCCESS_RATE_RE.search(content)
    if rate_match is not None:
        return _explicit_rate_value(rate_match.group(1))
    labeled_success = _SUCCESS_LABELED_VALUE_RE.search(content)
    if labeled_success is not None:
        raw_value = labeled_success.group(1).strip()
        numeric_rate = _explicit_rate_value(raw_value)
        if numeric_rate is not None:
            return numeric_rate
        marker = _success_marker(raw_value)
        return None if marker is None else float(marker)
    if _SUCCESS_NEG_CONTEXT_RE.search(content):
        return 0.0
    if _SUCCESS_KW_RE.search(content):
        return 1.0
    return None
def _fixer_table_success_rate(stats: dict[str, dict]) -> float | None:
    total = success = 0
    for entry in stats.values():
        if not isinstance(entry, dict):
            continue
        total += safe_int(entry.get("total"))
        success += safe_int(entry.get("success"))
    if total <= 0:
        return None
    return normalize_success_rate(success / total)
def _is_pdca_page(text: str) -> bool:
    return "pdca" in text
def _contains_any(text: str, *markers: str) -> bool:
    return any(marker in text for marker in markers)
def _is_fixer_perf_page(text: str) -> bool:
    return bool(_contains_any(text, "fixer", "修复器") and (
        _contains_any(text, "performance", "性能")
        or _PERF_WORD_RE.search(text)))
def _is_fix_learning_page(text: str) -> bool:
    return bool((_FIX_WORD_RE.search(text) or "修复" in text)
                and _contains_any(text, "pattern", "模式")
                and _contains_any(text, "learning", "学习", "template", "模板"))
def _is_regression_page(text: str) -> bool:
    return _contains_any(text, "regression", "回归检测", "诊断回归")
def _is_rule_evolution_page(text: str) -> bool:
    return (_contains_any(text, "rule", "规则")
            and _contains_any(text, "evolution", "演进"))
def _is_enhancement_impact_page(text: str) -> bool:
    return (("enhancement" in text and _contains_any(text, "impact", "效果"))
            or "增强效果追踪" in text)
def _is_cross_session_page(text: str) -> bool:
    return ("cross_session" in text
            or _contains_any(text, "跨会话经验", "跨会话顽固",
                             "跨会话成功修复", "跨会话失败修复",
                             "跨会话pdca", "跨会话趋势"))
def _is_diag_summary_page(text: str) -> bool:
    return (("diagnostic" in text and "summary" in text)
            or _contains_any(text, "诊断摘要", "diag-summary", "diag_summary"))
def _is_fp_pattern_page(text: str) -> bool:
    # 第二组必须是真正的"模式"指示词：此前混入的 "误报"/"false" 与第一组
    # 重叠，使 AND 退化为"含误报字样"，CV 调优/修复结果/振荡页只要提到
    # 误报率就被抢占为 fp_pattern（_CATEGORY_PREDICATES 中 FP 排在前）。
    return ((_FP_WORD_RE.search(text) is not None
             or _contains_any(text, "误报", "false positive"))
            and _contains_any(text, "pattern", "模式"))
def _is_tp_pattern_page(text: str) -> bool:
    # 同上："真阳性" 与第一组重叠，"true" 既覆盖 "true positive" 又会命中
    # 代码片段里的 True 字面量，均不是模式指示词。
    return ((_TP_WORD_RE.search(text) is not None
             or _contains_any(text, "真阳性", "确认模式", "true positive"))
            and _contains_any(text, "pattern", "模式", "确认"))
def _is_fix_result_page(text: str) -> bool:
    return bool((_FIX_WORD_RE.search(text) or "修复" in text)
                and _contains_any(text, "success", "result", "成功", "结果"))
def _is_oscillation_page(text: str) -> bool:
    return _contains_any(text, "oscillation", "振荡", "不稳定")
_CV_WORD_RE = re.compile(r"(?<![a-z0-9])cv(?![a-z])", re.IGNORECASE)
def _is_cv_tuning_page(text: str) -> bool:
    return ((_CV_WORD_RE.search(text) is not None and _contains_any(
        text, "tuning", "调优", "threshold", "阈值"))
            or "严重性校准" in text)
_CATEGORY_PREDICATES = [
    (CATEGORY_FIXER_PERF_SYNC, _is_fixer_perf_page),
    (CATEGORY_FIX_LEARNING, _is_fix_learning_page),
    (CATEGORY_REGRESSION, _is_regression_page),
    (CATEGORY_RULE_EVOLUTION, _is_rule_evolution_page),
    (CATEGORY_ENHANCEMENT_IMPACT, _is_enhancement_impact_page),
    (CATEGORY_DIAGNOSTIC_SUMMARY, _is_diag_summary_page),
    (CATEGORY_FP_PATTERN, _is_fp_pattern_page),
    (CATEGORY_TP_PATTERN, _is_tp_pattern_page),
    (CATEGORY_FIX_RESULT, _is_fix_result_page),
    (CATEGORY_OSCILLATION, _is_oscillation_page),
    (CATEGORY_CV_TUNING, _is_cv_tuning_page),
]
def infer_memory_category(path: str, summary: str, content: str) -> str:
    path = _as_str_field(path)
    summary = _as_str_field(summary)
    content = _as_str_field(content)
    text = f"{path} {summary} {content[:500]}".lower()
    _path_l = path.lower()
    header = f"{path} {summary}".lower()
    if _is_cross_session_page(header):
        return CATEGORY_CROSS_SESSION_LESSON
    page_name = _path_l.replace("\\", "/").rsplit("/", 1)[-1]
    if page_name.startswith(("复盘-", "复盘改进-", "质量趋势-")):
        return CATEGORY_DIAGNOSTIC_SUMMARY
    if "修复经验" in path or "fix-result" in _path_l or "fix_result" in _path_l:
        return CATEGORY_FIX_RESULT
    if _is_pdca_page(header):
        return CATEGORY_PDCA_TRACKING
    for category, predicate in _CATEGORY_PREDICATES:
        if predicate(text):
            return category
    return ""
def parse_pattern_memory(content: str, path: str) -> dict | None:
    if not content:
        return None
    rule_id = _extract_rule_id(content, path)
    if not rule_id:
        return None
    reason = _extract_reason(content) or content[:100]
    return {
        "rule_id": rule_id,
        "pattern": content[:200],
        "keywords": _fp_pattern_keywords(content),
        "reason": reason,
        "confidence": 0.7,
        "source_path": path,
    }
_FIXER_TABLE_ROW_RE = re.compile(
    rf"(?m)^\s*\|\s*{_FIXER_TABLE_CELL}\s*\|\s*(\d+)\s*/\s*(\d+)\s*"
    rf"\|\s*([\d.]+)%\s*\|\s*$")
def _parse_fixer_performance_table(content: str) -> dict[str, dict]:
    stats: dict[str, dict] = {}
    for match in _FIXER_TABLE_ROW_RE.finditer(content or ""):
        fixer = _fixer_cell_text(match.group(1))
        success = safe_int(match.group(2))
        total = safe_int(match.group(3))
        if not fixer or total <= 0:
            continue
        success = max(0, min(success, total))
        slot = stats.setdefault(
            fixer, {"success": 0, "total": 0, "success_rate": 0.0})
        slot["success"] += success
        slot["total"] += total
        slot["success_rate"] = slot["success"] / slot["total"]
    return stats
def _latest_fix_result_update(content: str) -> str | None:
    latest = None
    for match in re.finditer(
            rf"(?m)^ {{0,3}}{re.escape(FIX_RESULT_UPDATE_HEADING)}[ \t]*\r?$",
            content):
        latest = match
    return None if latest is None else content[latest.end():]
def parse_fix_result_memory(content: str, path: str) -> dict | None:
    if not content:
        return None
    rule_id = _extract_rule_id(content, path)
    if not rule_id:
        return None
    latest_update = _latest_fix_result_update(content)
    stats_scope = content if latest_update is None else latest_update
    fixer_name = extract_fixer_name(stats_scope) or "unknown"
    fixer_stats = _parse_fixer_performance_table(stats_scope)
    success_rate = _explicit_success_rate(stats_scope)
    if success_rate is None:
        success_rate = _fixer_table_success_rate(fixer_stats)
    return {
        "rule_id": rule_id,
        "fixer_name": fixer_name,
        "success": None if success_rate is None else success_rate >= 0.5,
        "success_rate": success_rate,
        "fixer_stats": fixer_stats,
        "source_path": path,
    }
def parse_oscillation_memory(content: str, path: str) -> dict | None:
    if not content:
        return None
    param_match = re.search(r"(?:param_name|param|参数)(?![A-Za-z0-9_])[:：\s]*(\w+)", content, re.IGNORECASE)
    param_name = param_match.group(1) if param_match else ""
    if not param_name:
        return None
    safe_match = re.search(r"(?:safe_value|safe|安全值)(?![A-Za-z0-9_])[:：\s]*([+-]?[\w.]+)", content, re.IGNORECASE)
    safe_value = safe_match.group(1) if safe_match else ""
    reason = _extract_reason(content)
    return {
        "param_name": param_name,
        "safe_value": safe_value,
        "reason": reason,
        "source_path": path,
    }
_SUMMARY_FINDINGS_SECTION_RE = re.compile(
    r"^## 规则严重度快照[ \t]*\r?\n(.*?)(?=^##\s|\Z)",
    re.MULTILINE | re.DOTALL)
_SUMMARY_FINDING_ROW_RE = re.compile(
    r"^\|\s*((?:\\.|[^|\r\n])*?)\s*\|\s*"
    r"((?:\\.|[^|\r\n])*?)\s*\|[ \t]*$", re.MULTILINE)
def _summary_snapshot_findings(content: str) -> list[dict] | None:
    section = _SUMMARY_FINDINGS_SECTION_RE.search(content)
    if section is None:
        return None
    findings: list[dict] = []
    for match in _SUMMARY_FINDING_ROW_RE.finditer(section.group(1)):
        rule_id = normalize_rule_id(match.group(1).replace(r"\|", "|"))
        severity = match.group(2).replace(r"\|", "|").strip()
        if (not rule_id or rule_id == "规则ID"
                or not rule_id.strip("-: ")):
            continue
        findings.append({"rule_id": rule_id, "severity": severity})
    return findings
def parse_diagnostic_summary(content: str, path: str) -> dict | None:
    if not content:
        return None
    summary = _summary_scalar_fields(content)
    if summary is None:
        return None
    summary.update(_summary_count_fields(content))
    snapshot = _summary_snapshot_findings(content)
    if snapshot is not None:
        summary["findings"] = snapshot
    if summary.get("total_findings") == 0:
        summary["findings"] = []
    summary["source_path"] = path
    return summary
_SUMMARY_COUNT_PATTERNS: tuple[tuple[str, str], ...] = (
    ("total_findings", r"(?:总发现数|总发现|total_findings)[:：\s|]*(\d+)"),
    ("cv_confirmed", r"(?:CV确认数|CV确认|cv_confirmed)[:：\s|]*(\d+)"),
    ("cv_rules_triggered", r"(?:CV规则触发|rules_triggered)[:：\s|]*(\d+)"),
)
_SUMMARY_RATE_PATTERNS: tuple[tuple[str, str], ...] = (
    ("fp_rate", r"(?:FP率|fp_rate)[:：\s|]*([\d.]+%?)"),
    ("fix_success_rate", r"(?:修复成功率|fix_success_rate)[:：\s|]*([\d.]+%?)"),
)
_SUMMARY_BASELINE_KEYS = ("total_findings", "cv_confirmed",
                          "fp_rate", "fix_success_rate", "review_score")
_SUMMARY_TREND_TOTAL_RE = re.compile(
    r"\|\s*总发现\s*\|\s*(?:\d+|N/A)\s*\|\s*(\d+|N/A)\s*\|",
    re.IGNORECASE)
def _summary_scalar_fields(content: str) -> dict | None:
    fields: dict[str, Any] = {}
    trend_total = _SUMMARY_TREND_TOTAL_RE.search(content)
    for key, pattern in _SUMMARY_COUNT_PATTERNS:
        if key == "total_findings" and trend_total is not None:
            fields[key] = (None if trend_total.group(1).upper() == "N/A"
                           else _parse_count(trend_total))
            continue
        match = re.search(pattern, content, re.IGNORECASE)
        fields[key] = _parse_count(match) if match is not None else None
    for key, pattern in _SUMMARY_RATE_PATTERNS:
        match = re.search(pattern, content, re.IGNORECASE)
        fields[key] = (_explicit_rate_value(match.group(1))
                       if match is not None else None)
    fields["review_score"] = _summary_review_score(content)
    if all(fields[key] is None for key in _SUMMARY_BASELINE_KEYS):
        return None
    return fields
def _summary_review_score(content: str) -> float | None:
    score_match = re.search(
        r"(?:\|\s*复盘评分\s*\|\s*(\d+(?:\.\d+)?(?![\d.]))\s*\|\s*$"
        r"|(?:复盘评分|review_score)['\"]?:\s*(\d+(?:\.\d+)?(?![\d.]))"
        r"|复盘评分\s*\d+(?:\.\d+)?\s*→\s*(\d+(?:\.\d+)?(?![\d.]))"
        r"|\|\s*复盘评分\s*\|\s*\d+(?:\.\d+)?\s*\|\s*(\d+(?:\.\d+)?(?![\d.]))\s*\|"
        r"|^\s*summary\s*:\s*复盘(\d+(?:\.\d+)?)分)",
        content, re.IGNORECASE | re.MULTILINE)
    return (safe_float(next(
        g for g in score_match.groups() if g is not None))
        if score_match else None)
def _summary_count_fields(content: str) -> dict:
    cv_tunings_match = re.search(r"(?:CV调优数|cv_tunings_count)[:：\s|]*(\d+)", content, re.IGNORECASE)
    enhancements_match = re.search(r"(?:增强建议数|enhancements_count)[:：\s|]*(\d+)", content, re.IGNORECASE)
    failed_match = re.search(r"(?:治疗失败|tx_failed)[:：\s|]*(\d+)", content, re.IGNORECASE)
    executed_match = re.search(r"(?:治疗执行|tx_executed)[:：\s|]*(\d+)", content, re.IGNORECASE)
    cv_tunings_count = min(
        _parse_count(cv_tunings_match), _SUMMARY_PLACEHOLDER_CAP)
    enhancements_count = min(
        _parse_count(enhancements_match), _SUMMARY_PLACEHOLDER_CAP)
    return {
        "cv_tunings": [{} for _ in range(cv_tunings_count)],
        "enhancements": [{} for _ in range(enhancements_count)],
        "failed_count": (
            _parse_count(failed_match) if failed_match is not None else None),
        "executed_count": (
            _parse_count(executed_match) if executed_match is not None else None),
    }
_CV_TUNING_RULE_LABEL_RE = re.compile(
    r"(?:rule_id|规则(?:ID)?)[:：\s|]*([A-Z]+-?\d+)", re.IGNORECASE)
_CV_TUNING_CONTEXT_RE = re.compile(
    r"调整|调优|阈值|校准|tuning|threshold|calibrat", re.IGNORECASE)
def _cv_tuning_rule_id(content: str) -> str:
    for labeled in _CV_TUNING_RULE_LABEL_RE.finditer(content):
        token = labeled.group(1).upper()
        if _is_rule_token(token):
            return token
    for line in content.splitlines():
        if not _CV_TUNING_CONTEXT_RE.search(line):
            continue
        for match in RULE_ID_BARE_RE.finditer(line):
            token = match.group(1)
            if _is_rule_token(token):
                return token.upper()
    return ""
def parse_cv_tuning_memory(content: str, path: str) -> dict | None:
    if not content:
        return None
    rule_id = _cv_tuning_rule_id(content)
    if not rule_id:
        return None
    adj_match = re.search(r"(?:adjustment|调整)[:：\s]*([+-]?[\d.]+)", content, re.IGNORECASE)
    adjustment = safe_float(adj_match.group(1)) if adj_match else 0.0
    reason = _extract_reason(content) or " ".join(content[:100].split())
    return {
        "rule_id": rule_id,
        "adjustment": adjustment,
        "reason": reason,
        "timestamp": extract_path_ts(path),
        "source_path": path,
    }
def extract_path_ts(path: str) -> str:
    if not isinstance(path, str):
        return ""
    m = re.search(r"(?<!\d)(\d{14})(?!\d)", path)
    if m:
        return m.group(1)
    m = re.search(r"(?<!\d)(\d{8})(?!\d)", path)
    return m.group(1) if m else ""
def ts_no_older(curr_ts: str, prev_ts: str) -> bool | None:
    if not curr_ts and not prev_ts:
        return None
    if curr_ts and not prev_ts:
        return True
    if not curr_ts and prev_ts:
        return False
    _n = min(len(curr_ts), len(prev_ts))
    return curr_ts[:_n] >= prev_ts[:_n]
def is_newer(current: dict, previous: dict) -> bool:
    current = current if isinstance(current, dict) else {}
    previous = previous if isinstance(previous, dict) else {}
    curr_ts = extract_path_ts(current.get("source_path", ""))
    prev_ts = extract_path_ts(previous.get("source_path", ""))
    _verdict = ts_no_older(curr_ts, prev_ts)
    if _verdict is not None:
        return _verdict
    curr_findings = total_findings_count(current)
    prev_findings = total_findings_count(previous)
    return curr_findings >= prev_findings
def _new_rule_evidence() -> dict:
    return {"fp_count": 0, "tp_count": 0, "fp_reasons": [], "tp_reasons": [],
            "historical_adjustment": 0.0}
def _accumulate_pattern_evidence(rule_evidence: dict[str, dict],
                                 patterns: list, count_key: str,
                                 reasons_key: str) -> None:
    for rid, pattern in iter_rule_findings(patterns):
        ev = rule_evidence.setdefault(rid, _new_rule_evidence())
        ev[count_key] += 1
        reason = pattern.get("reason")
        if isinstance(reason, str) and reason:
            ev[reasons_key].append(reason)
def collect_ctx_evidence(ctx: DiagnosticMemoryContext) -> dict[str, dict]:
    ctx = _coerce_diagnostic_context(ctx)
    if not ctx:
        return {}
    evidence: dict[str, dict] = {}
    _accumulate_pattern_evidence(evidence, as_list(ctx.known_fp_patterns),
                                 "fp_count", "fp_reasons")
    _accumulate_pattern_evidence(evidence, as_list(ctx.known_tp_patterns),
                                 "tp_count", "tp_reasons")
    for rid, hist in iter_rule_findings(ctx.cv_tuning_history):
        ev = evidence.setdefault(rid, _new_rule_evidence())
        ev["historical_adjustment"] += safe_float(hist.get("adjustment"))
    return evidence
def _calibration(rid: str, severity: str, reason: str,
                 confidence: float) -> dict:
    return {"rule_id": rid, "suggested_severity": severity,
            "reason": reason, "confidence": confidence}
def get_rule_severity_calibrations(
    ctx: DiagnosticMemoryContext,
) -> list[dict]:
    calibrations: list[dict] = []
    for rid, data in collect_ctx_evidence(ctx).items():
        total = data["fp_count"] + data["tp_count"]
        if total < 3:
            continue
        fp_rate = data["fp_count"] / total
        if fp_rate > 0.7:
            calibrations.append(_calibration(
                rid, "P3",
                f"FP率{fp_rate:.0%}({data['fp_count']}/{total})，建议降级为P3",
                fp_rate))
        elif fp_rate < 0.1 and data["tp_count"] >= 5:
            calibrations.append(_calibration(
                rid, "P1",
                f"TP率{1-fp_rate:.0%}({data['tp_count']}/{total})，建议升级为P1",
                1 - fp_rate))
    return calibrations
_MEMORY_SEARCH_QUERIES: tuple[tuple[str, str, str], ...] = (
    ('false positive 误报 pattern rule_id', CATEGORY_FP_PATTERN,
     '搜索历史误报模式，用于调整CV规则避免重复误报'),
    ('true positive 确认 finding rule', CATEGORY_TP_PATTERN,
     '搜索历史真阳性模式，用于提升已知正确发现的置信度'),
    ('fix 修复 success rate 成功率 fixer', CATEGORY_FIX_RESULT,
     '搜索历史修复结果，用于治疗方案优先级排序'),
    ('oscillation 振荡 参数 不稳定 threshold', CATEGORY_OSCILLATION,
     '搜索已知振荡参数，避免使用不稳定配置'),
    ('diagnostic summary 诊断摘要 findings CV', CATEGORY_DIAGNOSTIC_SUMMARY,
     '搜索上次诊断摘要，用于增量对比和质量趋势追踪'),
    ('CV rule tuning 调优 阈值 confidence', CATEGORY_CV_TUNING,
     '搜索CV规则调优历史，用于持续性阈值优化'),
    ('增强效果 impact PDCA 追踪 feedback effectiveness', CATEGORY_ENHANCEMENT_IMPACT,
     '搜索历史增强效果和PDCA追踪记录，评估记忆驱动增强的实际效果'),
    ('回归 regression 诊断 新增 消失 severity drift', CATEGORY_REGRESSION,
     '搜索历史回归检测记录，用于跨会话回归对比'),
    ('规则演进 rule evolution FP TP 严重度 变化', CATEGORY_RULE_EVOLUTION,
     '搜索规则演进历史，用于规则生命周期管理'),
    ('修复模式学习 fix pattern learning template 成功修复器', CATEGORY_FIX_LEARNING,
     '搜索可复用修复模板，用于修复器选择指导'),
    ('修复器性能 fixer performance 同步 成功率 回滚 rollback', CATEGORY_FIXER_PERF_SYNC,
     '搜索修复器性能快照，用于治疗优先级排序和风险规避'),
    ('跨会话经验 lesson 顽固问题 persistent 成功策略 失败总结', CATEGORY_CROSS_SESSION_LESSON,
     '搜索跨会话经验教训，用于整体诊断治疗策略优化'),
    ('PDCA tracking 诊断 治疗 验证 改进 闭环 plan do check act', CATEGORY_PDCA_TRACKING,
     '搜索PDCA闭环追踪记录，用于诊断→治疗→验证→改进完整闭环追踪'),
)
def get_memory_search_queries() -> list[dict]:
    return [{"query": query, "purpose": purpose, "description": description}
            for query, purpose, description in _MEMORY_SEARCH_QUERIES]
def _as_str_field(value: Any) -> str:
    if isinstance(value, str):
        return value
    return safe_str(value) if value else ""
def _consume_pattern(ctx: DiagnosticMemoryContext, content: str, path: str,
                     *, field: str) -> None:
    pattern = parse_pattern_memory(content, path)
    if pattern:
        getattr(ctx, field).append(pattern)
def _consume_fix_result(ctx: DiagnosticMemoryContext, content: str,
                        path: str) -> None:
    fix_info = parse_fix_result_memory(content, path)
    if fix_info:
        rule_id = fix_info.get("rule_id", "")
        if rule_id:
            ctx.historical_fix_rates.setdefault(rule_id, []).append(fix_info)
def _consume_oscillation(ctx: DiagnosticMemoryContext, content: str,
                         path: str) -> None:
    osc = parse_oscillation_memory(content, path)
    if not osc:
        return
    param_name = osc.get("param_name", "")
    if not param_name:
        return
    if not _snapshot_accepted(ctx.oscillation_params.get(param_name), path):
        return
    ctx.oscillation_params[param_name] = osc
def _is_auxiliary_summary_path(path: Any) -> bool:
    if not isinstance(path, str):
        return False
    page_name = path.replace("\\", "/").rsplit("/", 1)[-1]
    return page_name.startswith(("质量趋势-", "复盘-", "复盘改进-"))
def _consume_diagnostic_summary(ctx: DiagnosticMemoryContext, content: str,
                                path: str) -> None:
    summary_dict = parse_diagnostic_summary(content, path)
    if not summary_dict:
        return
    existing = last_summary_dict(ctx)
    if existing is not None:
        incoming_auxiliary = _is_auxiliary_summary_path(path)
        existing_auxiliary = _is_auxiliary_summary_path(
            existing.get("source_path"))
        if incoming_auxiliary != existing_auxiliary:
            if incoming_auxiliary:
                return
            ctx.last_diagnosis_summary = summary_dict
            return
    if existing is None or is_newer(summary_dict, existing):
        ctx.last_diagnosis_summary = summary_dict
def _consume_cv_tuning(ctx: DiagnosticMemoryContext, content: str,
                       path: str) -> None:
    tuning = parse_cv_tuning_memory(content, path)
    if tuning:
        ctx.cv_tuning_history.append(tuning)
def _snapshot_accepted(existing: dict | None, path: str) -> bool:
    if existing is None:
        return True
    return ts_no_older(
        extract_path_ts(path),
        extract_path_ts(existing.get("source_path") or "")) is not False
def _consume_fixer_perf(ctx: DiagnosticMemoryContext, content: str,
                        path: str) -> None:
    fixer_name = extract_fixer_name(content)
    if not fixer_name:
        return
    if not _snapshot_accepted(ctx.fixer_performance.get(fixer_name), path):
        return
    rate = _success_rate_from_content(content)
    if rate is None:
        logger.info("_consume_fixer_perf: 快照无有效显式成功率，保留既有记录: %s",
                    path)
        return
    ctx.fixer_performance[fixer_name] = {
        "success_rate": rate,
        "source_path": path,
    }
def _consume_fix_learning(ctx: DiagnosticMemoryContext, content: str,
                          path: str) -> None:
    rule_id = _extract_rule_id(content, path)
    fixer_name = extract_fixer_name(content)
    if rule_id and fixer_name:
        ctx.fix_patterns.append({
            "rule_id": rule_id,
            "fixer": fixer_name,
            "source_path": path,
        })
def _consume_rule_evolution(ctx: DiagnosticMemoryContext, content: str,
                            path: str) -> None:
    rule_id = extract_bare_rule_id(content)
    if rule_id:
        ctx.rule_evolution.append({
            "rule_id": rule_id,
            "source_path": path,
        })
def _consume_passthrough(ctx: DiagnosticMemoryContext, content: str, path: str,
                         *, field: str) -> None:
    getattr(ctx, field).append({"source_path": path, "content": content})
_CATEGORY_CONSUMERS: dict[str, Callable[[DiagnosticMemoryContext, str, str], None]] = {
    CATEGORY_FP_PATTERN: partial(_consume_pattern, field="known_fp_patterns"),
    CATEGORY_TP_PATTERN: partial(_consume_pattern, field="known_tp_patterns"),
    CATEGORY_FIX_RESULT: _consume_fix_result,
    CATEGORY_OSCILLATION: _consume_oscillation,
    CATEGORY_DIAGNOSTIC_SUMMARY: _consume_diagnostic_summary,
    CATEGORY_CV_TUNING: _consume_cv_tuning,
    CATEGORY_FIXER_PERF_SYNC: _consume_fixer_perf,
    CATEGORY_FIX_LEARNING: _consume_fix_learning,
    CATEGORY_RULE_EVOLUTION: _consume_rule_evolution,
    CATEGORY_PDCA_TRACKING: partial(_consume_passthrough, field="pdca_history"),
    CATEGORY_REGRESSION: partial(_consume_passthrough, field="regression_history"),
    CATEGORY_ENHANCEMENT_IMPACT: partial(
        _consume_passthrough, field="enhancement_impact_history"),
    CATEGORY_CROSS_SESSION_LESSON: partial(
        _consume_passthrough, field="cross_session_lessons"),
}
def _consume_memory_entry(ctx: DiagnosticMemoryContext, mem: Any) -> None:
    mem_entry = normalize_mem_entry(mem)
    if mem_entry is None:
        return
    path = mem_entry["path"]
    if path:
        ctx.raw_memory_paths.append(path)
    ctx.raw_search_results.append(mem_entry)
    consumer = _CATEGORY_CONSUMERS.get(infer_memory_category(
        path, mem_entry["summary"], mem_entry["content"]))
    if consumer is not None:
        consumer(ctx, mem_entry["content"], path)
def _memory_detail_rank(mem: Any) -> int:
    if not isinstance(mem, dict):
        return -1
    for rank, key in ((2, "content"), (1, "snippet"), (0, "summary")):
        if mem.get(key):
            return rank
    return -1
def _normalized_memory_entries(memories: list) -> list[dict]:
    normalized: list[dict] = []
    path_indexes: dict[str, int] = {}
    path_ranks: dict[str, int] = {}
    for mem in memories:
        entry = normalize_mem_entry(mem)
        if entry is None:
            continue
        path = entry["path"]
        rank = _memory_detail_rank(mem)
        if not path:
            normalized.append(entry)
        elif path in path_indexes:
            if rank >= path_ranks[path]:
                normalized[path_indexes[path]] = entry
                path_ranks[path] = rank
        else:
            path_indexes[path] = len(normalized)
            path_ranks[path] = rank
            normalized.append(entry)
    return normalized
def prepare_diagnostic_context(
    memory_search_results: list[dict],
    existing_memories: list[dict] | None = None,
) -> DiagnosticMemoryContext:
    ctx = DiagnosticMemoryContext()
    ctx.loaded_at = now_str()
    all_memories: list = []
    for source in (memory_search_results, existing_memories):
        all_memories.extend(materialize_existing_memories(source))
    for mem in _normalized_memory_entries(all_memories):
        _consume_memory_entry(ctx, mem)
    logger.info(
        "[MemoryBridge] 诊断上下文加载完成: FP=%d, TP=%d, FixRates=%d rules, "
        "Oscillation=%d, CVTuning=%d, Summary=%s",
        len(ctx.known_fp_patterns),
        len(ctx.known_tp_patterns),
        len(ctx.historical_fix_rates),
        len(ctx.oscillation_params),
        len(ctx.cv_tuning_history),
        "有" if ctx.last_diagnosis_summary else "无",
    )
    return ctx
def validate_memory_context(ctx: DiagnosticMemoryContext | None) -> list[str]:
    ctx = _coerce_diagnostic_context(ctx)
    if ctx is None:
        return ["记忆上下文为None，将以无记忆模式运行"]
    issues = []
    if not ctx.known_fp_patterns and not ctx.known_tp_patterns:
        issues.append("无FP/TP模式记忆，CV调优能力受限")
    if not ctx.historical_fix_rates:
        issues.append("无历史修复成功率数据，治疗增强能力受限")
    if not ctx.last_diagnosis_summary:
        issues.append("无上次诊断摘要，无法进行增量对比")
    return issues
_PRE_CREATION_SEARCH_QUERIES: tuple[tuple[str, str], ...] = (
    ("skill 技能 创建 经验 教训", "搜索技能创建的历史经验教训"),
    ("SKILL.md 规范 最佳实践", "搜索SKILL.md编写规范和最佳实践"),
    ("代码 审计 反模式 antipattern", "搜索已知代码反模式，避免在新技能中引入"),
)
def get_pre_creation_search_queries() -> list[dict]:
    return [{"query": query, "purpose": "pre_creation", "description": description}
            for query, description in _PRE_CREATION_SEARCH_QUERIES]
def _score_trend_block(prev_score: float | None, curr_score: float | None) -> dict:
    if prev_score is None or curr_score is None:
        return {
            "previous": prev_score,
            "current": curr_score,
            "delta": None,
            "direction": "unknown",
        }
    delta = curr_score - prev_score
    return {
        "previous": prev_score,
        "current": curr_score,
        "delta": round(delta, 1),
        "direction": "improving" if delta >= 5 else ("declining" if delta <= -5 else "stable"),
    }
def format_memory_trend_score(value: object) -> str:
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        try:
            number = float(value)
            if not math.isfinite(number):
                return "N/A"
            return f"{number:.1f}"
        except OverflowError as exc:
            log_swallowed(__name__, exc, context="format_memory_trend_score:OverflowError")
            return "N/A"
    return "N/A"
def _safe_count(value: Any) -> int:
    return len(value) if isinstance(value, (list, dict, set, tuple)) else 0
def _reason_text(source: dict) -> str:
    reason = source.get("reason")
    return reason if isinstance(reason, str) else ""
def _iter_known_fp_patterns(ctx: DiagnosticMemoryContext) -> Iterator[tuple[str, dict]]:
    for fp in as_list(ctx.known_fp_patterns):
        if isinstance(fp, dict):
            yield normalize_rule_id(fp.get("rule_id")), fp
def _apply_enhancement(result: dict, ctx: DiagnosticMemoryContext | None,
                       stage: str, apply: Callable[[dict, DiagnosticMemoryContext], None]) -> dict:
    if isinstance(result, Mapping):
        result = dict(result)
    else:
        logger.warning("[MemoryBridge] %s记忆增强输入非映射(%s)，按空结果处理",
                       stage, type(result).__name__)
        result = {}
    ctx = _coerce_diagnostic_context(ctx)
    if not ctx:
        return result
    try:
        enhanced = dict(result)
        apply(enhanced, ctx)
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] %s记忆增强异常: %s", stage, e)
        return result
    return enhanced
def _review_enhancements(enhanced: dict, ctx: DiagnosticMemoryContext) -> None:
    _review_score_trend(enhanced, ctx)
    _review_persistent_issues(enhanced, ctx)
    calibrations = get_rule_severity_calibrations(ctx)
    if calibrations:
        enhanced["_severity_calibrations"] = calibrations
def enhance_review_with_memory(
    review_result: dict,
    ctx: DiagnosticMemoryContext | None,
) -> dict:
    return _apply_enhancement(review_result, ctx, "复盘", _review_enhancements)
def _prev_score_or_none(ctx: DiagnosticMemoryContext) -> float | None:
    prev_raw = pick_first(last_summary_dict(ctx) or {}, ("review_score",))
    return safe_float(prev_raw) if is_valid_memory_score(prev_raw) else None
def _curr_score_or_none(result: dict) -> float | None:
    for key in ("overall_score", "score"):
        raw = result.get(key)
        if is_valid_memory_score(raw):
            return safe_float(raw)
    return None
def _review_score_trend(enhanced: dict, ctx: DiagnosticMemoryContext) -> None:
    if not last_summary_dict(ctx):
        return
    enhanced["_score_trend"] = _score_trend_block(
        _prev_score_or_none(ctx), _curr_score_or_none(enhanced))
def _review_persistent_issues(enhanced: dict,
                               ctx: DiagnosticMemoryContext) -> None:
    persistent_issues: list[dict] = []
    if ctx.known_fp_patterns:
        current_rules = pattern_rule_ids(enhanced.get("findings"))
        for rid, _fp in _iter_known_fp_patterns(ctx):
            if rid and rid in current_rules:
                persistent_issues.append({
                    "rule_id": rid,
                    "type": "persistent_fp",
                    "reason": f"规则{rid}在历史和当前诊断中均出现FP",
                })
    if persistent_issues:
        enhanced["_persistent_issues"] = persistent_issues
def _fupan_enhancements(enhanced: dict, ctx: DiagnosticMemoryContext) -> None:
    if last_summary_dict(ctx):
        enhanced["_memory_prev_score"] = _prev_score_or_none(ctx)
    enhanced["_memory_context_loaded"] = {
        "fp_patterns": _safe_count(ctx.known_fp_patterns),
        "tp_patterns": _safe_count(ctx.known_tp_patterns),
        "fix_rates": _safe_count(ctx.historical_fix_rates),
    }
    persistent = _fupan_persistent_patterns(ctx)
    if persistent:
        enhanced["_memory_persistent_patterns"] = persistent[:10]
def enhance_fupan_with_memory(
    fupan_result: dict,
    ctx: DiagnosticMemoryContext | None,
) -> dict:
    return _apply_enhancement(fupan_result, ctx, "fupan", _fupan_enhancements)
def _fupan_persistent_patterns(ctx: DiagnosticMemoryContext) -> list[dict]:
    persistent = []
    for rid, fp in _iter_known_fp_patterns(ctx):
        if not rid:
            continue
        persistent.append({
            "rule_id": rid,
            "type": "known_fp",
            "reason": _reason_text(fp)[:80],
        })
    return persistent
def _retro_enhancements(enhanced: dict, ctx: DiagnosticMemoryContext) -> None:
    if last_summary_dict(ctx):
        enhanced["_memory_score_trend"] = _score_trend_block(
            _prev_score_or_none(ctx), _curr_score_or_none(enhanced))
    _retro_persistent_improvements(enhanced, ctx)
def enhance_retrospective_with_memory(
    retro_result: dict,
    ctx: DiagnosticMemoryContext | None,
) -> dict:
    return _apply_enhancement(retro_result, ctx, "retrospective", _retro_enhancements)
def _retro_persistent_improvements(enhanced: dict,
                                    ctx: DiagnosticMemoryContext) -> None:
    improvements = as_list(enhanced.get("improvements"))
    if not (improvements and ctx.known_fp_patterns):
        return
    fp_rule_ids = pattern_rule_ids(ctx.known_fp_patterns)
    persistent_improvements = [
        imp for imp in improvements
        if isinstance(imp, dict)
        and normalize_rule_id(imp.get("rule_id")) in fp_rule_ids
    ]
    if persistent_improvements:
        enhanced["_memory_persistent_improvements"] = persistent_improvements
def _pc_fp_warnings(ctx: DiagnosticMemoryContext, code_content: str,
                    description: str) -> list[dict]:
    warnings: list[dict] = []
    for rid, fp in _iter_known_fp_patterns(ctx):
        if _fp_pattern_risk_matches(fp, code_content, description):
            warnings.append({
                "type": "known_fp_risk",
                "rule_id": rid or "",
                "reason": _reason_text(fp),
            })
    return warnings
_IDENTIFIER_TOKEN_RE = re.compile(
    r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*")
_FP_PATTERN_MAX_KEYWORDS = 8
_FP_PATTERN_MIN_TOKEN_LEN = 5
def _is_code_shaped_token(token: str) -> bool:
    return bool("_" in token or "." in token
                or re.search(r"[a-z][A-Z]", token)
                or sum(1 for ch in token if ch.isupper()) >= 2)
def _fp_pattern_keywords(pattern: str) -> list[str]:
    keywords: list[str] = []
    seen: set[str] = set()
    for match in _IDENTIFIER_TOKEN_RE.finditer(pattern):
        token = match.group(0).strip("._")
        if len(token) < _FP_PATTERN_MIN_TOKEN_LEN:
            continue
        if not _is_code_shaped_token(token):
            continue
        key = token.lower()
        if key in seen:
            continue
        seen.add(key)
        keywords.append(token)
        if len(keywords) >= _FP_PATTERN_MAX_KEYWORDS:
            break
    return keywords
def _fp_pattern_risk_matches(fp: dict, code_content: str,
                             description: str) -> bool:
    keywords = fp.get("keywords")
    if not (isinstance(keywords, list) and keywords):
        pattern = fp.get("pattern") or ""
        if not (isinstance(pattern, str) and pattern):
            return False
        keywords = _fp_pattern_keywords(pattern)
    haystack = f"{code_content}\n{description}"
    return any(kw in haystack for kw in keywords
               if isinstance(kw, str) and kw)
def _pc_osc_warnings(ctx: DiagnosticMemoryContext, code_content: str) -> list[dict]:
    warnings: list[dict] = []
    oscillation = ctx.oscillation_params if isinstance(ctx.oscillation_params, dict) else {}
    for param_name, info in oscillation.items():
        if not isinstance(param_name, str) or not isinstance(info, dict):
            continue
        if param_name in code_content:
            warnings.append({
                "type": "oscillation_param",
                "param": param_name,
                "safe_value": info.get("safe_value"),
                "reason": _reason_text(info),
            })
    return warnings
def _pc_fixer_suggestions(ctx: DiagnosticMemoryContext) -> list[dict]:
    suggestions: list[dict] = []
    if not isinstance(ctx.historical_fix_rates, dict):
        return suggestions
    for raw_rid, rates in ctx.historical_fix_rates.items():
        if not isinstance(rates, list):
            continue
        rid = normalize_rule_id(raw_rid)
        if not rid:
            continue
        for rate in rates:
            entry = _high_success_rate_entry(rate)
            if entry is not None:
                suggestions.append({
                    "type": "recommended_fixer",
                    "rule_id": rid,
                    "fixer": entry[0],
                    "success_rate": entry[1],
                })
    return suggestions
def _per_fixer_high_success_entry(stats: Any) -> tuple[str, float] | None:
    if not isinstance(stats, dict):
        return None
    candidates: list[tuple[str, float]] = []
    for fixer, entry in stats.items():
        if not isinstance(fixer, str) or not fixer or not isinstance(entry, dict):
            continue
        total = safe_int(entry.get("total"))
        if total <= 0:
            continue
        success = max(0, min(safe_int(entry.get("success")), total))
        rate = success / total
        if 0.8 <= rate <= 1.0:
            candidates.append((fixer, rate))
    return min(candidates, key=lambda item: (-item[1], item[0])) if candidates else None
def _high_success_rate_entry(rate: Any) -> tuple[str, float] | None:
    if not isinstance(rate, dict):
        return None
    stats = rate.get("fixer_stats")
    if isinstance(stats, dict) and stats:
        return _per_fixer_high_success_entry(stats)
    rate_value = rate.get("success_rate", 0)
    if not (_success_marker(rate.get("success")) is True
            and is_finite_num(rate_value)
            and 0.8 <= rate_value <= 1.0):
        return None
    fixer_name = rate.get("fixer_name")
    if isinstance(fixer_name, str) and fixer_name:
        return fixer_name, rate_value
    return None
def enhance_pre_creation_with_memory(
    description: str,
    code_content: str,
    ctx: DiagnosticMemoryContext | None = None,
) -> dict:
    result: dict[str, Any] = {
        "warnings": [],
        "suggestions": [],
        "known_patterns": {},
    }
    ctx = _coerce_diagnostic_context(ctx)
    if not ctx:
        return result
    description = description if isinstance(description, str) else ""
    code_content = code_content if isinstance(code_content, str) else ""
    try:
        result["warnings"] = (_pc_fp_warnings(ctx, code_content, description)
                              + _pc_osc_warnings(ctx, code_content))
        result["suggestions"] = _pc_fixer_suggestions(ctx)
        result["known_patterns"] = {
            "fp_count": _safe_count(ctx.known_fp_patterns),
            "tp_count": _safe_count(ctx.known_tp_patterns),
            "fix_rate_rules": _safe_count(ctx.historical_fix_rates),
        }
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] 创建前记忆增强异常: %s", e)
    return result
_IMPACT_RATE_FIELDS = ("fp_rate", "confirm_rate", "fix_success_rate")
_IMPACT_COUNT_FIELDS = ("total_findings", "cv_confirmed")
_IMPACT_COUNT_SOURCES = {
    "total_findings": (("total_findings",), ("findings",)),
    "cv_confirmed": (
        ("cv_confirmed", "confirmed_count", "confirmed"),
        ("confirmed_findings",),
    ),
}
_TRACKING_FP_RATE_RE = re.compile(
    r"FP率\s*(?:\d+(?:\.\d+)?%|N/A)\s*→\s*(?:(\d+(?:\.\d+)?)%|N/A)")
_TRACKING_CONFIRM_RATE_RE = re.compile(
    r"确认率\s*(?:\d+(?:\.\d+)?%|N/A)\s*→\s*(?:(\d+(?:\.\d+)?)%|N/A)")
_TRACKING_FIX_RATE_RE = re.compile(
    r"修复率\s*(?:\d+(?:\.\d+)?%|N/A)\s*→\s*(?:(\d+(?:\.\d+)?)%|N/A)")
_TRACKING_TOTAL_ROW_RE = re.compile(
    r"\|\s*总发现\s*\|\s*(\d+|N/A)\s*\|\s*(\d+|N/A)\s*\|")
def _tracking_rate(match: re.Match | None) -> float | None:
    if match is None or match.group(1) is None:
        return None
    rate = safe_float(match.group(1), None)
    return None if rate is None else rate / 100.0
def _impact_rates_from_entry(
    entry: Any,
) -> tuple[float | None, float | None, float | None] | None:
    if not isinstance(entry, dict):
        return None
    content = entry.get("content", "")
    if not isinstance(content, str):
        return None
    fp_match = _TRACKING_FP_RATE_RE.search(content)
    confirm_match = _TRACKING_CONFIRM_RATE_RE.search(content)
    fix_match = _TRACKING_FIX_RATE_RE.search(content)
    if fp_match is None and confirm_match is None and fix_match is None:
        return None
    return (_tracking_rate(fp_match), _tracking_rate(confirm_match),
            _tracking_rate(fix_match))
def _latest_impact_rates(
    history: list,
) -> tuple[dict[str, float], dict[str, str]]:
    latest: dict[str, float] = {}
    latest_ts: dict[str, str] = {}
    for entry in history:
        rates = _impact_rates_from_entry(entry)
        if rates is None:
            continue
        ts = extract_path_ts(entry.get("source_path") or "")
        for key, value in zip(_IMPACT_RATE_FIELDS, rates, strict=True):
            if value is None:
                continue
            if key not in latest or ts_no_older(ts, latest_ts[key]) is not False:
                latest[key] = value
                latest_ts[key] = ts
    return latest, latest_ts
def _latest_impact_total(history: list) -> tuple[int | None, str]:
    best_total: int | None = None
    best_ts = ""
    for entry in history:
        if not isinstance(entry, dict):
            continue
        content = entry.get("content")
        if not isinstance(content, str):
            continue
        match = _TRACKING_TOTAL_ROW_RE.search(content)
        if match is None or match.group(2) == "N/A":
            continue
        ts = extract_path_ts(entry.get("source_path") or "")
        if best_total is None or ts_no_older(ts, best_ts) is not False:
            best_total = safe_int(match.group(2))
            best_ts = ts
    return best_total, best_ts
def _baseline_from_impact_history(ctx: DiagnosticMemoryContext) -> dict | None:
    history = ctx.enhancement_impact_history
    if not isinstance(history, list) or not history:
        return None
    rates, rate_timestamps = _latest_impact_rates(history)
    total, total_timestamp = _latest_impact_total(history)
    if not rates and total is None:
        return None
    return {
        "total_findings": total,
        "cv_confirmed": None,
        "fp_rate": rates.get("fp_rate"),
        "confirm_rate": rates.get("confirm_rate"),
        "fix_success_rate": rates.get("fix_success_rate"),
        "review_score": None,
        "_field_timestamps": {
            **rate_timestamps,
            "total_findings": total_timestamp,
        },
    }
def _impact_history_is_newer(summary: dict, history: dict, field: str) -> bool:
    summary_ts = extract_path_ts(summary.get("source_path") or "")
    timestamps = history.get("_field_timestamps")
    history_ts = (timestamps.get(field, "")
                  if isinstance(timestamps, dict) else "")
    if not summary_ts or not history_ts:
        return False
    return ts_no_older(summary_ts, history_ts) is False
def _impact_baseline(ctx: DiagnosticMemoryContext) -> dict | None:
    summary = last_summary_dict(ctx)
    history = _baseline_from_impact_history(ctx)
    if not summary:
        return history
    if not history:
        return summary
    merged = dict(summary)
    for key in _IMPACT_RATE_FIELDS:
        if (not _impact_history_is_newer(summary, history, key)
                and _baseline_rate(merged.get(key)) is not None):
            continue
        fallback = _baseline_rate(history.get(key))
        if fallback is not None:
            merged[key] = fallback
    for key in _IMPACT_COUNT_FIELDS:
        if (not _impact_history_is_newer(summary, history, key)
                and _impact_baseline_count(merged, key) is not None):
            continue
        fallback = _impact_baseline_count(history, key)
        if fallback is not None:
            merged[key] = fallback
    return merged
def _collect_impact_current(current_result: dict) -> dict:
    diag_raw = current_result.get("stage1_diagnosis")
    diag = diag_raw if isinstance(diag_raw, dict) else {}
    cv_raw = current_result.get("stage2_cross_validation")
    cv = _unwrap_cv_results(cv_raw) if isinstance(cv_raw, dict) else {}
    tx = current_result.get("stage4_treatment_execution") or {}
    curr_total = total_findings_signal(diag)
    curr_confirmed = cv_confirmed_signal(cv) if cv else None
    curr_fp_filtered = cv_fp_count_signal(cv) if cv else None
    tx_counts = treatment_counts(tx)
    return {
        "total_findings": curr_total,
        "confirmed": curr_confirmed,
        "fp_filtered": curr_fp_filtered,
        "fixed": tx_counts["fixed"],
        "failed": tx_counts["failed"],
    }
def _impact_rate(value: Any) -> float:
    return min(1.0, max(0.0, safe_float(value)))
def _baseline_rate(value: Any) -> float | None:
    if not is_finite_num(value):
        return None
    return _impact_rate(value)
def _safe_ratio(numerator: float, denominator: float) -> float | None:
    return _impact_rate(numerator / denominator) if denominator > 0 else None
def _metric_block(previous: float | None, current: float | None) -> dict:
    if previous is None or current is None:
        return {
            "previous": None if previous is None else round(previous, 4),
            "current": None if current is None else round(current, 4),
            "delta": None,
        }
    return {"previous": round(previous, 4), "current": round(current, 4),
            "delta": round(current - previous, 4)}
def baseline_count(source: dict | None, count_keys: tuple[str, ...],
                    list_keys: tuple[str, ...] = ()) -> int | None:
    if not isinstance(source, dict):
        return None
    explicit, found = _pick_valid_count(source, count_keys)
    if found:
        return explicit
    for key in list_keys:
        value = source.get(key)
        if isinstance(value, list):
            return len(value)
    return None
def _impact_baseline_count(source: dict | None, field: str) -> int | None:
    count_keys, list_keys = _IMPACT_COUNT_SOURCES[field]
    return baseline_count(source, count_keys, list_keys)
def _build_impact_metrics(prev: dict, curr: dict) -> dict:
    prev_total = _impact_baseline_count(prev, "total_findings")
    prev_confirmed = _impact_baseline_count(prev, "cv_confirmed")
    prev_fp_rate = _baseline_rate(prev.get("fp_rate"))
    prev_fix_rate = _baseline_rate(prev.get("fix_success_rate"))
    curr_total = curr["total_findings"]
    curr_fp_rate = (
        _safe_ratio(curr["fp_filtered"], curr_total)
        if curr["fp_filtered"] is not None and curr_total is not None else None)
    curr_fix_rate = _safe_ratio(curr["fixed"], curr["fixed"] + curr["failed"])
    curr_confirm_rate = (
        _safe_ratio(curr["confirmed"], curr_total)
        if curr["confirmed"] is not None and curr_total is not None else None)
    prev_confirm_rate = (
        _safe_ratio(prev_confirmed, prev_total)
        if prev_confirmed is not None and prev_total is not None else None)
    if prev_confirm_rate is None:
        prev_confirm_rate = _baseline_rate(prev.get("confirm_rate"))
    return {
        "fp_rate": _metric_block(prev_fp_rate, curr_fp_rate),
        "confirm_rate": _metric_block(prev_confirm_rate, curr_confirm_rate),
        "fix_success_rate": _metric_block(prev_fix_rate, curr_fix_rate),
        "total_findings": {
            "previous": prev_total,
            "current": curr_total,
            "delta": (None if prev_total is None or curr_total is None
                      else curr_total - prev_total),
        },
    }
_RATE_SIGNIFICANCE_DELTA = 0.05
_TOTAL_SIGNIFICANCE_RATIO = 0.05
def _rate_metric_significant(metrics: dict) -> bool:
    return any(
        metrics[k]["delta"] is not None
        and abs(metrics[k]["delta"]) >= _RATE_SIGNIFICANCE_DELTA
        for k in ("fp_rate", "confirm_rate", "fix_success_rate")
        if k in metrics
    )
def _total_metric_significant(metric: dict) -> bool:
    delta = metric.get("delta")
    previous = metric.get("previous")
    if delta is None or previous is None:
        return False
    if previous > 0:
        return abs(delta / previous) >= _TOTAL_SIGNIFICANCE_RATIO
    return bool(delta)
def _is_impact_significant(metrics: dict) -> bool:
    return _rate_metric_significant(metrics) or _total_metric_significant(
        metrics.get("total_findings") or {})
def _fmt_rate(value: float | None) -> str:
    return "N/A" if value is None else f"{value:.2%}"
def _fmt_delta(value: float | None) -> str:
    return "N/A" if value is None else f"{value:+.2%}"
def _impact_conclusion(fp_delta: float | None, fix_delta: float | None,
                       confirm_delta: float | None = None) -> str:
    def _beyond(delta: float | None, sign: int) -> bool:
        return (delta is not None
                and sign * delta >= _RATE_SIGNIFICANCE_DELTA)
    degraded = (_beyond(fp_delta, 1) or _beyond(fix_delta, -1)
                or _beyond(confirm_delta, -1))
    if degraded:
        return "记忆增强需调优: 部分指标退化"
    improvements = []
    if _beyond(fp_delta, -1):
        improvements.append("FP率下降")
    if _beyond(fix_delta, 1):
        improvements.append("修复率提升")
    if _beyond(confirm_delta, 1):
        improvements.append("确认率提升")
    if improvements:
        return f"记忆增强有效: {'、'.join(improvements)}"
    if fp_delta is None and fix_delta is None and confirm_delta is None:
        return "记忆增强效果待观察: 比率指标未知，仅发现数变化显著"
    return "记忆增强效果稳定: 指标基本持平"
def _existing_memory_contents(ctx: DiagnosticMemoryContext) -> dict[str, str]:
    contents = {path: "" for path in str_memory_paths(ctx)}
    for entry in as_list(ctx.raw_search_results):
        if not isinstance(entry, dict):
            continue
        path = entry.get("path")
        content = entry.get("content")
        if not isinstance(path, str) or not path or not isinstance(content, str):
            continue
        contents.setdefault(path, "")
        # normalize_mem_entry 会用 snippet/summary 补足 content；这些短文本
        # 不能充当整页 patch 的 old_text，否则会产生必然失败的写操作。
        if content and content != entry.get("snippet") and content != entry.get("summary"):
            contents[path] = content
    return contents

def _dated_page_write_fields(path: str, content: str,
                             existing: Mapping[str, str]) -> dict | None:
    if path not in existing:
        return {"operation": "add"}
    old_text = existing[path]
    if not old_text:
        logger.warning("[MemoryBridge] 日期页已存在但缺少全文锚点，跳过更新: %s", path)
        return None
    if old_text == content:
        return None
    return {"operation": "patch", "old_text": old_text}

def _build_impact_tracking_op(metrics: dict,
                              existing: Mapping[str, str]) -> dict | None:
    date_str = memory_date_stamp()
    path = f"{WIKI_PROJECTS_PREFIX}/增强效果追踪-{date_str}"
    fp_rate = metrics["fp_rate"]
    confirm_rate = metrics["confirm_rate"]
    fix_rate = metrics["fix_success_rate"]
    total = metrics["total_findings"]
    total_prev_cell = ("N/A" if total["previous"] is None
                       else str(total["previous"]))
    total_curr_cell = ("N/A" if total["current"] is None
                       else str(total["current"]))
    total_delta_cell = ("N/A" if total["delta"] is None
                        else f"{int(total['delta']):+d}")
    summary_line = (
        f"FP率{_fmt_rate(fp_rate['previous'])}→{_fmt_rate(fp_rate['current'])}"
        f"(Δ{_fmt_delta(fp_rate['delta'])}), "
        f"确认率{_fmt_rate(confirm_rate['previous'])}→{_fmt_rate(confirm_rate['current'])}"
        f"(Δ{_fmt_delta(confirm_rate['delta'])}), "
        f"修复率{_fmt_rate(fix_rate['previous'])}→{_fmt_rate(fix_rate['current'])}"
        f"(Δ{_fmt_delta(fix_rate['delta'])})"
    )
    conclusion = _impact_conclusion(
        fp_rate["delta"], fix_rate["delta"], confirm_rate["delta"])
    content = f"""---
title: 记忆增强效果追踪 ({date_str})
summary: {summary_line}
---

## 记忆增强效果

| 维度 | 上次 | 本次 | 变化 |
|------|------|------|------|
| FP率 | {_fmt_rate(fp_rate['previous'])} | {_fmt_rate(fp_rate['current'])} | {_fmt_delta(fp_rate['delta'])} |
| 确认率 | {_fmt_rate(confirm_rate['previous'])} | {_fmt_rate(confirm_rate['current'])} | {_fmt_delta(confirm_rate['delta'])} |
| 修复成功率 | {_fmt_rate(fix_rate['previous'])} | {_fmt_rate(fix_rate['current'])} | {_fmt_delta(fix_rate['delta'])} |
| 总发现 | {total_prev_cell} | {total_curr_cell} | {total_delta_cell} |

## 结论

{conclusion}
"""
    write_fields = _dated_page_write_fields(path, content, existing)
    if write_fields is None:
        return None
    return {
        **write_fields,
        "path": path,
        "content": content,
        "category": CATEGORY_ENHANCEMENT_IMPACT,
        "quality_score": 8.5,
        "reason": (f"增强效果追踪: FP率Δ{_fmt_delta(fp_rate['delta'])}, "
                   f"修复率Δ{_fmt_delta(fix_rate['delta'])}"),
    }
def compute_enhancement_impact(
    current_result: dict,
    ctx: DiagnosticMemoryContext | None,
) -> dict:
    result: dict[str, Any] = {
        "impact_metrics": {},
        "memory_ops": [],
        "has_baseline": False,
    }
    ctx = _coerce_diagnostic_context(ctx)
    if not ctx:
        return result
    current_result = dict_or_empty(current_result)
    prev = _impact_baseline(ctx)
    if not prev:
        return result
    try:
        metrics = _build_impact_metrics(prev, _collect_impact_current(current_result))
        result["impact_metrics"] = metrics
        result["has_baseline"] = True
        if _is_impact_significant(metrics):
            op = _build_impact_tracking_op(metrics, _existing_memory_contents(ctx))
            if op is not None:
                result["memory_ops"].append(op)
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] 增强效果计算异常: %s", e)
    return result
def _severity_token(raw: Any) -> str:
    return raw if isinstance(raw, str) and raw else ""
_REGRESSION_GONE_LINE_RE = re.compile(
    r"^[ \t]*-[ \t]*disappeared_finding[ \t]*[:：].*$", re.MULTILINE)
def _rebuild_findings_from_history(ctx: DiagnosticMemoryContext) -> list[dict]:
    findings = []
    for record in as_list(ctx.regression_history):
        content = record.get("content") if isinstance(record, dict) else None
        if not isinstance(content, str) or not content:
            continue
        present = _REGRESSION_GONE_LINE_RE.sub("", content)
        findings.extend(
            {"rule_id": m.group(1).upper(), "severity": ""}
            for m in RULE_ID_BARE_RE.finditer(present)
            if _is_rule_token(m.group(1)))
    return findings
def _summary_declares_zero_findings(summary: dict) -> bool:
    raw = summary.get("total_findings")
    return (raw is not None and is_valid_count_form(raw)
            and safe_int(raw) == 0)
def _historical_findings(
    ctx: DiagnosticMemoryContext,
) -> tuple[list[dict], bool]:
    prev_summary = last_summary_dict(ctx)
    if prev_summary:
        findings = prev_summary.get("findings", [])
        if isinstance(findings, list):
            valid = [f for f in findings
                     if isinstance(f, dict) and normalize_rule_id(f.get("rule_id"))]
            if valid:
                return valid, True
            if _summary_declares_zero_findings(prev_summary):
                return [], True
    rebuilt = _rebuild_findings_from_history(ctx)
    return rebuilt, bool(rebuilt)
def _collect_rule_severities(findings: list[dict]) -> dict[str, frozenset[str]]:
    rules: dict[str, set[str]] = {}
    for f in findings:
        if isinstance(f, dict):
            rid = normalize_rule_id(f.get("rule_id"))
            if rid:
                rules.setdefault(rid, set()).add(
                    _severity_token(f.get("severity")))
    return {rid: frozenset(values) for rid, values in rules.items()}
def _filter_significant_regressions(regressions: list[dict]) -> list[dict]:
    return [
        r for r in regressions
        if r["type"] in ("new_finding", "severity_drift")
        or (r["type"] == "disappeared_finding"
            and _severity_comparison_key(
                r.get("previous_severity")) in ("P0", "P1"))
    ]
def _build_regression_op(significant_regressions: list[dict],
                         existing: Mapping[str, str]) -> dict | None:
    date_str = memory_date_stamp()
    path = f"{WIKI_LESSONS_PREFIX}/诊断回归检测-{date_str}"
    lines = []
    counts = {"new_finding": 0, "disappeared_finding": 0, "severity_drift": 0}
    for r in significant_regressions:
        rtype = r.get("type", "")
        if len(lines) < 20:
            lines.append(f"- {rtype}: {r.get('reason', '')}")
        if isinstance(rtype, str) and rtype in counts:
            counts[rtype] += 1
    summary_line = (f"检测到{len(significant_regressions)}项回归"
                    f"(新增{counts['new_finding']}/消失{counts['disappeared_finding']}"
                    f"/漂移{counts['severity_drift']})")
    body = "\n".join(lines)
    content = f"""---
title: 诊断回归检测 ({date_str})
summary: {summary_line}
---

## 回归详情

{body}
"""
    write_fields = _dated_page_write_fields(path, content, existing)
    if write_fields is None:
        return None
    return {
        **write_fields,
        "path": path,
        "content": content,
        "category": CATEGORY_REGRESSION,
        "quality_score": 8.0,
        "reason": f"诊断回归: {len(significant_regressions)}项显著变化",
    }
def _severity_comparison_key(raw: Any) -> str:
    text = _severity_token(raw).strip().upper()
    if not text:
        return ""
    if text in SEVERITY_RANK or text in DIAGNOSE_TO_P:
        return diag_severity_to_p(text)
    return f"RAW:{text}"
def _severity_sort_key(raw: str) -> tuple:
    key = _severity_comparison_key(raw)
    return (SEVERITY_RANK.get(key, 99), not bool(key), key, raw)
def _severity_text(values: frozenset[str], *, complete: bool = False) -> str:
    ordered = sorted(values, key=_severity_sort_key)
    if not complete:
        ordered = ordered[:1]
    return "/".join(ordered)
def _severity_comparison_keys(values: frozenset[str]) -> frozenset[str]:
    return frozenset(
        key for value in values
        if (key := _severity_comparison_key(value)))
def _diff_rule_severities(
    curr_rules: dict[str, frozenset[str]],
    prev_rules: dict[str, frozenset[str]],
) -> list[dict]:
    regressions: list[dict] = []
    for rid in sorted(set(curr_rules.keys()) - set(prev_rules.keys())):
        regressions.append({
            "type": "new_finding",
            "rule_id": rid,
            "severity": _severity_text(curr_rules[rid]),
            "reason": f"规则{rid}在历史诊断中未出现，可能是新引入的问题或回归",
        })
    for rid in sorted(set(prev_rules.keys()) - set(curr_rules.keys())):
        regressions.append({
            "type": "disappeared_finding",
            "rule_id": rid,
            "previous_severity": _severity_text(prev_rules[rid]),
            "reason": f"规则{rid}在历史诊断中存在但当前缺失，可能被过度过滤或已修复",
        })
    for rid in sorted(set(curr_rules.keys()) & set(prev_rules.keys())):
        prev_sevs = prev_rules[rid]
        curr_sevs = curr_rules[rid]
        prev_keys = _severity_comparison_keys(prev_sevs)
        curr_keys = _severity_comparison_keys(curr_sevs)
        if prev_keys and curr_keys and prev_keys != curr_keys:
            prev_text = _severity_text(prev_sevs, complete=True)
            curr_text = _severity_text(curr_sevs, complete=True)
            regressions.append({
                "type": "severity_drift",
                "rule_id": rid,
                "previous_severity": prev_text,
                "current_severity": curr_text,
                "reason": f"规则{rid}严重度从{prev_text}变为{curr_text}",
            })
    return regressions
def detect_diagnostic_regression(
    current_findings: list[dict],
    ctx: DiagnosticMemoryContext | None,
) -> dict:
    result: dict[str, Any] = {
        "regressions": [],
        "memory_ops": [],
        "has_history": False,
    }
    ctx = _coerce_diagnostic_context(ctx)
    if not ctx:
        return result
    prev_findings, has_history = _historical_findings(ctx)
    if not has_history:
        return result
    result["has_history"] = True
    current_findings = as_list(current_findings)
    try:
        prev_rules = _collect_rule_severities(prev_findings)
        curr_rules = _collect_rule_severities(current_findings)
        result["regressions"].extend(
            _diff_rule_severities(curr_rules, prev_rules))
        significant_regressions = _filter_significant_regressions(result["regressions"])
        if significant_regressions:
            op = _build_regression_op(
                significant_regressions, _existing_memory_contents(ctx))
            if op is not None:
                result["memory_ops"].append(op)
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] 诊断回归检测异常: %s", e)
    return result
def materialize_existing_memories(existing_memories) -> list:
    if not existing_memories:
        return []
    if isinstance(existing_memories, (str, bytes, bytearray)):
        return []
    if isinstance(existing_memories, list):
        return existing_memories
    if isinstance(existing_memories, dict):
        return [existing_memories]
    try:
        return list(existing_memories)
    except TypeError as _swallow_e:
        log_swallowed(__name__, _swallow_e,
                      context='materialize_existing_memories:TypeError')
        return []
def normalize_mem_entry(mem: Any) -> dict[str, Any] | None:
    if isinstance(mem, str):
        mem = {"path": mem}
    if not isinstance(mem, dict):
        return None
    path = _as_str_field(mem.get("path", ""))
    summary = _as_str_field(mem.get("summary", ""))
    snippet = _as_str_field(mem.get("snippet", ""))
    content = _as_str_field(mem.get("content", "")) or snippet or summary
    return {**mem, "path": path, "summary": summary,
            "snippet": snippet, "content": content}
def memory_raw_text(entry: dict[str, Any]) -> str:
    if not isinstance(entry, dict):
        return ""
    for key in ("content", "snippet", "summary"):
        value = entry.get(key)
        if isinstance(value, str) and value:
            return value
    return ""
_STOP_CN = {
    "的", "了", "在", "是", "我", "有", "和", "就", "不", "人", "都", "一",
    "上", "也", "很", "到", "说", "要", "去", "你", "会", "着", "没有",
    "看", "好", "自己", "这", "他", "她", "它", "们", "那", "些", "可以",
    "这个", "如果", "因为", "所以", "但是", "而且", "或者", "虽然", "应该",
    "能够", "需要", "已经", "还是", "比较", "非常", "可能", "一定", "通过",
    "进行", "使用", "对于", "关于", "以及", "包括", "其中", "其他",
    "之后", "之前", "然后", "最后", "首先", "其次", "再次",
}
_STOP_EN = {
    "the", "a", "an", "is", "are", "was", "were", "be", "been", "being",
    "have", "has", "had", "do", "does", "did", "will", "would", "could",
    "should", "may", "might", "can", "shall", "to", "of", "in", "for",
    "on", "with", "at", "by", "from", "as", "into", "through", "during",
    "before", "after", "above", "below", "between", "under", "again",
    "then", "once", "here", "there", "when", "where", "why", "how",
    "all", "both", "each", "few", "more", "most", "other", "some", "such",
    "no", "not", "only", "own", "same", "so", "than", "too", "very",
    "and", "but", "or", "nor", "this", "that", "these", "those",
    "it", "its", "he", "she", "they", "them", "we", "us", "you", "your",
}
_STOP_CN_RE = re.compile("|".join(
    re.escape(word) for word in sorted(_STOP_CN, key=len, reverse=True)))
_SENTENCE_BOUNDARY_RE = re.compile(r"[。！？；\n]|(?<=[.!?;])\s+")
def _empty_density() -> dict[str, Any]:
    return {"density": 0.0, "total_words": 0, "info_words": 0, "level": "empty",
            "needs_compression": False, "compressed_text": ""}
def _cjk_density_tokens(segment: str) -> list[str]:
    tokens: list[str] = []
    cursor = 0
    while cursor < len(segment):
        stop_match = _STOP_CN_RE.search(segment, cursor)
        meaningful_end = stop_match.start() if stop_match else len(segment)
        meaningful = segment[cursor:meaningful_end]
        if len(meaningful) == 1:
            tokens.append(meaningful)
        else:
            tokens.extend(meaningful[index:index + 2]
                          for index in range(len(meaningful) - 1))
        if stop_match is None:
            break
        tokens.append(stop_match.group(0))
        cursor = stop_match.end()
    return tokens
def _density_tokens(text: str) -> list[str]:
    tokens: list[str] = []
    cn_segments = _CJK_RUN_RE.findall(text)
    for seg in cn_segments:
        tokens.extend(_cjk_density_tokens(seg))
    en_words = re.findall(r"[a-zA-Z0-9_]+", text)
    tokens.extend(w.lower() for w in en_words)
    return tokens
def _count_stopwords(tokens: list[str]) -> int:
    return sum(1 for t in tokens if t.lower() in _STOP_EN or t in _STOP_CN)
def _density_level(density: float) -> tuple[str, bool]:
    if density < 0.35:
        return "low", True
    if density < 0.65:
        return "normal", False
    return "high", False
def compute_information_density(text: str) -> dict[str, Any]:
    if not isinstance(text, str):
        text = safe_str(text) if text else ""
    if not text or not text.strip():
        return _empty_density()
    tokens = _density_tokens(text)
    if not tokens:
        return _empty_density()
    total = len(tokens)
    stop_count = _count_stopwords(tokens)
    info_words = total - stop_count
    density = info_words / total
    level, needs_compression = _density_level(density)
    compressed = ""
    if needs_compression and len(text) > 50:
        compressed = _compress_low_density(text, tokens)
    return {"density": round(density, 3), "total_words": total,
            "info_words": info_words, "level": level,
            "needs_compression": needs_compression, "compressed_text": compressed}
def _extract_key_tokens(tokens, stop_en, stop_cn):
    key_tokens: list[str] = []
    seen = set()
    for t in tokens:
        tl = t.lower()
        if tl not in stop_en and t not in stop_cn and len(t) >= 2 and t not in seen:
            seen.add(t)
            key_tokens.append(t)
    return key_tokens
def _select_key_sentences(text, summary_words, max_sentences=3):
    if max_sentences <= 0:
        return []
    sentences = _SENTENCE_BOUNDARY_RE.split(text)
    key_sentences = []
    for raw_sent in sentences[:8]:
        sent = raw_sent.strip()
        if not sent:
            continue
        match_count = sum(1 for kw in summary_words[:5] if kw in sent)
        if match_count >= 1 or len(sent) < 30:
            key_sentences.append(sent)
        if len(key_sentences) >= max_sentences:
            break
    return key_sentences
def _join_key_sentences(sentences: list[str]) -> str:
    parts: list[str] = []
    for sent in sentences:
        if _CJK_RUN_RE.search(sent):
            parts.append(sent + "。")
        else:
            parts.append(sent.rstrip("。") + " ")
    return "".join(parts).strip()
def _compress_low_density(text, tokens):
    unique_keys = _extract_key_tokens(tokens, _STOP_EN, _STOP_CN)
    summary_words = unique_keys[:15]
    key_sentences = _select_key_sentences(text, summary_words)
    if key_sentences:
        compressed = _join_key_sentences(key_sentences)
        if len(compressed) > len(text) * 0.6:
            compressed = compressed[:int(len(text) * 0.6)] + "..."
        return compressed
    return " ".join(summary_words[:10]) + "..."
def _density_item_entry(item: Any) -> dict[str, Any] | None:
    if not isinstance(item, dict):
        return None
    detail = item.get("detail") or memory_raw_text(item)
    dinfo = compute_information_density(detail)
    return {
        "id": item.get("path") or item.get("id") or "",
        "category": item.get("category") or "",
        "density": dinfo["density"], "level": dinfo["level"],
        "needs_compression": dinfo["needs_compression"],
        "compressed_text": dinfo["compressed_text"]}
def _density_recommendations(low_count: int, total: int,
                             avg_density: float, has_results: bool) -> list[str]:
    recommendations = []
    if low_count > 0:
        recommendations.append(f"{low_count}/{total} 条经验信息密度偏低，建议压缩摘要后再存储")
    if has_results and avg_density < 0.4:
        recommendations.append(f"整体信息密度 {avg_density:.2f} 偏低，建议优化经验描述风格")
    return recommendations
def _density_items(items: Any) -> list:
    if (isinstance(items, (str, bytes, bytearray, Mapping))
            or not isinstance(items, Iterable)):
        return []
    try:
        return list(items)
    except TypeError as _swallow_e:
        log_swallowed(__name__, _swallow_e,
                      context='evaluate_memory_density:TypeError')
        return []
def evaluate_memory_density(items: list[dict[str, Any]]) -> dict[str, Any]:
    items = _density_items(items)
    results = []
    low_count = 0
    densities = []
    for item in items:
        entry = _density_item_entry(item)
        if entry is None:
            continue
        results.append(entry)
        densities.append(entry["density"])
        if entry["needs_compression"]:
            low_count += 1
    avg_density = sum(densities) / max(len(densities), 1)
    recommendations = _density_recommendations(
        low_count, len(results), avg_density, bool(results))
    logger.info("evaluate_memory_density 评估: total=%d low_count=%d avg_density=%.3f",
              len(results), low_count, avg_density)
    return {"ok": True, "results": results, "avg_density": round(avg_density, 3),
            "low_count": low_count, "total": len(results),
            FIELD_RECOMMENDATIONS: recommendations}
register_review_provider("precreation_memory_enhance",
                         enhance_pre_creation_with_memory)

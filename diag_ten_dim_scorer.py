from __future__ import annotations

import ast
import logging
import math
import os
import re
import time
from collections import Counter, defaultdict
from collections.abc import Callable
from dataclasses import asdict, dataclass, field
from typing import Any, ClassVar

from jwsgj.diag_file_scanner import FileMeta, ScanResult, quick_scan
from jwsgj.diag_guard_state import (
    JsonSerializableMixin,
)
from jwsgj.diag_types_vocab import (
    CAT_MAINTAINABILITY,
    FIELD_RECOMMENDATIONS,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    'DimensionScore',
    'TenDimConfig',
    'TenDimReport',
    'TenDimScorer',
    'quick_score',
]
_log = logging.getLogger(__name__)
_log.info("diag_ten_dim_scorer 十维评分域已加载: %d 项导出", len(__all__))
def _is_real_number(value: Any) -> bool:
    return not isinstance(value, bool) and isinstance(value, (int, float))
def _is_finite_metric(value: Any) -> bool:
    if not _is_real_number(value):
        return False
    try:
        return math.isfinite(value)
    except (OverflowError, TypeError, ValueError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc, context='_is_finite_metric:OverflowError')
        return False
@dataclass(frozen=True)
class _DimensionSpec:
    name: str
    label: str
    weight: float
    fp_tendency: float
    action: str
    scorer: Callable
def _compute_fp_aware_confidence(
    dimension_name: str,
    sample_count: int,
    min_samples: int = 10,
) -> float:
    fp_tendency = DIMENSION_FP_TENDENCY.get(dimension_name, 0.10)
    normalized_count = max(0, sample_count)
    base = min(1.0, normalized_count / max(min_samples, 1))
    return round(base * (1.0 - fp_tendency), 3)
@dataclass
class DimensionScore:
    name: str = ""
    label: str = ""
    score: float = 0.0
    weight: float = 0.0
    weighted_score: float = 0.0
    grade: str = "N/A"
    confidence: float = 1.0
    issues: list[dict[str, Any]] = field(default_factory=list)
    highlights: list[str] = field(default_factory=list)
    details: dict[str, Any] = field(default_factory=dict)
@dataclass
class TenDimReport(JsonSerializableMixin):
    project_root: str = ""
    project_name: str = ""
    overall_score: float = 0.0
    overall_grade: str = "N/A"
    overall_confidence: float = 1.0
    dimensions: list[DimensionScore] = field(default_factory=list)
    summary: str = ""
    recommendations: list[dict[str, Any]] = field(default_factory=list)
    scan_summary: dict[str, Any] = field(default_factory=dict)
    metadata: dict[str, Any] = field(default_factory=dict)
    timestamp: float = field(default_factory=time.time)
    def to_dict(self) -> dict[str, Any]:
        return {
            "project_root": self.project_root,
            "project_name": self.project_name,
            "overall_score": self.overall_score,
            "overall_grade": self.overall_grade,
            "overall_confidence": self.overall_confidence,
            "dimensions": [asdict(d) for d in self.dimensions],
            "summary": self.summary,
            FIELD_RECOMMENDATIONS: self.recommendations,
            "scan_summary": self.scan_summary,
            "metadata": self.metadata,
            "timestamp": self.timestamp,
        }
def _validated_weight_mapping(weights: Any) -> dict[str, float]:
    if not isinstance(weights, dict):
        raise TypeError(
            "TenDimConfig.weights 须为 dict，实际为 "
            f"{type(weights).__name__}")
    invalid_keys = [k for k in weights if not isinstance(k, str)]
    if invalid_keys:
        raise TypeError(
            "TenDimConfig.weights 键须为 str 维度名，非法键: "
            f"{[repr(k) for k in invalid_keys]}")
    non_numeric = sorted(k for k, v in weights.items()
                         if not _is_real_number(v))
    if non_numeric:
        raise TypeError(
            f"TenDimConfig.weights 须为数值，非数值维度: {non_numeric}")
    non_finite = sorted(k for k, v in weights.items()
                        if not _is_finite_metric(v))
    if non_finite:
        raise ValueError(
            f"TenDimConfig.weights 须为有限数值，非有限维度: {non_finite}")
    negative = sorted(k for k, v in weights.items() if v < 0)
    if negative:
        raise ValueError(
            f"TenDimConfig.weights 含负权重，权重语义域为非负: {negative}；"
            "维度不参与评分请显式置 0.0")
    unknown = sorted(set(weights) - set(DEFAULT_DIMENSION_WEIGHTS))
    if unknown:
        raise ValueError(
            f"TenDimConfig.weights 含未知维度: {unknown}；"
            f"可用维度: {sorted(DEFAULT_DIMENSION_WEIGHTS)}")
    return {name: float(weights.get(name, 0.0))
            for name in DEFAULT_DIMENSION_WEIGHTS}
def _normalize_weight_total(weights: dict[str, float]) -> dict[str, float]:
    total = sum(weights.values())
    if total <= 0 or abs(total - 1.0) <= 0.01:
        return weights
    if math.isfinite(total):
        return {k: v / total for k, v in weights.items()}
    scale = max(weights.values())
    scaled = {k: v / scale for k, v in weights.items()}
    scaled_total = math.fsum(scaled.values())
    return {k: v / scaled_total for k, v in scaled.items()}
@dataclass
class TenDimConfig:
    weights: dict[str, float] = field(
        default_factory=lambda: dict(DEFAULT_DIMENSION_WEIGHTS))
    grade_thresholds: dict[str, float] = field(default_factory=lambda: {
        "A": 85.0, "B": 70.0, "C": 55.0, "D": 35.0, "F": 0.0,
    })
    max_acceptable_complexity: float = 15.0
    max_acceptable_function_lines: int = 80
    max_acceptable_file_lines: int = 4000
    min_acceptable_comment_ratio: float = 0.05
    good_comment_ratio: float = 0.15
    security_patterns: list[str] = field(default_factory=lambda: [
        r"\beval\s*\(", r"\bexec\s*\(", r"(?<!\.)\bcompile\s*\(",
        r"\b__import__\s*\(", r"\bos\.system\s*\(", r"\bsubprocess\b",
        r"\bpickle\.loads?\s*\(", r"\bmarshal\.loads?\s*\(",
        r"\bexecfile\s*\(", r"\binput\s*\(",
        r"\braw_input\s*\(", r"\bgetattr\s*\([^)]*input",
        r"\bshelve\.open\s*\(", r"\byaml\.(unsafe_load|full_load)\s*\(",
        r"\bjinja2\.Environment\s*\([^)]*autoescape\s*=\s*False",
        r"\bmark_safe\s*\(", r"\bSafeString\s*\(",
        r"\bos\.popen\s*\(", r"\bcommands\.getoutput\s*\(",
        r"\b\.execute\s*\(.*%.*\)",
    ])
    performance_patterns: list[str] = field(default_factory=lambda: [
        r"\.copy\(\)",
        r"for\s+\w+\s+in\s+range\s*\(\s*len\s*\(",
        r"\+=\s*['\"]",
        r"\.keys\(\)\s*\)",
        r"\.values\(\)\s*\[\d+\]",
        r"list\(dict\.keys\(\)\)",
        r"\n[ \t]+import\s+\w+",
        r"time\.sleep\s*\([^)]*\)",
    ])
    max_files_per_dir: int = 30
    min_files_for_module: int = 5
    min_test_ratio: float = 0.10
    min_docstring_coverage: float = 0.50
    robustness_patterns: list[str] = field(default_factory=lambda: [
        r"except\s*:",
        r"except\s+Exception\s*:\s*pass",
        r"except\s+Exception\s*:\s*(\w+\s*=\s*['\"]|return\s+None)",
        r"assert\s+.*,\s*['\"]",
    ])
    def __post_init__(self):
        self.weights = _normalize_weight_total(
            _validated_weight_mapping(self.weights))
        _validate_grade_thresholds(self.grade_thresholds)
        _validate_numeric_config(self)
        for field_name in ("security_patterns", "performance_patterns",
                           "robustness_patterns"):
            patterns = getattr(self, field_name)
            if not isinstance(patterns, list) or any(
                    not isinstance(p, str) for p in patterns):
                raise TypeError(
                    f"TenDimConfig.{field_name} 须为 str 列表，实际为 "
                    f"{type(patterns).__name__}")
            for index, pattern in enumerate(patterns):
                try:
                    re.compile(pattern)
                except re.error as exc:
                    raise ValueError(
                        f"TenDimConfig.{field_name}[{index}] 非法正则: "
                        f"{pattern!r}（{exc}）") from exc
def _validate_grade_thresholds(thresholds) -> None:
    if not isinstance(thresholds, dict):
        raise TypeError(
            f"TenDimConfig.grade_thresholds 须为 dict，实际为 "
            f"{type(thresholds).__name__}")
    for grade, threshold in thresholds.items():
        if not isinstance(grade, str) or not grade.strip():
            raise TypeError(
                f"TenDimConfig.grade_thresholds 等级键须为非空 str，"
                f"实际为 {grade!r}")
        if not _is_finite_metric(threshold):
            raise ValueError(
                f"TenDimConfig.grade_thresholds[{grade!r}] 须为有限数值，"
                f"实际为 {threshold!r}")
    if not thresholds or min(
            float(value) for value in thresholds.values()) > 0.0:
        raise ValueError(
            "TenDimConfig.grade_thresholds 缺少兜底阈值：至少需要一个 "
            "<= 0 的等级阈值，否则低于全部阈值的分数会被静默判 F")
_NO_PRODUCTION_STATUS = "no_production_files"
def _not_applicable_details(status: str) -> dict[str, Any]:
    return {"status": status, "applicable": False}
_NUMERIC_CONFIG_FIELDS = (
    "max_acceptable_complexity", "max_acceptable_function_lines",
    "max_acceptable_file_lines", "min_acceptable_comment_ratio",
    "good_comment_ratio", "max_files_per_dir", "min_files_for_module",
    "min_test_ratio", "min_docstring_coverage",
)
_INT_CONFIG_FIELDS = frozenset({
    "max_acceptable_function_lines", "max_acceptable_file_lines",
    "max_files_per_dir", "min_files_for_module",
})
_UNIT_INTERVAL_CONFIG_FIELDS = frozenset({
    "min_acceptable_comment_ratio", "good_comment_ratio",
    "min_test_ratio", "min_docstring_coverage",
})
def _validate_numeric_config(config: TenDimConfig) -> None:
    for name in _NUMERIC_CONFIG_FIELDS:
        value = getattr(config, name)
        if name in _INT_CONFIG_FIELDS:
            if isinstance(value, bool) or not isinstance(value, int):
                raise TypeError(
                    f"TenDimConfig.{name} 须为整数，实际为 {value!r}")
        elif not _is_finite_metric(value):
            raise ValueError(
                f"TenDimConfig.{name} 须为有限数值，实际为 {value!r}")
        if value < 0:
            raise ValueError(
                f"TenDimConfig.{name} 须为非负值，实际为 {value!r}")
    for name in _UNIT_INTERVAL_CONFIG_FIELDS:
        value = getattr(config, name)
        if not 0.0 <= value <= 1.0:
            raise ValueError(
                f"TenDimConfig.{name} 须位于 [0, 1]，实际为 {value!r}")
    if config.good_comment_ratio < config.min_acceptable_comment_ratio:
        raise ValueError(
            "TenDimConfig.good_comment_ratio 不得小于 "
            "min_acceptable_comment_ratio，实际为 "
            f"{config.good_comment_ratio!r} < "
            f"{config.min_acceptable_comment_ratio!r}")
def _compute_grade(score: float, thresholds: dict[str, float]) -> str:
    ranked = sorted(
        ((grade, threshold) for grade, threshold in thresholds.items()
         if _is_finite_metric(threshold)),
        key=lambda kv: -kv[1])
    for grade, threshold in ranked:
        if score >= threshold:
            return grade
    return "F"
_HIGH_CONF_SECURITY_PATTERNS = (
    "eval", "exec", "compile", "__import__",
    "os.system", "subprocess",
    "pickle.loads", "marshal.loads",
    "unsafe_load", "full_load",
)
_MED_CONF_SECURITY_PATTERNS = (
    "input", "raw_input",
    "jinja2.Environment",
    "mark_safe", "SafeString",
    "shelve.open",
    "os.popen", "commands.getoutput",
)
_SECURITY_DEMOTIONS: tuple[tuple[tuple[str, ...], tuple[str, float]], ...] = (
    (("execfile",), ("P2", 0.40)),
    (("getattr", "input"), ("P2", 0.40)),
    (("execute", "%"), ("P2", 0.40)),
)
def _classify_security_pattern(pattern_match: str) -> tuple[str, float]:
    norm = pattern_match.replace(r"\.", ".")
    for _keywords, _demoted in _SECURITY_DEMOTIONS:
        if all(kw in norm for kw in _keywords):
            return _demoted
    for pat in _HIGH_CONF_SECURITY_PATTERNS:
        if pat in norm:
            return ("P0", 0.95)
    for pat in _MED_CONF_SECURITY_PATTERNS:
        if pat in norm:
            return ("P1", 0.70)
    return ("P2", 0.50)
def _classify_robustness_pattern(pattern_match: str) -> tuple[str, float]:
    if r"except\s+Exception\s*:\s*pass" in pattern_match:
        return ("P0", 0.85)
    if r"except\s+Exception\s*:\s*(" in pattern_match:
        return ("P1", 0.60)
    if r"except\s*:" in pattern_match or r"except\s+Exception\s*:" in pattern_match:
        return ("P0", 0.90)
    if pattern_match.startswith("assert"):
        return ("P2", 0.65)
    return ("P2", 0.50)
def _linear_score(value: float, best: float, worst: float = 0.0) -> float:
    if value >= best:
        return 100.0
    if value <= worst or best == worst:
        return 0.0
    return (value - worst) / (best - worst) * 100.0
def _ratio_band_score(value: float, good: float, acceptable: float,
                      floor: float = 60.0) -> float:
    if value >= good:
        return 100.0
    if good <= acceptable:
        return 0.0
    if value >= acceptable:
        return floor + ((value - acceptable) / (good - acceptable)
                        * (100.0 - floor))
    if acceptable <= 0:
        return 0.0
    return value / acceptable * floor
def _inverse_linear_score(value: float, worst: float, best: float = 0.0) -> float:
    if value <= best:
        return 100.0
    if value >= worst or worst == best:
        return 0.0
    return (worst - value) / (worst - best) * 100.0
def _issue(severity: str, message: str, dimension: str, *,
           affected: list[str] | None = None,
           details: Any = None) -> dict[str, Any]:
    issue: dict[str, Any] = {
        "severity": severity,
        "message": message,
        "dimension": dimension,
    }
    if affected is not None:
        issue["affected"] = affected
    if details is not None:
        issue["details"] = details
    return issue
def _read_source_safe(fmeta: FileMeta) -> str | None:
    try:
        with open(fmeta.abs_path, encoding=fmeta.encoding, errors="replace") as fh:
            return fh.read()
    except (OSError, LookupError, ValueError):
        _log.warning("skip unreadable file: %s", fmeta.rel_path, exc_info=True)
        return None
@dataclass
class _PatternScanResult:
    matches: dict[str, int]
    scanned_files: list[str]
    skipped_files: list[str]
    invalid_patterns: list[str]
    file_total: int
    pattern_total: int
    @property
    def status(self) -> str:
        if self.file_total and not self.scanned_files:
            return "unavailable"
        if (not self.pattern_total
                or len(self.invalid_patterns) >= self.pattern_total):
            return "unavailable"
        if self.skipped_files or self.invalid_patterns:
            return "partial"
        return "complete"
def _production_files(py_files: list[FileMeta]) -> list[FileMeta]:
    return [f for f in py_files if not f.is_test]
def _record_scan_scope(details: dict[str, Any],
                       py_files: list[FileMeta],
                       production: list[FileMeta]) -> None:
    details["scanned_production_files"] = len(production)
    details["excluded_test_files"] = len(py_files) - len(production)
def _match_patterns_across_files(
    files: list[FileMeta],
    patterns: list[str],
    *,
    flags: int,
    tag: str,
) -> _PatternScanResult:
    compiled_patterns: list[tuple[str, re.Pattern]] = []
    invalid_patterns: list[str] = []
    for pattern in patterns:
        try:
            compiled_patterns.append((pattern, re.compile(pattern, flags)))
        except re.error:
            _log.warning("invalid %s pattern, skip: %r", tag, pattern)
            invalid_patterns.append(pattern)
    counts: dict[str, int] = defaultdict(int)
    scanned_files: list[str] = []
    skipped_files: list[str] = []
    for fmeta in files:
        if fmeta.extra.get("ast_status") == "decode_failed":
            skipped_files.append(fmeta.rel_path)
            continue
        content = _read_source_safe(fmeta)
        if content is None:
            skipped_files.append(fmeta.rel_path)
            continue
        scanned_files.append(fmeta.rel_path)
        for pattern, compiled_pattern in compiled_patterns:
            matches = compiled_pattern.findall(content)
            if matches:
                counts[pattern] += len(matches)
    return _PatternScanResult(
        matches=dict(counts), scanned_files=scanned_files,
        skipped_files=skipped_files, invalid_patterns=invalid_patterns,
        file_total=len(files), pattern_total=len(patterns))
def _record_pattern_scan(
    details: dict[str, Any], result: _PatternScanResult,
    issues: list[dict], dimension: str,
) -> None:
    details["pattern_scan_status"] = result.status
    details["pattern_scan_file_total"] = result.file_total
    details["pattern_scan_pattern_total"] = result.pattern_total
    details["pattern_scanned_files"] = len(result.scanned_files)
    details["pattern_skipped_files"] = list(result.skipped_files)
    details["invalid_patterns"] = list(result.invalid_patterns)
    if result.status == "complete":
        return
    gaps: list[str] = []
    affected: list[str] = []
    if result.skipped_files:
        gaps.append(f"{len(result.skipped_files)} 个源码文件读取失败")
        affected.extend(result.skipped_files)
    if result.invalid_patterns:
        gaps.append(f"{len(result.invalid_patterns)} 个模式无效")
        affected.extend(result.invalid_patterns)
    if not result.pattern_total:
        gaps.append("未配置检测模式")
    issues.append(_issue(
        "P1", "；".join(gaps) + "，评分证据不完整",
        dimension, affected=affected))
def _import_facts_unavailable(fmeta: FileMeta) -> bool:
    status = fmeta.extra.get("ast_status")
    return status is not None and status != "ok"
def _imported_top_names_from_source(content: str) -> set[str] | None:
    try:
        tree = ast.parse(content)
    except (SyntaxError, ValueError, RecursionError, MemoryError):
        _log.debug("导入事实解析失败，标记证据不可用", exc_info=True)
        return None
    names: set[str] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            names.update(alias.name.split(".")[0] for alias in node.names)
        elif (isinstance(node, ast.ImportFrom) and node.module
                and not node.level):
            names.add(node.module.split(".")[0])
    return names
def _imported_top_names(fmeta: FileMeta) -> set[str] | None:
    if _import_facts_unavailable(fmeta):
        return None
    declared = fmeta.imported_modules
    if fmeta.extra.get("ast_status") == "ok" or declared:
        return {str(name).split(".")[0] for name in declared
                if isinstance(name, str)}
    content = _read_source_safe(fmeta)
    if content is None:
        return None
    return _imported_top_names_from_source(content)
def _probe_module_imports(
    files: list[FileMeta],
    modules: tuple[str, ...],
    *,
    facts_available: bool = True,
) -> tuple[dict[str, bool], list[str]]:
    flags = dict.fromkeys(modules, False)
    targets = set(modules)
    unavailable_files: list[str] = []
    for fmeta in files:
        if not facts_available or _import_facts_unavailable(fmeta):
            unavailable_files.append(fmeta.rel_path)
            continue
        imported = _imported_top_names(fmeta)
        if imported is None:
            unavailable_files.append(fmeta.rel_path)
            continue
        for module in targets & imported:
            flags[module] = True
    return flags, unavailable_files
def _record_import_analysis(
    details: dict[str, Any], issues: list[dict], dimension: str,
    files: list[FileMeta], unavailable_files: list[str], evidence_label: str,
) -> None:
    file_total = len(files)
    analyzed = max(0, file_total - len(unavailable_files))
    details["import_analysis_file_total"] = file_total
    details["import_analyzed_files"] = analyzed
    details["import_analysis_status"] = (
        "complete" if not unavailable_files
        else "partial" if analyzed else "unavailable")
    if not unavailable_files:
        return
    details["import_unavailable_files"] = list(unavailable_files)
    issues.append(_issue(
        "P1",
        f"{len(unavailable_files)} 个文件导入分析失败，{evidence_label}证据不完整",
        dimension, affected=list(unavailable_files)))
_README_BASENAME = "readme"
_README_DOC_EXTS = frozenset({
    "", ".md", ".markdown", ".mdown", ".mkd", ".rst", ".txt", ".textile",
    ".org", ".adoc", ".asciidoc", ".rdoc", ".mediawiki", ".wiki", ".pod",
})
_ENV_TEMPLATE_SUFFIXES = frozenset({
    "example", "sample", "template", "tpl", "dist", "schema", "defaults",
})
def _is_readme_name(name: str) -> bool:
    lowered = name.lower()
    stem, ext = os.path.splitext(lowered)
    if ext not in _README_DOC_EXTS:
        return False
    if stem == _README_BASENAME:
        return True
    return (stem.startswith(_README_BASENAME)
            and stem[len(_README_BASENAME)] in "._-")
def _is_env_file_name(name: str) -> bool:
    lowered = name.lower()
    if lowered == ".env":
        return True
    if not lowered.startswith(".env."):
        return False
    suffixes = lowered[len(".env."):].split(".")
    return not any(suffix in _ENV_TEMPLATE_SUFFIXES for suffix in suffixes)
def _root_dir_files(project_root) -> tuple[str, list[str]] | None:
    try:
        root = os.fspath(project_root)
    except (TypeError, ValueError):
        return None
    if not isinstance(root, str) or not root:
        return None
    try:
        entries = os.listdir(root)
    except (OSError, TypeError, ValueError) as _e:
        log_swallowed(__name__, _e, context='_root_dir_files:OSError')
        return None
    return root, entries
def _probe_root_names(project_root, predicate) -> list[str]:
    listed = _root_dir_files(project_root)
    if listed is None:
        return []
    root, entries = listed
    return [entry for entry in entries
            if predicate(entry) and os.path.isfile(os.path.join(root, entry))]
def _probe_readme_presence(scan_result, all_files) -> tuple[bool, list]:
    readme_files = [f for f in all_files if _is_readme_name(f.name)]
    if readme_files:
        return True, []
    probed = _probe_root_names(scan_result.project_root, _is_readme_name)
    return bool(probed), sorted(probed)
def _naming_traits(stem: str) -> tuple[bool, bool, bool]:
    return ("_" in stem, "-" in stem,
            stem != stem.lower() and stem != stem.upper())
def _is_uppercase_stem(stem: str) -> bool:
    return stem != stem.lower() and stem == stem.upper()
def _naming_style_consistency(py_files) -> tuple[Counter, str, float]:
    naming_styles: Counter = Counter()
    if not py_files:
        return naming_styles, "", 0.0
    for f in py_files:
        has_underscore, has_hyphen, has_camel = _naming_traits(f.stem)
        is_uppercase = _is_uppercase_stem(f.stem)
        if has_underscore:
            style = "UPPER_SNAKE_CASE" if is_uppercase else "snake_case"
            naming_styles[style] += 1
        elif has_hyphen:
            style = "UPPER-KEBAB-CASE" if is_uppercase else "kebab-case"
            naming_styles[style] += 1
        elif has_camel:
            naming_styles["mixedCase"] += 1
        else:
            naming_styles["UPPERCASE" if is_uppercase else "snake_case"] += 1
    if not naming_styles:
        return naming_styles, "", 0.0
    dominant_style, dominant_count = naming_styles.most_common(1)[0]
    return naming_styles, dominant_style, dominant_count / len(py_files)
def _import_style_counts_from_source(
    content: str, local_modules: set[str],
) -> tuple[int, int, int] | None:
    try:
        tree = ast.parse(content)
    except (SyntaxError, ValueError, RecursionError, MemoryError):
        _log.debug("导入风格事实解析失败，标记证据不可用", exc_info=True)
        return None
    abs_imports = 0
    rel_imports = 0
    external_abs_imports = 0
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            local_count = sum(
                alias.name in local_modules for alias in node.names)
            if local_count:
                abs_imports += 1
            if local_count < len(node.names):
                external_abs_imports += 1
        elif isinstance(node, ast.ImportFrom):
            if node.level > 0:
                rel_imports += 1
            elif node.module != "__future__":
                if node.module in local_modules:
                    abs_imports += 1
                else:
                    external_abs_imports += 1
    return abs_imports, rel_imports, external_abs_imports
def _count_import_styles(
    py_files, *, local_facts_available: bool,
) -> tuple[int, int, int, list[str]]:
    abs_imports = 0
    rel_imports = 0
    external_abs_imports = 0
    unavailable_files: list[str] = []
    for f in py_files:
        if not local_facts_available or _import_facts_unavailable(f):
            unavailable_files.append(f.rel_path)
            continue
        content = _read_source_safe(f)
        if content is None:
            unavailable_files.append(f.rel_path)
            continue
        file_counts = _import_style_counts_from_source(
            content, set(f.extra.get("local_absolute_imports", ())))
        if file_counts is None:
            unavailable_files.append(f.rel_path)
            continue
        file_abs, file_rel, file_external = file_counts
        abs_imports += file_abs
        rel_imports += file_rel
        external_abs_imports += file_external
    return abs_imports, rel_imports, external_abs_imports, unavailable_files
def _pattern_severity_counts(match_details, classify_fn) -> Counter:
    counts: Counter = Counter()
    for pattern, count in match_details.items():
        severity, _ = classify_fn(pattern)
        counts[severity] += count
    return counts
def _env_leak_scan(scan_result, all_files) -> tuple[int, list, list]:
    env_files = [f for f in all_files if _is_env_file_name(f.name)]
    probe_dirs = [(".", scan_result.project_root)]
    if os.path.isdir(scan_result.project_root):
        probe_dirs.extend(
            (directory.rel_path, directory.abs_path)
            for directory in scan_result.directories.values()
            if directory.rel_path != "."
        )
    probed_env: list[str] = []
    for rel_dir, abs_dir in probe_dirs:
        for name in _probe_root_names(abs_dir, _is_env_file_name):
            probed_env.append(
                name if rel_dir in ("", ".")
                else os.path.join(rel_dir, name))
    scanned_env = {
        os.path.normcase(os.path.normpath(f.rel_path)) for f in env_files
    }
    probed_by_path = {
        os.path.normcase(os.path.normpath(path)): path for path in probed_env
    }
    probed_only = sorted(
        path for key, path in probed_by_path.items() if key not in scanned_env)
    env_total = len(env_files) + len(probed_only)
    affected = [f.rel_path for f in env_files] + probed_only
    return env_total, affected, probed_only
def _duplicate_sha_groups(py_files) -> tuple[dict, int]:
    sha_groups: dict[str, list[str]] = defaultdict(list)
    for f in py_files:
        if not f.sha256 or f.code_lines <= 1:
            continue
        sha_groups[f.sha256].append(f.rel_path)
    duplicates = {sha: paths for sha, paths in sha_groups.items()
                  if len(paths) > 1}
    return duplicates, sum(len(paths) - 1 for paths in duplicates.values())
_COMMENTED_CODE_KEYWORDS = (
    "def ", "class ", "import ", "return ", "if ", "for ", "while ")
def _parses_as_code(body: str) -> bool:
    indented = "\n".join("    " + part for part in body.split("\n"))
    for source in (body, "def _commented():\n" + indented):
        try:
            compile(source, "<commented>", "exec")
            return True
        except (SyntaxError, ValueError, RecursionError, MemoryError):
            _log.debug("注释片段不是可解析代码，继续探测: %r", source, exc_info=True)
            continue
    return False
def _looks_like_commented_code(line: str) -> bool:
    if not line.startswith("#"):
        return False
    if not any(kw in line for kw in _COMMENTED_CODE_KEYWORDS):
        return False
    body = line.lstrip("#").strip()
    return bool(body) and _parses_as_code(body)
def _count_commented_code(
    py_files, unavailable_files: list[str] | None = None,
) -> int:
    commented = 0
    for f in py_files:
        content = _read_source_safe(f)
        if content is None:
            if unavailable_files is not None:
                unavailable_files.append(f.rel_path)
            continue
        for line in content.split("\n"):
            if _looks_like_commented_code(line.strip()):
                commented += 1
    return commented
def _robustness_pattern_issue(total_matches, p0_count) -> dict:
    if total_matches <= 5:
        return _issue(
            "P0" if p0_count > 0 else "P2",
            f"发现 {total_matches} 处异常处理问题", "robustness")
    return _issue(
        "P0" if p0_count > 0 else "P1",
        f"发现 {total_matches} 个异常处理问题"
        f"{' (含 ' + str(p0_count) + ' 个裸except/吞异常)' if p0_count > 0 else ''}",
        "robustness",
    )
def _dir_file_distribution(py_files: list[FileMeta]) -> dict[str, int]:
    dir_files: dict[str, int] = defaultdict(int)
    for fmeta in py_files:
        dir_files[os.path.dirname(fmeta.rel_path) or "."] += 1
    return dir_files
def _oversize_dir_issue(oversize_dirs: dict[str, int], limit: int) -> dict | None:
    if not oversize_dirs:
        return None
    top = sorted(oversize_dirs.items(), key=lambda kv: (-kv[1], kv[0]))[:3]
    return _issue(
        "P1", f"{len(oversize_dirs)} 个目录文件数超标 (> {limit})", "modularity",
        affected=[f"{d}: {c}文件" for d, c in top])
def _mini_dir_issue(mini_dirs: list[str], total_dirs: int,
                    min_files: int) -> dict | None:
    if len(mini_dirs) <= total_dirs * 0.5:
        return None
    return _issue(
        "P2", f"{len(mini_dirs)} 个迷你模块（文件数 < {min_files}）", "modularity")
def _avg_local_deps(py_files: list[FileMeta]) -> float:
    total_local_imports = sum(len(fmeta.local_imports) for fmeta in py_files)
    return total_local_imports / max(len(py_files), 1)
def _dim_result(score: float, issues: list[dict], highlights: list[str],
                details: dict[str, Any]) -> tuple[float, list[dict], list[str], dict]:
    if not _is_finite_metric(score):
        score = 0.0
    return max(0.0, min(100.0, score)), issues, highlights, details
def _collect_complexity_metric(py_files: list[FileMeta], cfg: TenDimConfig,
                               issues: list[dict], highlights: list[str],
                               details: dict) -> float:
    total_files = len(py_files)
    complex_files = [
        f for f in py_files
        if max(f.max_complexity, f.complexity) > cfg.max_acceptable_complexity]
    complex_ratio = len(complex_files) / max(total_files, 1)
    details["files_over_complexity"] = len(complex_files)
    details["complexity_threshold"] = cfg.max_acceptable_complexity
    if complex_files:
        top = sorted(
            complex_files,
            key=lambda x: (-max(x.max_complexity, x.complexity), x.rel_path))[:5]
        issues.append(_issue(
            "P1",
            f"{len(complex_files)}/{total_files} 个文件超复杂度阈值 ({complex_ratio:.0%})",
            CAT_MAINTAINABILITY, affected=[f.rel_path for f in top]))
    else:
        highlights.append("已分析文件圈复杂度均在阈值内")
    return _inverse_linear_score(complex_ratio, 0.5)
def _collect_function_size_metric(py_files: list[FileMeta], cfg: TenDimConfig,
                                  issues: list[dict], details: dict) -> float:
    oversized_funcs = [f for f in py_files
                       if f.max_function_lines > cfg.max_acceptable_function_lines]
    details["files_with_oversized_functions"] = len(oversized_funcs)
    if oversized_funcs:
        issues.append(_issue(
            "P2",
            f"{len(oversized_funcs)} 个文件含超长函数 (> {cfg.max_acceptable_function_lines}行)",
            CAT_MAINTAINABILITY))
    return _inverse_linear_score(len(oversized_funcs), len(py_files) // 2, 0)
def _collect_file_size_metric(py_files: list[FileMeta], cfg: TenDimConfig,
                              issues: list[dict], details: dict) -> float:
    large_files = [f for f in py_files if f.lines > cfg.max_acceptable_file_lines]
    details["large_files"] = len(large_files)
    if large_files:
        top3 = sorted(large_files, key=lambda x: (-x.lines, x.rel_path))[:3]
        issues.append(_issue(
            "P1", f"{len(large_files)} 个文件超过 {cfg.max_acceptable_file_lines} 行",
            CAT_MAINTAINABILITY,
            affected=[f"{f.rel_path} ({f.lines}行)" for f in top3]))
    return _inverse_linear_score(len(large_files), len(py_files) // 5, 0)
def _dim_maintainability(
    config: TenDimConfig,
    scan_result: ScanResult,
    py_files: list[FileMeta],
    all_files: list[FileMeta],
) -> tuple[float, list[dict], list[str], dict]:
    issues: list[dict] = []
    highlights: list[str] = []
    details: dict[str, Any] = {}
    if not py_files:
        details.update(_not_applicable_details("no_python_files"))
        return 0.0, issues, highlights, details
    analyzed = [
        f for f in py_files if f.extra.get("ast_status", "ok") == "ok"]
    unavailable = [
        f for f in py_files if f.extra.get("ast_status", "ok") != "ok"]
    details["ast_analysis_file_total"] = len(py_files)
    details["ast_analyzed_files"] = len(analyzed)
    details["ast_analysis_status"] = (
        "complete" if not unavailable
        else "partial" if analyzed else "unavailable")
    if unavailable:
        details["ast_unavailable_files"] = [f.rel_path for f in unavailable]
        issues.append(_issue(
            "P1",
            f"{len(unavailable)} 个 Python 文件 AST 分析失败，"
            "可维护性评分证据不完整",
            CAT_MAINTAINABILITY,
            affected=[f.rel_path for f in unavailable]))
    if not analyzed:
        details.update(_not_applicable_details("ast_analysis_unavailable"))
        return 0.0, issues, highlights, details
    complexity_score = _collect_complexity_metric(
        analyzed, config, issues, highlights, details)
    func_score = _collect_function_size_metric(analyzed, config, issues, details)
    file_score = _collect_file_size_metric(analyzed, config, issues, details)
    score = complexity_score * 0.5 + func_score * 0.25 + file_score * 0.25
    return _dim_result(score, issues, highlights, details)
def _dim_readability(
    config: TenDimConfig,
    scan_result: ScanResult,
    py_files: list[FileMeta],
    all_files: list[FileMeta],
) -> tuple[float, list[dict], list[str], dict]:
    issues: list[dict] = []
    highlights: list[str] = []
    details: dict[str, Any] = {}
    if not py_files:
        details.update(_not_applicable_details("no_python_files"))
        return 0.0, issues, highlights, details
    total_lines = sum(f.lines for f in py_files)
    total_comments = sum(f.comment_lines for f in py_files)
    comment_ratio = total_comments / max(total_lines, 1)
    details["comment_ratio"] = round(comment_ratio, 3)
    details["good_comment_ratio"] = config.good_comment_ratio
    if comment_ratio < config.min_acceptable_comment_ratio:
        issues.append(_issue(
            "P1",
            f"注释率仅 {comment_ratio:.1%}，低于最低要求 {config.min_acceptable_comment_ratio:.0%}",
            "readability"))
    elif comment_ratio >= config.good_comment_ratio:
        highlights.append(f"注释率良好 ({comment_ratio:.1%})")
    mixed_naming = 0
    for f in py_files:
        if sum(_naming_traits(f.stem)) > 1:
            mixed_naming += 1
    details["mixed_naming_files"] = mixed_naming
    if mixed_naming > 0:
        issues.append(_issue(
            "P2", f"{mixed_naming} 个文件存在混合命名风格", "readability"))
    comment_score = _ratio_band_score(
        comment_ratio, config.good_comment_ratio,
        config.min_acceptable_comment_ratio)
    naming_score = _inverse_linear_score(mixed_naming, len(py_files) // 4, 0)
    score = comment_score * 0.7 + naming_score * 0.3
    return _dim_result(score, issues, highlights, details)
def _dim_modularity(
    config: TenDimConfig,
    scan_result: ScanResult,
    py_files: list[FileMeta],
    all_files: list[FileMeta],
) -> tuple[float, list[dict], list[str], dict]:
    issues: list[dict] = []
    highlights: list[str] = []
    details: dict[str, Any] = {}
    if not py_files:
        details.update(_not_applicable_details("no_python_files"))
        return 0.0, issues, highlights, details
    dir_files = _dir_file_distribution(py_files)
    oversize_dirs = {d: c for d, c in dir_files.items()
                     if c > config.max_files_per_dir}
    module_dir_total = sum(1 for directory in dir_files if directory != ".")
    mini_dirs = [d for d, c in dir_files.items()
                 if c < config.min_files_for_module and d != "."]
    details["total_dirs"] = len(dir_files)
    details["module_dir_total"] = module_dir_total
    details["oversize_dirs"] = len(oversize_dirs)
    details["max_files_in_dir"] = max(dir_files.values()) if dir_files else 0
    details["mini_dirs"] = len(mini_dirs)
    issues.extend(filter(None, (
        _oversize_dir_issue(oversize_dirs, config.max_files_per_dir),
        _mini_dir_issue(mini_dirs, module_dir_total, config.min_files_for_module),
    )))
    local_facts_available = scan_result.config.get("extract_dependencies", True)
    dependency_files = [
        f for f in py_files
        if local_facts_available and not _import_facts_unavailable(f)]
    dependency_unavailable = [
        f.rel_path for f in py_files
        if not local_facts_available or _import_facts_unavailable(f)]
    _record_import_analysis(
        details, issues, "modularity", py_files,
        dependency_unavailable, "本地依赖")
    avg_deps = _avg_local_deps(dependency_files) if dependency_files else None
    details["avg_local_deps"] = (
        round(avg_deps, 2) if avg_deps is not None else None)
    oversize_score = _inverse_linear_score(len(oversize_dirs), 10, 0)
    mini_score = _inverse_linear_score(len(mini_dirs), module_dir_total * 0.5, 0)
    directory_score = oversize_score * 0.4 + mini_score * 0.3
    if dependency_files:
        deps_score = _inverse_linear_score(avg_deps, 15, 0)
        score = directory_score + deps_score * 0.3
    else:
        score = directory_score / 0.7
    return _dim_result(score, issues, highlights, details)
def _collect_test_files(scan_result: ScanResult,
                        py_files: list[FileMeta]) -> dict[str, FileMeta]:
    test_files = [
        f for f in scan_result.get_files_by_type("test") if f.is_python
    ]
    named_test_files = [
        f for f in py_files
        if f.stem.startswith("test_") or f.stem.endswith("_test")
    ]
    return {f.rel_path: f for f in test_files + named_test_files}
def _dim_test_coverage(
    config: TenDimConfig,
    scan_result: ScanResult,
    py_files: list[FileMeta],
    all_files: list[FileMeta],
) -> tuple[float, list[dict], list[str], dict]:
    issues: list[dict] = []
    highlights: list[str] = []
    details: dict[str, Any] = {}
    if not py_files:
        details.update(_not_applicable_details("no_python_files"))
        return 0.0, issues, highlights, details
    production = _production_files(py_files)
    _record_scan_scope(details, py_files, production)
    if not production:
        details.update(_not_applicable_details(_NO_PRODUCTION_STATUS))
        return 0.0, issues, highlights, details
    all_tests = _collect_test_files(scan_result, py_files)
    test_ratio = len(all_tests) / max(len(production), 1)
    details["test_files"] = len(all_tests)
    details["test_ratio"] = round(test_ratio, 3)
    if test_ratio < config.min_test_ratio:
        issues.append(_issue(
            "P1",
            f"测试文件比例 {test_ratio:.0%}，低于 {config.min_test_ratio:.0%}",
            "test_coverage"))
    elif test_ratio > 0.25:
        highlights.append(f"测试文件覆盖良好 ({test_ratio:.0%})")
    flags, import_unavailable = _probe_module_imports(
        py_files, ("pytest", "unittest"),
        facts_available=scan_result.config.get("extract_dependencies", True))
    _record_import_analysis(
        details, issues, "test_coverage", py_files,
        import_unavailable, "测试框架")
    details["has_pytest"] = flags["pytest"]
    details["has_unittest"] = flags["unittest"]
    frameworks = [name for name, found in flags.items() if found]
    if frameworks:
        highlights.append(f"检测到测试框架: {' '.join(frameworks)}")
    score = _linear_score(test_ratio, 0.4)
    return _dim_result(score, issues, highlights, details)
def _collect_readme_metric(scan_result: ScanResult, all_files: list[FileMeta],
                          issues: list[dict], highlights: list[str],
                          details: dict) -> bool:
    has_readme, probed = _probe_readme_presence(scan_result, all_files)
    details["has_readme"] = has_readme
    if probed:
        details["readme_detected_on_disk"] = probed
    if not has_readme:
        issues.append(_issue("P2", "未找到 README 文件", "documentation"))
    else:
        highlights.append("存在 README 文档")
    return has_readme
def _dim_documentation(
    config: TenDimConfig,
    scan_result: ScanResult,
    py_files: list[FileMeta],
    all_files: list[FileMeta],
) -> tuple[float, list[dict], list[str], dict]:
    issues: list[dict] = []
    highlights: list[str] = []
    details: dict[str, Any] = {}
    if not py_files:
        details.update(_not_applicable_details("no_python_files"))
        return 0.0, issues, highlights, details
    analyzed = [
        f for f in py_files if f.extra.get("ast_status", "ok") == "ok"]
    unavailable = [
        f for f in py_files if f.extra.get("ast_status", "ok") != "ok"]
    details["ast_analysis_file_total"] = len(py_files)
    details["ast_analyzed_files"] = len(analyzed)
    details["ast_analysis_status"] = (
        "complete" if not unavailable
        else "partial" if analyzed else "unavailable")
    if unavailable:
        details["ast_unavailable_files"] = [f.rel_path for f in unavailable]
        issues.append(_issue(
            "P1",
            f"{len(unavailable)} 个 Python 文件 AST 分析失败，"
            "文档评分证据不完整",
            "documentation",
            affected=[f.rel_path for f in unavailable]))
    if not analyzed:
        details.update(_not_applicable_details("ast_analysis_unavailable"))
        return 0.0, issues, highlights, details
    avg_doc = sum(f.docstring_coverage for f in analyzed) / len(analyzed)
    details["avg_docstring_coverage"] = round(avg_doc, 3)
    if avg_doc < config.min_docstring_coverage:
        issues.append(_issue(
            "P1",
            f"文档字符串覆盖率 {avg_doc:.0%} 低于 {config.min_docstring_coverage:.0%}",
            "documentation"))
    avg_types = sum(f.type_annotations for f in analyzed) / len(analyzed)
    details["avg_type_annotations"] = round(avg_types, 3)
    if avg_types < 0.3:
        issues.append(_issue(
            "P2", f"类型注解覆盖率 {avg_types:.0%} 偏低", "documentation"))
    elif avg_types > 0.6:
        highlights.append("类型注解覆盖率良好")
    has_readme = _collect_readme_metric(
        scan_result, all_files, issues, highlights, details)
    if avg_doc > 0.7:
        highlights.append("文档字符串覆盖率良好")
    doc_score = _linear_score(avg_doc, 0.8, 0.2)
    type_score = _linear_score(avg_types, 0.7, 0.2)
    readme_score = 100 if has_readme else 50
    score = doc_score * 0.4 + type_score * 0.3 + readme_score * 0.3
    return _dim_result(score, issues, highlights, details)
_IMPORT_STYLE_MIX_PENALTY = 10.0
def _dim_consistency(
    config: TenDimConfig,
    scan_result: ScanResult,
    py_files: list[FileMeta],
    all_files: list[FileMeta],
) -> tuple[float, list[dict], list[str], dict]:
    issues: list[dict] = []
    highlights: list[str] = []
    details: dict[str, Any] = {}
    if not py_files:
        details.update(_not_applicable_details("no_python_files"))
        return 0.0, issues, highlights, details
    naming_styles, dominant_style, consistency = _naming_style_consistency(py_files)
    details["dominant_style"] = dominant_style
    details["naming_consistency"] = round(consistency, 3)
    if consistency < 0.7:
        issues.append(_issue(
            "P2", f"文件命名风格不一致，主导风格占比仅 {consistency:.0%}",
            "consistency", details=dict(naming_styles)))
    elif consistency > 0.9:
        highlights.append(f"文件命名风格一致 ({dominant_style})")
    (abs_imports, rel_imports, external_abs_imports,
     import_unavailable) = _count_import_styles(
        py_files,
        local_facts_available=scan_result.config.get(
            "extract_dependencies", True),
    )
    _record_import_analysis(
        details, issues, "consistency", py_files,
        import_unavailable, "导入风格")
    details["abs_imports"] = abs_imports
    details["rel_imports"] = rel_imports
    details["external_abs_imports"] = external_abs_imports
    total_imports = abs_imports + rel_imports
    if total_imports > 0:
        details["import_style_mix"] = round(abs_imports / total_imports, 2)
    mixed_imports = abs_imports > 0 and rel_imports > 0
    if mixed_imports:
        issues.append(_issue(
            "P2",
            f"本地模块混用绝对/相对导入风格（绝对 {abs_imports} 处 / 相对 {rel_imports} 处），建议统一为绝对导入",
            "consistency"))
    elif total_imports > 0 and details["import_analysis_status"] == "complete":
        style = "绝对导入" if abs_imports else "相对导入"
        highlights.append(f"本地导入风格统一（{style}）")
    score = consistency * 100 - (_IMPORT_STYLE_MIX_PENALTY if mixed_imports else 0)
    return _dim_result(score, issues, highlights, details)
def _dim_security(
    config: TenDimConfig,
    scan_result: ScanResult,
    py_files: list[FileMeta],
    all_files: list[FileMeta],
) -> tuple[float, list[dict], list[str], dict]:
    issues: list[dict] = []
    highlights: list[str] = []
    details: dict[str, Any] = {}
    production = _production_files(py_files)
    _record_scan_scope(details, py_files, production)
    env_total, affected, probed_only = _env_leak_scan(
        scan_result, all_files)
    details["env_files_found"] = env_total
    if env_total:
        if probed_only:
            details["env_detected_on_disk"] = sorted(probed_only)
        issues.append(_issue(
            "P0", f"发现 {env_total} 个环境变量文件（可能包含敏感信息）",
            "security", affected=affected))
    if not production:
        details["pattern_scan_status"] = _NO_PRODUCTION_STATUS
        if not env_total:
            details.update(_not_applicable_details(_NO_PRODUCTION_STATUS))
            return 0.0, issues, highlights, details
        return _dim_result(
            100 - min(env_total * 15, 70), issues, highlights, details)
    pattern_scan = _match_patterns_across_files(
        production, config.security_patterns,
        flags=re.IGNORECASE, tag="security")
    match_details = pattern_scan.matches
    _record_pattern_scan(details, pattern_scan, issues, "security")
    if pattern_scan.status == "unavailable" and not env_total:
        status = ("source_unreadable" if pattern_scan.skipped_files
                  else "no_valid_security_patterns")
        details.update(_not_applicable_details(status))
        return 0.0, issues, highlights, details
    total_matches = sum(match_details.values())
    details["security_matches"] = total_matches
    details["pattern_details"] = dict(match_details)
    if total_matches == 0:
        if pattern_scan.status == "complete":
            highlights.append("未发现明显安全风险模式")
    else:
        severity_counts = _pattern_severity_counts(
            match_details, _classify_security_pattern)
        details["security_severity_counts"] = dict(severity_counts)
        p0_count = severity_counts["P0"]
        top_patterns = sorted(
            match_details.items(), key=lambda x: (-x[1], x[0]))[:5]
        severity = next(
            level for level in ("P0", "P1", "P2") if severity_counts[level])
        issues.append(_issue(
            severity, f"发现 {total_matches} 处潜在安全风险 (其中 {p0_count} 处高置信)",
            "security", details=[f"{pat}: {cnt}次" for pat, cnt in top_patterns]))
    penalty = min(total_matches * 8 + env_total * 15, 70)
    score = 100 - penalty
    return _dim_result(score, issues, highlights, details)
def _dim_performance(
    config: TenDimConfig,
    scan_result: ScanResult,
    py_files: list[FileMeta],
    all_files: list[FileMeta],
) -> tuple[float, list[dict], list[str], dict]:
    issues: list[dict] = []
    highlights: list[str] = []
    details: dict[str, Any] = {}
    production = _production_files(py_files)
    _record_scan_scope(details, py_files, production)
    if not production:
        details.update(_not_applicable_details(_NO_PRODUCTION_STATUS))
        return 0.0, issues, highlights, details
    pattern_scan = _match_patterns_across_files(
        production, config.performance_patterns, flags=0, tag="performance")
    pattern_counts = pattern_scan.matches
    _record_pattern_scan(details, pattern_scan, issues, "performance")
    if pattern_scan.status == "unavailable":
        status = ("source_unreadable" if pattern_scan.skipped_files
                  else "no_valid_performance_patterns")
        details.update(_not_applicable_details(status))
        return 0.0, issues, highlights, details
    total_matches = sum(pattern_counts.values())
    details["performance_matches"] = total_matches
    if total_matches == 0:
        if pattern_scan.status == "complete":
            highlights.append("未发现明显性能反模式")
    else:
        top = sorted(pattern_counts.items(),
                     key=lambda x: (-x[1], x[0]))[:3]
        issues.append(_issue(
            "P2", f"发现 {total_matches} 处潜在性能问题",
            "performance", details=[f"{pat}: {cnt}次" for pat, cnt in top]))
    penalty = min(total_matches * 3, 40)
    score = 100 - penalty
    return _dim_result(score, issues, highlights, details)
def _collect_duplicate_metric(py_files: list[FileMeta], issues: list[dict],
                             details: dict) -> tuple[dict, int]:
    duplicates, dup_count = _duplicate_sha_groups(py_files)
    details["duplicate_groups"] = len(duplicates)
    if duplicates:
        issues.append(_issue(
            "P1", f"发现 {dup_count} 个重复文件（{len(duplicates)} 组）",
            "simplicity",
            details={sha[:8]: paths for sha, paths in list(duplicates.items())[:3]}))
    return duplicates, dup_count
def _collect_commented_code_metric(py_files: list[FileMeta], issues: list[dict],
                                   details: dict) -> int:
    unavailable_files: list[str] = []
    commented_code = _count_commented_code(py_files, unavailable_files)
    details["commented_code_lines"] = commented_code
    file_total = len(py_files)
    analyzed = file_total - len(unavailable_files)
    details["source_analysis_file_total"] = file_total
    details["source_analyzed_files"] = analyzed
    details["source_analysis_status"] = (
        "complete" if not unavailable_files
        else "partial" if analyzed else "unavailable")
    if unavailable_files:
        details["source_unavailable_files"] = unavailable_files
        issues.append(_issue(
            "P1",
            f"{len(unavailable_files)} 个源码文件读取失败，简洁性评分证据不完整",
            "simplicity", affected=unavailable_files))
    if commented_code > 10:
        issues.append(_issue(
            "P2", f"发现 {commented_code} 行疑似注释掉的代码", "simplicity"))
    return commented_code
def _dim_simplicity(
    config: TenDimConfig,
    scan_result: ScanResult,
    py_files: list[FileMeta],
    all_files: list[FileMeta],
) -> tuple[float, list[dict], list[str], dict]:
    issues: list[dict] = []
    highlights: list[str] = []
    details: dict[str, Any] = {}
    if not py_files:
        details.update(_not_applicable_details("no_python_files"))
        return 0.0, issues, highlights, details
    empty_files = [f for f in py_files if f.code_lines <= 1 and f.stem != "__init__"]
    details["empty_files"] = len(empty_files)
    if empty_files:
        issues.append(_issue(
            "P1", f"发现 {len(empty_files)} 个几乎为空的文件",
            "simplicity", affected=[f.rel_path for f in empty_files[:5]]))
    duplicates, dup_count = _collect_duplicate_metric(py_files, issues, details)
    commented_code = _collect_commented_code_metric(py_files, issues, details)
    empty_score = _inverse_linear_score(len(empty_files), 15, 0)
    dup_score = _inverse_linear_score(dup_count, 25, 0)
    comment_score = _inverse_linear_score(commented_code, 100, 0)
    if (not empty_files and not duplicates and commented_code <= 10
            and details["source_analysis_status"] == "complete"):
        highlights.append("代码简洁，无冗余文件")
    if details["source_analysis_status"] == "unavailable":
        score = (empty_score * 0.30 + dup_score * 0.50) / 0.80
    else:
        score = empty_score * 0.30 + dup_score * 0.50 + comment_score * 0.20
    return _dim_result(score, issues, highlights, details)
def _dim_robustness(
    config: TenDimConfig,
    scan_result: ScanResult,
    py_files: list[FileMeta],
    all_files: list[FileMeta],
) -> tuple[float, list[dict], list[str], dict]:
    issues: list[dict] = []
    highlights: list[str] = []
    details: dict[str, Any] = {}
    production = _production_files(py_files)
    _record_scan_scope(details, py_files, production)
    if not production:
        details.update(_not_applicable_details(_NO_PRODUCTION_STATUS))
        return 0.0, issues, highlights, details
    pattern_scan = _match_patterns_across_files(
        production, config.robustness_patterns, flags=0, tag="robustness")
    pattern_counts = pattern_scan.matches
    _record_pattern_scan(details, pattern_scan, issues, "robustness")
    if pattern_scan.status == "unavailable":
        status = ("source_unreadable" if pattern_scan.skipped_files
                  else "no_valid_robustness_patterns")
        details.update(_not_applicable_details(status))
        return 0.0, issues, highlights, details
    total_matches = sum(pattern_counts.values())
    severity_counts = _pattern_severity_counts(
        pattern_counts, _classify_robustness_pattern)
    p0_count = severity_counts["P0"]
    details["robustness_issues"] = total_matches
    details["p0_robustness_issues"] = p0_count
    details["issue_patterns"] = dict(pattern_counts)
    if total_matches == 0:
        if pattern_scan.status == "complete":
            highlights.append("异常处理模式健康")
    else:
        issues.append(_robustness_pattern_issue(total_matches, p0_count))
    logging_flags, import_unavailable = _probe_module_imports(
        production, ("logging", "structlog"),
        facts_available=scan_result.config.get("extract_dependencies", True))
    _record_import_analysis(
        details, issues, "robustness", production,
        import_unavailable, "日志框架")
    has_logging, has_structlog = (
        logging_flags["logging"], logging_flags["structlog"])
    details["has_logging"] = has_logging
    details["has_structlog"] = has_structlog
    if has_structlog:
        highlights.append(
            "使用 logging 模块 + structlog" if has_logging
            else "使用 structlog 结构化日志")
    elif has_logging:
        highlights.append("使用 logging 模块")
    elif details["import_analysis_status"] == "complete":
        issues.append(_issue(
            "P2", "未检测到 logging 模块使用（建议使用结构化日志）", "robustness"))
    penalty = min(total_matches * 5, 50)
    score = 100 - penalty
    if has_logging:
        score = min(100, score + 5)
    if has_structlog:
        score = min(100, score + 3)
    return _dim_result(score, issues, highlights, details)
_DIMENSION_SPECS: tuple[_DimensionSpec, ...] = (
    _DimensionSpec(CAT_MAINTAINABILITY, "可维护性", 0.15, 0.12,
                   "拆分长函数和大文件，降低圈复杂度", _dim_maintainability),
    _DimensionSpec("readability", "可读性", 0.12, 0.05,
                   "增加注释，统一命名风格", _dim_readability),
    _DimensionSpec("security", "安全性", 0.15, 0.08,
                   "移除 eval/exec 等危险调用，审查输入验证", _dim_security),
    _DimensionSpec("performance", "性能", 0.08, 0.18,
                   "优化循环中的低效操作，使用更高效的数据结构", _dim_performance),
    _DimensionSpec("modularity", "模块化", 0.10, 0.06,
                   "拆分超大模块，合并碎片文件", _dim_modularity),
    _DimensionSpec("test_coverage", "测试覆盖", 0.08, 0.03,
                   "增加单元测试和集成测试覆盖", _dim_test_coverage),
    _DimensionSpec("documentation", "文档覆盖", 0.08, 0.04,
                   "补充文档字符串和类型注解", _dim_documentation),
    _DimensionSpec("consistency", "一致性", 0.08, 0.08,
                   "统一文件命名和代码风格", _dim_consistency),
    _DimensionSpec("simplicity", "简洁性", 0.08, 0.22,
                   "移除死代码和重复文件", _dim_simplicity),
    _DimensionSpec("robustness", "健壮性", 0.08, 0.22,
                   "规范异常处理，避免裸 except", _dim_robustness),
)
DEFAULT_DIMENSION_WEIGHTS: dict[str, float] = {
    spec.name: spec.weight for spec in _DIMENSION_SPECS}
DIMENSION_FP_TENDENCY: dict[str, float] = {
    spec.name: spec.fp_tendency for spec in _DIMENSION_SPECS}
_DIMENSION_SCORERS: dict[str, Callable] = {
    spec.name: spec.scorer for spec in _DIMENSION_SPECS}
_DIMENSION_ACTIONS: dict[str, str] = {
    spec.name: spec.action for spec in _DIMENSION_SPECS}
_DIMENSION_LABELS: list[tuple[str, str]] = [
    (spec.name, spec.label) for spec in _DIMENSION_SPECS]
class TenDimScorer:
    DIMENSIONS: ClassVar[list[tuple[str, str]]] = _DIMENSION_LABELS
    def __init__(self, config: TenDimConfig | None = None):
        if config is not None and not isinstance(config, TenDimConfig):
            raise TypeError(
                "TenDimScorer.config 须为 TenDimConfig 或 None，实际为 "
                f"{type(config).__name__}")
        self.config = config or TenDimConfig()
    def score(self, scan_result: ScanResult) -> TenDimReport:
        if not isinstance(scan_result, ScanResult):
            raise TypeError(
                "TenDimScorer.score 须接收 ScanResult，实际为 "
                f"{type(scan_result).__name__}")
        py_files = scan_result.get_python_files()
        if not py_files:
            dimensions = [
                self._not_applicable_dimension(dim_name, dim_label)
                for dim_name, dim_label in self.DIMENSIONS]
            return self._build_report(
                scan_result, dimensions, 0.0, 0.0,
                scoring_applicable=False,
                summary_override="未发现可评分的 Python 文件，十维评分不适用。")
        all_files = list(scan_result.files.values())
        dimensions = [
            self._score_dimension(dim_name, dim_label, scan_result,
                                  py_files, all_files)
            for dim_name, dim_label in self.DIMENSIONS]
        ast_failed = [
            f for f in py_files
            if f.extra.get("ast_status", "ok") not in {"ok", "disabled"}]
        if ast_failed:
            return self._build_report(
                scan_result, dimensions, 0.0, 0.0,
                scoring_applicable=False,
                summary_override=(
                    f"{len(ast_failed)} 个 Python 文件 AST 分析失败，"
                    "无法形成完整十维总分；维度结果仅作部分证据。"))
        applicable = [
            dimension for dimension in dimensions
            if dimension.details.get("applicable", True) is not False]
        total_weight = sum(dimension.weight for dimension in applicable)
        if total_weight <= 0:
            reason = (
                "已启用评分维度均缺乏可用评分证据，无法形成加权总分。"
                if any(dimension.weight > 0 for dimension in dimensions)
                else "未启用任何评分维度，十维评分不适用。")
            return self._build_report(
                scan_result, dimensions, 0.0, 0.0,
                scoring_applicable=False, summary_override=reason)
        overall = (
            sum(dimension.score * dimension.weight for dimension in applicable)
            / total_weight)
        avg_confidence = sum(
            dimension.confidence * dimension.weight
            for dimension in applicable) / total_weight
        return self._build_report(scan_result, dimensions, overall, avg_confidence)
    def _not_applicable_dimension(
        self, dim_name: str, dim_label: str, status: str = "no_python_files",
        details: dict[str, Any] | None = None,
        issues: list[dict[str, Any]] | None = None,
        highlights: list[str] | None = None,
    ) -> DimensionScore:
        weight = self.config.weights.get(dim_name, 0.0)
        payload: dict[str, Any] = dict(details or {})
        payload["status"] = status
        payload["applicable"] = False
        return DimensionScore(
            name=dim_name, label=dim_label, score=0.0, weight=weight,
            weighted_score=0.0, grade="N/A", confidence=0.0,
            issues=issues or [], highlights=highlights or [], details=payload)
    def _score_dimension(
        self, dim_name: str, dim_label: str, scan_result: ScanResult,
        py_files: list[FileMeta], all_files: list[FileMeta],
    ) -> DimensionScore:
        weight = self.config.weights.get(dim_name, 0.0)
        if weight <= 0:
            return self._not_applicable_dimension(
                dim_name, dim_label, status="disabled")
        score, issues, highlights, details = _DIMENSION_SCORERS[dim_name](
            self.config, scan_result, py_files, all_files)
        if details.get("applicable") is False:
            return self._not_applicable_dimension(
                dim_name, dim_label,
                status=str(details.get("status") or "not_applicable"),
                details=details, issues=issues, highlights=highlights)
        rounded_score = round(score, 1)
        sample_count = details.get(
            "scanned_production_files", len(py_files))
        if dim_name == "security":
            sample_count += details.get("env_files_found", 0)
        confidence = _compute_fp_aware_confidence(dim_name, sample_count)
        scan_file_total = details.get("pattern_scan_file_total", 0)
        if scan_file_total:
            evidence_ratio = (
                details.get("pattern_scanned_files", 0) / scan_file_total)
            scan_pattern_total = details.get("pattern_scan_pattern_total", 0)
            if scan_pattern_total:
                valid_patterns = (
                    scan_pattern_total - len(details.get("invalid_patterns", [])))
                evidence_ratio *= max(0, valid_patterns) / scan_pattern_total
            confidence = round(confidence * evidence_ratio, 3)
        analysis_total = details.get("ast_analysis_file_total", 0)
        if analysis_total:
            analysis_ratio = (
                details.get("ast_analyzed_files", 0) / analysis_total)
            confidence = round(confidence * analysis_ratio, 3)
        import_total = details.get("import_analysis_file_total", 0)
        if import_total:
            import_ratio = details.get("import_analyzed_files", 0) / import_total
            confidence = round(confidence * import_ratio, 3)
        source_total = details.get("source_analysis_file_total", 0)
        if source_total:
            source_ratio = details.get("source_analyzed_files", 0) / source_total
            confidence = round(confidence * source_ratio, 3)
        dimension = DimensionScore(
            name=dim_name, label=dim_label,
            score=rounded_score, weight=weight,
            weighted_score=round(rounded_score * weight, 1),
            grade=_compute_grade(rounded_score, self.config.grade_thresholds),
            confidence=confidence,
            issues=issues, highlights=highlights, details=details,
        )
        return dimension
    def _build_report(
        self, scan_result: ScanResult, dimensions: list[DimensionScore],
        overall: float, avg_confidence: float, *,
        scoring_applicable: bool = True,
        summary_override: str | None = None,
    ) -> TenDimReport:
        rounded_overall = round(overall, 1)
        overall_grade = (
            _compute_grade(rounded_overall, self.config.grade_thresholds)
            if scoring_applicable else "N/A")
        summary = (
            summary_override if summary_override is not None
            else self._generate_summary(
                rounded_overall, overall_grade, dimensions))
        recommendations = (self._generate_recommendations(dimensions)
                           if scoring_applicable else [])
        return TenDimReport(
            project_root=scan_result.project_root,
            project_name=os.path.basename(scan_result.project_root.rstrip("/\\")),
            overall_score=rounded_overall,
            overall_grade=overall_grade,
            overall_confidence=round(avg_confidence, 2),
            dimensions=dimensions,
            summary=summary,
            recommendations=recommendations,
            scan_summary={
                "total_files": scan_result.summary.total_files,
                "total_lines": scan_result.summary.total_lines,
                "scan_duration_ms": scan_result.summary.scan_duration_ms,
            },
        )
    def _generate_recommendations(self, dimensions: list[DimensionScore]) -> list[dict[str, Any]]:
        recs: list[dict[str, Any]] = []
        for d in dimensions:
            if d.weight <= 0 or d.grade == "N/A":
                continue
            severities = {
                str(issue.get("severity") or "").upper()
                for issue in d.issues if isinstance(issue, dict)}
            has_p0 = "P0" in severities
            scan_incomplete = (
                d.details.get("pattern_scan_status") in {"partial", "unavailable"}
                or d.details.get("ast_analysis_status") in {"partial", "unavailable"}
                or d.details.get("import_analysis_status") in {"partial", "unavailable"}
                or d.details.get("source_analysis_status") in {"partial", "unavailable"})
            if d.score >= 80 and not has_p0 and not scan_incomplete:
                continue
            if has_p0 or d.score < 50:
                priority = "P0"
            elif scan_incomplete or d.score < 70:
                priority = "P1"
            else:
                priority = "P2"
            recs.append({
                "priority": priority,
                "dimension": d.name,
                "dimension_label": d.label,
                "score": d.score,
                "message": f"维度「{d.label}」得分 {d.score:.1f}，建议优先改进",
                "action": _DIMENSION_ACTIONS.get(
                    d.name, "根据问题列表逐一修复"),
            })
        priority_order = {"P0": 0, "P1": 1, "P2": 2}
        recs.sort(key=lambda r: (priority_order.get(r["priority"], 99), r["score"]))
        return recs
    def _generate_summary(
        self, overall_score: float, overall_grade: str, dimensions: list[DimensionScore],
    ) -> str:
        active_dimensions = [
            d for d in dimensions if d.weight > 0 and d.grade != "N/A"]
        sorted_dims = sorted(active_dimensions, key=lambda d: d.score)
        has_score_spread = bool(
            sorted_dims
            and sorted_dims[0].score != sorted_dims[-1].score)
        k = min(3, len(sorted_dims) // 2) if has_score_spread else 0
        weakest = sorted_dims[:k]
        strongest = sorted_dims[len(sorted_dims) - k:][::-1] if k else []
        if strongest:
            weak_cut = strongest[-1].score
            weakest = [d for d in weakest if d.score < weak_cut]
        grade_desc = {
            "A": "优秀，各项指标均衡",
            "B": "良好，存在少量改进空间",
            "C": "一般，多个维度需要关注",
            "D": "较差，存在较多质量问题",
            "F": "严重，需要进行全面重构",
        }
        weak_names = "、".join(d.label for d in weakest)
        strong_names = "、".join(d.label for d in strongest)
        fragments: list[str] = []
        if strong_names:
            fragments.append(f"优势维度: {strong_names}")
        if weak_names:
            fragments.append(f"薄弱维度: {weak_names}")
        if overall_grade in grade_desc:
            head = f"项目整体质量{grade_desc[overall_grade]}（{overall_score:.1f}分）。"
        else:
            head = f"项目整体质量等级 {overall_grade}（{overall_score:.1f}分）。"
        if not fragments:
            return head
        return head + "；".join(fragments) + "。"
def _coerce_project_root(project_root: Any) -> str:
    try:
        root = os.fspath(project_root)
    except (TypeError, ValueError):
        return ""
    if isinstance(root, bytes):
        root = os.fsdecode(root)
    if not isinstance(root, str) or not root.strip():
        return ""
    return root
def quick_score(
    project_root: str,
    config: TenDimConfig | None = None,
    include_patterns: list[str] | None = None,
) -> TenDimReport:
    root = _coerce_project_root(project_root)
    if not root or not os.path.isdir(root):
        raise FileNotFoundError(
            f"quick_score 项目根目录不存在或不是目录: {project_root!r}"
            "（路径输入错误不得静默产出满分误报报告）")
    scan_result = quick_scan(root, include_patterns=include_patterns)
    scorer = TenDimScorer(config)
    return scorer.score(scan_result)

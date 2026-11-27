from __future__ import annotations

import ast
import codecs
import copy
import csv
import fnmatch
import hashlib
import io
import math
import os
import re
import sys
import time
import tokenize
from bisect import bisect_right
from collections import Counter
from collections.abc import Iterator
from dataclasses import asdict, dataclass, field
from functools import cache
from typing import Any, NamedTuple, Protocol

if __package__ in (None, ""):
    _JWSGJ_PARENT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    if _JWSGJ_PARENT not in sys.path:
        sys.path.insert(0, _JWSGJ_PARENT)
from jwsgj.diag_guard_io import (
    guarded_open,
)
from jwsgj.diag_guard_state import (
    JsonSerializableMixin,
)
from jwsgj.diag_shared_source_core import parse_cached
from jwsgj.diag_types_vocab import (
    MSG_EXCEPTION_BROAD_HANDLER,
    MSG_OSERROR_DEGRADED,
    MSG_SYNTAX_ERROR_SKIP,
)
from jwsgj.html_render_diag import render_file_scan_report_html
from jwsgj.html_report_stage_doc import emit_to_stage
from jwsgj.log_config import get_module_logger, log_swallowed, setup_logging
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import report_artifact_dir, stage_json_artifact_path
from jwsgj.skill_profile import LANGUAGE_BY_SUFFIX

__all__ = [
    "BOM_DERIVED_ENCODINGS",
    "ENCODING_SNIFF_BYTES",
    "ASTAnalyzer",
    "ConsoleProgress",
    "DirectoryMeta",
    "FileMeta",
    "FileScanner",
    "LineCounter",
    "ScanConfig",
    "ScanProgress",
    "ScanResult",
    "ScanSummary",
    "classify_file_type",
    "detect_encoding",
    "detect_encoding_bytes",
    "detect_language",
    "extract_encoding_declaration",
    "extract_shebang",
    "quick_scan",
]
logger = get_module_logger(__name__, __file__)
_DEFAULT_INCLUDE_PATTERNS: tuple[str, ...] = ("*.py",)
_DEFAULT_ENCODING = "utf-8"
class ScanProgress(Protocol):
    def on_scan_start(self, project_root: str, total_estimate: int) -> None:
        _ = (project_root, total_estimate)
    def on_file_scanned(self, filepath: str, index: int, total: int) -> None:
        _ = (filepath, index, total)
    def on_scan_complete(self, summary: ScanSummary) -> None:
        _ = summary
    def on_error(self, filepath: str, error: str) -> None:
        _ = (filepath, error)
class ConsoleProgress:
    def __init__(self, verbosity: int = 1):
        self.verbosity = verbosity
        self._start_time: float | None = None
    def _elapsed_seconds(self) -> float:
        if self._start_time is None:
            return 0.0
        return max(time.monotonic() - self._start_time, 0.0)
    def on_scan_start(self, project_root: str, total_estimate: int) -> None:
        self._start_time = time.monotonic()
        if self.verbosity >= 1:
            logger.info("[FileScanner] 开始扫描: %s（预估 %d 个文件）",
                        project_root, total_estimate)
    def on_file_scanned(self, filepath: str, index: int, total: int) -> None:
        if self.verbosity >= 2 and index % 50 == 0:
            elapsed = self._elapsed_seconds()
            rate = index / elapsed if elapsed > 0 else 0.0
            total_disp = total if total > 0 else "?"
            logger.info(f"  [{index}/{total_disp}] {filepath} ({rate:.0f} 文件/秒)")
    def on_scan_complete(self, summary: ScanSummary) -> None:
        elapsed = self._elapsed_seconds()
        if self.verbosity >= 1:
            logger.info(f"[FileScanner] 扫描完成: {summary.total_files} 个文件, "
                        f"{summary.total_lines} 行, {elapsed:.2f}秒")
    def on_error(self, filepath: str, error: str) -> None:
        if self.verbosity >= 1:
            logger.error(f"[FileScanner] 错误: {filepath} — {error}")
@dataclass
class FileMeta:
    rel_path: str
    abs_path: str
    name: str
    stem: str
    extension: str
    language: str
    file_type: str
    size_bytes: int
    lines: int
    code_lines: int
    comment_lines: int
    blank_lines: int
    mtime: float
    sha256: str
    encoding: str = _DEFAULT_ENCODING
    shebang: str = ""
    functions: int = 0
    classes: int = 0
    imports: int = 0
    complexity: float = 0.0
    max_complexity: int = 0
    max_function_lines: int = 0
    docstring_coverage: float = 0.0
    type_annotations: float = 0.0
    imported_modules: list[str] = field(default_factory=list)
    local_imports: list[str] = field(default_factory=list)
    extra: dict[str, Any] = field(default_factory=dict)
    @property
    def is_python(self) -> bool:
        return self.language == "python"
    @property
    def is_test(self) -> bool:
        return self.file_type == "test"
    @property
    def size_kb(self) -> float:
        return self.size_bytes / 1024.0
    @property
    def comment_ratio(self) -> float:
        return self.comment_lines / max(self.lines, 1)
@dataclass
class DirectoryMeta:
    rel_path: str
    abs_path: str
    file_count: int = 0
    total_lines: int = 0
    total_size: int = 0
    subdirs: list[str] = field(default_factory=list)
    files: list[str] = field(default_factory=list)
    total_functions: int = 0
    total_classes: int = 0
    total_imports: int = 0
    avg_complexity: float = 0.0
@dataclass
class ScanSummary:
    total_files: int = 0
    total_lines: int = 0
    total_code_lines: int = 0
    total_comment_lines: int = 0
    total_blank_lines: int = 0
    total_size_bytes: int = 0
    total_functions: int = 0
    total_classes: int = 0
    by_language: dict[str, int] = field(default_factory=dict)
    by_type: dict[str, int] = field(default_factory=dict)
    by_extension: dict[str, int] = field(default_factory=dict)
    largest_files: list[tuple[str, int]] = field(default_factory=list)
    most_complex_files: list[tuple[str, float]] = field(default_factory=list)
    complexity_distribution: dict[str, int] = field(default_factory=dict)
    size_distribution: dict[str, int] = field(default_factory=dict)
    scan_duration_ms: float = 0.0
_CSV_FIELDS: tuple[str, ...] = (
    "rel_path", "language", "file_type", "lines", "code_lines",
    "comment_lines", "blank_lines", "size_bytes", "functions",
    "classes", "imports", "complexity", "docstring_coverage",
    "type_annotations", "max_function_lines",
)
@dataclass
class ScanResult(JsonSerializableMixin):
    project_root: str
    config: dict[str, Any] = field(default_factory=dict)
    summary: ScanSummary = field(default_factory=ScanSummary)
    files: dict[str, FileMeta] = field(default_factory=dict)
    directories: dict[str, DirectoryMeta] = field(default_factory=dict)
    tree: dict[str, Any] = field(default_factory=dict)
    errors: list[dict[str, Any]] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    def get_python_files(self) -> list[FileMeta]:
        return [f for f in self.files.values() if f.is_python]
    def get_files_by_type(self, file_type: str) -> list[FileMeta]:
        return [f for f in self.files.values() if f.file_type == file_type]
    def get_top_importers(self, top_n: int = 10) -> list[tuple[str, int]]:
        import_counts: Counter = Counter()
        for f in self.get_python_files():
            for imprt in f.local_imports:
                import_counts[imprt] += 1
        return import_counts.most_common(top_n)
    def to_dict(self) -> dict[str, Any]:
        return {
            "project_root": self.project_root,
            "config": copy.deepcopy(self.config),
            "summary": asdict(self.summary),
            "files": {k: asdict(v) for k, v in self.files.items()},
            "directories": {k: asdict(v) for k, v in self.directories.items()},
            "tree": copy.deepcopy(self.tree),
            "errors": [dict(e) for e in self.errors],
            "warnings": list(self.warnings),
        }
    def _report_summary(self) -> dict[str, Any]:
        s = self.summary
        return {
            "total_files": s.total_files,
            "total_lines": s.total_lines,
            "total_code_lines": s.total_code_lines,
            "total_comment_lines": s.total_comment_lines,
            "total_blank_lines": s.total_blank_lines,
            "total_size_bytes": s.total_size_bytes,
            "total_functions": s.total_functions,
            "total_classes": s.total_classes,
            "scan_duration_ms": s.scan_duration_ms,
        }
    def report_data(self, include_tree: bool = True) -> dict[str, Any]:
        s = self.summary
        return {
            "summary": self._report_summary(),
            "by_language": dict(s.by_language),
            "by_type": dict(s.by_type),
            "largest_files": list(s.largest_files),
            "most_complex_files": list(s.most_complex_files),
            "warnings": list(self.warnings),
            "errors": [dict(e) for e in self.errors],
            "project_root": self.project_root,
            "tree": dict(self.tree) if include_tree else {},
        }
    def to_html(self, include_tree: bool = True) -> str:
        return render_file_scan_report_html(self.report_data(include_tree))
    def export_csv(self, filepath: str | None = None) -> str:
        output = io.StringIO()
        writer = csv.writer(output)
        writer.writerow(_CSV_FIELDS)
        for meta in sorted(self.files.values(), key=lambda x: x.rel_path):
            writer.writerow([getattr(meta, name) for name in _CSV_FIELDS])
        csv_content = output.getvalue()
        if filepath:
            with guarded_open(filepath, encoding="utf-8", newline="") as fh:
                fh.write(csv_content)
        return csv_content
_NUMERIC_LIMIT_FIELDS: tuple[str, ...] = (
    "max_depth", "max_files", "max_file_size_mb", "timeout_seconds",
)
_INTEGER_LIMIT_FIELDS = frozenset(("max_depth", "max_files"))
_BOOLEAN_CONFIG_FIELDS: tuple[str, ...] = (
    "follow_symlinks", "analyze_python_ast", "extract_dependencies",
)
def _validate_boolean_flags(config: ScanConfig) -> None:
    for name in _BOOLEAN_CONFIG_FIELDS:
        value = getattr(config, name)
        if not isinstance(value, bool):
            raise TypeError(
                f"ScanConfig: {name} 须为 bool（字符串/整数等真值会让开关"
                f"静默反转），实际为 {value!r}")
def _validate_numeric_limits(config: ScanConfig) -> None:
    for name in _NUMERIC_LIMIT_FIELDS:
        value = getattr(config, name)
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            raise TypeError(
                f"ScanConfig: {name} 须为数值，实际为 {value!r}")
        try:
            finite = math.isfinite(value)
        except OverflowError:
            finite = False
        if not finite:
            raise ValueError(
                f"ScanConfig: {name} 须为有限数值（NaN/inf 会使阈值比较静默失效 "
                f"或触发 OverflowError），实际为 {value!r}")
        if name in _INTEGER_LIMIT_FIELDS and not isinstance(value, int):
            raise TypeError(
                f"ScanConfig: {name} 须为整数，实际为 {value!r}")
        if name in ("max_depth", "max_files") and value < 0:
            raise ValueError(
                f"ScanConfig: {name} 不得为负数（负值会让扫描结果恒为空，"
                f"与空项目不可区分），实际为 {value!r}")
        if name == "max_files" and value == 0:
            raise ValueError(
                "ScanConfig: max_files 须为正整数（0 会让扫描结果恒为空，"
                f"与空项目不可区分），实际为 {value!r}")
        if name == "timeout_seconds" and value <= 0:
            raise ValueError(
                "ScanConfig: timeout_seconds 须为正数（0 或负值会让扫描"
                f"立即超时，结果恒为空），实际为 {value!r}")
        if name == "max_file_size_mb" and value <= 0:
            raise ValueError(
                "ScanConfig: max_file_size_mb 须为正数（0 或负值会让每个"
                "非空文件都被静默跳过，报告与「项目无文件」不可区分），"
                f"实际为 {value!r}")
_PATTERN_CONTAINER_FIELDS: tuple[str, ...] = (
    "include_patterns", "exclude_patterns", "exclude_dirs",
)
def _normalize_pattern_containers(config: ScanConfig) -> None:
    for name in _PATTERN_CONTAINER_FIELDS:
        value = getattr(config, name)
        if value is None:
            value = []
        elif isinstance(value, str):
            value = [value]
        else:
            try:
                value = list(value)
            except TypeError:
                raise TypeError(
                    f"ScanConfig: {name} 须为字符串或字符串序列，"
                    f"实际为 {value!r}") from None
        for index, pattern in enumerate(value):
            if not isinstance(pattern, str):
                raise TypeError(
                    f"ScanConfig: {name}[{index}] 须为字符串，"
                    f"实际为 {pattern!r}")
        setattr(config, name, value)
@dataclass
class ScanConfig:
    project_root: str
    include_patterns: list[str] = field(
        default_factory=lambda: list(_DEFAULT_INCLUDE_PATTERNS))
    exclude_patterns: list[str] = field(
        default_factory=lambda: [".*", ".DS_Store", "Thumbs.db"])
    exclude_dirs: list[str] = field(default_factory=lambda: [
        ".*", "__pycache__", ".git", ".svn", ".hg",
        "node_modules", ".venv", "venv", "env", ".env",
        ".tox", ".eggs", "*.egg-info", "build", "dist",
        ".pytest_cache", ".mypy_cache", ".ruff_cache",
        ".idea", ".vscode", "__MACOSX",
    ])
    max_depth: int = 50
    max_files: int = 10000
    max_file_size_mb: float = 10.0
    follow_symlinks: bool = False
    timeout_seconds: float = 300.0
    analyze_python_ast: bool = True
    extract_dependencies: bool = True
    progress: ScanProgress | None = None
    def __post_init__(self):
        root = self.project_root
        if not isinstance(root, str):
            try:
                root = os.fsdecode(root)
            except TypeError:
                raise ValueError(
                    f"ScanConfig: project_root 须为路径字符串，"
                    f"实际为 {self.project_root!r}") from None
        if not root:
            raise ValueError("ScanConfig: project_root 不得为空串（拒绝回落 cwd）")
        self.project_root = os.path.abspath(root)
        _validate_numeric_limits(self)
        _validate_boolean_flags(self)
        _normalize_pattern_containers(self)
_COMPLEXITY_BANDS: tuple[tuple[str, float], ...] = (
    ("low(0-5)", 6), ("medium(6-10)", 11), ("high(11-20)", 21),
)
_COMPLEXITY_OVERFLOW_BAND = "very_high(21+)"
_COMPLEXITY_UNMEASURED_BAND = "unmeasured"
_COMPLEXITY_BAND_NAMES = (
    *(name for name, _upper in _COMPLEXITY_BANDS),
    _COMPLEXITY_OVERFLOW_BAND,
    _COMPLEXITY_UNMEASURED_BAND,
)
_COMPLEXITY_BAND_UPPER_BOUNDS = tuple(upper for _name, upper in _COMPLEXITY_BANDS)
def _has_complexity_metrics(meta: FileMeta) -> bool:
    return meta.is_python and meta.extra.get("ast_status", "ok") == "ok"
def _complexity_distribution(files: dict[str, FileMeta]) -> dict[str, int]:
    dist = dict.fromkeys(_COMPLEXITY_BAND_NAMES, 0)
    for meta in files.values():
        if not meta.is_python:
            continue
        if not _has_complexity_metrics(meta):
            dist[_COMPLEXITY_UNMEASURED_BAND] += 1
            continue
        index = bisect_right(_COMPLEXITY_BAND_UPPER_BOUNDS, meta.complexity)
        dist[_COMPLEXITY_BAND_NAMES[index]] += 1
    return dist
_TOTAL_FIELD_MAP: tuple[tuple[str, str], ...] = (
    ("total_lines", "lines"),
    ("total_code_lines", "code_lines"),
    ("total_comment_lines", "comment_lines"),
    ("total_blank_lines", "blank_lines"),
    ("total_size_bytes", "size_bytes"),
    ("total_functions", "functions"),
    ("total_classes", "classes"),
)
def _aggregate_totals(files: dict[str, FileMeta], summary: ScanSummary) -> None:
    summary.total_files = len(files)
    for summary_field, meta_field in _TOTAL_FIELD_MAP:
        setattr(summary, summary_field, sum(
            getattr(meta, meta_field) for meta in files.values()))
def _count_by_category(files: dict[str, FileMeta], summary: ScanSummary) -> None:
    s = summary
    s.by_language = {}
    s.by_type = {}
    s.by_extension = {}
    for meta in files.values():
        s.by_language[meta.language] = s.by_language.get(meta.language, 0) + 1
        s.by_type[meta.file_type] = s.by_type.get(meta.file_type, 0) + 1
        s.by_extension[meta.extension] = s.by_extension.get(meta.extension, 0) + 1
def _aggregate_rankings(files: dict[str, FileMeta], summary: ScanSummary) -> None:
    s = summary
    sorted_by_lines = sorted(
        files.values(), key=lambda x: (-x.lines, x.rel_path))
    s.largest_files = [(f.rel_path, f.lines) for f in sorted_by_lines]
    sorted_by_complexity = sorted(
        [f for f in files.values() if f.complexity > 0],
        key=lambda x: (-x.complexity, x.rel_path),
    )
    s.most_complex_files = [(f.rel_path, f.complexity) for f in sorted_by_complexity]
_SIZE_BUCKETS: tuple[tuple[str, int, int | None], ...] = (
    ("tiny(<100)", 0, 100),
    ("small(100-499)", 100, 500),
    ("medium(500-1999)", 500, 2000),
    ("large(2000-4999)", 2000, 5000),
    ("huge(5000+)", 5000, None),
)
_SIZE_BUCKET_NAMES = tuple(name for name, _low, _high in _SIZE_BUCKETS)
_SIZE_BUCKET_UPPER_BOUNDS = tuple(
    high for _name, _low, high in _SIZE_BUCKETS if high is not None)
def _size_distribution(files: dict[str, FileMeta]) -> dict[str, int]:
    dist = dict.fromkeys(_SIZE_BUCKET_NAMES, 0)
    for meta in files.values():
        index = bisect_right(_SIZE_BUCKET_UPPER_BOUNDS, meta.lines)
        dist[_SIZE_BUCKET_NAMES[index]] += 1
    return dist
def _aggregate_summary(files: dict[str, FileMeta], summary: ScanSummary) -> None:
    _aggregate_totals(files, summary)
    _count_by_category(files, summary)
    _aggregate_rankings(files, summary)
    summary.complexity_distribution = _complexity_distribution(files)
    summary.size_distribution = _size_distribution(files)
_FUNC_NODE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef)
_DEFINITION_NODE_TYPES = (*_FUNC_NODE_TYPES, ast.ClassDef)
_COMPLEXITY_SCOPE_BOUNDARIES = (*_DEFINITION_NODE_TYPES, ast.Lambda)
_LANGUAGE_MAP: dict[str, str] = LANGUAGE_BY_SUFFIX
_DOC_STEMS = {"readme", "changelog", "license", "contributing",
              "authors", "code_of_conduct", "security", "codeowners",
              "architecture", "design", "roadmap", "todo"}
_BUILD_FILES = {"setup.py", "setup.cfg", "pyproject.toml", "makefile",
                "dockerfile", "cmakelists.txt", "pipfile", "pipfile.lock",
                "poetry.lock", "requirements.txt", "environment.yml",
                "package.json", "package-lock.json", "yarn.lock",
                "cargo.toml", "go.mod", "go.sum", "gemfile", "gemfile.lock",
                "pom.xml", "build.gradle", "build.gradle.kts", "settings.gradle",
                "meson.build", "conanfile.txt", "conanfile.py", "vcpkg.json"}
def _as_safe_path(value: object) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, os.PathLike):
        try:
            return os.fsdecode(value)
        except (TypeError, ValueError, OSError):
            logger.debug("PathLike 无法 fsdecode，按空路径处理: %r", value, exc_info=True)
            return ""
    return ""
def _as_safe_text(value: object) -> str:
    return value if isinstance(value, str) else ""
def _normalize_newlines(text: str) -> str:
    return text.replace("\r\n", "\n").replace("\r", "\n")
def detect_language(filepath: str) -> str:
    ext = os.path.splitext(_as_safe_path(filepath))[1]
    return _LANGUAGE_MAP.get(ext.lower(), "other")
def _cjk_text_count(text: str) -> int:
    return sum(
        1 for ch in text
        if 0x3000 <= ord(ch) <= 0x303F
        or 0x3040 <= ord(ch) <= 0x30FF
        or 0x4E00 <= ord(ch) <= 0x9FFF
        or 0xFF00 <= ord(ch) <= 0xFFEF
    )
def _kana_text_count(text: str) -> int:
    return sum(1 for ch in text if 0x3040 <= ord(ch) <= 0x30FF)
ENCODING_SNIFF_BYTES = 4096
_BOM_SIGNATURES: tuple[tuple[bytes, str], ...] = (
    (b"\xef\xbb\xbf", "utf-8-sig"),
    (b"\x00\x00\xfe\xff", "utf-32-be"),
    (b"\xff\xfe\x00\x00", "utf-32-le"),
    (b"\xfe\xff", "utf-16-be"),
    (b"\xff\xfe", "utf-16-le"),
)
BOM_DERIVED_ENCODINGS = frozenset(name for _, name in _BOM_SIGNATURES)
def _normalize_default_encoding(default: object) -> str:
    if not isinstance(default, str) or not default.strip():
        return _DEFAULT_ENCODING
    candidate = default.strip()
    try:
        codecs.lookup(candidate)
    except (LookupError, ValueError, TypeError):
        logger.warning(
            "[Encoding] 非法默认编码 %r，回退 %s", candidate, _DEFAULT_ENCODING)
        return _DEFAULT_ENCODING
    return candidate
def detect_encoding_bytes(raw: bytes, default: str = _DEFAULT_ENCODING, read_limit: int = ENCODING_SNIFF_BYTES) -> str:
    default = _normalize_default_encoding(default)
    bom = _bom_encoding(raw)
    if bom is not None:
        return bom
    utf8 = _utf8_or_none(raw, read_limit)
    if utf8 is not None:
        return utf8
    return _arbitrate_multibyte(raw, default, read_limit)
def _arbitrate_multibyte(raw: bytes, default: str,
                         read_limit: int) -> str:
    cjk_backed, best_enc, best_cjk = _cjk_probe(raw, read_limit)
    kana_enc = _kana_backed_encoding(cjk_backed)
    if kana_enc is not None:
        return kana_enc
    if cjk_backed:
        _enc, _kana, _cjk = cjk_backed[0]
        logger.info("[Encoding] 判定 %s（CJK 文字背书 %d 个，无假名，固定顺序首选）",
                    _enc, _cjk)
        return _enc
    return _single_byte_fallback(raw, default, best_enc, best_cjk)
def _kana_backed_encoding(cjk_backed: list[tuple[str, int, int]]) -> str | None:
    for _enc, _kana, _cjk in cjk_backed:
        if _kana >= 2:
            logger.info("[Encoding] 判定 %s（假名背书：%d 个全角假名 / %d 个 CJK 文字）",
                        _enc, _kana, _cjk)
            return _enc
    return None
def _single_byte_fallback(raw: bytes, default: str,
                          best_enc: str, best_cjk: int) -> str:
    try:
        raw.decode("cp1252")
        logger.info("[Encoding] 判定 cp1252（单字节兜底命中：无 CJK 文字背书）")
        return "cp1252"
    except UnicodeDecodeError:
        logger.debug("[Encoding] cp1252 解码失败，回退默认编码 %s", default)
    if best_enc:
        logger.info("[Encoding] 判定双字节弱候选 %s 兜底（CJK 文字 %d 个不足背书阈值且 cp1252 不可解）",
                    best_enc, best_cjk)
        return best_enc
    logger.info("[Encoding] 全候选不可解，终局回退默认编码 %s", default)
    return default
def _bom_encoding(raw: bytes) -> str | None:
    for signature, name in _BOM_SIGNATURES:
        if raw.startswith(signature):
            return name
    return None
def _is_incomplete_sniff_tail(
    raw: bytes, read_limit: int, error_start: int, max_tail_bytes: int,
) -> bool:
    return (len(raw) == read_limit
            and 0 < len(raw) - error_start <= max_tail_bytes)
def _utf8_truncated(raw: bytes, read_limit: int,
                    err: UnicodeDecodeError) -> str | None:
    if err.reason != "unexpected end of data":
        return None
    if _is_incomplete_sniff_tail(raw, read_limit, err.start, 3):
        try:
            raw[:err.start].decode("utf-8")
            logger.info("[Encoding] 判定 utf-8（截断边界：剥离尾部 %d 字节不完整序列后命中）",
                        len(raw) - err.start)
            return "utf-8"
        except UnicodeDecodeError:
            logger.debug("[Encoding] 截断尾部剥离后仍非 UTF-8，回退多字节探测")
    return None
def _utf8_or_none(raw: bytes, read_limit: int) -> str | None:
    try:
        raw.decode("utf-8")
        return "utf-8"
    except UnicodeDecodeError as e:
        logger.debug("[Encoding] UTF-8 解码失败(offset=%d, reason=%s)，回退多字节探测",
                     e.start, e.reason)
        return _utf8_truncated(raw, read_limit, e)
def _decode_without_tail(raw: bytes, enc: str, cut: int) -> str | None:
    try:
        return raw[:cut].decode(enc)
    except UnicodeDecodeError:
        logger.debug("[Encoding] %s 尾部剥离后仍不可解", enc)
        return None
def _decode_peeled(raw: bytes, enc: str, read_limit: int) -> str | None:
    try:
        return raw.decode(enc)
    except UnicodeDecodeError as e:
        logger.debug("[Encoding] %s 完整解码失败(pos=%d): %s", enc, e.start, e)
        if _is_incomplete_sniff_tail(raw, read_limit, e.start, 1):
            return _decode_without_tail(raw, enc, e.start)
        return None
def _cjk_probe(raw: bytes, read_limit: int,
               ) -> tuple[list[tuple[str, int, int]], str, int]:
    best_enc, best_cjk = "", 0
    cjk_backed: list[tuple[str, int, int]] = []
    for enc in ("gbk", "gb2312", "shift_jis"):
        decoded = _decode_peeled(raw, enc, read_limit)
        if decoded is None:
            logger.debug("[Encoding] %s 解码失败，尝试下一候选", enc)
            continue
        cjk = _cjk_text_count(decoded)
        if cjk >= 2:
            cjk_backed.append((enc, _kana_text_count(decoded), cjk))
        if cjk > best_cjk:
            best_enc, best_cjk = enc, cjk
    return cjk_backed, best_enc, best_cjk
def detect_encoding(filepath: str, default: str = _DEFAULT_ENCODING) -> str:
    default = _normalize_default_encoding(default)
    safe_path = _as_safe_path(filepath)
    try:
        with open(safe_path, "rb") as f:
            raw = f.read(ENCODING_SNIFF_BYTES)
    except (OSError, ValueError) as e:
        logger.warning("[Encoding] 读取失败，回退默认编码 %s: %s (%s)", default, filepath, e)
        return default
    return detect_encoding_bytes(raw, default)
def classify_file_type(rel_path: str) -> str:
    raw_path = _as_safe_path(rel_path).replace("\\", "/")
    rp = raw_path.lower()
    basename = os.path.basename(rp)
    raw_basename = os.path.basename(raw_path)
    ext = os.path.splitext(rp)[1].lower()
    if _is_test_type(rp, basename, raw_basename):
        return "test"
    if basename in _BUILD_FILES:
        return "build"
    if _is_doc_type(basename, ext):
        return "doc"
    if _is_ci_build_type(rp):
        return "build"
    if _is_config_type(basename, ext):
        return "config"
    if _is_data_type(ext):
        return "data"
    return "source"
_TEST_DIR_SEGMENTS = frozenset({
    "test", "tests", "__tests__", "spec", "specs",
})
_TEST_BASENAME_RE = re.compile(
    r"(?:(?:test|tests|conftest)\.py[wxi]?|test_.*\.py[wxi]?"
    r"|.*_test\.py[wxi]?"
    r"|.*\.(?:test|spec)\.[cm]?[jt]sx?"
    r"|.*_test\.(?:go|rb|exs)"
    r"|.*_spec\.rb)$"
)
_CAMEL_TEST_SUFFIXES = frozenset({
    ".java", ".kt", ".cs", ".swift", ".scala", ".php",
})
_CAMEL_TEST_PREFIX_RE = re.compile(r"^Tests?(?:$|(?=[A-Z0-9_]))")
def _is_camel_test_basename(raw_basename: str) -> bool:
    stem, ext = os.path.splitext(raw_basename)
    if ext.lower() not in _CAMEL_TEST_SUFFIXES:
        return False
    if _CAMEL_TEST_PREFIX_RE.match(stem):
        return True
    if stem.endswith(("Test", "Tests", "TestCase", "Spec", "Suite")):
        return True
    return (stem.endswith("IT") and len(stem) >= 3
            and stem[-3].islower())
def _is_test_type(rp: str, basename: str, raw_basename: str) -> bool:
    if any(seg in _TEST_DIR_SEGMENTS for seg in rp.split("/")[:-1]):
        return True
    if _TEST_BASENAME_RE.match(basename):
        return True
    return _is_camel_test_basename(raw_basename)
def _is_ci_build_type(rp: str) -> bool:
    return any(seg in (".github", ".circleci", ".gitlab")
               for seg in rp.split("/")[:-1])
def _is_doc_type(basename: str, ext: str) -> bool:
    if ext in (".md", ".rst", ".txt"):
        return True
    return not ext and any(basename.startswith(dn) for dn in _DOC_STEMS)
def _is_config_type(basename: str, ext: str) -> bool:
    if ext in (".yml", ".yaml", ".json", ".toml", ".ini", ".cfg", ".conf"):
        return True
    return basename == ".env"
def _is_data_type(ext: str) -> bool:
    return ext in (".csv", ".tsv", ".jsonl", ".parquet", ".feather",
                   ".db", ".sqlite", ".sqlite3")
def extract_encoding_declaration(source: str) -> str:
    lines = _normalize_newlines(_as_safe_text(source)).split("\n", 2)[:2]
    for index, line in enumerate(lines):
        if (index == 1 and not re.fullmatch(
                r"[ \t\f]*(?:#.*)?", lines[0])):
            break
        match = re.search(
            r"^[ \t\f]*#.*?coding[:=][ \t]*([-\w.]+)",
            line, re.IGNORECASE)
        if match:
            return match.group(1)
    return ""
def extract_shebang(first_line: str) -> str:
    first_line = _normalize_newlines(_as_safe_text(first_line)).split("\n", 1)[0]
    if first_line.startswith("#!"):
        return first_line[2:].strip()
    return ""
_MATCH_STMT_TYPES = ((ast.Match,) if hasattr(ast, "Match") else ())
class _StructuralStats(NamedTuple):
    functions: int
    classes: int
    imports: int
    function_nodes: list[ast.AST]
    definition_nodes: list[ast.AST]
class ASTAnalyzer:
    @staticmethod
    def analyze(source: str, extract_deps: bool = True,
                project_root: str = "") -> dict[str, Any]:
        if not isinstance(source, str):
            if isinstance(source, (bytes, bytearray)):
                raw_source = bytes(source)
                try:
                    byte_encoding, _ = tokenize.detect_encoding(
                        io.BytesIO(raw_source).readline)
                except (SyntaxError, UnicodeDecodeError) as exc:
                    logger.warning("[AST] 字节源码编码声明无效，回退 UTF-8: %s", exc)
                    byte_encoding = _DEFAULT_ENCODING
                try:
                    source = raw_source.decode(byte_encoding, errors="replace")
                except LookupError as exc:
                    logger.warning("[AST] 未知字节源码编码 %s，回退 UTF-8: %s",
                                   byte_encoding, exc)
                    source = raw_source.decode(_DEFAULT_ENCODING, errors="replace")
            else:
                logger.warning(MSG_SYNTAX_ERROR_SKIP)
                return ASTAnalyzer._empty_result(extract_deps, "invalid_input")
        try:
            tree = parse_cached(source)
        except (SyntaxError, ValueError, RecursionError, MemoryError):
            logger.warning(MSG_SYNTAX_ERROR_SKIP)
            return ASTAnalyzer._empty_result(extract_deps, "parse_failed")
        stats = ASTAnalyzer._scan_structure(tree)
        avg_complexity, max_complexity = ASTAnalyzer._complexity_stats(
            stats.function_nodes)
        result = {
            "analysis_status": "ok",
            "functions": stats.functions,
            "classes": stats.classes,
            "imports": stats.imports,
            "complexity": avg_complexity,
            "max_complexity": max_complexity,
            "max_function_lines": ASTAnalyzer._max_function_lines(
                tree, source, stats.function_nodes),
            "docstring_coverage": ASTAnalyzer._docstring_coverage(
                tree, stats.definition_nodes),
            "type_annotations": ASTAnalyzer._type_annotation_coverage(
                tree, stats.function_nodes),
        }
        if extract_deps:
            imported, local, local_absolute = ASTAnalyzer._extract_imports(
                tree, project_root)
            result["imported_modules"] = imported
            result["local_imports"] = local
            result["local_absolute_imports"] = local_absolute
        return result
    @staticmethod
    def _empty_result(extract_deps: bool, analysis_status: str) -> dict[str, Any]:
        result: dict[str, Any] = {
            "analysis_status": analysis_status,
            "functions": 0, "classes": 0, "imports": 0,
            "complexity": 0.0, "max_complexity": 0,
            "max_function_lines": 0, "docstring_coverage": 0.0,
            "type_annotations": 0.0,
        }
        if extract_deps:
            result["imported_modules"] = []
            result["local_imports"] = []
            result["local_absolute_imports"] = []
        return result
    @staticmethod
    def _scan_structure(tree: ast.AST) -> _StructuralStats:
        functions = classes = imports = 0
        function_nodes: list[ast.AST] = []
        definition_nodes: list[ast.AST] = []
        for node in walk_nodes(tree):
            if isinstance(node, _FUNC_NODE_TYPES):
                functions += 1
                function_nodes.append(node)
                definition_nodes.append(node)
            elif isinstance(node, ast.ClassDef):
                classes += 1
                definition_nodes.append(node)
            elif isinstance(node, (ast.Import, ast.ImportFrom)):
                imports += 1
        return _StructuralStats(
            functions, classes, imports, function_nodes, definition_nodes)
    @staticmethod
    def _complexity_stats(function_nodes: list[ast.AST]) -> tuple[float, int]:
        if not function_nodes:
            return 0.0, 0
        complexities = [
            ASTAnalyzer._cyclomatic_complexity(node)
            for node in function_nodes
        ]
        return (round(sum(complexities) / len(complexities), 2),
                max(complexities))
    @staticmethod
    def _iter_own_scope_nodes(func_node: ast.AST) -> Iterator[ast.AST]:
        stack = list(reversed(getattr(func_node, "body", [])))
        while stack:
            node = stack.pop()
            yield node
            if isinstance(node, _COMPLEXITY_SCOPE_BOUNDARIES):
                continue
            stack.extend(reversed(list(ast.iter_child_nodes(node))))
    @staticmethod
    def _cyclomatic_complexity(func_node: ast.AST) -> int:
        complexity = 1
        for node in ASTAnalyzer._iter_own_scope_nodes(func_node):
            complexity += ASTAnalyzer._cc_node_delta(node)
        return complexity
    @staticmethod
    def _cc_node_delta(node: ast.AST) -> int:
        if isinstance(node, ast.BoolOp):
            return len(node.values) - 1
        if isinstance(node, ast.comprehension):
            return 1 + len(node.ifs)
        if isinstance(node, (ast.If, ast.While, ast.For, ast.AsyncFor,
                             ast.ExceptHandler, ast.IfExp, ast.Assert)):
            return 1
        if isinstance(node, _MATCH_STMT_TYPES):
            return len(node.cases)
        return 0
    @staticmethod
    def _iter_function_nodes(tree: ast.AST) -> list[ast.AST]:
        return [node for node in walk_nodes(tree) if isinstance(node, _FUNC_NODE_TYPES)]
    @staticmethod
    def _max_function_lines(
        tree: ast.AST, source: str, function_nodes: list[ast.AST] | None = None,
    ) -> int:
        nodes = (ASTAnalyzer._iter_function_nodes(tree)
                 if function_nodes is None else function_nodes)
        max_lines = 0
        source_lines = _split_source_lines(source)
        for node in nodes:
            start_line = min(
                [node.lineno]
                + [decorator.lineno for decorator in node.decorator_list]
            )
            if hasattr(node, "end_lineno") and node.end_lineno:
                func_lines = node.end_lineno - start_line + 1
            else:
                func_lines = len(source_lines) - start_line + 1
            max_lines = max(max_lines, func_lines)
        return max_lines
    @staticmethod
    def _docstring_coverage(
        tree: ast.AST, definition_nodes: list[ast.AST] | None = None,
    ) -> float:
        funcs = definition_nodes
        if funcs is None:
            funcs = [node for node in walk_nodes(tree)
                     if isinstance(node, _DEFINITION_NODE_TYPES)]
        if not funcs:
            return 1.0
        with_doc = sum(
            1 for f in funcs if ast.get_docstring(f, clean=False) is not None)
        return round(with_doc / len(funcs), 2)
    @staticmethod
    def _iter_func_params(func: ast.AST) -> list[ast.arg]:
        params = (list(getattr(func.args, "posonlyargs", []) or [])
                  + list(func.args.args)
                  + list(func.args.kwonlyargs))
        if func.args.vararg:
            params.append(func.args.vararg)
        if func.args.kwarg:
            params.append(func.args.kwarg)
        return params
    @staticmethod
    def _param_annotation_counts(
        func: ast.AST, implicit_receiver: ast.arg | None = None,
    ) -> tuple[int, int]:
        total = 0
        annotated = 0
        for arg in ASTAnalyzer._iter_func_params(func):
            if arg is implicit_receiver:
                continue
            total += 1
            if arg.annotation:
                annotated += 1
        return total, annotated
    @staticmethod
    def _iter_class_methods(class_node: ast.ClassDef) -> Iterator[ast.AST]:
        stack = list(reversed(class_node.body))
        while stack:
            node = stack.pop()
            if isinstance(node, _FUNC_NODE_TYPES):
                yield node
                continue
            if isinstance(node, (ast.ClassDef, ast.Lambda)):
                continue
            stack.extend(reversed(list(ast.iter_child_nodes(node))))
    @staticmethod
    def _is_static_method(func_node: ast.AST) -> bool:
        for decorator in getattr(func_node, "decorator_list", []):
            target = decorator.func if isinstance(decorator, ast.Call) else decorator
            if ((isinstance(target, ast.Name) and target.id == "staticmethod")
                    or (isinstance(target, ast.Attribute)
                        and target.attr == "staticmethod")):
                return True
        return False
    @staticmethod
    def _implicit_method_receivers(tree: ast.AST) -> dict[int, ast.arg]:
        receivers: dict[int, ast.arg] = {}
        for node in walk_nodes(tree):
            if not isinstance(node, ast.ClassDef):
                continue
            for func in ASTAnalyzer._iter_class_methods(node):
                if ASTAnalyzer._is_static_method(func):
                    continue
                positional = (list(getattr(func.args, "posonlyargs", []) or [])
                              + list(func.args.args))
                if positional:
                    receivers[id(func)] = positional[0]
        return receivers
    @staticmethod
    def _type_annotation_coverage(
        tree: ast.AST, function_nodes: list[ast.AST] | None = None,
    ) -> float:
        funcs = (ASTAnalyzer._iter_function_nodes(tree)
                 if function_nodes is None else function_nodes)
        if not funcs:
            return 1.0
        receivers = ASTAnalyzer._implicit_method_receivers(tree)
        total_params = 0
        annotated_params = 0
        annotated_returns = 0
        for func in funcs:
            params, annotated = ASTAnalyzer._param_annotation_counts(
                func, receivers.get(id(func)))
            total_params += params
            annotated_params += annotated
            if func.returns:
                annotated_returns += 1
        param_cov = annotated_params / total_params if total_params else 1.0
        return_cov = annotated_returns / max(len(funcs), 1)
        return round((param_cov + return_cov) / 2, 2)
    @staticmethod
    def _imported_top_names(node: ast.AST) -> list[str]:
        if isinstance(node, ast.Import):
            return [alias.name.split(".")[0] for alias in node.names]
        if isinstance(node, ast.ImportFrom) and node.module and not node.level:
            return [node.module.split(".")[0]]
        return []
    @staticmethod
    def _extract_imports(
        tree: ast.AST, project_root: str,
    ) -> tuple[list[str], list[str], list[str]]:
        roots = _project_module_roots(project_root)
        modules: set[str] = set()
        local: set[str] = set()
        local_absolute: set[str] = set()
        for node in walk_nodes(tree):
            modules.update(ASTAnalyzer._imported_top_names(node))
            local.update(ASTAnalyzer._local_import_names(node, roots))
            local_absolute.update(
                ASTAnalyzer._local_absolute_import_names(node, roots))
        return sorted(modules), sorted(local), sorted(local_absolute)
    @staticmethod
    def _local_absolute_import_names(
        node: ast.AST, roots: tuple[str, ...] = (),
    ) -> list[str]:
        if isinstance(node, ast.Import):
            return [alias.name for alias in node.names
                    if _module_in_project(alias.name, roots)]
        if (isinstance(node, ast.ImportFrom) and not node.level
                and node.module and _module_in_project(node.module, roots)):
            return [node.module]
        return []
    @staticmethod
    def _local_import_names(
        node: ast.AST, roots: tuple[str, ...] = (),
    ) -> list[str]:
        if isinstance(node, ast.Import):
            return ASTAnalyzer._local_absolute_import_names(node, roots)
        if not isinstance(node, ast.ImportFrom):
            return []
        if node.level > 0:
            return ([node.module] if node.module
                    else [alias.name for alias in node.names
                          if alias.name != "*"])
        return ASTAnalyzer._local_absolute_import_names(node, roots)
def _project_module_roots(project_root: str) -> tuple[str, ...]:
    if not isinstance(project_root, str) or not project_root:
        return ()
    try:
        root = project_root
        if os.path.isfile(root):
            root = os.path.dirname(root)
        if not root:
            return ()
        roots = [os.path.abspath(root)]
        src = os.path.join(roots[0], "src")
        if os.path.isdir(src):
            roots.append(src)
    except (OSError, ValueError):  # jwsgj:silent-ok
        return ()
    return tuple(roots)
def _module_in_project(dotted: str, roots: tuple[str, ...]) -> bool:
    top = dotted.split(".", maxsplit=1)[0]
    if not top or not roots:
        return False
    for root in roots:
        module_path = os.path.join(root, top)
        try:
            root_is_named_package = (
                top == os.path.basename(os.path.normpath(root))
                and os.path.isfile(os.path.join(root, "__init__.py")))
            if (root_is_named_package or os.path.isfile(module_path + ".py")
                    or os.path.isdir(module_path)):
                return True
        except (OSError, ValueError):
            continue
    return False
def _split_source_lines(source: str) -> list[str]:
    if not source:
        return []
    lines = _normalize_newlines(source).split("\n")
    if lines[-1] == "":
        lines.pop()
    return lines
_TRIPLE_QUOTE_START_RE = re.compile(
    r"""^(?:[rR][bBfF]?|[bBfF][rR]?|[uU])?(?:'{3}|"{3})""")
class LineCounter:
    @staticmethod
    def _skip_short_string(line: str, start: int, quote: str) -> int:
        i = start + 1
        n = len(line)
        while i < n:
            if line[i] == "\\":
                i += 2
                continue
            if line[i] == quote:
                return i + 1
            i += 1
        return n
    @staticmethod
    def _advance_multiline_quote(
        line: str, start: int, active_quote: str,
    ) -> tuple[int, bool]:
        if line[start] == "\\":
            return start + 2, False
        if line.startswith(active_quote, start):
            return start + len(active_quote), True
        return start + 1, False
    @staticmethod
    def _advance_quote_state(line: str, active_quote: str) -> str:
        i, n = 0, len(line)
        while i < n:
            if active_quote:
                i, closed = LineCounter._advance_multiline_quote(
                    line, i, active_quote)
                if closed:
                    active_quote = ""
                continue
            ch = line[i]
            if ch == "#":
                break
            if ch in ("'", '"'):
                if line.startswith(ch * 3, i):
                    active_quote = ch * 3
                    i += 3
                    continue
                i = LineCounter._skip_short_string(line, i, ch)
                continue
            i += 1
        return active_quote
    @staticmethod
    def _docstring_spans(source: str) -> set[tuple[int, int, int, int]] | None:
        try:
            tree = parse_cached(source)
        except (SyntaxError, ValueError, RecursionError, MemoryError):
            return None
        spans: set[tuple[int, int, int, int]] = set()
        for node in walk_nodes(tree):
            if not isinstance(node, (ast.Module, *_DEFINITION_NODE_TYPES)):
                continue
            body = getattr(node, "body", [])
            if not body or not isinstance(body[0], ast.Expr):
                continue
            value = body[0].value
            if (isinstance(value, ast.Constant)
                    and isinstance(value.value, str)
                    and value.end_lineno is not None
                    and value.end_col_offset is not None):
                spans.add((value.lineno, value.col_offset,
                           value.end_lineno, value.end_col_offset))
        return spans
    @staticmethod
    def _is_docstring_token(
        token: tokenize.TokenInfo,
        spans: set[tuple[int, int, int, int]],
    ) -> bool:
        return any(
            (start_line, start_col) <= token.start
            and token.end <= (end_line, end_col)
            for start_line, start_col, end_line, end_col in spans
        )
    @staticmethod
    def _count_lexical(source: str) -> tuple[int, int, int, int]:
        total = code = comment = blank = 0
        active_quote = ""
        active_quote_is_comment = False
        for line in _split_source_lines(source):
            total += 1
            stripped = line.strip()
            if active_quote:
                if active_quote_is_comment:
                    comment += 1
                else:
                    code += 1
                active_quote = LineCounter._advance_quote_state(stripped, active_quote)
                if not active_quote:
                    active_quote_is_comment = False
                continue
            if not stripped:
                blank += 1
                continue
            if _TRIPLE_QUOTE_START_RE.match(stripped):
                comment += 1
                active_quote = LineCounter._advance_quote_state(stripped, "")
                active_quote_is_comment = bool(active_quote)
                continue
            if stripped.startswith(("#", "//")):
                comment += 1
                continue
            code += 1
            active_quote = LineCounter._advance_quote_state(stripped, "")
            active_quote_is_comment = False
        return total, code, comment, blank
    @staticmethod
    def count(source: str) -> tuple[int, int, int, int]:
        source = _normalize_newlines(_as_safe_text(source))
        lines = _split_source_lines(source)
        if not lines:
            return 0, 0, 0, 0
        spans = LineCounter._docstring_spans(source)
        if spans is None:
            return LineCounter._count_lexical(source)
        code_lines: set[int] = set()
        comment_lines: set[int] = set()
        ignored = {
            tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NL,
            tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
        }
        try:
            tokens = tokenize.generate_tokens(io.StringIO(source).readline)
            for token in tokens:
                if token.type in ignored:
                    continue
                start_line = token.start[0]
                end_line = max(token.end[0], start_line)
                token_lines = range(start_line, end_line + 1)
                if token.type == tokenize.COMMENT:
                    prefix = lines[start_line - 1][:token.start[1]]
                    if not prefix.strip():
                        comment_lines.add(start_line)
                    continue
                if (token.type == tokenize.STRING
                        and LineCounter._is_docstring_token(token, spans)):
                    comment_lines.update(token_lines)
                    continue
                code_lines.update(token_lines)
        except (tokenize.TokenError, IndentationError, SyntaxError):
            return LineCounter._count_lexical(source)
        comment_lines.difference_update(code_lines)
        classified_lines = code_lines | comment_lines
        blank = len(lines) - len(classified_lines)
        return len(lines), len(code_lines), len(comment_lines), blank
def _redecode_after_sniff_window(
    raw_bytes: bytes, source: str, encoding: str, abs_path: str,
) -> tuple[str, str]:
    if encoding != "utf-8" or "\ufffd" not in source:
        return source, encoding
    full = detect_encoding_bytes(raw_bytes)
    if full == encoding:
        return source, encoding
    try:
        repaired = raw_bytes.decode(full)
    except (LookupError, UnicodeDecodeError) as e:
        logger.warning(
            "[FileScanner] 全量重判编码 %s 解码失败，保留探测结果 %s: %s (%s)",
            full, encoding, abs_path, e)
        return source, encoding
    logger.info(
        "[FileScanner] 探测窗口外出现非 UTF-8 字节，按全量字节重判编码 %s: %s",
        full, abs_path)
    return repaired, full
def _decode_file_bytes(
    raw_bytes: bytes | None,
    language: str,
    abs_path: str,
) -> tuple[str, str, str, str, str]:
    encoding = (detect_encoding_bytes(raw_bytes[:ENCODING_SNIFF_BYTES])
                if raw_bytes is not None else _DEFAULT_ENCODING)
    declared_encoding = ""
    decode_error = ""
    if raw_bytes is not None:
        sha = hashlib.sha256(raw_bytes).hexdigest()
        source, encoding = _decode_with_fallback(raw_bytes, encoding)
        source, encoding = _redecode_after_sniff_window(
            raw_bytes, source, encoding, abs_path)
        source, encoding, declared_encoding = _pep263_redeclared(
            raw_bytes, source, encoding, language, abs_path)
        decode_error = _python_decode_error(
            raw_bytes, source, encoding, language, abs_path)
        source = source.removeprefix("\ufeff")
    else:
        sha = ""
        source = ""
    return sha, source, encoding, declared_encoding, decode_error
def _decode_with_fallback(raw_bytes: bytes, encoding: str) -> tuple[str, str]:
    try:
        return raw_bytes.decode(encoding, errors="replace"), encoding
    except (LookupError, UnicodeDecodeError) as e:
        logger.warning(
            "[FileScanner] 文件解码失败，回退 %s（原编码 %s）: %s",
            _DEFAULT_ENCODING, encoding, e)
        return (raw_bytes.decode(_DEFAULT_ENCODING, errors="replace"),
                _DEFAULT_ENCODING)
def _pep263_redeclared(raw_bytes: bytes, source: str, encoding: str,
                       language: str, abs_path: str) -> tuple[str, str, str]:
    declared_encoding = _verified_encoding_declaration(
        source, language, encoding, abs_path)
    if declared_encoding and declared_encoding != encoding:
        try:
            source = raw_bytes.decode(declared_encoding)
            return source, declared_encoding, declared_encoding
        except (LookupError, UnicodeDecodeError) as e:
            logger.warning(
                "[FileScanner] 声明编码 %s 解码失败，回退探测编码 %s: %s (%s)",
                           declared_encoding, encoding, abs_path, e)
            declared_encoding = ""
    return source, encoding, declared_encoding
def _verified_encoding_declaration(source: str, language: str,
                                    encoding: str, abs_path: str) -> str:
    if language != "python" or encoding in BOM_DERIVED_ENCODINGS:
        return ""
    declared_encoding = extract_encoding_declaration(source)
    if not declared_encoding:
        return ""
    try:
        return codecs.lookup(declared_encoding).name
    except (LookupError, ValueError, TypeError):
        logger.warning("[FileScanner] 非法编码声明，忽略: %s (%s)",
                       abs_path, declared_encoding)
        return ""
def _python_decode_error(raw_bytes: bytes, source: str, encoding: str,
                         language: str, abs_path: str) -> str:
    if language != "python":
        return ""
    try:
        contract_encoding, _consumed_lines = tokenize.detect_encoding(
            io.BytesIO(raw_bytes).readline)
    except SyntaxError as exc:
        logger.warning(
            "[FileScanner] Python 编码声明契约无效: %s (%s)", abs_path, exc)
        return str(exc)
    has_declared_contract = bool(
        _bom_encoding(raw_bytes) or extract_encoding_declaration(source))
    checked_encoding = (contract_encoding if has_declared_contract
                        else encoding)
    try:
        raw_bytes.decode(checked_encoding)
    except (LookupError, UnicodeDecodeError) as exc:
        logger.warning(
            "[FileScanner] Python 源码按 %s 严格解码失败: %s (%s)",
            checked_encoding, abs_path, exc)
        return str(exc)
    return ""
_READ_LIMIT_MAX = sys.maxsize - 1
def _read_limit_bytes(size_mb: float) -> int:
    limit = size_mb * 1024 * 1024
    if not math.isfinite(limit):
        return _READ_LIMIT_MAX
    return min(int(limit), _READ_LIMIT_MAX)
_READ_CHUNK_BYTES = 1024 * 1024
def _read_up_to(handle, max_read_bytes: int) -> bytes:
    if max_read_bytes >= _READ_LIMIT_MAX:
        return handle.read()
    chunks: list[bytes] = []
    remaining = max_read_bytes + 1
    while remaining > 0:
        chunk = handle.read(min(_READ_CHUNK_BYTES, remaining))
        if not chunk:
            break
        chunks.append(chunk)
        remaining -= len(chunk)
    return b"".join(chunks)
def _read_file_bounded(abs_path: str,
                       max_read_bytes: int) -> tuple[bytes | None, bool]:
    try:
        with open(abs_path, "rb") as f:
            raw_bytes = _read_up_to(f, max_read_bytes)
    except OSError:
        logger.warning("[FileScanner] 文件读取失败，跳过文件: %s",
                       abs_path, exc_info=True)
        return None, False
    if len(raw_bytes) > max_read_bytes:
        logger.info("[FileScanner] 读取超限（文件在扫描期间增长），跳过: %s",
                    abs_path)
        return raw_bytes, True
    return raw_bytes, False
def _apply_meta_extras(meta: FileMeta, source: str, language: str,
                       config: ScanConfig, declared_encoding: str,
                       decode_error: str) -> None:
    if declared_encoding:
        meta.extra["encoding_declared"] = declared_encoding
    if decode_error:
        meta.extra["decode_error"] = decode_error
    if language == "python":
        if not config.analyze_python_ast:
            meta.extra["ast_status"] = "disabled"
            return
        _apply_ast_metrics(meta, source, config, decode_error)
def _relpath_or_absolute(path: str, root: str) -> str:
    try:
        return os.path.relpath(path, root)
    except ValueError as exc:
        logger.warning(
            "[FileScanner] 无法计算相对路径，降级为绝对路径: %s (root=%s): %s",
            path, root, exc)
        return os.path.normpath(path)
def _create_file_meta(abs_path: str, config: ScanConfig, single_file: bool,
                      stat_result: os.stat_result) -> FileMeta:
    if single_file:
        rel_path = os.path.basename(abs_path)
    else:
        rel_path = _relpath_or_absolute(abs_path, config.project_root)
    name = os.path.basename(abs_path)
    stem, ext = os.path.splitext(name)
    language = detect_language(abs_path)
    file_type = classify_file_type(rel_path)
    return FileMeta(
        rel_path=rel_path,
        abs_path=abs_path,
        name=name,
        stem=stem,
        extension=ext,
        language=language,
        file_type=file_type,
        size_bytes=stat_result.st_size,
        lines=0,
        code_lines=0,
        comment_lines=0,
        blank_lines=0,
        mtime=stat_result.st_mtime,
        sha256="",
    )
def _apply_source_metrics(meta: FileMeta, raw_bytes: bytes | None,
                          config: ScanConfig) -> None:
    (sha, source, encoding, declared_encoding,
     decode_error) = _decode_file_bytes(
        raw_bytes, meta.language, meta.abs_path)
    source = _normalize_newlines(source)
    total, code, comment, blank = _count_source_lines(source, meta.language)
    meta.sha256 = sha
    meta.encoding = encoding
    meta.lines = total
    meta.code_lines = code
    meta.comment_lines = comment
    meta.blank_lines = blank
    meta.shebang = extract_shebang(source.split("\n", 1)[0])
    _apply_meta_extras(
        meta, source, meta.language, config, declared_encoding, decode_error)
class _ScanSkip(NamedTuple):
    reason: str
    unexpected: bool
def _scan_file_meta(abs_path: str, config: ScanConfig,
                    single_file: bool) -> tuple[FileMeta | None, _ScanSkip | None]:
    try:
        stat_result = os.stat(abs_path)
    except OSError as e:
        logger.warning(MSG_OSERROR_DEGRADED, exc_info=True)
        detail = e.strerror or str(e)
        return None, _ScanSkip(f"stat 失败: {detail}", True)
    size_mb = stat_result.st_size / (1024 * 1024)
    if size_mb > config.max_file_size_mb:
        logger.info("[FileScanner] 超出大小上限，跳过: %s (%.1fMB > %.1fMB)",
                    abs_path, size_mb, config.max_file_size_mb)
        return None, _ScanSkip(
            f"超出大小上限 {config.max_file_size_mb:g}MB", False)
    max_read_bytes = _read_limit_bytes(config.max_file_size_mb)
    raw_bytes, skip_growth = _read_file_bounded(
        abs_path, max_read_bytes)
    if skip_growth:
        return None, _ScanSkip("文件在扫描期间增长", True)
    if raw_bytes is None:
        return None, _ScanSkip("文件读取失败", True)
    meta = _create_file_meta(abs_path, config, single_file, stat_result)
    _apply_source_metrics(meta, raw_bytes, config)
    return meta, None
def _count_source_lines(source: str, language: str) -> tuple[int, int, int, int]:
    if language == "python":
        return LineCounter.count(source)
    lines_list = _split_source_lines(source)
    total = len(lines_list)
    blank = sum(1 for ln in lines_list if not ln.strip())
    return total, total - blank, 0, blank
def _apply_ast_metrics(meta: FileMeta, source: str, config: ScanConfig,
                       decode_error: str = "") -> None:
    ast_result = (
        ASTAnalyzer._empty_result(config.extract_dependencies, "decode_failed")
        if decode_error else ASTAnalyzer.analyze(
            source, extract_deps=config.extract_dependencies,
            project_root=config.project_root,
        )
    )
    meta.functions = ast_result["functions"]
    meta.classes = ast_result["classes"]
    meta.imports = ast_result["imports"]
    meta.complexity = ast_result["complexity"]
    meta.max_complexity = ast_result["max_complexity"]
    meta.max_function_lines = ast_result["max_function_lines"]
    meta.docstring_coverage = ast_result["docstring_coverage"]
    meta.type_annotations = ast_result["type_annotations"]
    meta.extra["ast_status"] = ast_result["analysis_status"]
    meta.imported_modules = ast_result.get("imported_modules", [])
    meta.local_imports = ast_result.get("local_imports", [])
    meta.extra["local_absolute_imports"] = ast_result.get(
        "local_absolute_imports", [])
_SCAN_ERRORS = (AttributeError, KeyError, TypeError, ValueError,
                RuntimeError, OSError)
def _record_error(result: ScanResult, phase: str, path: str,
                  error: str) -> None:
    record: dict[str, Any] = {"phase": phase}
    if path:
        record["path"] = path
    record["error"] = error
    result.errors.append(record)
class FileScanner:
    def __init__(self, config: ScanConfig):
        self.config = config
        self._start_time: float | None = None
        self._scanned_count: int = 0
        self._total_estimate: int = 0
        self._py_file_counts: dict[str, int] = {}
        self._single_file = os.path.isfile(config.project_root)
    def _estimate_total_files(self) -> int:
        if self._single_file:
            if (self.config.max_files <= 0 or self.config.max_depth < 0
                    or self._is_timed_out()):
                return 0
            name = os.path.basename(self.config.project_root)
            if not self._passes_file_filters(name, name):
                return 0
            return 1
        return self._count_candidate_files(self.config.project_root, 0)
    def _dir_identity(self, directory: str) -> str:
        try:
            return os.path.normcase(os.path.realpath(directory))
        except (OSError, ValueError) as e:
            logger.warning(
                "[FileScanner] 目录 realpath 解析失败，降级绝对路径: %s (%s)",
                directory, e)
            return os.path.normcase(os.path.abspath(directory))
    def _count_candidate_files(self, directory: str, depth: int,
                               ancestors: frozenset[str] = frozenset()) -> int:
        if (depth > self.config.max_depth or self.config.max_files <= 0
                or self._is_timed_out()):
            return 0
        identity = self._dir_identity(directory)
        if identity in ancestors:
            return 0
        ancestors = ancestors | {identity}
        entries = self._scandir_snapshot(directory)
        if entries is None:
            return 0
        count = 0
        for entry in entries:
            if count >= self.config.max_files or self._is_timed_out():
                return min(count, self.config.max_files)
            if self._entry_is_dir(entry):
                if self._matches_patterns(
                        entry.name, self.config.exclude_dirs):
                    continue
                count += self._count_candidate_files(
                    entry.path, depth + 1, ancestors)
            elif self._countable_file(entry):
                count += 1
        return min(count, self.config.max_files)
    @staticmethod
    def _scandir_snapshot(directory: str) -> list[os.DirEntry] | None:
        try:
            with os.scandir(directory) as it:
                return list(it)
        except OSError as _e:
            log_swallowed(__name__, _e,
                          context='FileScanner._scandir_snapshot:OSError')
            return None
    def _countable_file(self, entry: os.DirEntry) -> bool:
        try:
            if not entry.is_file(
                    follow_symlinks=self.config.follow_symlinks):
                return False
        except OSError as _e:
            log_swallowed(__name__, _e,
                          context='FileScanner._countable_file:OSError')
            return False
        return self._passes_file_filters(
            entry.name,
            _relpath_or_absolute(entry.path, self.config.project_root))
    def scan(self) -> ScanResult:
        self._start_time = time.monotonic()
        self._scanned_count = 0
        self._py_file_counts = {}
        self._single_file = os.path.isfile(self.config.project_root)
        result = ScanResult(
            project_root=self.config.project_root,
            config={
                "include_patterns": list(self.config.include_patterns),
                "exclude_patterns": list(self.config.exclude_patterns),
                "exclude_dirs": list(self.config.exclude_dirs),
                "max_depth": self.config.max_depth,
                "max_files": self.config.max_files,
                "max_file_size_mb": self.config.max_file_size_mb,
                "timeout_seconds": self.config.timeout_seconds,
                "follow_symlinks": self.config.follow_symlinks,
                "analyze_python_ast": self.config.analyze_python_ast,
                "extract_dependencies": self.config.extract_dependencies,
            },
        )
        try:
            self._total_estimate = self._estimate_total_files()
            self._notify_progress(
                "on_scan_start", self.config.project_root, self._total_estimate)
            if self._single_file:
                self._scan_single_file(result)
            else:
                self._scan_directory(
                    directory=self.config.project_root,
                    result=result,
                    current_depth=0,
                    tree_node=result.tree,
                    ancestors=frozenset(),
                )
        except KeyboardInterrupt:
            logger.warning("[FileScanner] 扫描被用户中断，结果不完整")
            result.warnings.append("扫描被用户中断")
        except _SCAN_ERRORS as e:
            logger.warning(MSG_EXCEPTION_BROAD_HANDLER, exc_info=True)
            _record_error(result, "scan", "", str(e))
        self._build_summary(result)
        self._notify_progress("on_scan_complete", result.summary)
        return result
    def _scan_single_file(self, result: ScanResult) -> None:
        if not self._has_scan_budget(result, 0, self.config.project_root):
            return
        _name = os.path.basename(self.config.project_root)
        if not self._passes_file_filters(_name, _name):
            self._warn_once(
                result,
                f"单文件目标被过滤规则排除（include/exclude）: {_name}")
            return
        dir_meta = DirectoryMeta(
            rel_path=".",
            abs_path=os.path.dirname(self.config.project_root),
        )
        if not self._scan_and_register(
                self.config.project_root, result, dir_meta, result.tree):
            return
        result.directories["."] = dir_meta
    @staticmethod
    def _warn_once(result: ScanResult, message: str) -> None:
        if message not in result.warnings:
            result.warnings.append(message)
    def _notify_progress(self, method: str, *args: Any) -> None:
        if not self.config.progress:
            return
        try:
            getattr(self.config.progress, method)(*args)
        except Exception:
            logger.warning("[FileScanner] progress.%s 回调异常，忽略",
                           method, exc_info=True)
    def _register_file(
        self,
        result: ScanResult,
        dir_meta: DirectoryMeta,
        tree_node: dict[str, Any],
        file_meta: FileMeta,
        name: str,
    ) -> None:
        result.files[file_meta.rel_path] = file_meta
        dir_meta.files.append(name)
        dir_meta.file_count += 1
        dir_meta.total_lines += file_meta.lines
        dir_meta.total_size += file_meta.size_bytes
        dir_meta.total_functions += file_meta.functions
        dir_meta.total_classes += file_meta.classes
        dir_meta.total_imports += file_meta.imports
        if _has_complexity_metrics(file_meta):
            _py_n = self._py_file_counts.get(dir_meta.rel_path, 0) + 1
            self._py_file_counts[dir_meta.rel_path] = _py_n
            dir_meta.avg_complexity += (
                (file_meta.complexity - dir_meta.avg_complexity) / _py_n)
        tree_node[name] = {
            "type": "file",
            "size": file_meta.size_bytes,
            "lines": file_meta.lines,
            "language": file_meta.language,
        }
        self._scanned_count += 1
    def _scan_and_register(
        self,
        abs_path: str,
        result: ScanResult,
        dir_meta: DirectoryMeta,
        tree_node: dict[str, Any],
    ) -> bool:
        file_meta, skip = _scan_file_meta(
            abs_path, self.config, self._single_file)
        if file_meta is None:
            if skip is not None:
                self._warn_once(
                    result, f"文件扫描跳过（{skip.reason}）: {abs_path}")
                if skip.unexpected:
                    _record_error(result, "scan_file", abs_path, skip.reason)
                    self._notify_progress("on_error", abs_path, skip.reason)
            return False
        self._register_file(
            result, dir_meta, tree_node, file_meta, file_meta.name)
        self._notify_progress(
            "on_file_scanned", file_meta.rel_path, self._scanned_count,
            self._total_estimate)
        return True
    def _entry_is_dir(self, entry: os.DirEntry) -> bool:
        try:
            return entry.is_dir(follow_symlinks=self.config.follow_symlinks)
        except OSError as _e:
            log_swallowed(__name__, _e, context='FileScanner._entry_is_dir:OSError')
            return False
    def _has_scan_budget(self, result: ScanResult, depth: int,
                         directory: str) -> bool:
        if depth > self.config.max_depth:
            self._warn_once(
                result, f"达到最大深度 {self.config.max_depth}: {directory}")
            return False
        if self._scanned_count >= self.config.max_files:
            self._warn_once(result, f"达到最大文件数 {self.config.max_files}")
            return False
        if self._is_timed_out():
            self._warn_once(result, "扫描超时")
            return False
        return True
    def _scan_directory(
        self,
        directory: str,
        result: ScanResult,
        current_depth: int,
        tree_node: dict[str, Any],
        ancestors: frozenset[str],
    ) -> bool:
        if not self._has_scan_budget(result, current_depth, directory):
            return False
        identity = self._dir_identity(directory)
        if identity in ancestors:
            self._warn_once(
                result,
                f"检测到目录环（符号链接指回祖先目录），跳过: {directory}")
            return False
        ancestors = ancestors | {identity}
        entries = self._list_dir_entries(directory, result)
        if entries is None:
            return False
        dir_meta = DirectoryMeta(
            rel_path=_relpath_or_absolute(
                directory, self.config.project_root),
            abs_path=directory,
        )
        result.directories[dir_meta.rel_path] = dir_meta
        for entry in entries:
            if self._scanned_count >= self.config.max_files:
                self._warn_once(result, f"达到最大文件数 {self.config.max_files}")
                return True
            if self._is_timed_out():
                self._warn_once(result, "扫描超时")
                return True
            self._scan_directory_entry(
                entry, result, dir_meta, tree_node, current_depth, ancestors)
        return True
    def _list_dir_entries(self, directory: str,
                          result: ScanResult) -> list[os.DirEntry] | None:
        try:
            with os.scandir(directory) as it:
                return sorted(it, key=lambda e: (not self._entry_is_dir(e), e.name))
        except PermissionError as e:
            logger.warning("[FileScanner] 扫描目录权限不足，跳过: %s (%s)",
                           directory, e)
            _record_error(result, "scan_dir", directory, "权限不足")
            self._notify_progress("on_error", directory, "权限不足")
        except OSError as e:
            logger.warning("[FileScanner] 扫描目录失败，跳过: %s (%s)", directory, e)
            _record_error(result, "scan_dir", directory, str(e))
            self._notify_progress("on_error", directory, str(e))
        return None
    def _scan_directory_entry(
        self,
        entry,
        result: ScanResult,
        dir_meta: DirectoryMeta,
        tree_node: dict[str, Any],
        current_depth: int,
        ancestors: frozenset[str],
    ) -> None:
        try:
            if entry.is_dir(follow_symlinks=self.config.follow_symlinks):
                self._enter_subdirectory(
                    entry, result, dir_meta, tree_node, current_depth,
                    ancestors)
            elif entry.is_file(follow_symlinks=self.config.follow_symlinks):
                self._scan_file_entry(entry, result, dir_meta, tree_node)
        except OSError as e:
            logger.warning("[FileScanner] 条目探测失败，跳过该条目: %s (%s)",
                           entry.path, e)
            _record_error(result, "scan_entry", entry.path, str(e))
            self._notify_progress("on_error", entry.path, str(e))
    def _enter_subdirectory(
        self,
        entry,
        result: ScanResult,
        dir_meta: DirectoryMeta,
        tree_node: dict[str, Any],
        current_depth: int,
        ancestors: frozenset[str],
    ) -> None:
        if self._matches_patterns(entry.name, self.config.exclude_dirs):
            return
        sub_tree: dict[str, Any] = {}
        if not self._scan_directory(
                entry.path, result, current_depth + 1, sub_tree, ancestors):
            return
        tree_node[entry.name] = sub_tree
        dir_meta.subdirs.append(entry.name)
    def _scan_file_entry(
        self,
        entry,
        result: ScanResult,
        dir_meta: DirectoryMeta,
        tree_node: dict[str, Any],
    ) -> None:
        if not self._passes_file_filters(
                entry.name,
                _relpath_or_absolute(entry.path, self.config.project_root)):
            return
        self._scan_and_register(entry.path, result, dir_meta, tree_node)
    def _passes_file_filters(self, filename: str,
                             rel_path: str = "") -> bool:
        return (not self._should_exclude_file(filename, rel_path)
                and self._matches_include(filename, rel_path))
    def _build_summary(self, result: ScanResult) -> None:
        _aggregate_summary(result.files, result.summary)
        result.summary.scan_duration_ms = round(
            (time.monotonic() - self._start_time) * 1000, 1)
    @staticmethod
    def _matches_patterns(name: str, patterns: list[str] | None) -> bool:
        return any(fnmatch.fnmatch(name, pattern) for pattern in (patterns or ()))
    @staticmethod
    def _globstar_path_match(rel_path: str, pattern: str) -> bool:
        pattern_parts = pattern.split("/")
        path_parts = rel_path.split("/")
        @cache
        def matches(pattern_index: int, path_index: int) -> bool:
            if pattern_index == len(pattern_parts):
                return path_index == len(path_parts)
            part = pattern_parts[pattern_index]
            if part == "**":
                return (matches(pattern_index + 1, path_index)
                        or (path_index < len(path_parts)
                            and matches(pattern_index, path_index + 1)))
            return (path_index < len(path_parts)
                    and fnmatch.fnmatch(path_parts[path_index], part)
                    and matches(pattern_index + 1, path_index + 1))
        return matches(0, 0)
    @staticmethod
    def _pattern_hits(pattern: str, filename: str, rel_path: str) -> bool:
        if fnmatch.fnmatch(filename, pattern):
            return True
        if not rel_path:
            return False
        rel_norm = rel_path.replace("\\", "/")
        pat_norm = pattern.replace("\\", "/")
        if "/" not in pat_norm:
            return False
        return FileScanner._globstar_path_match(rel_norm, pat_norm)
    def _should_exclude_file(self, filename: str,
                             rel_path: str = "") -> bool:
        return any(self._pattern_hits(pattern, filename, rel_path)
                   for pattern in self.config.exclude_patterns)
    def _matches_include(self, filename: str, rel_path: str = "") -> bool:
        patterns = self.config.include_patterns
        return (not patterns
                or any(self._pattern_hits(pattern, filename, rel_path)
                       for pattern in patterns))
    def _is_timed_out(self) -> bool:
        if self._start_time is None:
            return False
        return time.monotonic() - self._start_time > self.config.timeout_seconds
def quick_scan(
    project_root: str,
    include_patterns: list[str] | None = None,
    exclude_dirs: list[str] | str | None = None,
    analyze_ast: bool | None = None,
    extract_deps: bool | None = None,
    progress: ScanProgress | None = None,
) -> ScanResult:
    overrides: dict = {}
    if exclude_dirs is not None:
        overrides["exclude_dirs"] = exclude_dirs
    if analyze_ast is not None:
        overrides["analyze_python_ast"] = analyze_ast
    if extract_deps is not None:
        overrides["extract_dependencies"] = extract_deps
    if include_patterns is not None:
        overrides["include_patterns"] = include_patterns
    config = ScanConfig(
        project_root=project_root,
        progress=progress,
        **overrides,
    )
    scanner = FileScanner(config)
    return scanner.scan()
def _render_text_tree(node: dict[str, Any], prefix: str = "") -> list[str]:
    lines: list[str] = []
    entries = sorted(node.items(), key=lambda kv: str(kv[0]))
    for i, (name, child) in enumerate(entries):
        last = i == len(entries) - 1
        branch = "└─ " if last else "├─ "
        lines.append(f"{prefix}{branch}{name}")
        if (isinstance(child, dict) and child
                and child.get("type") != "file"):
            lines.extend(_render_text_tree(
                child, prefix + ("   " if last else "│  ")))
    return lines
def _ensure_output_dir(kind: str, label: str) -> str:
    try:
        target = report_artifact_dir(kind)
    except RuntimeError as e:
        logger.exception("[CLI] %s 目录解析失败", label)
        print(f"[ERROR] {label} 目录解析失败：{e}")
        sys.exit(1)
    os.makedirs(target, exist_ok=True)
    return target
def _emit_html_report(result: ScanResult, show_tree: bool) -> None:
    payload = result.report_data(include_tree=show_tree)
    try:
        path = emit_to_stage(
            "diag", result.project_root, "文件扫描报告",
            render_file_scan_report_html(payload),
            mid="file_scan", icon="📁", payload=payload,
            report_type="file_scan")
    except Exception as exc:
        logger.warning("[FileScanner] HTML 阶段报告生成失败: %s", exc,
                       exc_info=True)
        print(f"[ERROR] HTML 报告生成失败: {exc}")
        return
    if not path:
        print("[ERROR] HTML 报告未落盘（阶段聚合未返回路径）")
        return
    try:
        json_path = stage_json_artifact_path(path, result.project_root)
    except (OSError, RuntimeError, ValueError) as exc:
        logger.warning("[FileScanner] 配套 JSON 路径解析失败: %s", exc)
        json_path = ""
    print(f"HTML 报告已汇入诊断阶段: {path}")
    if json_path and os.path.isfile(json_path):
        print(f"配套 JSON: {json_path}")
def _emit_csv_report(result: ScanResult) -> None:
    report_dir = _ensure_output_dir("report", "CSV")
    csv_path = os.path.join(report_dir, "scan_report.csv")
    result.export_csv(csv_path)
    print(f"CSV 已保存: {csv_path}")
def _print_scan_summary(project_root: str, summary: ScanSummary) -> None:
    print(f"项目: {project_root}")
    print(f"文件数: {summary.total_files}")
    print(f"总行数: {summary.total_lines} (代码: {summary.total_code_lines}, "
          f"注释: {summary.total_comment_lines}, 空行: {summary.total_blank_lines})")
    print(f"函数: {summary.total_functions}  类: {summary.total_classes}")
    print(f"大小分布: {summary.size_distribution}")
    print(f"复杂度分布: {summary.complexity_distribution}")
    print(f"大小: {summary.total_size_bytes / 1024:.1f} KB")
    print(f"耗时: {summary.scan_duration_ms:.0f}ms")
def _print_scan_rankings(summary: ScanSummary) -> None:
    print("\nTop 5 最大文件:")
    for path, lines in summary.largest_files[:5]:
        print(f"  {path}: {lines} 行")
    if not summary.most_complex_files:
        return
    print("\nTop 5 最复杂文件:")
    for path, complexity in summary.most_complex_files[:5]:
        print(f"  {path}: 复杂度 {complexity:.1f}")
def _print_dependency_ranking(result: ScanResult) -> None:
    print("\n被导入最多的文件 (Top 10):")
    for path, count in result.get_top_importers(10):
        print(f"  {path}: {count} 次")
def _print_tree_block(result: ScanResult) -> None:
    tree_lines = _render_text_tree(result.tree)
    if tree_lines:
        print("\n目录树:")
        print("\n".join(tree_lines))
def _print_diagnostics(result: ScanResult) -> None:
    if result.warnings:
        print(f"\n警告: {result.warnings}")
    if result.errors:
        print(f"\n错误: {result.errors}")
def _print_text_report(result: ScanResult, show_deps: bool,
                       show_tree: bool) -> None:
    _print_scan_summary(result.project_root, result.summary)
    _print_scan_rankings(result.summary)
    if show_deps:
        _print_dependency_ranking(result)
    if show_tree:
        _print_tree_block(result)
    _print_diagnostics(result)
def _cli_usage() -> None:
    _script = os.path.basename(sys.argv[0] or "") or "diag_file_scanner.py"
    print(f"用法: python {_script} <project_root> [选项]")
    print("  --json    输出 JSON 格式")
    print("  --html    输出 HTML 格式")
    print("  --csv     输出 CSV 格式")
    print("  --all     扫描所有文件类型（默认仅 .py）")
    print("  --deps    显示依赖图")
    print("  --tree    显示目录树")
    sys.exit(1)
_CLI_FLAGS = frozenset({"--json", "--html", "--csv", "--all",
                       "--deps", "--tree"})
def _parse_cli_args(args: list[str]) -> tuple[str | None, set[str]]:
    root: str | None = None
    flags: set[str] = set()
    for arg in args:
        if arg in _CLI_FLAGS:
            flags.add(arg)
            continue
        if arg.startswith("-") or root is not None:
            _cli_usage()
        root = arg
    return root, flags
if __name__ == "__main__":
    setup_logging()
    _root, _flags = _parse_cli_args(sys.argv[1:])
    if _root is None:
        _cli_usage()
    _show_tree = "--tree" in _flags
    _patterns = [] if "--all" in _flags else list(_DEFAULT_INCLUDE_PATTERNS)
    _result = quick_scan(_root, include_patterns=_patterns,
                         progress=ConsoleProgress(verbosity=1))
    if "--json" in _flags:
        print(_result.to_json())
    elif "--html" in _flags:
        _emit_html_report(_result, _show_tree)
    elif "--csv" in _flags:
        _emit_csv_report(_result)
    else:
        _print_text_report(_result, "--deps" in _flags, _show_tree)

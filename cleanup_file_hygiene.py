from __future__ import annotations

import ast
import hashlib
import logging
import os
import re
import time
from collections import defaultdict
from collections.abc import Callable, Container, Iterable
from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
from typing import Any, NamedTuple, Self

from jwsgj.diag_shared_ast_nodes import (
    definition_time_exprs,
    is_docstring_stmt,
    iter_def_site_nodes,
    module_postpones_annotations,
    multiline_string_spans,
)
from jwsgj.diag_shared_ast_surface import is_all_assignment
from jwsgj.diag_shared_source_core import (
    aligned_source_lines,
    code_part,
    net_paren_depth,
    parse_py_source,
    parse_py_source_with_details,
    read_py_source_with_error,
)
from jwsgj.diag_types_defs import (
    PreinterventionResult,
    collect_findings,
    finish_check,
    prepare_tree,
)
from jwsgj.diag_types_normalize import (
    mean_std,
    normalize_input,
    normalize_py_filename,
)
from jwsgj.diag_types_vocab import (
    MSG_OSERROR_CONTINUE,
    PARSE_DEGRADE_EXC,
    SEVERITY_BLOCKING,
    SEVERITY_INFO,
    SEVERITY_WARNING,
    register_check_provider,
)
from jwsgj.html_render_pipeline import generate_html_report
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    GATE_SCAN_IGNORE_DIRS_LOWER,
    PROTECTED_CORE_FILES,
    SCAN_SKIP_DIRS,
    SKILL_LOG_DIR_NAME,
    STATE_DIR_NAME,
    TEST_DIR_CANDIDATES_LOWER,
    is_pruned_scan_dir,
)

__all__ = [
    'COMPAT_STUB',
    'MIXED_PORTAL',
    'PORTAL_INIT',
    'PORTAL_PURE',
    'S01_RULE',
    'S02_RULE',
    'S03_RULE',
    'STUB_CONSTRAINTS',
    'STUB_RESIDUE',
    'FileCleaner',
    'FileCleanupItem',
    'FileCleanupReport',
    'FileStatsProfile',
    'GitIgnoreParser',
    'ImportShape',
    'LineMarkers',
    'analyze_file',
    'check_stub_constraints_for_content',
    'check_stub_portal',
    'detect_new_compat_stubs',
    'get_stub_constraints',
    'print_report',
    'require_skill_dir',
    'scan_import_shape',
    'scan_line_markers',
    'scan_stubs',
]
_log = logging.getLogger(__name__)
_DEFAULT_CLEANUP_ITEM_SEVERITY = SEVERITY_INFO
def require_skill_dir(skill_dir: Any) -> Path:
    raw = os.fspath(skill_dir) if isinstance(skill_dir, (str, os.PathLike)) else ""
    if not isinstance(raw, str) or not raw.strip():
        raise ValueError(
            f"无效的技能目录: {skill_dir!r}（须为非空字符串或路径对象）")
    path = Path(raw)
    if not path.is_dir():
        raise ValueError(f"无效的技能目录: {skill_dir}")
    return path
@dataclass
class FileCleanupItem:
    file_path: str = ""
    file_size: int = 0
    category: str = ""
    severity: str = _DEFAULT_CLEANUP_ITEM_SEVERITY
    description: str = ""
    suggestion: str = ""
    is_directory: bool = False
    last_modified: float = 0.0
    age_days: int = 0
    age_tier: str = ""
@dataclass
class FileStatsProfile:
    by_extension: dict[str, int] = field(default_factory=dict)
    by_extension_size: dict[str, int] = field(default_factory=dict)
    total_files: int = 0
    total_size: int = 0
    mean_size: float = 0.0
    std_size: float = 0.0
    largest_files: list[tuple[str, int]] = field(default_factory=list)
@dataclass
class FileCleanupReport:
    skill_dir: str = ""
    total_files_scanned: int = 0
    total_size_bytes: int = 0
    items: list[FileCleanupItem] = field(default_factory=list)
    stats_profile: FileStatsProfile | None = None
    freed_bytes: int = 0
    errors: list[str] = field(default_factory=list)
    @staticmethod
    def _format_size(size_bytes: int) -> str:
        if size_bytes < 1024:
            return f"{size_bytes} B"
        if size_bytes < 1024 * 1024:
            return f"{size_bytes / 1024:.1f} KB"
        if size_bytes < 1024 * 1024 * 1024:
            return f"{size_bytes / (1024 * 1024):.1f} MB"
        return f"{size_bytes / (1024 * 1024 * 1024):.2f} GB"
@dataclass
class _ScanStats:
    content_map: dict[str, list[str]] = field(
        default_factory=lambda: defaultdict(list))
    file_sizes: list[int] = field(default_factory=list)
    ext_stats: dict[str, list[int]] = field(
        default_factory=lambda: defaultdict(list))
    size_pairs: list[tuple[str, int]] = field(default_factory=list)
@dataclass(frozen=True)
class _FileAge:
    mtime: float = 0.0
    age_days: int = 0
_UNKNOWN_AGE = _FileAge()
def _file_age(mtime: float, now: float) -> _FileAge:
    return _FileAge(
        mtime=mtime, age_days=max(0, int((now - mtime) / 86400)))
@dataclass(frozen=True)
class _FileFacts:
    fpath: Any
    file_path: str
    size: int
    age: _FileAge
_PYC_TAG_RE = re.compile(
    r"\.(?:cpython|pypy|jython|ironpython)[0-9a-zA-Z.\-]*$",
    re.IGNORECASE)
def _is_orphan_pyc(f: Path) -> bool:
    if not f.name.casefold().endswith(".pyc"):
        return False
    source_names = {f.with_suffix(".py").name}
    m = _PYC_TAG_RE.search(f.stem)
    if m:
        source_names.add(f.stem[:m.start()] + ".py")
    source_dirs = [f.parent]
    if f.parent.name.casefold() == "__pycache__":
        source_dirs.append(f.parent.parent)
    return not any(
        os.path.exists(directory / name)
        for directory in source_dirs for name in source_names
    )
_USELESS_PATTERNS = [
    (_is_orphan_pyc, "孤立 .pyc（对应 .py 已删除）"),
    (lambda f: f.name.casefold().endswith(".pyo"), "编译缓存 .pyo 文件"),
    (lambda f: f.name.startswith("~$"), "Office 临时锁定文件"),
    (lambda f: f.name.casefold().endswith(".tmp"), "临时文件 .tmp"),
    (lambda f: f.name.casefold() == "thumbs.db", "Windows 缩略图缓存"),
    (lambda f: f.name.casefold() == ".ds_store", "macOS 目录元数据"),
    (lambda f: f.name.casefold() == "desktop.ini", "Windows 文件夹配置"),
    (lambda f: f.name.casefold() == ".coverage", "coverage 数据文件"),
]
_ARTIFACT_DIRS = {
    "__pycache__", ".pytest_cache", ".mypy_cache", ".ruff_cache",
    "dist", "build", "egg-info", ".eggs", ".egg-info",
    "htmlcov", ".coverage", ".tox", ".nox",
    "node_modules", ".hypothesis",
}
_ARTIFACT_DIRS_CASEFOLD = frozenset(
    name.casefold() for name in _ARTIFACT_DIRS)
def _is_artifact_dir(name: str) -> bool:
    folded = name.casefold()
    return (folded in _ARTIFACT_DIRS_CASEFOLD
            or folded.endswith(".egg-info"))
_ARTIFACT_EXTENSIONS = {
    ".log", ".pyc", ".pyo", ".egg", ".whl",
    ".coverage", ".prof", ".err", ".out",
}
_LOG_PATTERNS = [
    re.compile(r".*\.log(?:\.\d+)?$", re.IGNORECASE),
    re.compile(r".*\.err$", re.IGNORECASE),
    re.compile(r".*\.out$", re.IGNORECASE),
    re.compile(r".*\.trace$", re.IGNORECASE),
]
_BACKUP_NAME_TOKENS = tuple(sorted({
    ".bak", ".old", ".orig", ".backup", ".swp", ".swo",
    "~", ".save", ".prev", ".v0", ".v1", ".v2",
}, key=lambda _t: (-len(_t), _t)))
_BACKUP_NAME_PATTERNS = [
    re.compile(r".*_backup\d*$", re.IGNORECASE),
    re.compile(r".*_bak\d*$", re.IGNORECASE),
    re.compile(r".*_old\d*$", re.IGNORECASE),
    re.compile(r".*\.\d{4}-\d{2}-\d{2}$"),
    re.compile(r".*_copy\d*$", re.IGNORECASE),
    re.compile(r"^copy\s*\(?\d*\)?\s*of\s+", re.IGNORECASE),
]
_VERSION_DIR_PATTERNS = (
    r"^_versions?$",
    r"^\.versions?$",
    r"^backups?$",
    r"^_backups?$",
    r"^old_versions?$",
    r"^archive[sd]?$",
    r"^_archive[sd]?$",
)
_VERSION_DIR_RE = re.compile(
    "|".join(f"(?:{p})" for p in _VERSION_DIR_PATTERNS), re.IGNORECASE)
_SKILL_ONLY_RUNTIME_DIRS_LOWER = frozenset({
    SKILL_LOG_DIR_NAME.casefold(), STATE_DIR_NAME.casefold(),
})
_NO_RUNTIME_DIRS = frozenset()
def _runtime_asset_dirs(root: Any) -> frozenset[str]:
    names = frozenset(str(name).casefold() for name in SCAN_SKIP_DIRS)
    text = os.fspath(root) if isinstance(root, (str, os.PathLike)) else ""
    if isinstance(text, str) and text and os.path.isfile(
            os.path.join(text, "SKILL.md")):
        return names
    return names - _SKILL_ONLY_RUNTIME_DIRS_LOWER
def _is_scan_excluded_dir(name: str,
                          runtime_dirs: Container[str] = _NO_RUNTIME_DIRS) -> bool:
    return (is_pruned_scan_dir(name, runtime_dirs)
            or _is_artifact_dir(name)
            or _VERSION_DIR_RE.match(name) is not None)
_PROTECTED_FILES = PROTECTED_CORE_FILES | frozenset({
    "MANIFEST.in", "requirements.txt",
})
_PROTECTED_FILES_CASEFOLD = frozenset(
    name.casefold() for name in _PROTECTED_FILES)
_LOCK_SUFFIX = ".lock"
_EMPTY_BY_DESIGN_NAMES = frozenset({
    ".gitkeep", ".keep", "py.typed", "conftest.py",
})
_EMPTY_BY_DESIGN_NAMES_CASEFOLD = frozenset(
    name.casefold() for name in _EMPTY_BY_DESIGN_NAMES)
def _is_empty_by_design(f: Path) -> bool:
    folded = f.name.casefold()
    return (folded.endswith(_LOCK_SUFFIX)
            or folded in _EMPTY_BY_DESIGN_NAMES_CASEFOLD)
_VERSION_FILE_PATTERN = re.compile(
    r"(?:.*_)?version(?:_info)?\.py$", re.IGNORECASE)
_COLD_DATA_THRESHOLD = 180
_WARM_DATA_THRESHOLD = 30
_ANOMALY_STD_MULTIPLIER = 5.0
_KNOWN_BIG_FILE_EXTS = (".pth", ".bin", ".h5", ".pb", ".onnx", ".zip", ".tar.gz")
_STUB_DETAIL_LIMIT = 5
_GITIGNORE_SYNTHETIC_PATTERNS = [
    *(name + "/" for name in sorted(_ARTIFACT_DIRS)),
    "*.egg-info/",
]
def _consume_star_run(pattern: str, pos: int) -> int:
    i = pos
    while i < len(pattern) and pattern[i] == "*":
        i += 1
    return i
def _is_segment_start(pattern: str, pos: int) -> bool:
    return pos == 0 or pattern[pos - 1] == "/"
def _glob_star_tail(pattern: str, pos: int) -> tuple[str, int]:
    end = _consume_star_run(pattern, pos)
    if end == pos + 1:
        return r"[^/]*", end
    if not _is_segment_start(pattern, pos):
        return r"[^/]*", end
    if end < len(pattern) and pattern[end] == "/":
        return r"(?:[^/]+/)*", end + 1
    if end >= len(pattern):
        return r".*", end
    return r"[^/]*", end
_POSIX_CLASS_FRAGMENTS = {
    "alnum": "0-9A-Za-z",
    "alpha": "A-Za-z",
    "blank": r" \t",
    "cntrl": r"\x00-\x1f\x7f",
    "digit": "0-9",
    "graph": r"\x21-\x7e",
    "lower": "a-z",
    "print": r"\x20-\x7e",
    "punct": r"\x21-\x2f\x3a-\x40\x5b-\x60\x7b-\x7e",
    "space": r"\t\n\v\f\r ",
    "upper": "A-Z",
    "xdigit": "0-9A-Fa-f",
}
_POSIX_CLASS_RE = re.compile(r"\[:(?P<name>[a-z]+):\]")
def _class_body_end(pattern: str, pos: int) -> int:
    n = len(pattern)
    j = pos + 1
    if j < n and pattern[j] in {"!", "^"}:
        j += 1
    if j < n and pattern[j] == "]":
        j += 1
    while j < n and pattern[j] != "]":
        if pattern[j] == "\\" and j + 1 < n:
            j += 2
            continue
        if pattern.startswith("[:", j):
            posix_end = pattern.find(":]", j + 2)
            if posix_end >= 0:
                j = posix_end + 2
                continue
        j += 1
    return j if j < n else -1
def _posix_class_fragment(match: re.Match[str]) -> str:
    name = match.group("name")
    if os.name == "nt" and name in {"lower", "upper"}:
        return "A-Za-z"
    try:
        return _POSIX_CLASS_FRAGMENTS[name]
    except KeyError:
        raise re.error(f"未知 POSIX 字符类: {name}") from None
def _translate_glob_class(stuff: str) -> str:
    parts: list[str] = []
    i = 0
    while i < len(stuff):
        if stuff[i] == "\\":
            if i + 1 < len(stuff):
                parts.append(re.escape(stuff[i + 1]))
                i += 2
            else:
                parts.append(r"\\")
                i += 1
            continue
        posix_match = _POSIX_CLASS_RE.match(stuff, i)
        if posix_match is not None:
            parts.append(_posix_class_fragment(posix_match))
            i = posix_match.end()
            continue
        char = stuff[i]
        parts.append(re.escape(char) if char in {"[", "]"} else char)
        i += 1
    return "".join(parts)
def _glob_class_tail(pattern: str, pos: int) -> tuple[str, int]:
    end = _class_body_end(pattern, pos)
    if end < 0:
        return r"\[", pos + 1
    stuff = pattern[pos + 1:end]
    if stuff.startswith(("!", "^")):
        stuff = "^" + stuff[1:]
    stuff = _translate_glob_class(stuff)
    return f"(?!/)[{stuff}]", end + 1
@lru_cache(maxsize=4096)
def _glob_regex(pattern: str) -> re.Pattern[str]:
    parts = ["(?s:"]
    i, n = 0, len(pattern)
    while i < n:
        c = pattern[i]
        if c == "*":
            frag, i = _glob_star_tail(pattern, i)
            parts.append(frag)
        elif c == "?":
            parts.append("[^/]")
            i += 1
        elif c == "[":
            frag, i = _glob_class_tail(pattern, i)
            parts.append(frag)
        elif c == "\\" and i + 1 < n:
            parts.append(re.escape(pattern[i + 1]))
            i += 2
        else:
            parts.append(re.escape(c))
            i += 1
    parts.append(r")\Z")
    return re.compile("".join(parts))
def _glob_match(pattern: str, path: str) -> bool:
    pat = pattern.lower() if os.name == "nt" else pattern
    name = os.path.normcase(path).replace("\\", "/")
    try:
        compiled = _glob_regex(pat)
    except re.error as exc:
        _log.warning("gitignore 模式无法编译，按不匹配处理: %r: %s", pattern, exc)
        return False
    return compiled.match(name) is not None
def _strip_gitignore_trailing_spaces(line: str) -> str:
    end = len(line)
    while end and line[end - 1] == " ":
        backslashes = 0
        pos = end - 2
        while pos >= 0 and line[pos] == "\\":
            backslashes += 1
            pos -= 1
        if backslashes % 2:
            break
        end -= 1
    return line[:end]
def _parse_gitignore_lines(text: str):
    for raw in text.split("\n"):
        line = _strip_gitignore_trailing_spaces(raw.rstrip("\r"))
        if not line or line.startswith("#"):
            continue
        is_negation = line.startswith("!") and not line.startswith("\\!")
        yield (line[1:] if is_negation else line), is_negation
class GitIgnoreParser:
    def __init__(self: Self, skill_dir: str | os.PathLike) -> None:
        self._skill_dir = require_skill_dir(skill_dir)
        self._patterns: list[tuple[str, str, bool]] = []
        self._load()
    def _load(self: Self) -> None:
        runtime_dirs = _runtime_asset_dirs(self._skill_dir)
        for root, dirs, _ in os.walk(self._skill_dir):
            dirs[:] = sorted(
                d for d in dirs
                if not _is_scan_excluded_dir(d, runtime_dirs))
            gitignore_path = Path(root) / ".gitignore"
            if not gitignore_path.is_file():
                continue
            base = os.path.relpath(
                root, self._skill_dir).replace("\\", "/")
            if base == ".":
                base = ""
            try:
                self._patterns.extend(
                    (base, pattern, is_negation)
                    for pattern, is_negation in _parse_gitignore_lines(
                        gitignore_path.read_text(encoding="utf-8-sig")))
            except (OSError, UnicodeDecodeError):
                _log.warning(MSG_OSERROR_CONTINUE, exc_info=True)
        self._patterns[:0] = [
            ("", pat, False) for pat in _GITIGNORE_SYNTHETIC_PATTERNS
        ]
    @staticmethod
    def _match_root_anchored(pattern: str, path: str, is_dir: bool) -> bool:
        if pattern.endswith("/") and not is_dir:
            return False
        anchored_pat = pattern.lstrip("/").rstrip("/")
        return bool(anchored_pat) and _glob_match(anchored_pat, path)
    @staticmethod
    def _match_dir_pattern(pattern: str, path: str, is_dir: bool) -> bool:
        if not is_dir:
            return False
        stripped = pattern[:-1]
        target = path if "/" in stripped else path.rsplit("/", maxsplit=1)[-1]
        return _glob_match(stripped, target)
    @staticmethod
    def _match_pattern(pattern: str, path: str, is_dir: bool) -> bool:
        if pattern.startswith("/"):
            return GitIgnoreParser._match_root_anchored(pattern, path, is_dir)
        if pattern.endswith("/"):
            return GitIgnoreParser._match_dir_pattern(pattern, path, is_dir)
        target = path if "/" in pattern else path.rsplit("/", maxsplit=1)[-1]
        return _glob_match(pattern, target)
    def _is_ignored_single(self: Self, path: str, is_dir: bool) -> bool:
        last_negation = False
        matched = False
        normalized_path = os.path.normcase(path).replace("\\", "/")
        for base, pattern, is_negation in self._patterns:
            scoped_path = normalized_path
            if base:
                prefix = os.path.normcase(base).replace("\\", "/") + "/"
                if not normalized_path.startswith(prefix):
                    continue
                scoped_path = normalized_path[len(prefix):]
            if GitIgnoreParser._match_pattern(pattern, scoped_path, is_dir):
                matched = True
                last_negation = is_negation
        return matched and not last_negation
    def is_ignored(self: Self, path: str) -> bool:
        path = path.replace("\\", "/")
        is_dir = path.endswith("/")
        parts = [part for part in path.split("/") if part]
        if not parts:
            return False
        for depth in range(1, len(parts)):
            parent = "/".join(parts[:depth])
            if self._is_ignored_single(parent, is_dir=True):
                return True
        return self._is_ignored_single("/".join(parts), is_dir=is_dir)
def _stat_file_meta(fp: str, now: float) -> tuple[int, _FileAge] | None:
    try:
        fsize = os.path.getsize(fp)
        mtime = os.path.getmtime(fp)
        return fsize, _file_age(mtime, now)
    except OSError as e:
        _log.warning("[FileCleaner] 文件元数据获取失败: %s: %s", fp, e)
        return None
def _classify_age(age_days: int) -> str:
    if age_days > _COLD_DATA_THRESHOLD:
        return "cold"
    if age_days > _WARM_DATA_THRESHOLD:
        return "warm"
    return "hot"
def _make_item(file_path: str, file_size: int, category: str,
               description: str, suggestion: str, *,
               severity: str = _DEFAULT_CLEANUP_ITEM_SEVERITY,
               age: _FileAge | None = None,
               is_directory: bool = False) -> FileCleanupItem:
    age_days = age.age_days if age is not None else None
    return FileCleanupItem(
        file_path=file_path, file_size=file_size, category=category,
        severity=severity, description=description, suggestion=suggestion,
        is_directory=is_directory,
        last_modified=age.mtime if age is not None else 0.0,
        age_days=age_days if age_days is not None else 0,
        age_tier="" if age_days is None else _classify_age(age_days),
    )
def _build_stats_profile(all_files: list[str],
                         stats: _ScanStats) -> FileStatsProfile:
    profile = FileStatsProfile()
    profile.total_files = len(all_files)
    profile.total_size = sum(stats.file_sizes)
    if stats.file_sizes:
        profile.mean_size, profile.std_size = mean_std(stats.file_sizes)
    profile.by_extension = {
        ext: len(sizes) for ext, sizes in stats.ext_stats.items()
    }
    profile.by_extension_size = {
        ext: sum(sizes) for ext, sizes in stats.ext_stats.items()
    }
    file_size_pairs = list(stats.size_pairs)
    file_size_pairs.sort(key=lambda x: -x[1])
    profile.largest_files = file_size_pairs[:10]
    return profile
def _anomaly_threshold(file_sizes: list[int],
                       profile: FileStatsProfile | None = None) -> tuple[float, float] | None:
    if not file_sizes or len(file_sizes) < 5:
        return None
    if profile is not None and profile.total_files == len(file_sizes):
        mean_size = profile.mean_size
        std_size = profile.std_size
    else:
        mean_size, std_size = mean_std(file_sizes)
    threshold = mean_size + _ANOMALY_STD_MULTIPLIER * std_size
    if std_size < 1 or threshold < mean_size * 2:
        return None
    return mean_size, threshold
def _is_anomaly_large(fp: str, fsize: int, threshold: float) -> bool:
    if fsize <= threshold or fsize <= 1024 * 100:
        return False
    fname = os.path.basename(fp)
    return not any(fname.lower().endswith(ext) for ext in _KNOWN_BIG_FILE_EXTS)
def _accumulate_dir_files(dp: str, fnames: list[str]) -> tuple[int, int]:
    size = 0
    count = 0
    for fn in fnames:
        try:
            size += os.path.getsize(os.path.join(dp, fn))
            count += 1
        except OSError:
            _log.warning(MSG_OSERROR_CONTINUE, exc_info=True)
    return size, count
def _compute_dir_size(dir_path: str) -> tuple[int, int]:
    total_size = 0
    file_count = 0
    try:
        for dp, _, fnames in os.walk(dir_path):
            size, count = _accumulate_dir_files(dp, fnames)
            total_size += size
            file_count += count
    except OSError:
        _log.warning(MSG_OSERROR_CONTINUE, exc_info=True)
    return total_size, file_count
def _collect_imported_modules(
        py_files: list[str], py_stems: set[str],
) -> tuple[set[str], dict[str, str], bool]:
    imported_modules: set[str] = set()
    contents: dict[str, str] = {}
    complete = True
    for fp in py_files:
        content, err = read_py_source_with_error(fp)
        if content is None:
            _log.warning("[FileCleaner] 读取失败,跳过 %s: %s", fp, err)
            complete = False
            continue
        contents[fp] = content
        import_result = _parse_import_names(content, fp, py_stems)
        if import_result is None:
            complete = False
            continue
        imported_names, import_surface_complete = import_result
        imported_modules |= imported_names
        complete = complete and import_surface_complete
    return imported_modules, contents, complete
def _parse_import_names(
        content: str, file_path: str, py_stems: set[str]
) -> tuple[set[str], bool] | None:
    try:
        tree = ast.parse(content, filename=file_path)
    except PARSE_DEGRADE_EXC as exc:
        _log.debug("源码解析失败（导入面不完整）: %s: %s", file_path, exc)
        return None
    names, complete = _harvest_import_names(tree, py_stems)
    if not complete:
        _log.debug("动态导入目标不可静态解析（导入面不完整）: %s", file_path)
    return names, complete
_DYNAMIC_IMPORT_SOURCE_NAMES = {
    "importlib": "import_module",
    "builtins": "__import__",
}
_DEFAULT_DYNAMIC_IMPORT_NAMES = frozenset(_DYNAMIC_IMPORT_SOURCE_NAMES.values())
def _dynamic_import_function_names(tree: ast.Module) -> frozenset[str]:
    names = set(_DEFAULT_DYNAMIC_IMPORT_NAMES)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ImportFrom) or node.level != 0:
            continue
        source_name = _DYNAMIC_IMPORT_SOURCE_NAMES.get(node.module or "")
        if source_name is not None:
            names.update(
                alias.asname or alias.name for alias in node.names
                if alias.name == source_name)
    return frozenset(names)
def _dynamic_import_name(
        node: ast.Call,
        dynamic_names: Container[str] = _DEFAULT_DYNAMIC_IMPORT_NAMES,
) -> str | None:
    func = node.func
    is_dynamic_import = (
        isinstance(func, ast.Attribute)
        and func.attr in _DEFAULT_DYNAMIC_IMPORT_NAMES
    ) or (
        isinstance(func, ast.Name) and func.id in dynamic_names
    )
    if not is_dynamic_import:
        return None
    if node.args:
        target = node.args[0]
    else:
        target = next(
            (keyword.value for keyword in node.keywords
             if keyword.arg == "name"),
            None,
        )
    if not (isinstance(target, ast.Constant)
            and isinstance(target.value, str)):
        return ""
    module = target.value
    if not module or module.endswith("."):
        return ""
    return module.rsplit(".", 1)[-1]
def _dynamic_import_fromlist_names(
        node: ast.Call, py_stems: set[str],
        dynamic_names: Container[str] = _DEFAULT_DYNAMIC_IMPORT_NAMES,
) -> tuple[set[str], bool]:
    func = node.func
    if not (
        (isinstance(func, ast.Name) and func.id in dynamic_names)
        or (isinstance(func, ast.Attribute)
            and func.attr in _DEFAULT_DYNAMIC_IMPORT_NAMES)
    ):
        return set(), True
    if len(node.args) >= 4:
        target = node.args[3]
    else:
        target = next(
            (keyword.value for keyword in node.keywords
             if keyword.arg == "fromlist"),
            None,
        )
    if target is None or (
            isinstance(target, ast.Constant) and target.value is None):
        return set(), True
    if not isinstance(target, (ast.List, ast.Tuple, ast.Set)):
        return set(), False
    names: set[str] = set()
    complete = True
    for element in target.elts:
        if not (isinstance(element, ast.Constant)
                and isinstance(element.value, str)
                and element.value and element.value != "*"):
            complete = False
            continue
        name = element.value.rsplit(".", 1)[-1]
        if name in py_stems:
            names.add(name)
    return names, complete
def _harvest_import_names(
        tree: ast.Module, py_stems: set[str]
) -> tuple[set[str], bool]:
    names: set[str] = set()
    dynamic_names = _dynamic_import_function_names(tree)
    complete = True
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            names.update(
                alias.name.rsplit(".", 1)[-1] for alias in node.names
            )
        elif isinstance(node, ast.ImportFrom):
            names.update(_from_import_names(node, py_stems))
        elif isinstance(node, ast.Call):
            dynamic_name = _dynamic_import_name(node, dynamic_names)
            if dynamic_name is None:
                continue
            if dynamic_name:
                names.add(dynamic_name)
            else:
                complete = False
            fromlist_names, fromlist_complete = (
                _dynamic_import_fromlist_names(
                    node, py_stems, dynamic_names))
            names.update(fromlist_names)
            complete = complete and fromlist_complete
    return names, complete
def _from_import_names(node: ast.ImportFrom, py_stems: set[str]) -> set[str]:
    names: set[str] = set()
    if node.module:
        names.add(node.module.rsplit(".", 1)[-1])
    names.update(
        alias.name for alias in node.names
        if alias.name != "*" and alias.name in py_stems
    )
    return names
_TEST_MODULE_RE = re.compile(r"^(?:test_.+|.+_test)\.py$", re.IGNORECASE)
def _is_test_module_relpath(rel_norm: str) -> bool:
    parts = rel_norm.split("/")
    if any(part.casefold() in TEST_DIR_CANDIDATES_LOWER for part in parts[:-1]):
        return True
    return _TEST_MODULE_RE.match(parts[-1]) is not None
def _is_entry_script(content: str) -> bool:
    first_line = content.split("\n", 1)[0].strip()
    return (first_line.startswith("#!") and "python" in first_line) or bool(
        re.search(r'if\s+__name__\s*==\s*["\']__main__["\']', content))
def _orphan_script_item(
        file_path: str, file_name: str, content: str, now: float
        ) -> FileCleanupItem:
    is_entry = _is_entry_script(content)
    file_size, age = _stat_file_meta(file_path, now) or (0, _UNKNOWN_AGE)
    description = _orphan_description(
        file_name, is_entry, age.age_days, age_tier=_classify_age(age.age_days))
    return _make_item(
        file_path, file_size, "useless", description,
        f"检查是否需要保留 '{file_name}'，否则删除",
        age=age)
def _orphan_description(fname: str, is_entry: bool,
                        age_days: int, age_tier: str) -> str:
    if is_entry:
        if age_tier == "cold":
            return f"冷数据入口脚本（{age_days} 天未修改，有 shebang/__main__）: {fname}"
        return f"入口脚本（有 shebang/__main__，未被 import 引用）: {fname}"
    if age_tier == "cold":
        return f"孤立脚本（冷数据: {age_days} 天未修改）: {fname}"
    if age_tier == "warm":
        return f"孤立脚本（温数据: {age_days} 天未修改）: {fname}"
    return f"孤立脚本（未被其他文件引用）: {fname}"
def _file_digest(file_path: str, chunk_size: int = 65536) -> str:
    sha = hashlib.sha256()
    with open(file_path, "rb") as f:
        while True:
            chunk = f.read(chunk_size)
            if not chunk:
                break
            sha.update(chunk)
    return sha.hexdigest()
def _detect_anomalies(file_sizes: list[int],
                      all_files: list[str],
                      now: float,
                      reported: set[str] | None = None,
                      profile: FileStatsProfile | None = None) -> list[FileCleanupItem]:
    items: list[FileCleanupItem] = []
    gate = _anomaly_threshold(file_sizes, profile)
    if gate is None:
        return items
    mean_size, threshold = gate
    for fp in all_files:
        if reported and fp in reported:
            continue
        meta = _stat_file_meta(fp, now)
        if meta is None or not _is_anomaly_large(fp, meta[0], threshold):
            continue
        items.append(_anomaly_item(fp, meta[0], meta[1], mean_size))
    return items
def _anomaly_item(
        fp: str, fsize: int, age: _FileAge, mean_size: float) -> FileCleanupItem:
    ratio = fsize / mean_size if mean_size > 0 else 0
    fmt = FileCleanupReport._format_size
    return _make_item(
        fp, fsize, "anomaly",
        f"异常大文件: {fmt(fsize)}（是平均大小的 {ratio:.0f}x，"
        f"均值 {fmt(int(mean_size))}）",
        f"检查 '{os.path.basename(fp)}' 是否可压缩/拆分/移除",
        severity=SEVERITY_WARNING, age=age)
class FileCleaner:
    def __init__(self: Self, skill_dir: str) -> None:
        self._skill_dir = require_skill_dir(skill_dir)
        self._runtime_dirs = _runtime_asset_dirs(self._skill_dir)
        self._git_ignore = GitIgnoreParser(str(self._skill_dir))
    def _check_backup_files(self: Self, facts: _FileFacts,
                             report: FileCleanupReport) -> bool:
        name = facts.fpath.name
        folded = name.casefold()
        desc = next(
            (f"备份文件 ({token})" for token in _BACKUP_NAME_TOKENS
             if folded.endswith(token)),
            None,
        )
        if desc is None:
            desc = next(
                ("备份文件（名称模式匹配）"
                 for pattern in _BACKUP_NAME_PATTERNS if pattern.match(name)),
                None,
            )
        if desc is None:
            return False
        return self._report_file_item(
            facts, report, "backup", desc,
            f"删除备份文件: {facts.file_path}")
    def _collect_file_stats(self: Self, fpath: Path, file_path: str, now: float,
                            report: FileCleanupReport,
                            stats: _ScanStats) -> None:
        file_size, age = self._record_stats(fpath, file_path, now, report,
                                            stats)
        facts = _FileFacts(fpath, file_path, file_size, age)
        if (self._check_useless(facts, report)
                or self._check_backup_files(facts, report)
                or self._check_artifact(facts, report)):
            return
        self._collect_digest(file_path, file_size, stats)
    def _record_stats(self: Self, fpath: Path, file_path: str, now: float,
                      report: FileCleanupReport,
                      stats: _ScanStats) -> tuple[int, _FileAge]:
        try:
            fstat = fpath.stat()
        except OSError as e:
            _log.warning("[FileCleaner] 获取文件统计失败,用默认: %s: %s", fpath, e)
            return 0, _UNKNOWN_AGE
        file_size = fstat.st_size
        mtime = fstat.st_mtime
        age = _file_age(mtime, now)
        report.total_size_bytes += file_size
        stats.file_sizes.append(file_size)
        stats.ext_stats[fpath.suffix.lower() or "(无扩展名)"].append(file_size)
        stats.size_pairs.append((file_path, file_size))
        return file_size, age
    @staticmethod
    def _collect_digest(file_path: str, file_size: int,
                        stats: _ScanStats) -> None:
        if not 0 < file_size < 10 * 1024 * 1024:
            return
        try:
            stats.content_map[_file_digest(file_path)].append(file_path)
        except OSError:
            _log.warning(MSG_OSERROR_CONTINUE, exc_info=True)
    def _detect_duplicate_files(self: Self, content_map: dict, now: float,
                                report: FileCleanupReport) -> None:
        for dup_files in content_map.values():
            if len(dup_files) <= 1:
                continue
            for dup_path in dup_files[1:]:
                dup_size, dup_age = (
                    _stat_file_meta(dup_path, now) or (0, _UNKNOWN_AGE))
                report.items.append(_make_item(
                    dup_path, dup_size, "redundant",
                    f"重复文件（与 {os.path.basename(dup_files[0])} 内容相同）",
                    f"删除重复文件: {dup_path}", severity=SEVERITY_WARNING,
                    age=dup_age))
    def analyze(self: Self) -> FileCleanupReport:
        report = FileCleanupReport(skill_dir=str(self._skill_dir))
        now = time.time()
        artifact_items, artifact_files = self._scan_artifact_dirs()
        report.items.extend(artifact_items)
        report.total_size_bytes += sum(it.file_size for it in artifact_items)
        all_files = self._collect_all_files()
        report.total_files_scanned = len(all_files) + artifact_files
        stats = _ScanStats()
        for file_path in all_files:
            fpath = Path(file_path)
            self._collect_file_stats(fpath, file_path, now, report, stats)
        self._detect_duplicate_files(stats.content_map, now, report)
        reported = {it.file_path for it in report.items}
        report.items.extend(self._detect_orphan_scripts(
            all_files, now, reported,
            import_files=list(self._iter_scanned_py_files())))
        report.stats_profile = _build_stats_profile(all_files, stats)
        reported = {it.file_path for it in report.items}
        report.items.extend(
            _detect_anomalies(stats.file_sizes, all_files, now, reported,
                              profile=report.stats_profile))
        report.items.sort(key=lambda x: x.file_size, reverse=True)
        report.freed_bytes = sum(
            item.file_size for item in report.items
            if item.category != "anomaly")
        return report
    def _relative_posix(self: Self, full_path: str) -> str:
        return os.path.relpath(
            full_path, str(self._skill_dir)).replace("\\", "/")
    def _iter_scanned_py_files(self: Self):
        for root, dirs, filenames in os.walk(self._skill_dir):
            dirs[:] = sorted(
                d for d in dirs
                if not _is_scan_excluded_dir(d, self._runtime_dirs))
            for fname in sorted(filenames):
                if not fname.casefold().endswith(".py"):
                    continue
                full_path = os.path.join(root, fname)
                if self._git_ignore.is_ignored(self._relative_posix(full_path)):
                    continue
                yield full_path
    def _collect_all_files(self: Self) -> list[str]:
        files: list[str] = []
        for root, dirs, filenames in os.walk(self._skill_dir):
            dirs[:] = sorted(
                d for d in dirs
                if not _is_scan_excluded_dir(d, self._runtime_dirs))
            for fname in sorted(filenames):
                if fname.casefold() in _PROTECTED_FILES_CASEFOLD:
                    continue
                if _VERSION_FILE_PATTERN.match(fname):
                    continue
                full_path = os.path.join(root, fname)
                rel = self._relative_posix(full_path)
                if self._git_ignore.is_ignored(rel):
                    continue
                files.append(full_path)
        return files
    def _scan_artifact_dirs(self: Self) -> tuple[list[FileCleanupItem], int]:
        items: list[FileCleanupItem] = []
        file_total = 0
        for root, dirs, _ in os.walk(self._skill_dir):
            dirs.sort()
            hits = [d for d in dirs if _is_artifact_dir(d)]
            for d in hits:
                full_path = os.path.join(root, d)
                rel = self._relative_posix(full_path)
                if not self._git_ignore.is_ignored(rel + "/"):
                    continue
                total_size, file_count = _compute_dir_size(full_path)
                file_total += file_count
                items.append(_make_item(
                    full_path, total_size, "artifact",
                    f"过程产物目录: {d}（{file_count} 个文件）",
                    f"删除产物目录: {full_path}",
                    severity=SEVERITY_WARNING, is_directory=True))
            dirs[:] = [
                d for d in dirs
                if not _is_scan_excluded_dir(d, self._runtime_dirs)]
        return items, file_total
    def _detect_orphan_scripts(self: Self, all_files: list[str],
                               now: float | None = None,
                               reported: set[str] | None = None,
                               import_files: list[str] | None = None
                               ) -> list[FileCleanupItem]:
        if now is None:
            now = time.time()
        items: list[FileCleanupItem] = []
        py_files = [f for f in all_files if f.lower().endswith(".py")]
        if len(py_files) < 5:
            return items
        surface = py_files if import_files is None else list(
            dict.fromkeys(py_files + list(import_files)))
        py_stems = {os.path.splitext(os.path.basename(f))[0] for f in surface}
        imported_modules, contents, import_surface_complete = (
            _collect_imported_modules(surface, py_stems))
        if not import_surface_complete:
            _log.warning(
                "[FileCleaner] 导入面读取、解析或动态导入分析不完整，"
                "跳过孤立脚本判定")
            return []
        for fp in py_files:
            fname = os.path.basename(fp)
            if not self._is_orphan_candidate(fp, fname, imported_modules, reported):
                continue
            items.append(_orphan_script_item(
                fp, fname, contents.get(fp, ""), now))
        return items
    def _is_regular_package_member(self: Self, fp: str) -> bool:
        root = self._skill_dir.resolve()
        parent = Path(fp).resolve().parent
        if parent != root and root not in parent.parents:
            return False
        while parent != root and root in parent.parents:
            if (parent / "__init__.py").is_file():
                return True
            parent = parent.parent
        return (root / "__init__.py").is_file()
    def _is_orphan_candidate(self: Self, fp: str, fname: str,
                             imported_modules: set[str],
                             reported: set[str] | None) -> bool:
        if reported and fp in reported:
            return False
        if fname.casefold() in _PROTECTED_FILES_CASEFOLD:
            return False
        if _is_test_module_relpath(self._relative_posix(fp)):
            return False
        if self._is_regular_package_member(fp):
            return False
        module_name = os.path.splitext(fname)[0]
        return module_name not in imported_modules
    def _check_useless(self: Self, facts: _FileFacts,
                       report: FileCleanupReport) -> bool:
        if _is_empty_by_design(facts.fpath):
            return False
        if facts.size == 0 and self._confirm_zero_byte(facts, report):
            return True
        for check_fn, desc in _USELESS_PATTERNS:
            try:
                if check_fn(facts.fpath):
                    return self._report_file_item(
                        facts, report, "useless", desc,
                        f"删除此文件: {facts.file_path}")
            except OSError as e:
                _log.warning("[FileCleaner] 检测失败,跳过 %s: %s", facts.fpath, e)
        return False
    def _confirm_zero_byte(self: Self, facts: _FileFacts,
                           report: FileCleanupReport) -> bool:
        try:
            if facts.fpath.stat().st_size != 0:
                return False
        except OSError as e:
            _log.warning("[FileCleaner] 零字节确认失败,跳过 %s: %s", facts.fpath, e)
            return False
        return self._report_file_item(
            facts, report, "useless", "零字节空文件",
            f"删除此文件: {facts.file_path}")
    @staticmethod
    def _report_file_item(facts: _FileFacts, report: FileCleanupReport,
                          category: str, desc: str,
                          suggestion: str) -> bool:
        report.items.append(_make_item(
            facts.file_path, facts.size, category, desc, suggestion,
            age=facts.age))
        return True
    def _check_artifact(self: Self, facts: _FileFacts,
                        report: FileCleanupReport) -> bool:
        suffix = facts.fpath.suffix.lower()
        if suffix in _ARTIFACT_EXTENSIONS:
            return self._report_file_item(
                facts, report, "artifact",
                f"过程产物 ({facts.fpath.suffix})",
                f"删除过程产物: {facts.file_path}")
        if any(p.match(facts.fpath.name) for p in _LOG_PATTERNS):
            return self._report_file_item(
                facts, report, "artifact",
                f"日志文件: {facts.fpath.name}",
                f"删除日志文件: {facts.file_path}")
        return False
class _StubRule(NamedTuple):
    rule_id: str
    name: str
    severity: str
    description: str
    suggestion: str
_S01 = _StubRule(
    rule_id="S01",
    name="禁止自动添加兼容桩",
    severity="P0",
    description=(
        "迁移符号后，默认不加 `from new_loc import X` 兼容桩。"
        "直接更新所有消费者 import。仅当外部消费者或 10+ 内部消费者时才加，"
        "且须标注 `# TEMPORARY COMPAT STUB`"
    ),
    suggestion=("迁移符号后直接更新所有消费者 import，不加兼容桩；"
                "仅外部消费者或 10+ 内部消费者时加桩并标注 "
                "`# TEMPORARY COMPAT STUB`"),
)
_S02 = _StubRule(
    rule_id="S02",
    name="禁止纯门户文件",
    severity="P1",
    description=(
        "模块合并后，源文件不应保留为纯 re-export 门户。"
        "应删除原文件并更新所有消费者 import"
    ),
    suggestion="合并模块后删除原文件并更新所有消费者 import，不保留纯 re-export 门户",
)
_S03 = _StubRule(
    rule_id="S03",
    name="清理注释残留",
    severity="P2",
    description=(
        "重构完成后，清理 `# Re-export for...`、`# === Auto-fix ===` 等"
        "历史注释标记"
    ),
    suggestion="重构收尾时清理 `# Re-export for...` 等历史注释标记",
)
_STUB_RULES: tuple[_StubRule, ...] = (_S01, _S02, _S03)
S01_RULE = _S01.rule_id
S02_RULE = _S02.rule_id
S03_RULE = _S03.rule_id
STUB_CONSTRAINTS: list[dict] = [
    {
        "rule_id": rule.rule_id,
        "name": rule.name,
        "rule_name": rule.name,
        "severity": rule.severity,
        "description": rule.description,
        "suggestion": rule.suggestion,
        "category": "STUB",
    }
    for rule in _STUB_RULES
]
_REEXPORT_COMMENT_MARKERS = ("re-export", "reexport")
_AUTOFIX_COMMENT_MARKERS = ("auto-fix",)
_REEXPORT_NEG_PREFIXES = (
    "非", "不是", "并非", "无", "没有",
    "不使用", "不用", "不需要", "无需", "不许",
    "禁用", "禁止", "避免", "不允许", "不保留",
    "取消", "去掉", "移除", "删除",
)
_EN_REEXPORT_NEG_PREFIX_RE = re.compile(
    r"(?<![a-z])(?:not|no|no\s+longer|without|avoid(?:s|ed|ing)?|"
    r"skip(?:s|ped|ping)?|remove[sd]?|drop(?:s|ped|ping)?|"
    r"isn'?t|aren'?t|don'?t)(?:\s+an?\s+)?\s*$",
    re.IGNORECASE,
)
def _is_negated_reexport_occurrence(prefix_text: str) -> bool:
    tail = prefix_text[-16:] if len(prefix_text) > 16 else prefix_text
    stripped = tail.rstrip()
    for neg in _REEXPORT_NEG_PREFIXES:
        if stripped.endswith(neg):
            return True
    return bool(_EN_REEXPORT_NEG_PREFIX_RE.search(tail))
def _contains_reexport_marker(text: str) -> bool:
    low = text.lower()
    for marker in _REEXPORT_COMMENT_MARKERS:
        start = 0
        while (pos := low.find(marker, start)) != -1:
            if not _is_negated_reexport_occurrence(low[:pos]):
                return True
            start = pos + len(marker)
    return False
def _is_reexport_comment_line(line: str) -> bool:
    s = line.strip().lower()
    return s.startswith("#") and _contains_reexport_marker(s)
def _import_stmt_line_spans(tree: ast.Module) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    for node in walk_nodes(tree):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            spans.append((node.lineno, node.end_lineno or node.lineno))
    return spans
def _import_line_numbers(spans: Iterable[tuple[int, int]]) -> frozenset[int]:
    return frozenset(line for start, end in spans
                     for line in range(start, end + 1))
def _adjacent_from_spans(spans: Iterable[tuple[int, int]]) -> set[int]:
    adjacent: set[int] = set()
    for start, end in spans:
        adjacent.update(range(start, end + 1))
        adjacent.add(start - 1)
        adjacent.add(end + 1)
    return adjacent
def _is_reexport_marker_line(line: str, lineno: int,
                             import_adjacent: Container[int]) -> bool:
    return (lineno in import_adjacent
            and _is_reexport_comment_line(line))
def _is_autofix_comment_line(line: str) -> bool:
    s = line.strip().lower()
    if not s.startswith("#"):
        return False
    body = s.lstrip("#").strip("=-*~_ \t")
    return body.startswith(_AUTOFIX_COMMENT_MARKERS)
def _multiline_string_body_lines(tree: ast.Module) -> set[int]:
    return {line
            for start, end in multiline_string_spans(tree, include_joined=True)
            for line in range(start + 1, end + 1)}
def _is_legacy_comment_line(line: str, lineno: int,
                            import_adjacent: Container[int]) -> bool:
    return (_is_reexport_marker_line(line, lineno, import_adjacent)
            or _is_autofix_comment_line(line))
COMPAT_STUB = "COMPAT_STUB"
PORTAL_PURE = "PORTAL_PURE"
PORTAL_INIT = "PORTAL_INIT"
STUB_RESIDUE = "STUB_RESIDUE"
MIXED_PORTAL = "MIXED_PORTAL"
SEVERITY_ORDER = {
    COMPAT_STUB: 0,
    PORTAL_PURE: 1,
    PORTAL_INIT: 2,
    STUB_RESIDUE: 3,
    MIXED_PORTAL: 4,
}
_UNKNOWN_STUB_SEVERITY_RANK = max(SEVERITY_ORDER.values()) + 1
_IMPORT_STMT_PREFIX_RE = re.compile(r"(?:from|import)\s")
def _count_imports(lines: Iterable[str]) -> dict:
    count = 0
    import_lines = 0
    in_block = False
    depth = 0
    for line in lines:
        code = code_part(line).strip()
        segments = _match_import_segments(code)
        if segments:
            count += len(segments)
            import_lines += 1
            depth, in_block = _block_state(0, segments)
        elif in_block:
            import_lines += 1
            depth, in_block = _block_state(depth, [code])
    return {"count": count, "lines": import_lines}
def _block_state(depth: int, code_parts: Iterable[str]) -> tuple[int, bool]:
    parts = list(code_parts)
    depth += sum(net_paren_depth(part) for part in parts)
    return depth, depth > 0 or any(p.rstrip().endswith("\\")
                                   for p in parts)
def _match_import_segments(code_text: str) -> list[str]:
    return [seg.strip() for seg in code_text.split(";")
            if _IMPORT_STMT_PREFIX_RE.match(seg.strip())]
def _count_own_defs(tree: ast.AST) -> int:
    count = 0
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if node.name.startswith("__") and node.name.endswith("__"):
                continue
            count += 1
        elif isinstance(node, ast.ClassDef):
            count += 1
    return count
_SCOPE_CONTAINERS = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
_TRY_STATEMENT_TYPES = tuple(
    t for t in (ast.Try, getattr(ast, "TryStar", None)) if t is not None
)
_COMPOUND_FLOW_STATEMENTS = (
    ast.If, ast.While, ast.For, ast.AsyncFor, ast.With, ast.AsyncWith,
    ast.Match, *_TRY_STATEMENT_TYPES,
)
def _import_group_key(node: ast.stmt, alias: ast.alias) -> tuple:
    bound = alias.asname or alias.name
    if isinstance(node, ast.ImportFrom):
        return ("from", node.level, node.module or "", alias.name, bound)
    return ("import", 0, "", alias.name, bound)
_DuplicateImportOccurrence = tuple[
    ast.Import | ast.ImportFrom, ast.alias, tuple[int, ...]]
@dataclass
class _RedundantImportRecord:
    lines: list[int] = field(default_factory=list)
    occurrences: list[_DuplicateImportOccurrence] = field(default_factory=list)
class _ImportAnalysisDetails(list[str]):
    def __init__(self: Self) -> None:
        super().__init__()
        self.scope_records: list[dict[tuple, _RedundantImportRecord]] = []
def _format_redundant_import(key: tuple, lines_list: list[int]) -> str:
    kind, level, mod, name, bound = key
    shown = f"{name} as {bound}" if bound != name else name
    if kind == "from":
        return f"from {'.' * level}{mod} import {shown} (行 {lines_list})"
    return f"import {shown} (行 {lines_list})"
def _bind_assignment_target(target: ast.AST, names: set[str]) -> None:
    if isinstance(target, ast.Name):
        names.add(target.id)
    elif isinstance(target, (ast.Tuple, ast.List)):
        for element in target.elts:
            _bind_assignment_target(element, names)
    elif isinstance(target, ast.Starred):
        _bind_assignment_target(target.value, names)
def _is_star_import(node: ast.AST) -> bool:
    return (isinstance(node, ast.ImportFrom)
            and any(alias.name == "*" for alias in node.names))
def _collect_current_scope_bindings(
    node: ast.AST, names: set[str], annotations_evaluated: bool,
) -> None:
    if _is_star_import(node):
        names.add("*")
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return
    if isinstance(node, (*_SCOPE_CONTAINERS, ast.Lambda)):
        if not isinstance(node, ast.Lambda):
            names.add(node.name)
        expressions = list(
            iter_def_site_nodes(node)
            if annotations_evaluated or isinstance(node, ast.ClassDef)
            else definition_time_exprs(node))
        for expression in expressions:
            _collect_current_scope_bindings(
                expression, names, annotations_evaluated)
        return
    if isinstance(node, ast.NamedExpr):
        _bind_assignment_target(node.target, names)
    elif isinstance(node, ast.Assign):
        for target in node.targets:
            _bind_assignment_target(target, names)
    elif isinstance(node, ast.AnnAssign):
        if node.value is not None:
            _bind_assignment_target(node.target, names)
    elif isinstance(node, ast.AugAssign):
        _bind_assignment_target(node.target, names)
    elif isinstance(node, ast.Delete):
        for target in node.targets:
            _bind_assignment_target(target, names)
    elif isinstance(node, (ast.For, ast.AsyncFor)):
        _bind_assignment_target(node.target, names)
    elif isinstance(node, (ast.With, ast.AsyncWith)):
        for item in node.items:
            if item.optional_vars is not None:
                _bind_assignment_target(item.optional_vars, names)
    elif isinstance(node, (ast.ExceptHandler, ast.MatchAs, ast.MatchStar)) \
            and node.name:
        names.add(node.name)
    elif isinstance(node, ast.MatchMapping) and node.rest:
        names.add(node.rest)
    elif type(node).__name__ == "TypeAlias":
        # PEP 695 type 语句的绑定名在 name（ast.Name），节点没有 target 字段。
        names.add(node.name.id)
    for child in ast.iter_child_nodes(node):
        _collect_current_scope_bindings(child, names, annotations_evaluated)
def _import_key_binding_name(key: tuple) -> str:
    kind, _level, _module, name, bound = key
    if kind == "import" and bound == name:
        return name.split(".", 1)[0]
    return bound
def _compound_header_bindings(
    stmt: ast.stmt, names: set[str], annotations_evaluated: bool,
) -> None:
    """只收集进入复合语句体之前就已生效的绑定。

    分支体与处理器体内的重绑只影响各自路径，由 _scan_compound_import_path
    按路径合并；若在此处把整条语句的绑定一并清空 seen，兄弟分支的一次重绑
    会抹掉语句前已建立的导入历史，导致语句体内对既有导入的重复导入漏报。
    """
    if isinstance(stmt, (ast.If, ast.While)):
        _collect_current_scope_bindings(stmt.test, names, annotations_evaluated)
    elif isinstance(stmt, (ast.For, ast.AsyncFor)):
        _bind_assignment_target(stmt.target, names)
        _collect_current_scope_bindings(stmt.iter, names, annotations_evaluated)
    elif isinstance(stmt, (ast.With, ast.AsyncWith)):
        for item in stmt.items:
            _collect_current_scope_bindings(
                item.context_expr, names, annotations_evaluated)
            if item.optional_vars is not None:
                _bind_assignment_target(item.optional_vars, names)
    elif isinstance(stmt, ast.Match):
        _collect_current_scope_bindings(
            stmt.subject, names, annotations_evaluated)
        for case in stmt.cases:
            _collect_current_scope_bindings(
                case.pattern, names, annotations_evaluated)
            if case.guard is not None:
                _collect_current_scope_bindings(
                    case.guard, names, annotations_evaluated)
    elif isinstance(stmt, _TRY_STATEMENT_TYPES):
        for handler in stmt.handlers:
            if handler.name:
                names.add(handler.name)
def _invalidate_statement_rebindings(
    stmt: ast.stmt,
    seen: dict[tuple, list[int]],
    annotations_evaluated: bool,
) -> dict[tuple, list[int]]:
    names: set[str] = set()
    if isinstance(stmt, _COMPOUND_FLOW_STATEMENTS):
        _compound_header_bindings(stmt, names, annotations_evaluated)
    else:
        _collect_current_scope_bindings(stmt, names, annotations_evaluated)
    if not names:
        return seen
    if "*" in names:
        return {}
    return {
        key: list(lines) for key, lines in seen.items()
        if _import_key_binding_name(key) not in names
    }
def _copy_import_seen(seen: dict[tuple, list[int]]) -> dict[tuple, list[int]]:
    return {key: list(lines) for key, lines in seen.items()}
def _merge_guaranteed_imports(
    paths: list[dict[tuple, list[int]]],
) -> dict[tuple, list[int]]:
    if not paths:
        return {}
    first, *rest = paths
    return {
        key: sorted({line for path in paths for line in path[key]})
        for key in first
        if all(key in path for path in rest)
    }
def _record_scope_import(
    node: ast.Import | ast.ImportFrom,
    seen: dict[tuple, list[int]],
    found: dict[tuple, _RedundantImportRecord],
) -> None:
    for alias in node.names:
        key = _import_group_key(node, alias)
        binding = _import_key_binding_name(key)
        for previous_key in tuple(seen):
            if (previous_key != key
                    and _import_key_binding_name(previous_key) == binding):
                del seen[previous_key]
        lines = seen.setdefault(key, [])
        previous_lines = tuple(lines)
        lines.append(node.lineno)
        if len(lines) > 1:
            record = found.setdefault(key, _RedundantImportRecord())
            record.lines = sorted(set(record.lines + lines))
            record.occurrences.append((node, alias, previous_lines))
def _analyze_import_scope(
    body: list[ast.stmt], details: list[str],
    annotations_evaluated: bool | None = None,
) -> None:
    if annotations_evaluated is None:
        annotations_evaluated = not module_postpones_annotations(
            ast.Module(body=list(body), type_ignores=[]))
    found: dict[tuple, _RedundantImportRecord] = {}
    _scan_import_path(body, {}, found, details, annotations_evaluated)
    if isinstance(details, _ImportAnalysisDetails):
        details.scope_records.append(found)
    for key, record in found.items():
        details.append(_format_redundant_import(key, record.lines))
def _scan_import_branches(
    branches: list[list[ast.stmt]],
    seen: dict[tuple, list[int]],
    found: dict[tuple, list[int]],
    details: list[str],
    annotations_evaluated: bool,
) -> dict[tuple, list[int]]:
    paths = [
        _scan_import_path(
            branch, _copy_import_seen(seen), found, details,
            annotations_evaluated)
        for branch in branches
    ]
    return _merge_guaranteed_imports(paths)
def _scan_import_path(
    body: list[ast.stmt],
    seen: dict[tuple, list[int]],
    found: dict[tuple, list[int]],
    details: list[str],
    annotations_evaluated: bool,
) -> dict[tuple, list[int]]:
    for stmt in body:
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            if _is_star_import(stmt):
                seen = {}
            else:
                _record_scope_import(stmt, seen, found)
            continue
        seen = _invalidate_statement_rebindings(
            stmt, seen, annotations_evaluated)
        if isinstance(stmt, _SCOPE_CONTAINERS):
            _analyze_import_scope(
                stmt.body, details, annotations_evaluated)
        else:
            seen = _scan_compound_import_path(
                stmt, seen, found, details, annotations_evaluated)
    return seen
def _loop_body_has_break(body: list[ast.stmt]) -> bool:
    pending: list[ast.AST] = list(body)
    while pending:
        node = pending.pop()
        if isinstance(node, ast.Break):
            return True
        if isinstance(node, (ast.For, ast.AsyncFor, ast.While,
                             *_SCOPE_CONTAINERS, ast.Lambda)):
            continue
        pending.extend(ast.iter_child_nodes(node))
    return False
def _scan_compound_import_path(
    stmt: ast.stmt,
    seen: dict[tuple, list[int]],
    found: dict[tuple, list[int]],
    details: list[str],
    annotations_evaluated: bool,
) -> dict[tuple, list[int]]:
    if isinstance(stmt, ast.If):
        branches = [stmt.body, stmt.orelse or []]
        return _scan_import_branches(
            branches, seen, found, details, annotations_evaluated)
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        # with 体无异常时必然执行完，其导入对后续语句是既有导入，须延续 seen；
        # 体内重绑同样只会在该路径上移除对应导入。
        return _scan_import_path(
            stmt.body, seen, found, details, annotations_evaluated)
    if isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
        _scan_import_path(
            stmt.body, _copy_import_seen(seen), found, details,
            annotations_evaluated)
        if stmt.orelse:
            else_seen = _scan_import_path(
                stmt.orelse, _copy_import_seen(seen), found, details,
                annotations_evaluated)
            if not _loop_body_has_break(stmt.body):
                return else_seen
        return seen
    if isinstance(stmt, _TRY_STATEMENT_TYPES):
        return _scan_try_import_path(
            stmt, seen, found, details, annotations_evaluated)
    if isinstance(stmt, ast.Match):
        branches = [case.body for case in stmt.cases]
        exhaustive = any(
            isinstance(case.pattern, ast.MatchAs)
            and case.pattern.pattern is None and case.guard is None
            for case in stmt.cases
        )
        if not exhaustive:
            branches.append([])
        return _scan_import_branches(
            branches, seen, found, details, annotations_evaluated)
    return seen
def _scan_try_import_path(
    stmt: ast.Try,
    seen: dict[tuple, list[int]],
    found: dict[tuple, list[int]],
    details: list[str],
    annotations_evaluated: bool,
) -> dict[tuple, list[int]]:
    branches = [list(stmt.body) + list(stmt.orelse)]
    branches.extend(handler.body for handler in stmt.handlers)
    completed = _scan_import_branches(
        branches, seen, found, details, annotations_evaluated)
    if not stmt.finalbody:
        return completed
    final_entry = _merge_guaranteed_imports([completed, seen])
    _scan_import_path(
        stmt.finalbody, _copy_import_seen(final_entry), found, details,
        annotations_evaluated)
    return _scan_import_path(
        stmt.finalbody, _copy_import_seen(completed), {}, [],
        annotations_evaluated)
def _find_redundant_imports(tree: ast.Module) -> list[str]:
    details: list[str] = []
    _analyze_import_scope(tree.body, details)
    return details
def _find_module_getattr(
    tree: ast.Module,
) -> ast.FunctionDef | ast.AsyncFunctionDef | None:
    for node in tree.body:
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                and node.name == "__getattr__"):
            return node
    return None
def _has_value_return_in_current_scope(node: ast.AST) -> bool:
    for child in ast.iter_child_nodes(node):
        if isinstance(child, ast.Return):
            if child.value is not None:
                return True
            continue
        if isinstance(child, (*_SCOPE_CONTAINERS, ast.Lambda)):
            continue
        if _has_value_return_in_current_scope(child):
            return True
    return False
def _has_delayed_import_in_current_scope(
        node: ast.AST,
        dynamic_names: Container[str] = _DEFAULT_DYNAMIC_IMPORT_NAMES,
) -> bool:
    for child in ast.iter_child_nodes(node):
        if isinstance(child, (ast.Import, ast.ImportFrom)):
            return True
        if (isinstance(child, ast.Call)
                and _dynamic_import_name(child, dynamic_names) is not None):
            return True
        if isinstance(child, (*_SCOPE_CONTAINERS, ast.Lambda)):
            continue
        if _has_delayed_import_in_current_scope(child, dynamic_names):
            return True
    return False
def _has_only_imports(tree: ast.AST) -> bool:
    return all(_is_stub_allowed_stmt(node)
               for node in ast.iter_child_nodes(tree))
def _is_all_annotation(node: ast.AST) -> bool:
    return (isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name)
            and node.target.id == "__all__" and node.value is None)
def _is_stub_allowed_stmt(node: ast.AST) -> bool:
    return (isinstance(node, (ast.Import, ast.ImportFrom))
            or is_all_assignment(node)
            or _is_all_annotation(node)
            or is_docstring_stmt(node))
def _has_any_import(tree: ast.AST) -> bool:
    return any(isinstance(node, (ast.Import, ast.ImportFrom))
               for node in ast.iter_child_nodes(tree))
@dataclass(frozen=True)
class LineMarkers:
    import_lines: frozenset[int]
    import_adjacent: frozenset[int]
    string_body: frozenset[int]
    def has_marker_text(self, content: str) -> bool:
        low = content.lower()
        return any(marker in low for marker in _REEXPORT_COMMENT_MARKERS)
    def is_reexport_import_line(self, line: str, lineno: int) -> bool:
        if lineno not in self.import_lines:
            return False
        _, _, comment_part = line.strip().partition("#")
        return _contains_reexport_marker(comment_part)
    def is_reexport_marker_line(self, line: str, lineno: int) -> bool:
        if lineno in self.string_body:
            return False
        return _is_reexport_marker_line(line, lineno, self.import_adjacent)
    def is_legacy_comment(self, line: str, lineno: int) -> bool:
        if lineno in self.string_body:
            return False
        return _is_legacy_comment_line(
            line.strip(), lineno, self.import_adjacent)
@dataclass(frozen=True)
class ImportShape:
    import_count: int
    import_lines: int
    own_defs: int
    has_any_import: bool
    only_imports: bool
    module_getattr: ast.FunctionDef | ast.AsyncFunctionDef | None
    redundant_imports: tuple[str, ...]
def scan_line_markers(tree: ast.Module) -> LineMarkers:
    spans = _import_stmt_line_spans(tree)
    return LineMarkers(
        import_lines=_import_line_numbers(spans),
        import_adjacent=frozenset(_adjacent_from_spans(spans)),
        string_body=frozenset(_multiline_string_body_lines(tree)),
    )
def scan_import_shape(
    tree: ast.AST | None,
    lines: Iterable[str] = (),
) -> ImportShape:
    if tree is None:
        counters = _count_imports(lines)
        return ImportShape(
            import_count=counters["count"], import_lines=counters["lines"],
            own_defs=0, has_any_import=False, only_imports=False,
            module_getattr=None, redundant_imports=())
    spans = _import_stmt_line_spans(tree)
    return ImportShape(
        import_count=len(spans),
        import_lines=len(_import_line_numbers(spans)),
        own_defs=_count_own_defs(tree),
        has_any_import=_has_any_import(tree),
        only_imports=_has_only_imports(tree),
        module_getattr=_find_module_getattr(tree),
        redundant_imports=tuple(_find_redundant_imports(tree)),
    )
def get_stub_constraints() -> list[dict]:
    return [dict(c) for c in STUB_CONSTRAINTS]
def _scan_rule_lines(
    source: str,
    rule: _StubRule,
    message_prefix: str,
    predicate: Callable[[str, int], bool],
) -> list[dict]:
    return [
        {
            "rule_id": rule.rule_id,
            "severity": rule.severity,
            "line": lineno,
            "message": f"{message_prefix}: {line.strip()[:80]}",
        }
        for lineno, line in enumerate(aligned_source_lines(source), 1)
        if predicate(line, lineno)
    ]
def _is_pure_import_shell(shape: ImportShape) -> bool:
    return (shape.has_any_import and shape.import_count > 0
            and shape.own_defs == 0 and shape.only_imports)
def _check_s02_pure_portal(tree: ast.Module, filename: str) -> list[dict]:
    shape = scan_import_shape(tree)
    if filename.casefold() != "__init__.py" and _is_pure_import_shell(shape):
        return [{
            "rule_id": S02_RULE,
            "severity": _S02.severity,
            "line": 1,
            "message": f"纯门户文件（无自身定义，仅 import）: {filename}",
        }]
    return []
def _check_source_stub_violations(source: str, filename: str) -> list[dict]:
    tree, err = parse_py_source(source)
    if tree is None:
        _log.warning("[cleanup_file_hygiene] 语法解析失败跳过: %s: %s: %s",
                     filename, type(err).__name__, err)
        return []
    markers = scan_line_markers(tree)
    violations = _scan_rule_lines(
        source, _S01, "检测到 re-export 导入",
        markers.is_reexport_import_line)
    violations.extend(_check_s02_pure_portal(tree, filename))
    violations.extend(_scan_rule_lines(
        source, _S03, "历史注释残留", markers.is_legacy_comment))
    return violations
def check_stub_constraints_for_content(content: str,
                                       filename: str = "<content>") -> list[dict]:
    if not content or not content.strip():
        return []
    return _check_source_stub_violations(content, filename)
_RULE_TYPE_MAP = {
    S01_RULE: "REEXPORT_IMPORT",
    S02_RULE: "PORTAL_PURE",
    S03_RULE: "LEGACY_COMMENT",
}
def detect_new_compat_stubs(skill_dir: str,
                            changed_files: list[str] | None = None) -> list[dict]:
    findings: list[dict] = []
    changed_files = _normalize_changed_files(skill_dir, changed_files)
    for fpath in changed_files:
        _scan_file_stub_violations(fpath, findings)
    return findings
def _normalize_stub_filename(filename: str) -> str:
    return normalize_py_filename(filename or "") or "拟生成文件"
def _collect_stub_violations(content: str, label: str,
                             skill_dir: str) -> list:
    violations = list(check_stub_constraints_for_content(content, label))
    if skill_dir and os.path.isdir(skill_dir):
        try:
            violations.extend(detect_new_compat_stubs(skill_dir))
        except OSError:
            _log.warning("[check_stub_portal] 目录扫描失败: %s",
                         skill_dir, exc_info=True)
    return violations
def _stub_findings(violations: list) -> tuple[list, list, bool]:
    stub_suggestions = {c["rule_id"]: c["suggestion"]
                        for c in get_stub_constraints()}
    return collect_findings(
        (f"[{v.get('rule_id', 'S??')}] {v.get('message', '')}",
         v.get("rule_id", ""),
         f"{v.get('file')}:line:{v.get('line', 0)}" if v.get('file')
         else f"line:{v.get('line', 0)}",
         stub_suggestions.get(v.get("rule_id", "")),
         v.get("severity") == "P0")
        for v in violations)
def check_stub_portal(content: str = "", skill_dir: str | os.PathLike = "",
                      filename: str = "") -> PreinterventionResult:
    content = normalize_input(content, "check_stub_portal 参数 content")
    skill_dir = normalize_input(skill_dir, "check_stub_portal 参数 skill_dir",
                                 allow_path=True)
    filename = normalize_input(filename, "check_stub_portal 参数 filename")
    label = _normalize_stub_filename(filename)
    if content:
        _tree, parse_result = prepare_tree(content, "stub_portal_check")
        if parse_result is not None:
            return parse_result
    if skill_dir and not os.path.isdir(skill_dir):
        details, suggestions, _ = collect_findings([(
            f"技能目录不存在或不是目录: {skill_dir}",
            "INVALID_SKILL_DIR",
            f"path:{skill_dir}",
            "传入已存在的技能目录；仅检查 content 时将 skill_dir 留空",
            True,
        )])
        return finish_check(
            "stub_portal_check", "兼容桩/门户检查", False,
            SEVERITY_BLOCKING, details, suggestions)
    violations = _collect_stub_violations(content, label, skill_dir)
    if not violations:
        result = finish_check(
            "stub_portal_check", "兼容桩/门户检查", True,
            SEVERITY_INFO, [], [])
    else:
        details, suggestions, has_blocking = _stub_findings(violations)
        severity = SEVERITY_BLOCKING if has_blocking else SEVERITY_WARNING
        result = finish_check(
            "stub_portal_check", "兼容桩/门户检查", False, severity,
            details, suggestions)
    if result.passed:
        _log.debug("[preintervention] %s 通过（%d 项明细）",
                   result.check_name, len(result.details))
    else:
        _log.info("[preintervention] %s 未通过 severity=%s 明细 %d 项",
                  result.check_name, result.severity, len(result.details))
    return result
def _stub_portal_check_provider() -> dict:
    return {"stub_portal_check": check_stub_portal}
register_check_provider(_stub_portal_check_provider)
def _normalize_changed_files(skill_dir, changed_files) -> list:
    if changed_files is None:
        if not isinstance(skill_dir, (str, os.PathLike)) or not os.path.isdir(skill_dir):
            _log.warning("[cleanup_file_hygiene] 自动扫描 skill_dir 非目录"
                         "（增量检测降级空）: %r", skill_dir)
            return []
        return _collect_recent_py_files(skill_dir)
    if isinstance(changed_files, (str, bytes, os.PathLike)):
        files = [changed_files]
    else:
        try:
            files = list(changed_files)
        except TypeError:
            _log.warning("[cleanup_file_hygiene] changed_files 非可迭代形态"
                         "（增量检测降级空）: %r", changed_files)
            return []
    return [_resolve_changed_file(skill_dir, fpath) for fpath in files]
def _resolve_changed_file(skill_dir: Any, fpath: Any) -> Any:
    if not isinstance(fpath, (str, bytes, os.PathLike)):
        return fpath
    path = os.fsdecode(fpath)
    if (os.path.isabs(path)
            or not isinstance(skill_dir, (str, bytes, os.PathLike))):
        return path
    return os.path.normpath(os.path.join(os.fsdecode(skill_dir), path))
def _scan_file_stub_violations(fpath, findings: list[dict]) -> None:
    if not isinstance(fpath, (str, bytes, os.PathLike)):
        _log.debug("changed_files 含非路径形态条目（跳过）: %r", fpath)
        return
    fpath = os.fsdecode(fpath)
    if not fpath.lower().endswith(".py"):
        return
    content, err = read_py_source_with_error(fpath)
    if content is None:
        _log.debug("文件读取失败（跳过）: %s: %s", fpath, err)
        return
    fname = os.path.basename(fpath)
    for v in check_stub_constraints_for_content(content, fname):
        v["file"] = fpath
        v["type"] = _RULE_TYPE_MAP.get(v["rule_id"], v["rule_id"])
        findings.append(v)
def _collect_recent_py_files(skill_dir: str, window_s: float = 60.0) -> list:
    recent: list = []
    runtime_dirs = _runtime_asset_dirs(skill_dir)
    for root, dirs, files in os.walk(skill_dir):
        dirs[:] = _scannable_subdirs(dirs, runtime_dirs)
        for f in sorted(files):
            fp = _recent_py_file(root, f, window_s)
            if fp is not None:
                recent.append(fp)
    return recent
def _scannable_subdirs(
        dirs: list[str],
        runtime_dirs: Container[str] = _NO_RUNTIME_DIRS) -> list[str]:
    return sorted(
        d for d in dirs
        if d.lower() not in GATE_SCAN_IGNORE_DIRS_LOWER
        and not _is_scan_excluded_dir(d, runtime_dirs))
def _recent_py_file(root: str, filename: str,
                    window_s: float) -> str | None:
    if not filename.lower().endswith(".py"):
        return None
    fp = os.path.join(root, filename)
    return fp if _is_recent_file(fp, window_s) else None
def _is_recent_file(fp: str, window_s: float) -> bool:
    try:
        age_s = time.time() - os.path.getmtime(fp)
        return 0 <= age_s < window_s
    except OSError as e:
        _log.debug("文件状态探测失败（跳过）: %s: %s", fp, e)
        return False
def _append_stub_details(info: dict, details) -> None:
    capacity = max(0, _STUB_DETAIL_LIMIT - len(info["stub_details"]))
    if capacity:
        info["stub_details"].extend(list(details)[:capacity])
def _collect_reexport_comment_details(info: dict, markers: LineMarkers,
                                      content: str, lines: list) -> None:
    if not markers.has_marker_text(content):
        return
    reexport_comment_lines = [
        line.strip() for i, line in enumerate(lines, 1)
        if markers.is_reexport_marker_line(line, i)
    ]
    if not reexport_comment_lines:
        return
    info["has_reexport_comment"] = True
    _append_stub_details(
        info, (f"re-export 注释: {s[:100]}" for s in reexport_comment_lines))
def _detect_stub_indicators(
        info: dict, markers: LineMarkers, shape: ImportShape,
        content: str, lines: list,
        dynamic_names: Container[str] = _DEFAULT_DYNAMIC_IMPORT_NAMES,
) -> None:
    getattr_def = shape.module_getattr
    has_delayed_import = (
        getattr_def is not None
        and _has_value_return_in_current_scope(getattr_def)
        and _has_delayed_import_in_current_scope(
            getattr_def, dynamic_names))
    if has_delayed_import:
        info["has_getattr_stub"] = True
        if 1 <= getattr_def.lineno <= len(lines):
            _append_stub_details(
                info,
                [f"__getattr__: {lines[getattr_def.lineno - 1].strip()[:100]}"])
    _collect_reexport_comment_details(info, markers, content, lines)
    if shape.redundant_imports:
        info["has_redundant_import"] = True
        _append_stub_details(info, shape.redundant_imports)
def _detect_pure_reexport_portal(info: dict, filename: str,
                                  shape: ImportShape) -> None:
    if _is_pure_import_shell(shape) and not info["has_getattr_stub"]:
        info["is_pure_reexport"] = True
        info["stub_type"] = (
            PORTAL_INIT if (filename or "").casefold() == "__init__.py"
            else PORTAL_PURE)
def _apply_stub_classification(info: dict) -> None:
    if info["has_getattr_stub"]:
        info["stub_type"] = COMPAT_STUB
    elif (info["stub_type"] == "" and info["has_reexport_comment"]
            and info["own_defs"] > 0):
        info["stub_type"] = MIXED_PORTAL
    elif info["stub_type"] == "" and info["has_redundant_import"]:
        info["stub_type"] = STUB_RESIDUE
def _new_stub_info(filepath: str) -> dict:
    return {
        "filename": os.path.basename(filepath),
        "filepath": filepath,
        "total_lines": 0,
        "is_pure_reexport": False,
        "has_getattr_stub": False,
        "has_reexport_comment": False,
        "has_redundant_import": False,
        "stub_type": "",
        "stub_details": [],
        "scan_errors": [],
        "own_defs": 0,
        "import_count": 0,
    }
def analyze_file(filepath: str) -> dict:
    raw = (os.fspath(filepath)
           if isinstance(filepath, (str, os.PathLike)) else "")
    if not isinstance(raw, str) or not raw.strip():
        info = _new_stub_info("")
        error = f"路径非法: {filepath!r}"
        info["stub_details"].append(error)
        info["scan_errors"].append(error)
        return info
    filepath = raw
    info = _new_stub_info(filepath)
    content = _read_stub_content(filepath, info)
    if content is None:
        return info
    lines = aligned_source_lines(content)
    filename = info["filename"]
    info["total_lines"] = len(lines)
    detail_start = len(info["stub_details"])
    tree = parse_py_source_with_details(content, info["stub_details"])
    shape = scan_import_shape(tree, lines)
    info["import_count"] = shape.import_count
    if tree is None:
        parse_errors = info["stub_details"][detail_start:]
        info["scan_errors"].extend(
            parse_errors or ["语法解析失败，无法完整判定兼容桩/门户"])
        return info
    info["own_defs"] = shape.own_defs
    markers = scan_line_markers(tree)
    _detect_stub_indicators(
        info, markers, shape, content, lines,
        _dynamic_import_function_names(tree))
    _detect_pure_reexport_portal(info, filename, shape)
    _apply_stub_classification(info)
    return info
def _read_stub_content(filepath: str, info: dict) -> str | None:
    content, err = read_py_source_with_error(filepath)
    if content is None:
        _log.warning("[cleanup_file_hygiene] 读取失败 %s: %s", filepath, err)
        error = f"读取失败: {err}"
        info["stub_details"].append(error)
        info["scan_errors"].append(error)
    return content
def _emit_stub_scan_html(summary: dict, status: str | None = None) -> None:
    try:
        _payload = dict(summary)
        _payload["_step_name"] = "stub_scan"
        _payload["status"] = (
            summary.get("status", "completed") if status is None else status)
        _payload["summary"] = (
            f"{summary.get('total_py_files', 0)} 个 py 文件，"
            f"存量桩/门户 {summary.get('total_stubs', 0)} 个")
        generate_html_report(_payload, summary.get("skill_dir", ""), "step")
    except Exception as _e:  # noqa: BLE001 — 留痕失败不阻断扫描返回
        _log.warning("[cleanup_file_hygiene] HTML 报告生成失败(不阻断): %s", _e)
def _category_file_entry(entry: dict) -> dict:
    return {
        "filename": entry.get("rel_path") or entry["filename"],
        "total_lines": entry["total_lines"],
        "own_defs": entry["own_defs"],
        "import_count": entry["import_count"],
        "details": entry["stub_details"][:_STUB_DETAIL_LIMIT],
        "has_getattr_stub": entry["has_getattr_stub"],
        "is_pure_reexport": entry["is_pure_reexport"],
    }
def _build_categories_summary(skill_dir: str, results: list[dict],
                                total: int) -> dict:
    results.sort(key=lambda r: (
        SEVERITY_ORDER.get(r["stub_type"], _UNKNOWN_STUB_SEVERITY_RANK),
        r["filename"]))
    categories: dict[str, list[dict]] = defaultdict(list)
    for r in results:
        categories[r["stub_type"]].append(r)
    summary = {
        "skill_dir": skill_dir,
        "total_py_files": total,
        "total_stubs": len(results),
        "status": "completed",
        "categories": {},
    }
    for cat, files in categories.items():
        summary["categories"][cat] = {
            "count": len(files),
            "files": [_category_file_entry(f) for f in files],
        }
    return summary
def _degraded_scan_summary(skill_dir: str, error: str) -> dict:
    degraded = {"skill_dir": skill_dir, "total_py_files": 0,
                "total_stubs": 0, "status": "degraded",
                "error": error, "categories": {}}
    _emit_stub_scan_html(degraded)
    return degraded
def _collect_stub_infos(skill_dir: str, filenames: list[str],
                        scan_errors: list[str] | None = None) -> list[dict]:
    results: list[dict] = []
    for rel_path in filenames:
        info = analyze_file(os.path.join(skill_dir, rel_path))
        info["rel_path"] = rel_path.replace(os.sep, "/")
        if scan_errors is not None:
            scan_errors.extend(
                f"{info['rel_path']}: {error}"
                for error in info["scan_errors"])
        if info["stub_type"]:
            results.append(info)
    return results
def _log_scan_summary(total: int, results: list[dict], summary: dict) -> None:
    _log.info(
        "[cleanup_file_hygiene] scan_stubs 盘点完成: %d 个 py 文件, "
        "存量桩/门户 %d 个 (%s)",
        total, len(results),
        ", ".join(f"{cat}={cat_info['count']}"
                  for cat, cat_info in summary["categories"].items()) or "无分类",
    )
def scan_stubs(skill_dir: str | None = None) -> dict:
    if skill_dir is None:
        skill_dir = os.getcwd()
    else:
        raw = (os.fspath(skill_dir)
               if isinstance(skill_dir, (str, os.PathLike)) else "")
        if not isinstance(raw, str) or not raw.strip():
            _log.warning("[cleanup_file_hygiene] skill_dir 非法（降级空盘点）: %r",
                         skill_dir)
            return _degraded_scan_summary(
                "", f"skill_dir 非法: {skill_dir!r}")
        skill_dir = raw
    skill_dir = os.path.normpath(skill_dir)
    walk_errors: list[OSError] = []
    all_files = _list_py_files(skill_dir, walk_errors)
    if all_files is None:
        return _degraded_scan_summary(skill_dir, "目录不可达或不可读")
    total = len(all_files)
    scan_errors = [f"目录遍历失败: {error}" for error in walk_errors]
    results = _collect_stub_infos(skill_dir, all_files, scan_errors)
    summary = _build_categories_summary(skill_dir, results, total)
    if scan_errors:
        summary["status"] = "degraded"
        summary["error"] = "; ".join(scan_errors)
    _log_scan_summary(total, results, summary)
    _emit_stub_scan_html(summary)
    return summary
def _list_py_files(skill_dir: str,
                  walk_errors: list[OSError] | None = None) -> list[str] | None:
    if not os.path.isdir(skill_dir):
        _log.warning("[cleanup_file_hygiene] 目录不可达 %s", skill_dir)
        return None
    rel_paths: list[str] = []
    errors: list[OSError] = []
    runtime_dirs = _runtime_asset_dirs(skill_dir)
    for current, dirnames, filenames in os.walk(skill_dir,
                                               onerror=errors.append):
        dirnames[:] = sorted(_scannable_subdirs(dirnames, runtime_dirs))
        for filename in sorted(filenames):
            if filename.lower().endswith('.py'):
                rel_paths.append(os.path.relpath(
                    os.path.join(current, filename), skill_dir))
    if errors:
        _log.warning("[cleanup_file_hygiene] 目录部分不可达 %s: %s",
                     skill_dir, errors[0])
        if walk_errors is not None:
            walk_errors.extend(errors)
    return rel_paths
_CATEGORY_LABELS = {
    COMPAT_STUB: "兼容桩（__getattr__ 延迟导入）",
    PORTAL_PURE: "纯门户文件（纯 re-export）",
    PORTAL_INIT: "__init__.py 门户",
    STUB_RESIDUE: "兼容桩残留（重复 import）",
    MIXED_PORTAL: "混合门户（re-export 注释 + 业务逻辑）",
}
def print_report(summary: dict) -> None:
    sep = "=" * 80
    dash = "─" * 60
    print(sep)
    print("兼容桩和门户文件存量盘点报告")
    print(f"项目目录: {summary['skill_dir']}")
    print(sep)
    if summary.get("status") == "degraded":
        print("扫描状态: 降级（结果可能不完整）")
        if summary.get("error"):
            print(f"降级原因: {summary['error']}")
    print(f"总文件数: {summary['total_py_files']} 个py文件")
    print(f"发现兼容桩/门户文件: {summary['total_stubs']} 个")
    print()
    ordered = sorted(
        summary.get("categories", {}).items(),
        key=lambda kv: (
            SEVERITY_ORDER.get(kv[0], _UNKNOWN_STUB_SEVERITY_RANK), kv[0]))
    for cat_key, cat_info in ordered:
        _print_category_block(cat_key, cat_info, _CATEGORY_LABELS, dash)
def _print_category_block(cat_key: str, cat_info: dict,
                          label_map: dict, dash: str) -> None:
    print(f"\n{dash}")
    print(f"类别: {label_map.get(cat_key, cat_key)} ({cat_info['count']} 个文件)")
    print(dash)
    for entry in cat_info["files"]:
        _print_file_entry(entry)
def _print_file_entry(entry: dict) -> None:
    print(f"  {entry['filename']:40s} {entry['total_lines']:4d} 行  "
          f"defs:{entry['own_defs']:2d}  imports:{entry['import_count']:2d}")
    for detail in entry["details"]:
        print(f"    → {detail}")
    if entry.get("has_getattr_stub"):
        print("    → 有 __getattr__ 延迟导入")
    if entry.get("is_pure_reexport"):
        print("    → 纯 re-export 门户")

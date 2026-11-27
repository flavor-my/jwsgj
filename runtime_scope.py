from __future__ import annotations  # noqa: I001
import fnmatch
import functools
import hashlib
import importlib.util
import io
import logging
import os
import queue
import re
import sys
import tempfile
import threading
import tokenize
from collections.abc import Iterator
from concurrent.futures import (
    Future,
    InvalidStateError,
)
from concurrent.futures import (
    TimeoutError as _FutureTimeoutError,
)
from contextlib import contextmanager
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any
from jwsgj.diag_types_vocab import DIAG_REPORT_DIRNAME, PROJECT_ROOT_MARKERS
from jwsgj.log_config import log_swallowed
from jwsgj.skill_profile import (
    PROFILE_FILENAME,
    detect_layout,
    is_appledouble_basename,
    is_scan_py_name,
    is_temp_artifact_dir,
    is_test_source_name,
)
_LOGGER = logging.getLogger(__name__)
PY_SUFFIXES: frozenset[str] = frozenset({".py"})
PACKAGE_NAME: str = ((__package__ or "").split(".", 1)[0]
                     or Path(__file__).resolve().parent.name)
SKIP_DEPS_ENV_VAR: str = (
    "".join(ch if ch.isalnum() else "_" for ch in PACKAGE_NAME).upper()
    + "_SKIP_DEPS")
__all__ = [
    "AUDIT_SCAN_SKIP_DIRS",
    "BAK_NAME_RE",
    "CACHE_TEMP_DIR_NAMES",
    "DEFAULT_TEST_DIR_NAME",
    "DIAG_OUT_OF_SCOPE_DIRS",
    "FINGERPRINT_PRUNE_DIRS",
    "FINGERPRINT_PRUNE_DIRS_LOWER_NO_RUNTIME",
    "GATE_SCAN_IGNORE_DIRS",
    "GATE_SCAN_IGNORE_DIRS_LOWER",
    "GENERIC_ARCHIVE_ONLY_DIRS",
    "GENERIC_DIAG_OUT_OF_SCOPE_DIRS",
    "GENERIC_SCAN_IGNORE_DIRS_LOWER",
    "IDENT_NAME_RE",
    "LEGACY_BACKUP_DIR_NAME",
    "PACKAGE_EXCLUDE_DIR_NAMES",
    "PACKAGE_EXCLUDE_FILE_NAMES",
    "PACKAGE_EXCLUDE_FILE_PREFIXES",
    "PACKAGE_NAME",
    "PACKAGE_VERSION",
    "PRODUCTION_TEST_PREFIX_MODULES",
    "PROTECTED_CORE_FILES",
    "PY_SUFFIXES",
    "RUNTIME_ARTIFACT_SUFFIXES",
    "RUNTIME_DIR_NAME",
    "SCAN_COLLECT_PRUNE_DIRS",
    "SCAN_COLLECT_PRUNE_DIRS_LOWER",
    "SCAN_COLLECT_PRUNE_DIRS_LOWER_NO_RUNTIME",
    "SCAN_IGNORE_DIRS",
    "SCAN_IGNORE_DIRS_LOWER",
    "SCAN_IGNORE_DIRS_LOWER_NO_RUNTIME",
    "SCAN_SKIP_DIRS",
    "SKILL_LOG_DIR_NAME",
    "SKILL_PACKAGE_ALLOWED_HIDDEN",
    "SKILL_PACKAGE_REQUIRED_FILES",
    "SKIP_DEPS_ENV_VAR",
    "STATE_DIR_NAME",
    "SYS_TMP_ROOT",
    "TEST_ARTIFACT_DIRS",
    "TEST_DIR_CANDIDATES",
    "TEST_DIR_CANDIDATES_LOWER",
    "DependencyGraph",
    "adaptive_workers",
    "call_with_timeout",
    "canonical_path",
    "coerce_skill_dir",
    "collect_baseline_py_files",
    "collect_gate_scan_files",
    "collect_migration_py_files",
    "collect_py_files",
    "collect_py_files_default",
    "collect_python_files",
    "collect_scan_py_files",
    "count_py_files_under",
    "count_test_files",
    "cycle_member_groups",
    "detect_cycles",
    "detect_layout",
    "expand_git_bash_path",
    "import_key",
    "is_appledouble_basename",
    "is_archive_or_cache_path",
    "is_audit_skip_dir",
    "is_backup_artifact_name",
    "is_backup_like_dir",
    "is_backup_path",
    "is_backup_snapshot_dir",
    "is_baseline_py_file",
    "is_diagnosis_out_of_scope",
    "is_generic_archive_or_cache_path",
    "is_out_of_scope_dir",
    "is_package_excluded_file",
    "is_pruned_dirname",
    "is_pruned_scan_dir",
    "is_py_source_file",
    "is_real_skill_dir",
    "is_runtime_log_artifact",
    "is_runtime_temp_path",
    "is_scan_excluded",
    "is_scan_py_name",
    "is_scan_scope_path",
    "is_temp_artifact_dir",
    "is_temp_root_path",
    "is_test_caller_name",
    "is_test_dir_candidate",
    "is_test_dir_name",
    "is_test_dir_path",
    "is_test_file_path",
    "is_test_scan_asset",
    "is_test_source_basename",
    "is_transient_module_name",
    "is_under_root",
    "is_unregistered_package_root_file",
    "isolated_import_scope",
    "iter_baseline_py_dirs",
    "iter_diagnosis_scan_targets",
    "iter_prod_py_files",
    "iter_py_files",
    "iter_py_files_under",
    "iter_py_source_files",
    "iter_scan_py_files",
    "iter_skill_py_files",
    "keep_inventory_dir",
    "normalize_skill_dir",
    "normalize_text",
    "parse_timeout_env",
    "prune_ignore_dirs",
    "prune_scan_dirnames",
    "prune_walk_dirs",
    "py_stem",
    "read_diagnostic_source_strict",
    "relative_module_base",
    "resolve_finding_file_path",
    "resolve_internal_dependency",
    "resolve_scan_root",
    "resolve_search_root",
    "resolve_skill_relative_path",
    "rglob_paths_tolerant",
    "safe_ns",
    "safe_relpath",
    "scan_exclude_dirs",
    "scan_prune_dirs",
    "skill_root_of",
    "source_fingerprint",
    "strip_stale_coding_declaration",
    "tarjan_scc",
    "validate_source_paths",
    "verify_isolated_import",
]
def safe_ns(name: str) -> str:
    cleaned = "".join(c for c in name if c not in '\\/:*?"<>|' and ord(c) >= 32)
    cleaned = cleaned.strip()
    if not cleaned or cleaned.strip(".") == "":
        return "_unnamed_skill"
    return cleaned
RUNTIME_DIR_NAME = "Temp"
JSON_ROOT_DIR_NAME = DIAG_REPORT_DIRNAME
TEST_DIR_CANDIDATES: tuple[str, ...] = ("test", "tests")
TEST_DIR_CANDIDATES_LOWER: frozenset[str] = frozenset(TEST_DIR_CANDIDATES)
TEST_ARTIFACT_DIRS: frozenset[str] = (
    TEST_DIR_CANDIDATES_LOWER | {"fixtures"})
DEFAULT_TEST_DIR_NAME: str = "tests"
_DEFAULT_INCLUDE_TESTS = False
def is_test_dir_candidate(name: str) -> bool:
    return str(name or "").lower() in TEST_DIR_CANDIDATES_LOWER
STATE_DIR_NAME = "jinhua"
_SKILL_RUNTIME_LOG_DIR = "log"
SKILL_LOG_DIR_NAME: str = _SKILL_RUNTIME_LOG_DIR
_SKILL_REFERENCE_DIR_NAME = "cankaowendang"
_SKILL_SCRATCH_DIR_NAME = "_notes"
_SKILL_ONLY_SCAN_DIR_NAMES_LOWER = frozenset({
    STATE_DIR_NAME.lower(), _SKILL_RUNTIME_LOG_DIR, _SKILL_REFERENCE_DIR_NAME,
    _SKILL_SCRATCH_DIR_NAME,
})
LEGACY_BACKUP_DIR_NAME = "jwsgj_backups"
SCAN_IGNORE_DIRS = frozenset((
    "__pycache__", "node_modules", ".git", "venv", ".venv",
    RUNTIME_DIR_NAME, "_cache", "_intermediate", "htmlcov", "env", "env3",
    "dist", "build", STATE_DIR_NAME, _SKILL_SCRATCH_DIR_NAME,
    JSON_ROOT_DIR_NAME, "htm", "report_34",
))
SCAN_IGNORE_DIRS_LOWER = frozenset(s.lower() for s in SCAN_IGNORE_DIRS)
SCAN_IGNORE_DIRS_LOWER_NO_RUNTIME = frozenset(
    s.lower() for s in SCAN_IGNORE_DIRS if s != RUNTIME_DIR_NAME)
GENERIC_SCAN_IGNORE_DIRS_LOWER = frozenset(
    SCAN_IGNORE_DIRS_LOWER - _SKILL_ONLY_SCAN_DIR_NAMES_LOWER)
SCAN_COLLECT_PRUNE_DIRS = frozenset(SCAN_IGNORE_DIRS) | {
    _SKILL_RUNTIME_LOG_DIR, _SKILL_REFERENCE_DIR_NAME,
}
SCAN_COLLECT_PRUNE_DIRS_LOWER = frozenset(
    s.lower() for s in SCAN_COLLECT_PRUNE_DIRS)
SCAN_COLLECT_PRUNE_DIRS_LOWER_NO_RUNTIME = frozenset(
    s.lower() for s in SCAN_COLLECT_PRUNE_DIRS if s != RUNTIME_DIR_NAME)
GATE_SCAN_IGNORE_DIRS = frozenset(SCAN_IGNORE_DIRS) | TEST_ARTIFACT_DIRS
GATE_SCAN_IGNORE_DIRS_LOWER = frozenset(
    s.lower() for s in GATE_SCAN_IGNORE_DIRS)
AUDIT_SCAN_SKIP_DIRS = frozenset((
    "__pycache__", ".rundata", ".safe_ops_backups", ".refactor_backups",
    RUNTIME_DIR_NAME, "mutation", JSON_ROOT_DIR_NAME, "htm", "report_34",
))
_AUDIT_SCAN_SKIP_DIRS_LOWER = frozenset(
    name.lower() for name in AUDIT_SCAN_SKIP_DIRS)
SCAN_SKIP_DIRS = frozenset({RUNTIME_DIR_NAME.lower(), _SKILL_RUNTIME_LOG_DIR,
                           STATE_DIR_NAME, "baselines",
                           JSON_ROOT_DIR_NAME, "htm"})
_SOURCE_SCAN_PRUNE_DIRS_LOWER = (
    SCAN_COLLECT_PRUNE_DIRS_LOWER | SCAN_SKIP_DIRS)
def _is_collectable_dir(d: str, lower_view: frozenset) -> bool:
    return (not d.startswith((".", "__"))
            and d != RUNTIME_DIR_NAME
            and d.lower() not in lower_view
            and not is_temp_artifact_dir(d))
def is_real_skill_dir(base: str) -> bool:
    base = _coerce_dir_arg(base)
    try:
        if not os.path.isdir(base):
            return False
        if (os.path.isfile(os.path.join(base, "SKILL.md"))
                or os.path.isfile(os.path.join(base, "__init__.py"))):
            return True
        return _has_live_py(base)
    except OSError as e:
        _LOGGER.debug("[temp_base] 真实目录判定 IO 异常（按 fake 拒绝）: %s: %s", base, e)
        return False
def skill_root_of(target_path: Any, *, include_profile_declaration: bool = False) -> str:
    target_path = _coerce_dir_arg(target_path)
    if not target_path.strip():
        return ""
    current = (os.path.abspath(target_path) if os.path.isdir(target_path)
               else os.path.dirname(os.path.abspath(target_path)))
    while True:
        if (os.path.isfile(os.path.join(current, "SKILL.md"))
                or (include_profile_declaration
                    and os.path.isfile(os.path.join(current, PROFILE_FILENAME)))):
            return current
        parent = os.path.dirname(current)
        if parent == current:
            return ""
        current = parent
def _has_live_py(base: str) -> bool:
    prune_view = _scan_dirs_for_root(
        base, SCAN_COLLECT_PRUNE_DIRS_LOWER_NO_RUNTIME)
    for _root, dirs, files in os.walk(base, onerror=_on_walk_error):
        dirs[:] = [d for d in dirs
                   if _is_collectable_dir(d, prune_view)]
        if any(is_scan_py_name(f) for f in files):
            return True
    return False
_TEMP_ROOT_CACHE: dict[str, str] = {}
def _system_temp_root() -> str:
    raw = os.path.abspath(tempfile.gettempdir())
    cached = _TEMP_ROOT_CACHE.get(raw)
    if cached is not None:
        return cached
    value = os.path.realpath(raw).replace("\\", "/").lower().rstrip("/")
    if len(_TEMP_ROOT_CACHE) >= 8:
        _TEMP_ROOT_CACHE.clear()
    _TEMP_ROOT_CACHE[raw] = value
    return value
SYS_TMP_ROOT = _system_temp_root()
BAK_NAME_RE = re.compile(
    r"(?:\.bak(?:[_.][^/\\]*)?|\.mutation_backup_\d+)$", re.IGNORECASE)
IDENT_NAME_RE = re.compile(r"^[a-zA-Z_][a-zA-Z0-9_]*$")
def is_backup_artifact_name(name: str) -> bool:
    return bool(BAK_NAME_RE.search(str(name)))
@functools.lru_cache(maxsize=8192)
def _canonical_path_cached(abs_path: str) -> str:
    return os.path.normcase(os.path.realpath(abs_path))
def canonical_path(path: str) -> str:
    """路径规范形式：``abspath`` → ``realpath`` → ``normcase``。

    Windows 上 ``os.path.realpath`` 每次都要开句柄走
    ``GetFinalPathNameByHandle``，单次约 0.2–0.3 ms；同一轮治理会对同一批
    目录（工作区根、技能根、Temp、zhenduan）反复规范化。实测单批次
    17,245 次调用只对应 1,855 个不同路径（去重率 89.24%），累计 3.955 s、
    占墙钟 6.36%。本函数是纯函数，按绝对路径记忆化即可消除全部重复。

    约定：先 ``abspath`` 再进缓存，故缓存键已含当前工作目录，cwd 变化
    不会命中陈旧结果。
    """
    return _canonical_path_cached(os.path.abspath(str(path)))
canonical_path.cache_clear = _canonical_path_cached.cache_clear
canonical_path.cache_info = _canonical_path_cached.cache_info
canonical_path.cache_parameters = _canonical_path_cached.cache_parameters
def is_runtime_temp_path(path: str) -> bool:
    try:
        p = canonical_path(path).replace("\\", "/").lower()
    except (OSError, ValueError) as e:
        _LOGGER.debug("[temp_path] 路径归一失败（按非 Temp 段判定）: %s: %s", path, e)
        return False
    sys_tmp = _system_temp_root()
    if p.startswith(sys_tmp + "/"):
        p = p[len(sys_tmp) + 1:]
    return "temp" in p.split("/")
DIAG_OUT_OF_SCOPE_DIRS = frozenset((
    "__pycache__", ".pytest_cache",
    _SKILL_RUNTIME_LOG_DIR, _SKILL_REFERENCE_DIR_NAME,
    STATE_DIR_NAME, _SKILL_SCRATCH_DIR_NAME, "htmlcov", "node_modules",
)) | TEST_ARTIFACT_DIRS
GENERIC_DIAG_OUT_OF_SCOPE_DIRS = frozenset(
    DIAG_OUT_OF_SCOPE_DIRS - _SKILL_ONLY_SCAN_DIR_NAMES_LOWER)
_BACKUP_TS_SUFFIX_RE = re.compile(
    r"^(?:.+?[_-])?backup[_-]?(?:\d{8}(?:[-_]\d{4,6})?|\d{12,17})$",
    re.IGNORECASE)
_BACKUP_DIR_SUFFIXES: tuple[str, ...] = ("_backups", "-backups")
_BACKUP_DIR_LITERALS: frozenset[str] = frozenset({"backups", "_backups"})
def is_backup_snapshot_dir(name: str) -> bool:
    n = str(name or "").lower()
    return (n.startswith(("_backup", "backup_pre_fix"))
            or n in _BACKUP_DIR_LITERALS
            or n.endswith(_BACKUP_DIR_SUFFIXES)
            or bool(_BACKUP_TS_SUFFIX_RE.match(n)))
_OUT_OF_SCOPE_DIR_NAMES = frozenset(
    s.lower() for s in DIAG_OUT_OF_SCOPE_DIRS | {RUNTIME_DIR_NAME}
    if s.lower() != _SKILL_RUNTIME_LOG_DIR)
RUNTIME_ARTIFACT_SUFFIXES: tuple[str, ...] = (".log", ".jsonl")
_RUNTIME_ARTIFACT_LOCK_SUFFIXES: tuple[str, ...] = tuple(
    f"{suffix}.lock" for suffix in RUNTIME_ARTIFACT_SUFFIXES)
def is_runtime_log_artifact(name: str) -> bool:
    lowered = str(name).lower()
    return (lowered.endswith(RUNTIME_ARTIFACT_SUFFIXES)
            or lowered.endswith(_RUNTIME_ARTIFACT_LOCK_SUFFIXES))
def is_out_of_scope_dir(name: str) -> bool:
    lowered = name.lower()
    return (lowered.startswith('.') or lowered in _OUT_OF_SCOPE_DIR_NAMES
            or is_backup_snapshot_dir(lowered))
def is_temp_root_path(path: str) -> bool:
    try:
        tmp_l = _system_temp_root()
        root = os.path.realpath(os.path.abspath(str(path)))
    except Exception as e:  # noqa: BLE001 —— gettempdir 环境敏感异常软降级，不阻断主流程
        _LOGGER.debug("[temp_root] 临时根探测失败（按非临时根判定）: %s: %s", path, e)
        return False
    root_l = root.replace("\\", "/").lower().rstrip("/")
    if root_l == tmp_l or root_l.startswith(tmp_l + "/"):
        return True
    return any(seg.startswith("pytest-of-") for seg in root_l.split("/"))
def is_audit_skip_dir(name: str) -> bool:
    return (name.lower() in _AUDIT_SCAN_SKIP_DIRS_LOWER
            or name.startswith(".")
            or is_backup_snapshot_dir(name))
def is_backup_like_dir(name: str) -> bool:
    n = str(name or "").lower()
    return "backup" in n or is_backup_snapshot_dir(n)
PRODUCTION_TEST_PREFIX_MODULES: frozenset = frozenset()
def is_py_source_file(fname: str) -> bool:
    base = os.path.basename(str(fname or ""))
    return (base.lower().endswith(".py")
            and not is_appledouble_basename(base))
def is_test_source_basename(base: str) -> bool:
    b = (base or "").lower()
    if b.removesuffix(".py") in PRODUCTION_TEST_PREFIX_MODULES:
        return False
    return is_test_source_name(b)
_SNAPSHOT_NAME_RE = re.compile(
    r"_(?:backup_|bak(?:\d+)?(?:[._]|$)|orig_|fixed_)", re.IGNORECASE)
_TRANSIENT_TEST_PREFIXES = ("_test_", "test_")
_STANDARD_DUNDER_MODULES = frozenset({"__init__.py", "__main__.py"})
def is_transient_module_name(name: str) -> bool:
    base = os.path.basename(str(name or ""))
    if base.startswith("__") and base not in _STANDARD_DUNDER_MODULES:
        return True
    lower = base.lower()
    if _SNAPSHOT_NAME_RE.search(base):
        return True
    return lower.startswith(_TRANSIENT_TEST_PREFIXES)
def _norm_segments(path: str) -> list[str]:
    return [s.lower()
            for s in str(path or "").replace("\\", "/").split("/") if s]
def _has_backup_snapshot_segment(segs) -> bool:
    return any(is_backup_snapshot_dir(seg) for seg in segs)
_OUT_OF_SCOPE_MEMO: dict[tuple, bool] = {}
_OUT_OF_SCOPE_MEMO_MAX = 50000
def _memo_verdict(memo: dict, limit: int, key, verdict, *args):
    cached = memo.get(key)
    if cached is not None:
        return cached
    result = verdict(*args)
    if len(memo) >= limit:
        memo.clear()
    memo[key] = result
    return result
def is_diagnosis_out_of_scope(path: str, root_dir: str | os.PathLike | None = None) -> bool:
    key = path or ""
    if not key:
        return False
    if root_dir is None:
        memo_key = (key, PRODUCTION_TEST_PREFIX_MODULES)
        excluded_dirs = DIAG_OUT_OF_SCOPE_DIRS
        probe = key
    else:
        probe = _scan_probe_path(key, root_dir)
        memo_key = (probe, _is_skill_scan_root(root_dir),
                    PRODUCTION_TEST_PREFIX_MODULES, key)
        excluded_dirs = _scan_dirs_for_root(root_dir, DIAG_OUT_OF_SCOPE_DIRS)
    return _memo_verdict(_OUT_OF_SCOPE_MEMO, _OUT_OF_SCOPE_MEMO_MAX, memo_key,
                         _out_of_scope_verdict, probe, excluded_dirs, key)
def _out_of_scope_verdict(
        key: str, excluded_dirs, runtime_key: str | None = None) -> bool:
    segs = _norm_segments(key)
    base = segs[-1] if segs else ""
    if any(seg in excluded_dirs or _is_test_dir_seg(seg) for seg in segs):
        return True
    if is_backup_path(key):
        return True
    if _is_hidden_basename(base):
        return True
    if is_test_source_basename(base):
        return True
    # conftest.py 是 pytest 配置文件，与 is_test_file_path 保持一致：
    # 生产扫描不应把根目录/包目录下的 conftest.py 当作业务代码。
    if base == "conftest.py":
        return True
    return is_runtime_temp_path(key if runtime_key is None else runtime_key)
def _is_hidden_basename(name: str) -> bool:
    return str(name or "").startswith(".")
def _is_test_dir_seg(seg: str) -> bool:
    return (seg in TEST_ARTIFACT_DIRS
            or seg.endswith("_tests"))
def is_test_dir_path(filepath: str) -> bool:
    segs = _norm_segments(filepath)
    return bool(segs) and any(_is_test_dir_seg(seg) for seg in segs[:-1])
def is_test_file_path(filepath: str) -> bool:
    segs = _norm_segments(filepath)
    if not segs:
        return False
    if is_test_dir_path(filepath):
        return True
    return is_test_source_basename(segs[-1]) or segs[-1] == "conftest.py"
def is_test_caller_name(caller: str, functions: dict) -> bool:
    if not caller:
        return False
    caller = str(caller)
    if caller.startswith("<"):
        return "test" in caller.lower()
    if _test_name_segments(caller.split(".")):
        return True
    return _test_filepath_caller(caller, functions)
def _test_name_segments(segs) -> bool:
    if not segs:
        return False
    if is_test_source_basename(segs[-1] + ".py") or segs[-1] == "conftest":
        return True
    return any(s in TEST_ARTIFACT_DIRS or s.startswith("test_")
               for s in segs[:-1])
def _test_filepath_caller(caller: str, functions: dict) -> bool:
    fnode = functions.get(caller)
    if fnode is None:
        return False
    filepath = str(getattr(fnode, "filepath", "") or "")
    return is_test_file_path(filepath)
_TEST_DIR_NAME_TOKENS = frozenset(TEST_ARTIFACT_DIRS | {"testing"})
def is_test_dir_name(name: str) -> bool:
    if not isinstance(name, str):
        return False
    return not _TEST_DIR_NAME_TOKENS.isdisjoint(
        re.split(r"[^a-z0-9]+", name.lower()))
_ARCHIVE_ONLY_DIRS = frozenset(DIAG_OUT_OF_SCOPE_DIRS - TEST_ARTIFACT_DIRS)
GENERIC_ARCHIVE_ONLY_DIRS = frozenset(
    GENERIC_DIAG_OUT_OF_SCOPE_DIRS
    - (TEST_ARTIFACT_DIRS | {_SKILL_RUNTIME_LOG_DIR}))
FINGERPRINT_PRUNE_DIRS = frozenset(SCAN_IGNORE_DIRS) | DIAG_OUT_OF_SCOPE_DIRS
FINGERPRINT_PRUNE_DIRS_LOWER_NO_RUNTIME = frozenset(
    s.lower() for s in FINGERPRINT_PRUNE_DIRS if s != RUNTIME_DIR_NAME)
def _match_archive_or_cache(
        key: str, archive_dirs: frozenset[str],
        runtime_key: str | None = None) -> bool:
    segs = _norm_segments(key)
    if any(seg in archive_dirs for seg in segs):
        return True
    if is_backup_path(key):
        return True
    return is_runtime_temp_path(key if runtime_key is None else runtime_key)
def is_archive_or_cache_path(path: str, root_dir: str | os.PathLike | None = None) -> bool:
    key = path or ""
    if not key:
        return False
    if root_dir is None:
        return _match_archive_or_cache(key, _ARCHIVE_ONLY_DIRS)
    archive_dirs = _scan_dirs_for_root(root_dir, _ARCHIVE_ONLY_DIRS)
    return _match_archive_or_cache(
        _scan_probe_path(key, root_dir), archive_dirs, key)
def is_generic_archive_or_cache_path(path: str) -> bool:
    key = path or ""
    if not key:
        return False
    return _match_archive_or_cache(key, GENERIC_ARCHIVE_ONLY_DIRS)
def _fingerprint_candidate(fname: str) -> bool:
    return is_scan_py_name(fname) and not is_test_source_basename(fname)
def read_diagnostic_source_strict(path: str) -> str:
    with open(path, "rb") as f:
        data = f.read()
    try:
        enc = tokenize.detect_encoding(io.BytesIO(data).readline)[0]
    except (SyntaxError, LookupError) as _e:
        log_swallowed(__name__, _e, context='read_diagnostic_source_strict:SyntaxError')
        raise UnicodeDecodeError(
            "python-source", data, 0, min(1, len(data)),
            f"非法 Python 编码声明: {_e}") from _e
    text = data.decode(enc)
    return text.replace("\r\n", "\n").replace("\r", "\n")
def source_fingerprint(skill_dir: str) -> tuple[int, str]:
    skill_dir = _coerce_dir_arg(skill_dir)
    h = hashlib.md5(usedforsecurity=False)
    n = 0
    prune_view = _scan_dirs_for_root(
        skill_dir, FINGERPRINT_PRUNE_DIRS_LOWER_NO_RUNTIME)
    for root, dirs, files in os.walk(skill_dir, onerror=_on_walk_error):
        _prune_collectable_dirs(dirs, prune_view)
        dirs.sort()
        for fname in sorted(files):
            if not _fingerprint_candidate(fname):
                continue
            if _hash_file_into(h, os.path.join(root, fname), skill_dir):
                n += 1
    return n, h.hexdigest()
def _hash_file_into(h, fpath: str, skill_dir: str) -> bool:
    try:
        with open(fpath, "rb") as fh:
            _rel = os.path.relpath(fpath, skill_dir).replace("\\", "/")
            h.update(_rel.encode("utf-8", "replace"))
            h.update(b"\x00")
            h.update(fh.read())
            h.update(b"\x00")
        return True
    except OSError as e:
        _LOGGER.debug("文件读取失败（跳过）: %s: %s", fpath, e)
        return False
_INVENTORY_EXCLUDED_DIRS = (frozenset(SCAN_COLLECT_PRUNE_DIRS)
                           | TEST_ARTIFACT_DIRS)
_INVENTORY_EXCLUDED_DIRS_LOWER = frozenset(
    name.lower() for name in _INVENTORY_EXCLUDED_DIRS)
def keep_inventory_dir(dirname: str) -> bool:
    if not isinstance(dirname, str):
        return False
    return (_is_collectable_dir(dirname, _INVENTORY_EXCLUDED_DIRS_LOWER)
            and not is_backup_snapshot_dir(dirname))
def _prune_collectable_dirs(dirs: list[str], skip) -> None:
    dirs[:] = [d for d in dirs
               if _is_collectable_dir(d, skip)
               and not is_backup_snapshot_dir(d)]
def prune_ignore_dirs(
        dirs: list[str], root_dir: str | os.PathLike | None = None) -> None:
    skip = (SCAN_IGNORE_DIRS_LOWER_NO_RUNTIME if root_dir is None
            else _scan_dirs_for_root(
                root_dir, SCAN_IGNORE_DIRS_LOWER_NO_RUNTIME))
    _prune_collectable_dirs(dirs, skip)
def iter_py_files_under(dir_path: str) -> Iterator[str]:
    dir_path = _coerce_dir_arg(dir_path)
    skip = _scan_dirs_for_root(dir_path, SCAN_IGNORE_DIRS_LOWER_NO_RUNTIME)
    for root, dirs, fnames in os.walk(dir_path, onerror=_on_walk_error):
        _prune_collectable_dirs(dirs, skip)
        for fn in fnames:
            if fn.lower().endswith(".py") and not fn.startswith("."):
                yield os.path.join(root, fn)
def prune_walk_dirs(
        dirs: list[str], root_dir: str | os.PathLike | None = None) -> None:
    skip = (GATE_SCAN_IGNORE_DIRS_LOWER if root_dir is None
            else _scan_dirs_for_root(root_dir, GATE_SCAN_IGNORE_DIRS_LOWER))
    prune_scan_dirnames(dirs, skip)
_DIAG_PRUNE_DIRS_LOWER = frozenset(s.lower() for s in FINGERPRINT_PRUNE_DIRS)
_DIAG_PRUNE_DIRS_LOWER_NO_TESTS = frozenset(
    _DIAG_PRUNE_DIRS_LOWER - TEST_ARTIFACT_DIRS)
def is_pruned_dirname(name: str, *, prune_tests: bool = False) -> bool:
    skip = (_DIAG_PRUNE_DIRS_LOWER if prune_tests
            else _DIAG_PRUNE_DIRS_LOWER_NO_TESTS)
    return is_pruned_scan_dir(name, skip)
_BACKUP_PATH_RE = re.compile(r"(^|[\\/])_[^\\/]*backup[^\\/]*([\\/]|$)", re.IGNORECASE)
def is_backup_path(fp: str) -> bool:
    norm = str(fp or "").replace("\\", "/")
    if _BACKUP_PATH_RE.search(norm):
        return True
    return any(is_backup_snapshot_dir(seg) for seg in norm.split("/"))
def safe_relpath(filepath: str, base: str, *, normalize: bool = True) -> str:
    try:
        rel = os.path.relpath(filepath, base)
    except ValueError:
        _LOGGER.debug("relpath 跨盘/参数异常(回退原路径): %s vs %s",
                     filepath, base)
        return filepath.replace("\\", "/") if normalize else filepath
    return rel.replace("\\", "/") if normalize else rel
_CODING_DECL_RE = re.compile(r"^[ \t\f]*#.*?coding[:=][ \t]*([-\w.]+)")
_CODING_DECL_SECOND_LINE_PREFIX_RE = re.compile(r"^[ \t\f]*(?:[#\r]|$)")
_UTF8_DECL_SAFE = frozenset({
    "utf8", "utf_8", "utf8sig", "utf_8_sig", "ascii", "us_ascii", "usascii",
})
_SCAN_EXCLUDED_MEMO: dict[tuple, bool] = {}
_SCAN_EXCLUDED_MEMO_MAX = 10000
_SCAN_IGNORE_DIRS_LITE = (frozenset(SCAN_COLLECT_PRUNE_DIRS)
                          | DIAG_OUT_OF_SCOPE_DIRS)
_SCAN_IGNORE_DIRS_LITE_LOWER = frozenset(
    d.lower() for d in _SCAN_IGNORE_DIRS_LITE if d != RUNTIME_DIR_NAME)
def _is_test_scan_segment(seg: str) -> bool:
    return _is_test_dir_seg(seg) or seg.startswith("test_")
def _is_test_segment(probe: str, fname: str) -> bool:
    directory, path_name = probe.rsplit('/', 1)
    return (any(_is_test_scan_segment(seg)
                for seg in directory.split('/') if seg)
            or is_test_source_basename(path_name)
            or is_test_source_basename(fname)
            # conftest.py 不是 test_*.py 命名，但属于 pytest 测试配置，
            # 生产扫描必须与 is_test_file_path 的判定保持一致。
            or path_name == "conftest.py"
            or fname.lower() == "conftest.py")
def _is_nondelivery_segment(
        norm_path: str, probe: str, segs, excluded_dirs) -> bool:
    return (is_runtime_temp_path(norm_path)
            or '/backup/' in probe
            or _has_backup_snapshot_segment(segs)
            or any(seg in excluded_dirs for seg in segs))
_SKILL_LAYOUT_RESOURCE_DIRS = frozenset({"references", "assets"})
def scan_exclude_dirs(root_dir: str | os.PathLike | None = None) -> set[str]:
    excluded = {name.lower()
                for name in DIAG_OUT_OF_SCOPE_DIRS | SCAN_IGNORE_DIRS}
    root = _coerce_dir_arg(root_dir)
    excluded = set(_scan_dirs_for_root(root, frozenset(excluded)))
    if _is_skill_scan_root(root):
        excluded |= _SKILL_LAYOUT_RESOURCE_DIRS
    return excluded
def _scan_probe_path(norm_path: str, root_dir: Any) -> str:
    root = _coerce_dir_arg(root_dir)
    if not root:
        return norm_path
    if not os.path.isabs(norm_path):
        return norm_path
    try:
        relative = os.path.relpath(norm_path, root)
    except (OSError, TypeError, ValueError):
        return norm_path
    if (relative == os.pardir
            or relative.startswith(os.pardir + os.sep)):
        return norm_path
    return relative
def is_scan_excluded(
        norm_path: str, fname: str, root_dir: str | os.PathLike | None = None) -> bool:
    probe_path = _scan_probe_path(norm_path, root_dir)
    if root_dir is None:
        memo_key = (norm_path, fname, PRODUCTION_TEST_PREFIX_MODULES)
        excluded_dirs = _SCAN_IGNORE_DIRS_LITE_LOWER
    else:
        memo_key = (probe_path, fname, _is_skill_scan_root(root_dir),
                    norm_path, PRODUCTION_TEST_PREFIX_MODULES)
        excluded_dirs = _scan_dirs_for_root(
            root_dir, _SCAN_IGNORE_DIRS_LITE_LOWER)
    return _memo_verdict(_SCAN_EXCLUDED_MEMO, _SCAN_EXCLUDED_MEMO_MAX,
                         memo_key, _scan_excluded_verdict,
                         probe_path, fname, excluded_dirs, norm_path)
def _scan_excluded_verdict(
        norm_path: str, fname: str, excluded_dirs,
        runtime_path: str | None = None) -> bool:
    if _is_hidden_basename(fname):
        return True
    _probe = norm_path.replace('\\', '/').lower()
    _probe = _probe if _probe.startswith('/') else '/' + _probe
    _segs = _probe.split('/')
    return (_is_test_segment(_probe, fname.lower())
            or _is_nondelivery_segment(
                norm_path if runtime_path is None else runtime_path,
                _probe, _segs, excluded_dirs))
def iter_py_source_files(root_dir: str) -> Iterator[tuple[str, str]]:
    root_dir = _coerce_dir_arg(root_dir)
    if not os.path.isdir(root_dir):
        return
    skip = _scan_dirs_for_root(root_dir, GATE_SCAN_IGNORE_DIRS_LOWER)
    for dirpath, dirnames, filenames in os.walk(root_dir, onerror=_on_walk_error):
        prune_scan_dirnames(dirnames, skip)
        dirnames.sort()
        filenames.sort()
        for fname in filenames:
            if is_scan_py_name(fname):
                fpath = os.path.join(dirpath, fname)
                yield os.path.relpath(fpath, root_dir).replace(os.sep, "/"), fpath
def is_baseline_py_file(
        fname: str, root_dir: str, *, scan_root: str | os.PathLike | None = None) -> bool:
    return (is_scan_py_name(fname)
            and not is_diagnosis_out_of_scope(
                os.path.join(root_dir, fname), root_dir=scan_root))
def iter_baseline_py_dirs(root_dir: str) -> Iterator[tuple[str, list[str]]]:
    root_dir = _coerce_dir_arg(root_dir)
    if not os.path.isdir(root_dir):
        return
    skip = _scan_dirs_for_root(root_dir, GATE_SCAN_IGNORE_DIRS_LOWER)
    for dirpath, dirnames, filenames in os.walk(root_dir, onerror=_on_walk_error):
        prune_scan_dirnames(dirnames, skip)
        dirnames.sort()
        filenames.sort()
        yield dirpath, [name for name in filenames
                        if is_baseline_py_file(
                            name, dirpath, scan_root=root_dir)]
def collect_baseline_py_files(root_dir: str) -> list[str]:
    return [os.path.join(dirpath, name)
            for dirpath, names in iter_baseline_py_dirs(root_dir)
            for name in names]
def iter_scan_py_files(root_dir: str) -> Iterator[str]:
    root_dir = _coerce_dir_arg(root_dir)
    skip = _scan_dirs_for_root(root_dir, SCAN_IGNORE_DIRS_LOWER)
    for dirpath, dirnames, filenames in os.walk(root_dir, onerror=_on_walk_error):
        dirnames[:] = sorted(
            d for d in dirnames if not is_pruned_scan_dir(d, skip))
        for fname in sorted(filenames):
            if not is_scan_py_name(fname):
                continue
            fpath = os.path.join(dirpath, fname)
            if is_scan_excluded(
                    fpath.replace('\\', '/'), fname, root_dir=root_dir):
                continue
            yield fpath
def _on_walk_error(exc: OSError) -> None:
    _LOGGER.warning("[Scan] 目录枚举失败，已跳过: %s", exc)
def coerce_skill_dir(value: Any) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, (bytes, bytearray)):
        return os.fsdecode(bytes(value))
    if isinstance(value, os.PathLike):
        try:
            return os.fsdecode(value)
        except (TypeError, ValueError, OSError) as exc:
            _LOGGER.debug("目录入参 PathLike 解码失败（按无根处理）: %r: %s",
                          value, exc)
    elif value is not None:
        _LOGGER.debug("目录入参类型非法（按无根处理）: %s",
                      type(value).__name__)
    return ""
_coerce_dir_arg = coerce_skill_dir
def _is_skill_scan_root(root_dir: Any) -> bool:
    root = _coerce_dir_arg(root_dir)
    return bool(root) and os.path.isfile(os.path.join(root, "SKILL.md"))
def _scan_dirs_for_root(root_dir: Any, excluded) -> frozenset[str]:
    names = frozenset(excluded)
    if _is_skill_scan_root(root_dir):
        return names
    return frozenset(
        name for name in names
        if str(name).lower() not in _SKILL_ONLY_SCAN_DIR_NAMES_LOWER)
def resolve_search_root(start_dir: str) -> str:
    if not start_dir:
        return '.'
    start = os.path.abspath(start_dir)
    if not os.path.isdir(start):
        return start
    return _first_search_root(start) or start
def _first_search_root(start: str) -> str | None:
    cur = start
    while True:
        if _is_search_root(cur):
            return cur
        parent = os.path.dirname(cur)
        if parent == cur:
            return None
        cur = parent
def _is_search_root(path: str) -> bool:
    if os.path.exists(os.path.join(path, '__init__.py')):
        return True
    return any(os.path.exists(os.path.join(path, marker))
               for marker in PROJECT_ROOT_MARKERS)
def count_test_files(skill_dir_raw: str) -> tuple[int, tuple[str, ...]]:
    root = _coerce_dir_arg(skill_dir_raw)
    if not root:
        return 0, ()
    total = 0
    found: list[str] = []
    for dirname in TEST_DIR_CANDIDATES:
        tests_dir = os.path.join(root, dirname)
        if not os.path.isdir(tests_dir):
            continue
        found.append(dirname)
        for current, dirs, files in os.walk(
                tests_dir, onerror=_on_walk_error):
            prune_scan_dirnames(dirs, SCAN_IGNORE_DIRS_LOWER)
            total += sum(
                1 for name in files
                if is_test_source_basename(name)
                and os.path.isfile(os.path.join(current, name)))
    return total, tuple(found)
def resolve_scan_root(skill_dir: str) -> Path | None:
    _root = _coerce_dir_arg(skill_dir)
    if not _root.strip():
        _LOGGER.warning("[Scan] 技能目录为空路径，已跳过枚举（不回退扫描 cwd）")
        return None
    return Path(_root)
def iter_skill_py_files(sp: Path, include_tests: bool = True):
    skip = _SOURCE_SCAN_PRUNE_DIRS_LOWER
    if not include_tests:
        skip = skip | TEST_ARTIFACT_DIRS
    skip = _scan_dirs_for_root(sp, skip)
    for root, dirs, files in os.walk(_coerce_dir_arg(sp),
                                     onerror=_on_walk_error):
        prune_scan_dirnames(dirs, skip)
        for fname in files:
            if not is_scan_py_name(fname):
                continue
            if not include_tests and is_test_source_basename(fname):
                continue
            yield Path(root) / fname
def iter_prod_py_files(skill_dir: str) -> list[str]:
    sp = resolve_scan_root(skill_dir)
    if sp is None:
        return []
    return [str(path) for path in iter_skill_py_files(sp, include_tests=False)]
def rglob_paths_tolerant(root: Path, pattern: str) -> tuple[list[Path], bool]:
    found: list[Path] = []
    _root = _coerce_dir_arg(root)
    if not _root:
        return found, False
    walker = Path(_root).rglob(pattern)
    while True:
        try:
            found.append(next(walker))
        except StopIteration:
            return found, False
        except OSError as exc:
            _LOGGER.warning(
                "[Scan] 目录遍历中段失败（枚举失败，已枚举 %d 项保留） %s: %s",
                len(found), root, exc)
            return found, True
def strip_stale_coding_declaration(text: str) -> str:
    lines = text.split("\n")
    changed = False
    i = 0
    scanned = 0
    while scanned < 2 and i < len(lines):
        status = _coding_decl_status(lines[i])
        if status == "none":
            if (scanned == 0
                    and not _CODING_DECL_SECOND_LINE_PREFIX_RE.match(lines[i])):
                break
            i += 1
            scanned += 1
            continue
        if status == "safe":
            break
        del lines[i]
        changed = True
        scanned += 1
    return "\n".join(lines) if changed else text
def _coding_decl_status(line: str) -> str:
    m = _CODING_DECL_RE.match(line)
    if m is None:
        return "none"
    codec = m.group(1).lower().replace("-", "_")
    return "safe" if codec in _UTF8_DECL_SAFE else "stale"
def is_under_root(path: str, root: str) -> bool:
    path = _coerce_dir_arg(path)
    root = _coerce_dir_arg(root)
    if not path.strip() or not root.strip():
        return False
    try:
        # 同时准备「规范化」与「仅绝对化」两种形态：junction 只在被解析的那一段
        # 改写目标，root 自身不是联接而 path 穿过联接时，两侧 realpath 会落在
        # 不同前缀上（.../target_skills vs .../user_skills/...），单看规范化形态
        # 会得出「不在根下」的假否定。仅绝对化形态保留调用方传入的真实前缀。
        candidates = (
            (canonical_path(path), canonical_path(root)),
            (os.path.normcase(os.path.abspath(path)),
             os.path.normcase(os.path.abspath(root))),
        )
    except (OSError, ValueError, TypeError) as _e:
        _LOGGER.debug('静默降级[is_under_root:OSError]: %s: %s', type(_e).__name__, _e)
        return False
    for p, r in candidates:
        if not r.endswith(os.sep):
            r = r + os.sep
        if p == r.rstrip(os.sep) or p.startswith(r):
            return True
    return False
CACHE_TEMP_DIR_NAMES = frozenset({'__pycache__', 'temp', 'tmp'})
PACKAGE_EXCLUDE_DIR_NAMES = frozenset(
    CACHE_TEMP_DIR_NAMES | {_SKILL_RUNTIME_LOG_DIR, STATE_DIR_NAME, '.analysis'})
PACKAGE_EXCLUDE_FILE_NAMES = frozenset({
    '.coverage', '.defs_tmp.txt', 'louvain_groups.json', 'ms_init.json',
})
PACKAGE_EXCLUDE_FILE_PREFIXES = ('_moved_',)
SKILL_PACKAGE_REQUIRED_FILES = frozenset({
    'SKILL.md', 'requirements.txt', 'pytest.ini',
    'pyproject.toml',
    'skill_profile.json',
})
SKILL_PACKAGE_ALLOWED_HIDDEN = frozenset({
    '.git', '.gitignore', '.gitattributes', '.gitmodules', '.gitkeep',
    '.github', '.gitlab', '.hg', '.hgignore', '.svn',
    '.editorconfig', '.flake8', '.pylintrc', '.ruff.toml', '.isort.cfg',
    '.pre-commit-config.yaml', '.pre-commit-hooks.yaml',
    '.coveragerc', '.mailmap', '.dockerignore',
    '.npmrc', '.nvmrc', '.python-version',
    '.venv', 'venv', '.env', '.tox', '.nox',
})
PROTECTED_CORE_FILES: frozenset[str] = frozenset({
    '__init__.py', 'SKILL.md', 'facade.py', 'setup.py', 'conftest.py',
    'README.md', 'LICENSE', 'pyproject.toml', '_version.py',
    '_version_meta.py', '__main__.py',
})
def is_package_excluded_file(name: str) -> bool:
    if not name:
        return False
    return (name in PACKAGE_EXCLUDE_FILE_NAMES
            or name.startswith(PACKAGE_EXCLUDE_FILE_PREFIXES)
            or name.endswith('.pyc'))
def is_unregistered_package_root_file(name: str) -> bool:
    if not name:
        return False
    if name.startswith('__'):
        return False
    if name in PROTECTED_CORE_FILES:
        return False
    if name.startswith('.'):
        if name in PACKAGE_EXCLUDE_FILE_NAMES:
            return False
        return name not in SKILL_PACKAGE_ALLOWED_HIDDEN
    if name.startswith('_'):
        return True
    if is_py_source_file(name):
        return False
    return name not in SKILL_PACKAGE_REQUIRED_FILES
PACKAGE_VERSION = '3.336.0'
_DEFAULT_TIMEOUT_S = 5
def parse_timeout_env(raw, default: int = _DEFAULT_TIMEOUT_S) -> int:
    try:
        val = int(raw)
        return val if val > 0 else default
    except (TypeError, ValueError, OverflowError):
        _LOGGER.debug("超时环境变量非法(降级默认 %ss): %r", default, raw)
        return default
def _try_set_exception(future: Future, exc: BaseException) -> None:
    try:
        future.set_exception(exc)
    except InvalidStateError:
        _LOGGER.debug("future 已终态，异常无处安放(丢弃): %r", exc)
class _ElasticTimeoutPool:
    def __init__(self) -> None:
        self._q: queue.SimpleQueue = queue.SimpleQueue()
        self._idle = 0
        self._lock = threading.Lock()
    def _spawn_worker(self) -> None:
        threading.Thread(target=self._worker_loop, daemon=True).start()
    def _worker_loop(self) -> None:
        while True:
            fn, args, kwargs, future = self._q.get()
            try:
                future.set_result(fn(*args, **kwargs))
            except Exception as exc:  # noqa: BLE001
                log_swallowed(__name__, exc, context='_ElasticTimeoutPool._worker_loop:Exc')
                _try_set_exception(future, exc)
            except BaseException as exc:  # noqa: BLE001
                log_swallowed(__name__, exc, context='_ElasticTimeoutPool._worker_loop:BaseExc')
                _try_set_exception(future, RuntimeError(f"fatal-in-worker: {exc!r}"))
            finally:
                with self._lock:
                    self._idle += 1
    def submit(self, fn, args, kwargs) -> Future:
        future: Future = Future()
        with self._lock:
            if self._idle > 0:
                self._idle -= 1
            else:
                self._spawn_worker()
        self._q.put((fn, args, kwargs, future))
        return future
def _coerce_timeout_seconds(value: Any, default: Any = None) -> float:
    fallback = (float(_DEFAULT_TIMEOUT_S) if default is None
                else float(default))
    try:
        seconds = float(value)
    except (TypeError, ValueError, OverflowError):
        _LOGGER.debug("超时参数非法(降级默认 %ss): %r", fallback, value)
        return fallback
    if not 0 < seconds < float("inf"):
        _LOGGER.debug("超时参数非正(降级默认 %ss): %r", fallback, value)
        return fallback
    return seconds
_TIMEOUT_POOL = _ElasticTimeoutPool()
def call_with_timeout(fn: Any, args: Any, kwargs: Any,
                      timeout: Any = None) -> Any:
    timeout = (parse_timeout_env(
        os.environ.get("JWSGJ_CHECK_FN_TIMEOUT", str(_DEFAULT_TIMEOUT_S)))
        if timeout is None else _coerce_timeout_seconds(timeout))
    future = _TIMEOUT_POOL.submit(fn, args, kwargs)
    try:
        return future.result(timeout=timeout)
    except (TimeoutError, _FutureTimeoutError):
        _LOGGER.warning(
            "check_fn %s 超时 (%ss), 返回 False",
            getattr(fn, "__name__", "?"), timeout,
        )
        return False
    except Exception as e:
        _LOGGER.warning(
            "check_fn %s raised: %s",
            getattr(fn, "__name__", "?"), e, exc_info=True,
        )
        return False
@contextmanager
def isolated_import_scope(skill_dir: str, *, with_search_path: bool = False,
                          skill_name: str = ""):
    raw_dir = _coerce_dir_arg(skill_dir)
    if not raw_dir.strip():
        raise ValueError(
            "isolated_import_scope: skill_dir 不能为空：空根会被解析为进程 cwd，"
            "误摘调用方同名模块")
    _name = skill_name or os.path.basename(os.path.abspath(raw_dir))
    _parent = os.path.dirname(os.path.abspath(raw_dir))
    _path_added = False
    if with_search_path:
        sys.path.insert(0, _parent)
        _path_added = True
    _previous_modules = _detach_module_namespace(_name)
    try:
        yield _name
    finally:
        _restore_module_namespace(_name, _previous_modules)
        if _path_added:
            try:
                sys.path.remove(_parent)
            except ValueError as exc:
                log_swallowed(__name__, exc,
                              context='isolated_import_scope:sys.path.remove')
def _namespace_keys(skill_name: str) -> list[str]:
    _prefix = skill_name + '.'
    return [key for key in sys.modules
            if key == skill_name or key.startswith(_prefix)]
def _detach_module_namespace(skill_name: str) -> dict:
    previous_modules = {
        key: sys.modules[key] for key in _namespace_keys(skill_name)}
    for key in previous_modules:
        sys.modules.pop(key, None)
    return previous_modules
def _restore_module_namespace(skill_name: str, previous_modules: dict) -> None:
    for key in _namespace_keys(skill_name):
        sys.modules.pop(key, None)
    sys.modules.update(previous_modules)
def _is_probe_added_module(key: str, module: Any, module_name: str,
                           probe_root: str) -> bool:
    if key == module_name or key.startswith(module_name + "."):
        return True
    mod_file = getattr(module, "__file__", None)
    if not isinstance(mod_file, str):
        return False
    return is_under_root(mod_file, probe_root)
def _cleanup_probe_modules(module_name: str, pre_modules: set[str],
                           package_root: str) -> None:
    probe_root = os.path.realpath(os.path.dirname(package_root))
    for key in list(sys.modules):
        if key not in pre_modules and _is_probe_added_module(
                key, sys.modules.get(key), module_name, probe_root):
            del sys.modules[key]
def _import_failure(module_name: str, err: str) -> tuple[dict, list[str]]:
    return ({"module": module_name, "importable": False, "error": err},
            [err])
def _exec_skill_module(module_name: str, init_path: str,
                       package_root: str) -> tuple[Any, str | None]:
    spec = importlib.util.spec_from_file_location(
        module_name, init_path,
        submodule_search_locations=[package_root])
    if spec is None or spec.loader is None:
        return None, f"cannot build import spec for {module_name} from {init_path}"
    mod = importlib.util.module_from_spec(spec)
    previous = sys.modules.get(module_name, mod)
    sys.modules[module_name] = mod
    try:
        spec.loader.exec_module(mod)
    finally:
        if previous is not mod:
            sys.modules[module_name] = previous
    return mod, None
def _local_python_roots(parent: str) -> set[str]:
    roots = set()
    for name in os.listdir(parent):
        path = os.path.join(parent, name)
        if name.lower().endswith(".py") and os.path.isfile(path):
            roots.add(name[:-3])
        elif os.path.isfile(os.path.join(path, "__init__.py")):
            roots.add(name)
    return roots
def _detach_local_companions(parent: str, module_name: str) -> dict:
    roots = _local_python_roots(parent)
    target_root = module_name.split(".", 1)[0]
    previous = {}
    for key in list(sys.modules):
        root = key.split(".", 1)[0]
        if root != target_root and root in roots:
            previous[key] = sys.modules.pop(key)
    return previous
def _restore_probe_search_path(parent: str, path_added: bool) -> None:
    if path_added:
        try:
            sys.path.remove(parent)
        except ValueError:
            _LOGGER.debug("已被移除:%s", parent)
def verify_isolated_import(skill_dir: str, module_name: str
                           ) -> tuple[dict[str, Any], list[str]]:
    raw_dir = coerce_skill_dir(skill_dir)
    if not raw_dir.strip():
        return _import_failure(
            str(module_name or ""),
            "skill_dir 不能为空：空根会把进程 cwd 当成技能包父目录")
    skill_dir = os.path.normpath(raw_dir)
    layout = detect_layout(skill_dir)
    package_root = os.path.normpath(layout.package_root or skill_dir)
    module_name = (module_name or layout.package_name
                   or os.path.basename(package_root))
    init_path = os.path.join(package_root, "__init__.py")
    if not os.path.isfile(init_path):
        return _import_failure(
            module_name, f"__init__.py not found under skill_dir: {package_root}")
    parent = os.path.dirname(package_root)
    try:
        previous_companions = _detach_local_companions(parent, module_name)
    except OSError as exc:
        log_swallowed(__name__, exc, context="verify_isolated_import:OSError")
        return _import_failure(module_name, f"cannot scan local modules: {exc}")
    path_added = parent not in sys.path
    if path_added:
        sys.path.insert(0, parent)
    pre_modules = set(sys.modules)
    try:
        with isolated_import_scope(package_root, skill_name=module_name):
            try:
                mod, spec_err = _exec_skill_module(
                    module_name, init_path, package_root)
            except SystemExit as exc:
                _LOGGER.debug("技能包导入退出转结构化错误: %s", exc)
                return _import_failure(module_name, f"SystemExit({exc.code})")
            except Exception as exc:  # noqa: BLE001 — 导入异常转结构化错误
                _LOGGER.debug("技能包导入失败转结构化错误: %s", exc)
                return _import_failure(module_name, str(exc))
            finally:
                _cleanup_probe_modules(module_name, pre_modules, package_root)
                sys.modules.update(previous_companions)
    finally:
        _restore_probe_search_path(parent, path_added)
    if spec_err:
        return _import_failure(module_name, spec_err)
    public_api = [name for name in dir(mod) if not name.startswith("_")]
    return ({
        "module": module_name,
        "public_api_count": len(public_api),
        "public_api_sample": public_api[:20],
        "importable": True,
    }, [])
@dataclass
class DependencyGraph:
    nodes: set[str] = field(default_factory=set)
    edges: dict[str, set[str]] = field(default_factory=dict)
    implicit_edges: dict[str, set[str]] = field(default_factory=dict)
    def add_edge(self, source: str, target: str, *,
                 register_target: bool = True) -> None:
        self._link(self.edges, source, target, register_target)
    def add_implicit_edge(self, source: str, target: str, *,
                          register_target: bool = True) -> None:
        self._link(self.implicit_edges, source, target, register_target)
    def _link(self, edges: dict[str, set[str]], source: str,
              target: str, register_target: bool) -> None:
        self.nodes.add(source)
        if register_target:
            self.nodes.add(target)
        edges.setdefault(source, set()).add(target)
    @property
    def total_edges(self) -> int:
        return sum(len(v) for v in self.edges.values()) + sum(len(v) for v in self.implicit_edges.values())
    @property
    def fan_in(self) -> dict[str, int]:
        result: dict[str, int] = {}
        for targets in self.edges.values():
            for t in targets:
                result[t] = result.get(t, 0) + 1
        for targets in self.implicit_edges.values():
            for t in targets:
                result[t] = result.get(t, 0) + 1
        return result
    @property
    def fan_out(self) -> dict[str, int]:
        result: dict[str, int] = {}
        for m in self.nodes:
            out = len(self.edges.get(m, set())) + len(self.implicit_edges.get(m, set()))
            if out > 0:
                result[m] = out
        return result
    def summary(self) -> dict:
        return {
            "nodes": len(self.nodes),
            "static_edges": sum(len(v) for v in self.edges.values()),
            "implicit_edges": sum(len(v) for v in self.implicit_edges.values()),
        }
    def has_cycle(self) -> bool:
        if any(len(scc) > 1 for scc in tarjan_scc(self.edges)):
            return True
        return any(node in targets for node, targets in self.edges.items())
@dataclass
class _TarjanState:
    index: dict[str, int] = field(default_factory=dict)
    lowlink: dict[str, int] = field(default_factory=dict)
    stack: list[str] = field(default_factory=list)
    on_stack: set[str] = field(default_factory=set)
    counter: int = 0
    def push(self, node: str) -> None:
        self.index[node] = self.lowlink[node] = self.counter
        self.counter += 1
        self.stack.append(node)
        self.on_stack.add(node)
    def next_child(self, v: str, neighbours) -> str | None:
        for w in neighbours:
            if w not in self.index:
                return w
            if w in self.on_stack:
                self.lowlink[v] = min(self.lowlink[v], self.index[w])
        return None
    def pop_scc(self, v: str) -> set[str]:
        scc: set[str] = set()
        while True:
            w = self.stack.pop()
            self.on_stack.discard(w)
            scc.add(w)
            if w == v:
                return scc
def tarjan_scc(edges: dict[str, set[str]]) -> list[set[str]]:
    state = _TarjanState()
    result: list[set[str]] = []
    for start in list(edges.keys()):
        if start in state.index:
            continue
        state.push(start)
        work: list[list] = [[start, iter(sorted(edges.get(start, ())))]]
        while work:
            v, neighbours = work[-1]
            child = state.next_child(v, neighbours)
            if child is not None:
                state.push(child)
                work.append([child, iter(sorted(edges.get(child, ())))])
                continue
            work.pop()
            if work:
                parent = work[-1][0]
                state.lowlink[parent] = min(state.lowlink[parent], state.lowlink[v])
            if state.lowlink[v] == state.index[v]:
                result.append(state.pop_scc(v))
    return result
def cycle_member_groups(
        edges: dict[str, set[str]],
        known_nodes: set[str] | None = None) -> list[list[str]]:
    groups: list[list[str]] = []
    for component in tarjan_scc(edges):
        members = sorted(node for node in component
                         if known_nodes is None or node in known_nodes)
        if (len(members) > 1
                or members and members[0] in edges.get(members[0], ())):
            groups.append(members)
    return groups
def detect_cycles(graph: dict) -> list:
    if not hasattr(graph, "get"):
        return []
    cycles = []
    visited = set()
    rec_stack = set()
    path = []
    pos: dict = {}
    seen_cycles: set = set()
    frames: list = []
    def _push(node):
        visited.add(node)
        rec_stack.add(node)
        pos[node] = len(path)
        path.append(node)
        frames.append((node, iter(graph.get(node, ()))))
    for node in graph:
        if node in visited:
            continue
        _push(node)
        while frames:
            _cur, neighbors = frames[-1]
            next_node = _next_unvisited(
                neighbors, visited, rec_stack, path, pos, seen_cycles, cycles)
            if next_node is not None:
                _push(next_node)
                continue
            _pop_frame(frames, path, rec_stack, pos)
    return cycles
def _next_unvisited(neighbors, visited: set, rec_stack: set, path: list,
                    pos: dict, seen_cycles: set, cycles: list):
    for nb in neighbors:
        if nb not in visited:
            return nb
        if nb in rec_stack:
            _record_cycle(nb, path, pos, seen_cycles, cycles)
    return None
def _pop_frame(frames: list, path: list, rec_stack: set, pos: dict) -> None:
    cur, _neighbors = frames.pop()
    path.pop()
    rec_stack.discard(cur)
    del pos[cur]
def _record_cycle(
    start, path: list, pos: dict, seen_cycles: set, cycles: list,
) -> None:
    cycle = tuple(path[pos[start]:])
    if cycle in seen_cycles:
        return
    seen_cycles.add(cycle)
    cycles.append(list(cycle))
def normalize_text(value) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, (bytes, bytearray)):
        return bytes(value).decode("utf-8", errors="replace")
    return "" if value is None else str(value)
def py_stem(name: Any) -> str:
    if not isinstance(name, str):
        return ""
    return name[:-3] if name.lower().endswith(".py") else name
def import_key(name: str) -> str:
    return name.replace("-", "_") if name else ""
def normalize_skill_dir(
        skill_dir: str | bytes | os.PathLike, *, require_valid: bool = False) -> str:
    if not isinstance(skill_dir, (str, bytes, os.PathLike)):
        raise TypeError(
            f"normalize_skill_dir: skill_dir 须为 str/bytes/PathLike 路径，实际为 "
            f"{type(skill_dir).__name__}: {skill_dir!r}")
    try:
        normalized = os.fsdecode(os.fspath(skill_dir))
    except (TypeError, ValueError, OSError) as exc:
        raise ValueError(
            f"normalize_skill_dir: 路径无法解析: {skill_dir!r}") from exc
    if not normalized.strip():
        if require_valid:
            raise ValueError(_invalid_skill_dir_message(normalized))
        return ""
    normalized = os.path.abspath(expand_git_bash_path(normalized))
    if require_valid and not is_real_skill_dir(normalized):
        raise ValueError(_invalid_skill_dir_message(normalized))
    return normalized
def expand_git_bash_path(path: str) -> str:
    path = os.path.expanduser(path)
    if os.name == "nt" and _is_git_bash_drive_path(path):
        path = path[1].upper() + ':' + path[2:]
    return path
def _is_git_bash_drive_path(path: str) -> bool:
    return (path.startswith('/') and len(path) > 2
            and path[2] == '/'
            and path[1].isascii() and 'a' <= path[1].lower() <= 'z')
def _invalid_skill_dir_message(skill_dir: str) -> str:
    return (
        f"无效的技能目录: {skill_dir!r}。请传入技能根目录的绝对路径"
        f"（包含 SKILL.md / __init__.py / .py 文件的目录）。"
        f"相对路径会基于当前工作目录解析，可能指向不存在的目录，"
        f"导致诊断扫描 0 文件而静默返回「0 发现」。"
    )
def adaptive_workers(n_tasks: int) -> int:
    n = os.cpu_count() or 1
    return max(1, min(int(n_tasks), n))
def validate_source_paths(source_paths) -> None:
    if isinstance(source_paths, (str, bytes, os.PathLike)):
        raise TypeError(
            f"source_paths 须为文件/目录路径列表或 None，得到"
            f"{type(source_paths).__name__}；单路径请传 [path]，"
            f"项目根扫描请传 None")
def relative_module_base(module: str) -> str:
    return "/".join(module.split("."))
def resolve_internal_dependency(
    import_module: str, base_dir: Path,
) -> str | None:
    base_dir = Path(base_dir) if not isinstance(base_dir, Path) else base_dir
    parts = [part for part in import_module.replace("/", ".").split(".")
             if part]
    if not parts:
        return None
    tails = [parts] + ([parts[1:]] if len(parts) > 1 else [])
    for tail in tails:
        for end in range(len(tail), 0, -1):
            rel = "/".join(tail[:end])
            if ((base_dir / f"{rel}.py").is_file()
                    or (base_dir / rel).is_dir()):
                return rel
    return None
def resolve_finding_file_path(file_path: str, skill_dir: str) -> str:
    if not file_path:
        return ""
    skill_dir = skill_dir or ""
    basename = _with_py_ext(os.path.basename(file_path))
    found = _first_existing(
        _finding_path_candidates(file_path, skill_dir, basename))
    if found is not None:
        return os.path.abspath(found)
    walked = _walk_find_basename(skill_dir, basename)
    return os.path.abspath(walked) if walked else ""
def resolve_skill_relative_path(file_path: str, skill_dir: str) -> str:
    if file_path and not os.path.isabs(file_path):
        _resolved_fp = resolve_finding_file_path(file_path, skill_dir)
        if _resolved_fp:
            file_path = _resolved_fp
    return file_path
def _first_existing(candidates) -> str | None:
    for candidate in candidates:
        if os.path.isfile(candidate):
            return candidate
    return None
def _finding_path_candidates(
    file_path: str, skill_dir: str, basename: str,
) -> tuple[str, str, str]:
    first = (file_path if os.path.isabs(file_path)
             else os.path.join(skill_dir, file_path))
    return (_with_py_ext(first),
            os.path.join(skill_dir, basename),
            os.path.join(skill_dir, "tests", basename))
def _walk_find_basename(skill_dir: str, basename: str) -> str:
    skip = _scan_dirs_for_root(skill_dir, SCAN_COLLECT_PRUNE_DIRS_LOWER)
    matches: list[str] = []
    for root, dirs, files in os.walk(skill_dir, onerror=_on_walk_error):
        prune_scan_dirnames(dirs, skip)
        if basename in files:
            matches.append(os.path.join(root, basename))
            if len(matches) > 1:
                _LOGGER.warning(
                    "[Path] 同名文件回退解析存在歧义（拒绝任意选择）: %s -> %s",
                    basename, matches)
                return ""
    return matches[0] if matches else ""
def _with_py_ext(path: str) -> str:
    return path if os.path.splitext(path)[1] else path + ".py"
def is_pruned_scan_dir(dirname: str, skip: frozenset) -> bool:
    return (dirname.startswith((".", "__"))
            or is_backup_like_dir(dirname)
            or is_temp_artifact_dir(dirname)
            or dirname.lower() in skip)
def prune_scan_dirnames(dirnames: list[str], skip: frozenset) -> None:
    dirnames[:] = [d for d in dirnames if not is_pruned_scan_dir(d, skip)]
def scan_prune_dirs(root_dir: str | os.PathLike | None = None) -> frozenset[str]:
    if root_dir is None:
        return SCAN_IGNORE_DIRS_LOWER
    return _scan_dirs_for_root(root_dir, SCAN_IGNORE_DIRS_LOWER)
def _normalize_scan_root(root) -> str | None:
    if isinstance(root, (bool, int)):
        return None
    if not isinstance(root, (str, bytes, os.PathLike)):
        return None
    try:
        return os.fsdecode(os.fspath(root))
    except (TypeError, ValueError, OSError) as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_normalize_scan_root:TypeError+')
        return None
def count_py_files_under(root) -> int:
    root = _normalize_scan_root(root)
    if root is None:
        return 0
    count = 0
    if os.path.isdir(root):
        skip = _scan_dirs_for_root(root, SCAN_IGNORE_DIRS_LOWER)
        for _, dirs, files in os.walk(root, onerror=_on_walk_error):
            prune_scan_dirnames(dirs, skip)
            count += sum(1 for fn in files if is_scan_py_name(fn))
    return count
def collect_python_files(skill_dir: str, *,
                         include_tests: bool = True,
                         max_files: int = 0,
                         walk_errors: list[OSError] | None = None) -> list[str]:
    if type(max_files) is not int or max_files < 0:
        _LOGGER.warning(
            "[Scan] 非法 max_files=%r（按 0=不限制处理，禁止隐式截断）",
            max_files)
        max_files = 0
    root = normalize_skill_dir(skill_dir, require_valid=True)
    prune_dirs = _scan_dirs_for_root(root, SCAN_COLLECT_PRUNE_DIRS_LOWER)
    collected: list[str] = []
    def _on_collect_error(exc: OSError) -> None:
        _on_walk_error(exc)
        if walk_errors is not None:
            walk_errors.append(exc)
    for current, dirs, files in os.walk(root, onerror=_on_collect_error):
        dirs[:] = sorted(
            name for name in dirs
            if not is_pruned_scan_dir(name, prune_dirs)
        )
        for name in sorted(files):
            if not is_scan_py_name(name):
                continue
            path = os.path.join(current, name)
            if (not include_tests
                    and is_diagnosis_out_of_scope(path, root_dir=root)):
                continue
            collected.append(path)
            if max_files and len(collected) >= max_files:
                return sorted(collected)
    return sorted(collected)
def collect_py_files_default(skill_dir: str) -> list:
    skill_dir = _coerce_dir_arg(skill_dir)
    skip = _scan_dirs_for_root(skill_dir, _COLLECT_SKIP_DIRS)
    py_files: list = []
    for root, dirs, files in os.walk(skill_dir, onerror=_on_walk_error):
        dirs[:] = [d for d in dirs if not is_pruned_scan_dir(d, skip)]
        for fn in files:
            if _is_collectable_py(fn):
                py_files.append(os.path.join(root, fn))
    return py_files
def _keep_gate_scan_file(
        dirpath: str, fname: str, skill_dir: str,
        scan_root: str | os.PathLike | None) -> bool:
    if not is_scan_py_name(fname):
        return False
    path = os.path.join(dirpath, fname)
    if skill_dir:
        try:
            path = os.path.relpath(path, skill_dir)
        except ValueError as exc:
            log_swallowed(__name__, exc, context='_keep_gate_scan_file:relpath')
    return not is_diagnosis_out_of_scope(path, root_dir=scan_root)
def collect_gate_scan_files(skill_dir: str, errors: list | None = None) -> list[str]:
    def _onerror(exc):
        if errors is not None:
            errors.append(exc)
    file_list = []
    skip = _scan_dirs_for_root(skill_dir, GATE_SCAN_IGNORE_DIRS_LOWER)
    for root, dirs, files in os.walk(skill_dir, onerror=_onerror):
        dirs[:] = [d for d in dirs if not is_pruned_scan_dir(d, skip)]
        file_list.extend(os.path.join(root, fn) for fn in files
                         if _keep_gate_scan_file(
                             root, fn, skill_dir, scan_root=skill_dir))
    return file_list
def _keep_diagnosis_scan_file(fp: str, include_file: Any) -> bool:
    if include_file is None:
        return True
    try:
        return bool(include_file(fp))
    except Exception as exc:  # noqa: BLE001
        _LOGGER.warning("include_file 谓词异常(保守包含): %s: %s", fp, exc)
        return True
def collect_scan_py_files(
    skill_dir: str,
    include_tests: bool = _DEFAULT_INCLUDE_TESTS,
    include_file: Any = None,
) -> list[str]:
    if include_file is None and callable(include_tests):
        include_file = include_tests
        include_tests = False
    skill_dir = _coerce_dir_arg(skill_dir)
    if not skill_dir:
        return []
    if os.path.isfile(skill_dir):
        if (not is_scan_py_name(os.path.basename(skill_dir))
                or not is_scan_scope_path(skill_dir, include_tests)):
            return []
        return [skill_dir] if _keep_diagnosis_scan_file(skill_dir, include_file) else []
    py_files: list[str] = []
    for root, _dirs, files in _iter_scan_scope_walk(os.path.abspath(skill_dir)):
        for name in files:
            fp = os.path.join(root, name)
            if (is_scan_py_name(name)
                    and is_scan_scope_path(
                        fp, include_tests, root_dir=skill_dir)
                    and _keep_diagnosis_scan_file(fp, include_file)):
                py_files.append(fp)
    return sorted(py_files)
def is_scan_scope_path(
        fp: str, include_tests: bool, root_dir: str | os.PathLike | None = None) -> bool:
    if include_tests:
        return not is_archive_or_cache_path(fp, root_dir=root_dir)
    return not is_diagnosis_out_of_scope(fp, root_dir=root_dir)
def _iter_scan_scope_walk(abs_dir: str):
    skip = _scan_dirs_for_root(abs_dir, SCAN_IGNORE_DIRS_LOWER)
    for root, dirs, files in os.walk(abs_dir, onerror=_on_walk_error):
        dirs[:] = [d for d in dirs if not is_pruned_scan_dir(d, skip)]
        yield root, dirs, files
_DEFAULT_DIAGNOSIS_SCAN_PATTERN = "*.py"
def iter_diagnosis_scan_targets(
        dir_path: str, pattern: str = _DEFAULT_DIAGNOSIS_SCAN_PATTERN):
    dir_path = _coerce_dir_arg(dir_path)
    if not dir_path:
        return
    _pattern = str(pattern or _DEFAULT_DIAGNOSIS_SCAN_PATTERN).lower()
    for root, _dirs, fnames in _iter_scan_scope_walk(os.path.abspath(dir_path)):
        for fname in fnames:
            if not fnmatch.fnmatch(fname.lower(), _pattern):
                continue
            fp = os.path.join(root, fname)
            if is_scan_scope_path(fp, False, root_dir=dir_path):
                yield fp
def collect_py_files(skill_dir: str, ctx=None) -> list[str]:
    skill_dir = _coerce_dir_arg(skill_dir)
    if ctx is not None and hasattr(ctx, "py_files"):
        return sorted(safe_relpath(fp, skill_dir) for fp in ctx.py_files)
    return sorted(_walk_collectable_py_files(skill_dir))
def _walk_collectable_py_files(skill_dir: str) -> list[str]:
    skill_dir = _coerce_dir_arg(skill_dir)
    skip = _scan_dirs_for_root(skill_dir, SCAN_COLLECT_PRUNE_DIRS_LOWER)
    py_files: list[str] = []
    for root, dirs, files in os.walk(skill_dir, onerror=_on_walk_error):
        dirs[:] = [d for d in dirs if not is_pruned_scan_dir(d, skip)]
        for f in files:
            if is_scan_py_name(f):
                py_files.append(safe_relpath(os.path.join(root, f), skill_dir))
    return py_files
def _is_collectable_py(filename: str) -> bool:
    return is_scan_py_name(filename) and not is_test_source_basename(filename)
_COLLECT_SKIP_DIRS = (frozenset(SCAN_COLLECT_PRUNE_DIRS_LOWER)
                      | TEST_ARTIFACT_DIRS)
_ITER_SKIP_DIRS = _COLLECT_SKIP_DIRS | {"test_tmp"}
def iter_py_files(skill_dir: str) -> Iterator[str]:
    _root = _coerce_dir_arg(skill_dir)
    if not _root:
        return
    base = Path(_root)
    skip = _scan_dirs_for_root(base, _ITER_SKIP_DIRS)
    for fpath in base.rglob("*.[pP][yY]"):
        if not fpath.is_file():
            continue
        parts = fpath.relative_to(base).parts
        if any(is_pruned_scan_dir(p, skip) for p in parts[:-1]):
            continue
        if parts[-1].startswith("."):
            continue
        yield str(fpath)
_MIGRATION_SKILL_LAYOUT_EXCLUDE_DIRS = frozenset({"references"})
_MIGRATION_SKILL_LAYOUT_EXCLUDE_DIRS_LOWER = frozenset(
    d.lower() for d in _MIGRATION_SKILL_LAYOUT_EXCLUDE_DIRS)
def _migration_scan_exclude_dirs(
    root_dir: str, *, include_tests: bool = _DEFAULT_INCLUDE_TESTS,
) -> frozenset[str]:
    base = (_SOURCE_SCAN_PRUNE_DIRS_LOWER if include_tests
            else _SOURCE_SCAN_PRUNE_DIRS_LOWER | TEST_ARTIFACT_DIRS)
    excludes = set(_scan_dirs_for_root(root_dir, base))
    if _is_skill_scan_root(root_dir):
        excludes |= _MIGRATION_SKILL_LAYOUT_EXCLUDE_DIRS_LOWER
    return frozenset(excludes)
def collect_migration_py_files(
    skill_dir: str, *, include_tests: bool = _DEFAULT_INCLUDE_TESTS,
) -> list[str]:
    skill_dir = _coerce_dir_arg(skill_dir)
    py_files: list[str] = []
    skip = _migration_scan_exclude_dirs(
        skill_dir, include_tests=include_tests)
    for root, dirs, files in os.walk(skill_dir, onerror=_on_walk_error):
        dirs[:] = sorted(d for d in dirs if not is_pruned_scan_dir(d, skip))
        py_files.extend(
            os.path.join(root, f)
            for f in sorted(files)
            if is_scan_py_name(f)
            and (include_tests or not is_test_source_basename(f)))
    return py_files
def is_test_scan_asset(path: Path, root: Path) -> bool:
    try:
        rel = path.relative_to(root)
    except ValueError as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc, context='is_test_scan_asset:ValueError')
        return False
    return is_scan_excluded(rel.as_posix(), rel.name, root_dir=root)

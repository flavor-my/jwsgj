from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import posixpath
import re
import shutil
import subprocess as _sp
import sys
import threading
import time
from collections import Counter, defaultdict
from collections.abc import Collection, Iterable, Iterator, Mapping
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Any, NamedTuple

try:
    import psutil as _psutil
except ImportError:
    _psutil = None  # type: ignore[assignment]

from jwsgj.diag_guard_io import (
    check_path_traversal,
    detect_source_encoding,
    read_source_text_strict,
    sandbox_path,
    two_level_rmtree,
)
from jwsgj.diag_guard_state import (
    read_json_artifact,
    write_json_artifact,
)
from jwsgj.diag_testing_coverage import (
    locate_pytest_summary_line,
    parse_pytest_summary_counts,
)
from jwsgj.diag_testing_source import build_mutation_test_mapping
from jwsgj.diag_types_vocab import OUTPUT_TRUNCATE_LEN
from jwsgj.log_config import (
    get_module_logger,
    log_swallowed,
)
from jwsgj.runtime_paths import (
    get_temp_base,
    make_temp_dir,
    source_import_roots,
    subprocess_noartifact_env,
)
from jwsgj.runtime_scope import (
    SKILL_LOG_DIR_NAME,
    is_out_of_scope_dir,
    is_runtime_log_artifact,
    is_test_source_basename,
)
from jwsgj.testsuite_registry import test_tree_dirs

_log = get_module_logger(__name__)
__all__ = [
    'MUTATION_CACHE_MAX_ENTRIES',
    'MUTATION_TIMEOUT',
    'REMOVE_FUNCTION',
    'REMOVE_LINE',
    'MutationProbeOutcome',
    'MutationResultCache',
    'fingerprint_matches',
    'get_mutation_test_bridge',
    'in_tests_tree',
    'install_mutation_test_bridge',
    'iter_test_assets',
    'mutation_bridge_runner',
    'prepare_mutation_sandbox',
    'probe_mutation',
    'proc_verdict',
    'run_mutation_batch',
    'sandbox_pkg_dst',
    'sandbox_pkg_name',
    'set_mutation_test_bridge',
]
_log.info("diag_testing_mutation_runtime 执行层已加载：%d 项导出", len(__all__))
_BASELINE_FAILED_ERROR = 'baseline_tests_failed_inconclusive'
_TEST_TREE_DIR_NAMES = frozenset({'tests', 'test'})
_TEST_TREE_PRUNE_DIR_NAMES = frozenset({'__pycache__', '.pytest_cache'})
_TEST_TREE_BYTECODE_SUFFIXES = ('.pyc', '.pyo')
_PYTEST_QUIET_ARGS: tuple[str, ...] = (
    '-q', '--no-header', '-p', 'no:cacheprovider', '-o', 'addopts=')
def _norm_rel(path: str, root: str) -> str:
    rel = os.path.relpath(path, root)
    if rel == os.curdir:
        return ""
    return rel.replace(os.sep, "/")
def _test_tree_names(test_dirs: Iterable[str] | str) -> list[str]:
    if isinstance(test_dirs, str):
        test_dirs = [test_dirs]
    names: list[str] = []
    for entry in test_dirs or ():
        try:
            normalized = os.fspath(entry)
        except TypeError:
            continue
        if not isinstance(normalized, str) or not normalized.strip():
            continue
        raw = normalized.strip().replace(os.sep, "/")
        if raw.startswith("/") or re.match(r"^[A-Za-z]:", raw):
            continue
        normalized = posixpath.normpath(raw).strip("/")
        if not normalized or normalized == ".":
            continue
        if normalized == ".." or normalized.startswith("../"):
            continue
        if normalized not in names:
            names.append(normalized)
    return names
def in_tests_tree(root: str, skill_dir: str,
                  test_dirs: Iterable[str] | str | None = None) -> bool:
    try:
        rel = _norm_rel(os.path.abspath(root), os.path.abspath(skill_dir))
    except (OSError, TypeError, ValueError):  # jwsgj:silent-ok 纯值降级：入参不可解析时返回安全默认值，无副作用可留痕
        return False
    if not rel or rel == ".." or rel.startswith("../"):
        return False
    trees = test_tree_dirs(skill_dir) if test_dirs is None else test_dirs
    return any(
        rel == tree or rel.startswith(tree + "/")
        for tree in _test_tree_names(trees))
def _test_tree_walkable(test_dirs: Iterable[str]) -> set[str]:
    names = set(_TEST_TREE_DIR_NAMES)
    for tree in _test_tree_names(test_dirs):
        names.add(tree.rsplit("/", 1)[-1].lower())
    return names
def _walk_asset_tree(skill_dir: str) -> Iterator[tuple[str, list[str], bool]]:
    test_dirs = test_tree_dirs(skill_dir)
    walkable = _test_tree_walkable(test_dirs)
    for root, dirs, files in os.walk(skill_dir):
        in_tests = in_tests_tree(root, skill_dir, test_dirs)
        if in_tests:
            dirs[:] = sorted(
                d for d in dirs
                if d.lower() not in _TEST_TREE_PRUNE_DIR_NAMES)
        else:
            dirs[:] = sorted(
                d for d in dirs
                if not is_out_of_scope_dir(d) or d.lower() in walkable)
        yield root, sorted(files), in_tests
def _is_test_asset(name: str, in_tests: bool) -> bool:
    return (in_tests or is_test_source_basename(name)
            or name.lower() == "conftest.py")
def iter_test_assets(skill_dir: str) -> Iterator[str]:
    for root, files, in_tests in _walk_asset_tree(skill_dir):
        for name in files:
            if not name.lower().endswith(".py") or name.startswith("."):
                continue
            if _is_test_asset(name, in_tests):
                yield os.path.join(root, name)
def _fingerprint_assets(skill_dir: str, paths: Iterable[str],
                        label: str) -> tuple[int, str]:
    digest = hashlib.md5(usedforsecurity=False)
    total = 0
    seen = 0
    for path in paths:
        file_digest = hashlib.md5(usedforsecurity=False)
        file_size = 0
        try:
            with open(path, "rb") as fh:
                while chunk := fh.read(1024 * 1024):
                    file_digest.update(chunk)
                    file_size += len(chunk)
        except OSError as e:
            _log.warning("[%s] 资产读取失败（执行指纹不可用，禁用缓存）: %s",
                         label, e)
            return 0, ""
        rel = os.path.relpath(path, skill_dir).replace(os.sep, "/")
        digest.update(rel.encode("utf-8"))
        digest.update(b"\x00")
        digest.update(file_digest.digest())
        digest.update(b"\x00")
        total += file_size
        seen += 1
    return total, digest.hexdigest() if seen else ""
def _iter_execution_assets(skill_dir: str) -> Iterator[str]:
    for root, files, in_tests in _walk_asset_tree(skill_dir):
        for name in files:
            if in_tests and name.lower().endswith(
                    _TEST_TREE_BYTECODE_SUFFIXES):
                continue
            if name.startswith(".") and not in_tests:
                continue
            if _is_test_asset(name, in_tests):
                yield os.path.join(root, name)
                continue
            if not should_copy_file(name):
                continue
            if is_runtime_log_artifact(name):
                continue
            yield os.path.join(root, name)
def fingerprint_matches(entry: dict, size_key: str, digest_key: str,
                        size: int, digest: str) -> bool:
    if size_key not in entry or digest_key not in entry:
        return False
    cached_size = entry.get(size_key)
    cached_digest = entry.get(digest_key)
    if (isinstance(cached_size, bool) or not isinstance(cached_size, int)
            or not isinstance(cached_digest, str)):
        return False
    return cached_size == size and cached_digest == digest
MUTATION_CACHE_MAX_ENTRIES = 500
_MUTATION_CACHE_SCHEMA_VERSION = 2
class MutationResultCache:
    def __init__(self, skill_dir: str):
        cache_root = get_temp_base(skill_dir)
        project_key = os.path.normcase(
            os.path.realpath(os.path.abspath(skill_dir)))
        project_namespace = hashlib.sha256(
            project_key.encode("utf-8")).hexdigest()[:16]
        self.dir = os.path.join(
            cache_root, "_mutation_cache", project_namespace)
        self.file = os.path.join(self.dir, "results.json")
        self.skill_dir = skill_dir
        self.execution_fp = (0, "")
        self.refresh_execution_fingerprint()
        self.data = self.load()
    def refresh_execution_fingerprint(self) -> None:
        self.execution_fp = _fingerprint_assets(
            self.skill_dir,
            _iter_execution_assets(self.skill_dir),
            "MutationExecution",
        )
    def load(self) -> dict:
        if not os.path.isfile(self.file):
            return {}
        data, kind, error = read_json_artifact(self.file)
        if kind != "ok":
            _log.warning("[XV_Mutation] 加载验证缓存失败,返回空: %s: %s",
                         self.file, error or kind)
            return {}
        if not isinstance(data, dict):
            _log.warning("[XV_Mutation] 缓存顶层非对象,返回空: %s: %s",
                         self.file, type(data).__name__)
            return {}
        return data
    def save(self) -> None:
        try:
            os.makedirs(self.dir, exist_ok=True)
            if len(self.data) > MUTATION_CACHE_MAX_ENTRIES:
                _items = sorted(self.data.items(),
                                key=lambda kv: _evict_ts(kv[1]))
                for _k, _v in _items[:len(self.data) - MUTATION_CACHE_MAX_ENTRIES]:
                    self.data.pop(_k, None)
            write_json_artifact(self.file, self.data, indent=2)
        except (OSError, TypeError, ValueError, RecursionError) as e:
            _log.warning("[Mutation] 缓存写入失败: %s", e)
    def get(self, locator: str, file_size: int,
            file_digest: str) -> dict | None:
        if not self.execution_fp[1]:
            return None
        entry = self.data.get(locator)
        if not (entry and isinstance(entry, dict)):
            return None
        if entry.get("_cache_schema") != _MUTATION_CACHE_SCHEMA_VERSION:
            return None
        if not fingerprint_matches(entry, "_file_size", "_file_digest",
                                   file_size, file_digest):
            return None
        if not fingerprint_matches(entry, "_execution_size", "_execution_digest",
                                   self.execution_fp[0], self.execution_fp[1]):
            return None
        return entry
    def put(self, locator: str, file_size: int, file_digest: str,
            result_dict: dict) -> None:
        if not self.execution_fp[1]:
            return
        result_dict["_cache_schema"] = _MUTATION_CACHE_SCHEMA_VERSION
        result_dict["_file_size"] = file_size
        result_dict["_file_digest"] = file_digest
        result_dict["_execution_size"] = self.execution_fp[0]
        result_dict["_execution_digest"] = self.execution_fp[1]
        result_dict["_cached_at"] = time.time()
        self.data[locator] = result_dict
        self.save()
def _evict_ts(entry) -> float:
    if not isinstance(entry, dict):
        return 0.0
    ts = entry.get("_cached_at")
    return ts if isinstance(ts, (int, float)) else 0.0
_STALE_SANDBOX_SECONDS = 3600
_SANDBOX_ACTIVE_MARKER = ".mutation_active.json"
def _mark_sandbox_active(tmp_dir: str) -> None:
    create_time = None
    if _psutil is not None:
        try:
            create_time = _psutil.Process(os.getpid()).create_time()
        except (_psutil.Error, OSError):
            _log.debug("[Mutation] 沙箱进程启动时间不可读，使用保守所有权标记",
                       exc_info=True)
    write_json_artifact(
        os.path.join(tmp_dir, _SANDBOX_ACTIVE_MARKER),
        {"pid": os.getpid(), "create_time": create_time})
def _sandbox_owner_active(tmp_dir: str) -> bool:
    marker = os.path.join(tmp_dir, _SANDBOX_ACTIVE_MARKER)
    if not os.path.isfile(marker):
        return False
    data, kind, _error = read_json_artifact(marker)
    if kind != "ok" or not isinstance(data, dict):
        return True
    pid = data.get("pid")
    if isinstance(pid, bool) or not isinstance(pid, int) or pid <= 0:
        return True
    if _psutil is None:
        return True
    try:
        process = _psutil.Process(pid)
        create_time = data.get("create_time")
        if (isinstance(create_time, (int, float))
                and not isinstance(create_time, bool) and create_time > 0):
            return abs(process.create_time() - create_time) <= 1e-3
        return True
    except _psutil.NoSuchProcess:
        return False
    except (_psutil.Error, OSError):
        _log.debug("[Mutation] 沙箱所有者身份不可判定，保守保留: %s",
                   tmp_dir, exc_info=True)
        return True
def sandbox_pkg_name(skill_dir: str) -> str:
    return os.path.basename(os.path.normpath(skill_dir)) or "skill_root"
def sandbox_pkg_dst(tmp_dir: str, skill_dir: str) -> str:
    return os.path.join(tmp_dir, sandbox_pkg_name(skill_dir))
def cleanup_stale_entries(tmp_base: str, label: str) -> None:
    try:
        now = time.time()
        for stale in os.listdir(tmp_base):
            path = os.path.join(tmp_base, stale)
            try:
                if (os.path.isdir(path)
                        and now - os.path.getmtime(path) > _STALE_SANDBOX_SECONDS):
                    if _sandbox_owner_active(path):
                        _log.debug("%s 跳过活跃或所有权不可判定的沙箱: %s",
                                   label, path)
                        continue
                    two_level_rmtree(path)
            except OSError:
                _log.debug("%s entry cleanup failed: %s",
                             label, path, exc_info=True)
    except OSError:
        _log.debug("%s cleanup failed", label, exc_info=True)
MAX_COPY_FILE_SIZE = 5 * 1024 * 1024
_SOURCE_FILE_SUFFIXES: tuple[str, ...] = (".py", ".pyi", ".pyx", ".pxd")
def _mutation_copy_size_limit(name: str, in_tests: bool = False) -> int | None:
    if in_tests or name.lower().endswith(_SOURCE_FILE_SUFFIXES):
        return None
    return MAX_COPY_FILE_SIZE
def _ensure_parent_dir(dst: str, rel: str) -> bool:
    try:
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        return True
    except OSError:
        _log.warning("[Mutation] 跳过目录创建失败文件 %s", rel, exc_info=True)
        return False
def _within_size_limit(src: str, rel: str,
                      max_file_size: int | None) -> bool:
    if max_file_size is None:
        return True
    try:
        _size = os.path.getsize(src)
    except OSError:
        _log.warning("[Mutation] 跳过 stat 失败文件 %s", rel, exc_info=True)
        return False
    if _size > max_file_size:
        _log.warning("[Mutation] 跳过大文件 %s (%d bytes)", rel, _size)
        return False
    return True
def _copy_file(src: str, dst: str, rel: str) -> bool:
    try:
        shutil.copy2(src, dst)
        return True
    except OSError:
        _log.warning("[Mutation] 跳过复制失败文件 %s", rel, exc_info=True)
        return False
def copy_one_mutation_file(src: str, rel: str, target_dir: str,
                          max_file_size: int | None) -> bool:
    dst = os.path.join(target_dir, rel)
    return (_ensure_parent_dir(dst, rel)
            and _within_size_limit(src, rel, max_file_size)
            and _copy_file(src, dst, rel))
def _is_sandbox_copy_dir_excluded(
    name: str, skill_dir: str, current_dir: str,
) -> bool:
    if is_out_of_scope_dir(name):
        return True
    if name.lower() != SKILL_LOG_DIR_NAME.lower():
        return False
    at_skill_root = (os.path.normcase(os.path.abspath(current_dir))
                     == os.path.normcase(os.path.abspath(skill_dir)))
    return (at_skill_root
            and os.path.isfile(os.path.join(skill_dir, 'SKILL.md')))
def _sandbox_walk_dirs(dirs: list[str], skill_dir: str, current_dir: str,
                       keep_test_tree: bool = False,
                       test_dirs: Iterable[str] | None = None) -> None:
    trees = test_tree_dirs(skill_dir) if test_dirs is None else test_dirs
    if keep_test_tree and in_tests_tree(current_dir, skill_dir, trees):
        dirs[:] = [d for d in dirs
                   if d.lower() not in _TEST_TREE_PRUNE_DIR_NAMES]
        return
    keep = _test_tree_walkable(trees) if keep_test_tree else set()
    dirs[:] = [d for d in dirs
               if d.lower() in keep
               or not _is_sandbox_copy_dir_excluded(
                   d, skill_dir, current_dir)]
def should_copy_file(
    name: str, extensions: Collection[str] | None = None,
    allow_hidden: bool = False,
) -> bool:
    return ((allow_hidden or not name.startswith("."))
            and (extensions is None
                 or os.path.splitext(name)[1].lower() in extensions))
def copy_for_mutation(
    target_dir: str,
    source_dir: str,
    copy_extensions: Collection[str] | None = None,
) -> None:
    test_dirs = test_tree_dirs(source_dir)
    for root, dirs, files in os.walk(source_dir):
        _sandbox_walk_dirs(
            dirs, source_dir, root,
            keep_test_tree=True, test_dirs=test_dirs)
        in_tests = in_tests_tree(root, source_dir, test_dirs)
        for f in files:
            if in_tests and f.lower().endswith(_TEST_TREE_BYTECODE_SUFFIXES):
                continue
            if not should_copy_file(
                    f, copy_extensions, allow_hidden=in_tests):
                continue
            if not in_tests and is_runtime_log_artifact(f):
                continue
            src = os.path.join(root, f)
            rel = os.path.relpath(src, source_dir)
            copy_one_mutation_file(
                src, rel, target_dir,
                _mutation_copy_size_limit(f, in_tests))
def _copy_package_sources(skill_dir, pkg_dst) -> None:
    test_dirs = test_tree_dirs(skill_dir)
    for root, dirs, files in os.walk(skill_dir):
        _sandbox_walk_dirs(dirs, skill_dir, root, test_dirs=test_dirs)
        dirs[:] = [
            d for d in dirs
            if not in_tests_tree(
                os.path.join(root, d), skill_dir, test_dirs)
        ]
        at_skill_root = (os.path.normcase(os.path.abspath(root))
                         == os.path.normcase(os.path.abspath(skill_dir)))
        for f in sorted(files):
            if at_skill_root and (
                    f.lower() == 'conftest.py' or is_test_source_basename(f)):
                continue
            if not should_copy_file(f) or is_runtime_log_artifact(f):
                continue
            src = os.path.join(root, f)
            rel = os.path.relpath(src, skill_dir)
            copy_one_mutation_file(
                src, rel, pkg_dst, _mutation_copy_size_limit(f))
def _mirror_root_asset_dir(src_dir, tmp_dir, rel_dir) -> None:
    for root, dirs, files in os.walk(src_dir):
        dirs[:] = [d for d in dirs if not is_out_of_scope_dir(d)]
        for name in sorted(files):
            if name.lower().endswith(_SOURCE_FILE_SUFFIXES):
                continue
            if not should_copy_file(name) or is_runtime_log_artifact(name):
                continue
            src = os.path.join(root, name)
            rel = os.path.join(rel_dir, os.path.relpath(src, src_dir))
            copy_one_mutation_file(
                src, rel, tmp_dir, _mutation_copy_size_limit(name))
def _copy_project_root_assets(skill_dir, tmp_dir) -> None:
    try:
        names = sorted(os.listdir(skill_dir))
    except OSError as e:
        _log.warning("[TestQuality] 根级资产列举失败（跳过根级镜像）: %s", e)
        return
    for name in names:
        src = os.path.join(skill_dir, name)
        if os.path.isdir(src):
            if not _is_sandbox_copy_dir_excluded(name, skill_dir, skill_dir):
                _mirror_root_asset_dir(src, tmp_dir, name)
            continue
        if not os.path.isfile(src):
            continue
        if name.lower() == 'conftest.py' or is_test_source_basename(name):
            copy_one_mutation_file(src, name, tmp_dir, None)
            continue
        if name.lower().endswith(_SOURCE_FILE_SUFFIXES):
            continue
        if not should_copy_file(name) or is_runtime_log_artifact(name):
            continue
        copy_one_mutation_file(
            src, name, tmp_dir, _mutation_copy_size_limit(name))
def _inside_package_dir(skill_dir: str, rel_dir: str) -> bool:
    parts = [part for part in rel_dir.split('/') if part]
    for depth in range(1, len(parts) + 1):
        if os.path.isfile(os.path.join(
                skill_dir, *parts[:depth], '__init__.py')):
            return True
    return False
def _copy_tests_dir(skill_dir, tmp_dir, pkg_dst=None) -> None:
    for name in test_tree_dirs(skill_dir):
        inside_package = bool(pkg_dst) and _inside_package_dir(skill_dir, name)
        target_root = pkg_dst if inside_package else tmp_dir
        dst = os.path.join(target_root, name)
        if inside_package and os.path.isdir(dst):
            continue
        shutil.copytree(
            os.path.join(skill_dir, name), dst,
            dirs_exist_ok=True,
            ignore=shutil.ignore_patterns(
                '__pycache__', '*.pyc', '*.pyo', '.pytest_cache'))
def _sandbox_test_path(tmp_dir: str, pkg_dst: str, rel_test: str) -> str:
    try:
        rel = str(rel_test or '').replace(os.sep, '/')
        parts = os.path.relpath(
            sandbox_path(tmp_dir, rel), tmp_dir).split(os.sep)
    except (OSError, TypeError, ValueError) as e:
        raise ValueError(
            f'测试路径越出突变沙箱，拒绝执行: {rel_test!r}') from e
    if os.path.isfile(os.path.join(pkg_dst, *parts)):
        return os.path.join(pkg_dst, *parts)
    return os.path.join(tmp_dir, *parts)
def copy_sandbox_sources(skill_dir, tmp_dir, pkg_dst) -> None:
    _copy_package_sources(skill_dir, pkg_dst)
    _copy_project_root_assets(skill_dir, tmp_dir)
    _copy_tests_dir(skill_dir, tmp_dir, pkg_dst)
def pin_minimal_pytest_ini(tmp_dir) -> None:
    try:
        with open(os.path.join(tmp_dir, 'pytest.ini'), 'w',
                  encoding='utf-8') as _ini_f:
            _ini_f.write("[pytest]\naddopts =\n")
    except OSError as e:
        _log.warning("[TestQuality] 副本 pytest.ini 生成失败（回退默认探测）: %s", e)
def prepare_mutation_sandbox(skill_dir: str) -> tuple[str, str] | None:
    tmp_base = os.path.join(get_temp_base(skill_dir), 'mutant_batch')
    try:
        os.makedirs(tmp_base, exist_ok=True)
    except OSError as e:
        _log.warning("[TestQuality] mutant_batch 目录准备失败（整批标记未杀死）: %s", e)
        return None
    cleanup_stale_entries(tmp_base, "stale mutant_batch")
    try:
        tmp_dir = make_temp_dir('mutant_batch_', tmp_base)
    except OSError as e:
        _log.warning("[TestQuality] mutant_batch 临时目录创建失败（整批标记未杀死）: %s", e)
        return None
    pkg_dst = sandbox_pkg_dst(tmp_dir, skill_dir)
    try:
        _mark_sandbox_active(tmp_dir)
        copy_sandbox_sources(skill_dir, tmp_dir, pkg_dst)
        pin_minimal_pytest_ini(tmp_dir)
    except (OSError, shutil.Error) as e:
        _log.warning("[TestQuality] 突变体副本准备失败（整批标记未杀死）: %s", e)
        _discard_sandbox(tmp_dir)
        return None
    return tmp_dir, pkg_dst
def _discard_sandbox(tmp_dir: str) -> None:
    if not tmp_dir:
        return
    try:
        two_level_rmtree(tmp_dir)
    except Exception as e:
        _log.warning("[TestQuality] 突变沙箱回收失败: %s", e, exc_info=True)
MUTATION_TIMEOUT = 30
SANDBOX_ENABLED = True
SANDBOX_ENV_VARS = {
    "MUTATION_SANDBOX": "1",
    "NO_NETWORK": "1",
    "ALLOWED_FS_ROOT": "",
}
SANDBOX_SKIP_ENV_VARS = {
    "SSH_AUTH_SOCK", "AWS_ACCESS_KEY_ID", "AWS_SECRET_ACCESS_KEY",
    "GITHUB_TOKEN", "GITLAB_TOKEN", "DOCKER_CONFIG",
    "KUBECONFIG", "AZURE_CLIENT_SECRET",
}
REMOVE_LINE = "line"
REMOVE_FUNCTION = "func"
_PYTEST_EXIT_NO_TESTS = 5
_UNITTEST_RAN_PATTERN = re.compile(r"^Ran (\d+) tests?", re.MULTILINE)
_UNITTEST_FAILURES_PATTERN = re.compile(r"FAILED \(.*?failures=(\d+)")
_UNITTEST_ERRORS_PATTERN = re.compile(r"FAILED \(.*?errors=(\d+)")
_UNITTEST_UNEXPECTED_SUCCESSES_PATTERN = re.compile(
    r"\bunexpected successes=(\d+)")
_UNITTEST_NOT_EXECUTED_PATTERNS = (
    re.compile(r"\bskipped=(\d+)"),
)
_NO_TESTS_MARKERS: tuple[str, ...] = (
    "no tests found",
    "no tests ran",
    "ran 0 tests",
    "ran 0 test",
    "collected 0 items",
)
_NO_TESTS_VERDICT_MARKER = f" [{_NO_TESTS_MARKERS[1]}]"
_NO_TESTS_ERROR = "no_tests_inconclusive"
_UNRELATED_FAILURE_MARKERS = (
    "ModuleNotFoundError", "ImportError",
    "fixture '", "FixtureLookupError",
    "collection error",
)
@dataclass
class MutationProbeOutcome:
    tests_passed: bool = False
    tests_ran: int = 0
    tests_failed: int = 0
    error: str = ""
    env_error: bool = False
def _source_lines(source: str) -> list[str]:
    normalized = source.replace('\r\n', '\n').replace('\r', '\n')
    lines = normalized.split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    return [line + '\n' for line in lines]
def _target_text_form(path: str) -> tuple[str, str]:
    try:
        with open(path, 'rb') as fh:
            raw = fh.read()
    except OSError:
        return 'utf-8', '\n'
    encoding = detect_source_encoding(raw)
    if b'\r\n' in raw:
        return encoding, '\r\n'
    return encoding, ('\r' if b'\r' in raw else '\n')
def _write_source_text(path: str, text: str) -> None:
    encoding, newline = _target_text_form(path)
    body = text.replace('\r\n', '\n').replace('\r', '\n')
    with open(path, 'w', encoding=encoding, newline=newline) as fh:
        fh.write(body)
def _remove_range(filepath: str, start_line: int, end_line: int) -> str | None:
    try:
        source = read_source_text_strict(filepath)
    except (OSError, UnicodeError, SyntaxError, ValueError) as e:
        _log.warning("[TestQuality] 待变异源码读取失败(不可判定): %s: %s",
                     filepath, e)
        return None
    lines = _source_lines(source)
    if start_line < 1 or end_line > len(lines) or end_line < start_line:
        return None
    removed_lines = lines[:start_line - 1] + lines[end_line:]
    cleaned = _clean_consecutive_blanks(removed_lines, start_line - 1)
    return "".join(cleaned)
def _clean_consecutive_blanks(lines: list, delete_pos: int) -> list:
    if not lines:
        return lines
    result = lines[:]
    pos = min(max(delete_pos, 0), len(result))
    start = pos
    while start > 0 and result[start - 1].strip() == "":
        start -= 1
    end = pos
    while end < len(result) and result[end].strip() == "":
        end += 1
    if end - start > 1:
        result = result[:start] + result[start:start + 1] + result[end:]
    return result
def _pytest_counts(output: str) -> dict[str, int]:
    return parse_pytest_summary_counts(locate_pytest_summary_line(output))
def _unittest_executed_count(output: str) -> int:
    matches = list(_UNITTEST_RAN_PATTERN.finditer(output))
    if not matches:
        return 0
    total = int(matches[-1].group(1))
    non_pass = 0
    for pattern in _UNITTEST_NOT_EXECUTED_PATTERNS:
        found = list(pattern.finditer(output))
        if found:
            non_pass += int(found[-1].group(1))
    return max(0, total - non_pass)
def _build_exec_env(prepend: Iterable[str], import_root: str,
                    allowed_root: str) -> dict[str, str]:
    env = _sandbox_env_base()
    entries = [entry for entry in prepend if entry]
    entries.extend(source_import_roots(import_root))
    ambient = env.get("PYTHONPATH", "")
    if ambient:
        entries.append(ambient)
    env["PYTHONPATH"] = os.pathsep.join(entries)
    if SANDBOX_ENABLED:
        env["ALLOWED_FS_ROOT"] = allowed_root
    return env
def _build_probe_env(work_dir: str) -> dict[str, str]:
    try:
        work_abs = os.path.abspath(work_dir)
    except (OSError, ValueError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc,
            context=f'_build_probe_env:{type(_swallowed_exc).__name__}')
        work_abs = work_dir
    return _build_exec_env(
        [work_abs, os.path.dirname(work_abs)], work_abs, work_abs)
def _pytest_error_sections(output: str) -> str:
    sections = []
    in_errors = False
    for line in output.splitlines():
        stripped = line.strip()
        if re.fullmatch(r"=+\s+ERRORS\s+=+", stripped):
            in_errors = True
        elif in_errors and re.fullmatch(r"=+\s+[^=]+?\s+=+", stripped):
            in_errors = False
        if in_errors:
            sections.append(line)
    return "\n".join(sections)
def _unrelated_tag_of(output: str) -> str:
    error_output = _pytest_error_sections(output)
    has_unrelated = any(m in error_output for m in _UNRELATED_FAILURE_MARKERS)
    return " [unrelated_failure]" if has_unrelated else ""
def _output_tail(output: str, *, mark_unrelated: bool = False) -> str:
    tail = output[-OUTPUT_TRUNCATE_LEN:]
    return tail + _unrelated_tag_of(output) if mark_unrelated else tail
def _interpret_pytest_output(
    proc, output: str,
) -> tuple[bool, int, int, str] | None:
    counts = _pytest_counts(output)
    ran = counts["passed"] + counts["failed"] + counts["errors"]
    if proc.returncode == 0:
        return True, counts["passed"], 0, _output_tail(output)
    if proc.returncode == 1:
        return False, ran, counts["failed"], _output_tail(
            output, mark_unrelated=True)
    if proc.returncode == _PYTEST_EXIT_NO_TESTS:
        return False, 0, 0, (
            _output_tail(output) + _NO_TESTS_VERDICT_MARKER)
    return False, 0, 0, _output_tail(output)
def _run_with_policy(
    cmd: list[str], work_dir: str, timeout: int, env: dict[str, str],
    interpret, *, label: str, missing_result,
    error_text,
):
    try:
        proc = _sp.run(  # jwsgj:suppress SYM-TAINT — 审计认可：cmd 由 _run_pytest/_run_unittest 内部构造（sys.executable 起始），覆盖测试为内部文件列表
            cmd,
            cwd=work_dir,
            capture_output=True,
            text=True, encoding="utf-8", errors="replace",
            timeout=timeout,
            env=env,
            check=False,
        )
    except _sp.TimeoutExpired as e:
        _log.warning("%s 运行超时: %s", label, e, exc_info=True)
        return False, 0, 0, "timeout"
    except FileNotFoundError:
        _log.warning("%s 测试运行器未找到", label, exc_info=True)
        return missing_result
    except (OSError, _sp.SubprocessError) as e:
        _log.warning("%s 运行错误: %s", label, e, exc_info=True)
        return False, 0, 0, error_text(e)
    return interpret(proc, proc.stdout + proc.stderr)
def _test_targets(test_files: Iterable[str] | str | None) -> list[str]:
    if isinstance(test_files, str):
        test_files = [test_files]
    targets: list[str] = []
    for target in test_files or ():
        try:
            value = os.fspath(target)
        except TypeError:
            continue
        if isinstance(value, str) and value:
            targets.append(value)
    return targets
def _run_pytest(
    work_dir: str, timeout: int, env: dict[str, str],
    test_files: Iterable[str] | str | None = None,
) -> tuple[bool, int, int, str] | None:
    if importlib.util.find_spec("pytest") is None:
        _log.warning("pytest not available, falling back to unittest")
        return None
    return _run_with_policy(
        [sys.executable, "-m", "pytest", "--maxfail=3", "--tb=short",
         *_PYTEST_QUIET_ARGS, *_test_targets(test_files)],
        work_dir, timeout, env, _interpret_pytest_output,
        label="pytest", missing_result=None, error_text=lambda _e: "")
def _interpret_unittest_output(
    proc, output: str,
) -> tuple[bool, int, int, str]:
    if proc.returncode == 0:
        return True, _unittest_executed_count(output), 0, _output_tail(output)
    if proc.returncode == 1:
        ran = _unittest_executed_count(output)
        fail_match = _UNITTEST_FAILURES_PATTERN.search(output)
        err_match = _UNITTEST_ERRORS_PATTERN.search(output)
        unexpected_match = _UNITTEST_UNEXPECTED_SUCCESSES_PATTERN.search(output)
        failed = (int(fail_match.group(1)) if fail_match else 0) + (
            int(unexpected_match.group(1)) if unexpected_match else 0)
        errors = int(err_match.group(1)) if err_match else 0
        text = _output_tail(output, mark_unrelated=True)
        if errors and not failed:
            text += " [unittest_errors_inconclusive]"
        return False, ran, failed, text
    return False, 0, 0, _output_tail(output)
def _unittest_cmds(
    work_dir: str, test_files: Iterable[str] | str | None,
) -> list[list[str]]:
    targets = _test_targets(test_files)
    if targets:
        return [[sys.executable, "-m", "unittest", *targets]]
    start_dirs = [
        candidate for name in test_tree_dirs(work_dir)
        if os.path.isdir(candidate := os.path.join(work_dir, name))
    ] or [work_dir]
    return [
        [sys.executable, "-m", "unittest", "discover", "-s", start_dir]
        for start_dir in start_dirs
    ]
def _run_unittest(
    work_dir: str, timeout: int, env: dict[str, str],
    test_files: Iterable[str] | str | None = None,
) -> tuple[bool, int, int, str]:
    outcomes = []
    for cmd in _unittest_cmds(work_dir, test_files):
        outcome = _run_with_policy(
            cmd, work_dir, timeout, env, _interpret_unittest_output,
            label="unittest",
            missing_result=(False, 0, 0, "no test runner found"),
            error_text=lambda e: str(e)[:OUTPUT_TRUNCATE_LEN])
        outcomes.append(outcome)
        if not outcome[0]:
            break
    return (
        all(outcome[0] for outcome in outcomes),
        sum(outcome[1] for outcome in outcomes),
        sum(outcome[2] for outcome in outcomes),
        _output_tail("\n".join(outcome[3] for outcome in outcomes if outcome[3])),
    )
def run_tests_in_dir(
    work_dir: str, timeout: int = MUTATION_TIMEOUT,
    test_files: Iterable[str] | str | None = None,
) -> tuple[bool, int, int, str]:
    env = _build_probe_env(work_dir)
    result = _run_pytest(work_dir, timeout, env, test_files)
    if result is not None:
        return result
    return _run_unittest(work_dir, timeout, env, test_files)
def _log_proc_stderr(killed: bool, returncode: int, stderr_tail: str) -> None:
    if not stderr_tail:
        return
    if killed:
        _log.debug(
            "[TestQuality] 突变体子进程 stderr(被杀死): %s",
            stderr_tail)
    else:
        _log.warning(
            "[TestQuality] 突变体子进程 returncode=%s "
            "但 stderr 非空: %s", returncode, stderr_tail)
def _pytest_exit_verdict(
    returncode, output: str | None = None,
) -> tuple[bool, str]:
    try:
        rc = int(returncode)
    except (TypeError, ValueError) as e:
        _log.debug("_pytest_exit_verdict 退出码不可解析: %r (%s)",
                     returncode, e)
        return False, "pytest_exit_unknown_inconclusive"
    counts = _pytest_counts(output or "")
    if rc == 0:
        if counts["passed"] == 0:
            return False, _NO_TESTS_ERROR
        return False, ""
    if rc == 1:
        if counts["failed"] > 0:
            return True, ""
        return False, "pytest_exit_1_no_failed_inconclusive"
    if rc == _PYTEST_EXIT_NO_TESTS:
        return False, _NO_TESTS_ERROR
    return False, f"pytest_exit_{rc}_inconclusive"
def proc_verdict(proc) -> tuple[bool, str]:
    _stdout = getattr(proc, 'stdout', None) or ''
    _stderr = getattr(proc, 'stderr', None) or ''
    killed, error = _pytest_exit_verdict(
        getattr(proc, 'returncode', None), _stdout + _stderr)
    if error:
        _log.warning(
            "[TestQuality] 突变体子进程退出码 %s 未产生用例失败"
            "（测试未正常评估，判不可判定）",
            getattr(proc, 'returncode', None))
    _stderr_tail = _stderr.strip()[-500:]
    _log_proc_stderr(killed, getattr(proc, 'returncode', None), _stderr_tail)
    return killed, error
_mutation_bridge_base: Any = None
_mutation_bridge_contexts: list[tuple[object, Any]] = []
_test_bridge_for_mutation: Any = None
_test_bridge_for_mutation_lock = threading.Lock()
def _refresh_mutation_bridge_locked() -> None:
    global _test_bridge_for_mutation
    _test_bridge_for_mutation = (
        _mutation_bridge_contexts[-1][1]
        if _mutation_bridge_contexts else _mutation_bridge_base
    )
def set_mutation_test_bridge(bridge: Any) -> None:
    global _mutation_bridge_base
    with _test_bridge_for_mutation_lock:
        _mutation_bridge_base = bridge
        _refresh_mutation_bridge_locked()
@contextmanager
def install_mutation_test_bridge(bridge: Any) -> Iterator[None]:
    global _test_bridge_for_mutation
    token = object()
    with _test_bridge_for_mutation_lock:
        _mutation_bridge_contexts.append((token, bridge))
        _test_bridge_for_mutation = bridge
    try:
        yield
    finally:
        with _test_bridge_for_mutation_lock:
            for index, (installed_token, _) in enumerate(
                    _mutation_bridge_contexts):
                if installed_token is token:
                    _mutation_bridge_contexts.pop(index)
                    break
            _refresh_mutation_bridge_locked()
def get_mutation_test_bridge() -> Any:
    with _test_bridge_for_mutation_lock:
        return _test_bridge_for_mutation
def mutation_bridge_runner() -> Any:
    bridge = get_mutation_test_bridge()
    if bridge is None or not hasattr(bridge, "runner"):
        return None
    runner = getattr(bridge, "runner", None)
    if not hasattr(runner, "run_mutation_check"):
        return None
    return runner
def _syntax_precheck(modified_source: str, filepath: str) -> str | None:
    try:
        compile(modified_source, filepath, "exec")
    except (SyntaxError, ValueError) as syn_err:
        log_swallowed(
            __name__, syn_err,
            context=f'_syntax_precheck:{type(syn_err).__name__}')
        return ("mutation_syntax_error_inconclusive: "
                f"{getattr(syn_err, 'msg', type(syn_err).__name__)[:120]}")
    return None
def _probe_sandbox_guard(filepath: str, skill_dir: str) -> tuple[str, str]:
    try:
        rel = os.path.relpath(filepath, skill_dir)
    except ValueError as e:
        log_swallowed(
            __name__, e, context='_probe_sandbox_guard:ValueError')
        return "", "path_escape_inconclusive: 目标文件越出技能根沙箱"
    if (rel == os.pardir or rel.startswith(os.pardir + os.sep)
            or os.path.isabs(rel)):
        return rel, "path_escape_inconclusive: 目标文件越出技能根沙箱"
    path_safe, path_error = check_path_traversal(skill_dir, filepath)
    if not path_safe:
        return rel, f"path_escape_inconclusive: {path_error}"
    return rel, ""
_BRIDGE_FALLBACK_ERRORS = (
    OSError, ValueError, KeyError, TypeError, RuntimeError,
    _sp.TimeoutExpired,
)
def _bridge_outcome(bridge_result: Any) -> MutationProbeOutcome:
    killed = getattr(bridge_result, "killed", False)
    survived = getattr(bridge_result, "survived", False)
    tests_ran = getattr(bridge_result, "tests_ran", 0)
    tests_failed = getattr(bridge_result, "tests_failed", 0)
    outcome = MutationProbeOutcome(
        tests_ran=tests_ran if type(tests_ran) is int else 0,
        tests_failed=tests_failed if type(tests_failed) is int else 0,
    )
    invalid = (
        type(killed) is not bool or type(survived) is not bool
        or (killed and survived)
        or type(tests_ran) is not int or type(tests_failed) is not int
        or tests_ran < 0 or tests_failed < 0 or tests_failed > tests_ran
        or (killed and tests_failed == 0)
        or (survived and (tests_ran == 0 or tests_failed != 0))
    )
    if invalid:
        outcome.error = "invalid_bridge_result_inconclusive"
        outcome.env_error = True
        return outcome
    bridge_error = getattr(bridge_result, "error", None)
    if bridge_error:
        bridge_error_text = str(bridge_error)
        outcome.error = bridge_error_text[:300]
        outcome.env_error = bridge_error_text != _NO_TESTS_ERROR
        return outcome
    if survived:
        outcome.tests_passed = True
    elif not killed:
        outcome.error = "inconclusive_bridge"
        outcome.env_error = True
    return outcome
def _try_bridge_mutation(
    filepath: str, modified_source: str, timeout: int,
) -> MutationProbeOutcome | None:
    runner = mutation_bridge_runner()
    if runner is None:
        return None
    try:
        original_source = read_source_text_strict(filepath)
        baseline = _bridge_outcome(runner.run_mutation_check(
            filepath, original_source, timeout=timeout,
        ))
        if baseline.error:
            baseline.error = f"baseline_{baseline.error}"
            baseline.tests_passed = False
            baseline.env_error = True
            return baseline
        if not baseline.tests_passed:
            baseline.error = _BASELINE_FAILED_ERROR
            baseline.env_error = True
            return baseline
        bridge_result = runner.run_mutation_check(
            filepath, modified_source, timeout=timeout,
        )
    except _BRIDGE_FALLBACK_ERRORS as e:
        _log.warning("[Mutation] bridge 快路径失败，回退沙箱复制模式: %s", e)
        return None
    return _bridge_outcome(bridge_result)
def _interpret_test_outcome(passed: bool, ran: int, failed: int,
                            output: str) -> MutationProbeOutcome:
    output = output or ""
    outcome = MutationProbeOutcome(
        tests_passed=passed, tests_ran=ran, tests_failed=failed)
    output_tail = output.rstrip()
    if not passed and output_tail.endswith(" [unrelated_failure]"):
        outcome.error = "unrelated_test_failure_inconclusive"
        outcome.env_error = True
        return outcome
    if not passed and output_tail.endswith(" [unittest_errors_inconclusive]"):
        outcome.error = "unittest_errors_inconclusive"
        outcome.env_error = True
        return outcome
    if not ran and not failed:
        output_lower = output.lower()
        if passed or any(p in output_lower for p in _NO_TESTS_MARKERS):
            outcome.error = _NO_TESTS_ERROR
        else:
            outcome.error = "timeout_or_runner_error_inconclusive"
            outcome.env_error = True
        return outcome
    if not passed and failed == 0:
        outcome.error = "no_failed_tests_inconclusive"
        outcome.env_error = True
    return outcome
def _mapped_test_files(test_map: Mapping[str, dict] | None,
                       rel_path: str) -> list[str]:
    if not isinstance(test_map, Mapping):
        return []
    entry = test_map.get(rel_path)
    if not isinstance(entry, Mapping):
        return []
    return _test_targets(entry.get('test_files'))
def _run_baseline_probe(
    work_dir: str, timeout: int, test_files: Iterable[str] | str | None,
) -> MutationProbeOutcome:
    outcome = _interpret_test_outcome(*run_tests_in_dir(
        work_dir, timeout, test_files=test_files))
    if not outcome.error and outcome.tests_passed:
        return outcome
    outcome.error = (f"baseline_{outcome.error}" if outcome.error
                     else _BASELINE_FAILED_ERROR)
    outcome.tests_passed = False
    outcome.env_error = True
    return outcome
def _copy_probe_run(rel: str, modified_source: str,
                    skill_dir: str, timeout: int,
                    test_files: Iterable[str] | str | None = None
                    ) -> MutationProbeOutcome:
    outcome = MutationProbeOutcome()
    tmp_dir = None
    try:
        _tmp_base = os.path.join(get_temp_base(skill_dir), 'mutation')
        os.makedirs(_tmp_base, exist_ok=True)
        cleanup_stale_entries(_tmp_base, "stale mutation sandbox")
        tmp_dir = make_temp_dir("mutation_", _tmp_base)
        _mark_sandbox_active(tmp_dir)
        pkg_dir = sandbox_pkg_dst(tmp_dir, skill_dir)
        copy_for_mutation(pkg_dir, skill_dir)
        pin_minimal_pytest_ini(pkg_dir)
        try:
            test_paths = [_sandbox_test_path(tmp_dir, pkg_dir, tf)
                          for tf in _test_targets(test_files)]
        except (OSError, TypeError, ValueError) as e:
            _log.warning(
                "[TestQuality] 测试路径越出突变沙箱（不可判定）: %s", e)
            return MutationProbeOutcome(
                error="path_escape_inconclusive")
        baseline = _run_baseline_probe(pkg_dir, timeout, test_paths)
        if baseline.error:
            return baseline
        tmp_file = os.path.join(pkg_dir, rel)
        os.makedirs(os.path.dirname(tmp_file), exist_ok=True)
        _write_source_text(tmp_file, modified_source)
        passed, ran, failed, output = run_tests_in_dir(
            pkg_dir, timeout, test_files=test_paths)
        outcome = _interpret_test_outcome(passed, ran, failed, output)
    finally:
        try:
            if tmp_dir is not None:
                two_level_rmtree(tmp_dir)
        except Exception as e:
            _log.warning(
                "[Mutation] 突变探针沙箱清理失败: %s", e, exc_info=True)
    return outcome
def probe_mutation(
    filepath: str,
    target_type: str,
    start_line: int,
    end_line: int,
    skill_dir: str,
    timeout: int = MUTATION_TIMEOUT,
    test_map: Mapping[str, dict] | None = None,
) -> MutationProbeOutcome:
    rel, _guard_error = _probe_sandbox_guard(filepath, skill_dir)
    if _guard_error:
        return MutationProbeOutcome(error=_guard_error)
    if target_type not in (REMOVE_FUNCTION, REMOVE_LINE):
        return MutationProbeOutcome(
            error=f"invalid_target_type_inconclusive: {target_type!r}")
    try:
        start = int(start_line)
        end = int(end_line)
    except (TypeError, ValueError):
        return MutationProbeOutcome(
            error=f"invalid_range_inconclusive: {start_line!r}-{end_line!r}")
    if start < 1 or end < start:
        return MutationProbeOutcome(
            error=f"invalid_range_inconclusive: {start}-{end}")
    modified_source = _remove_range(
        filepath, start, end if target_type == REMOVE_FUNCTION else start)
    if modified_source is None:
        return MutationProbeOutcome(
            error="target_removal_unavailable_inconclusive")
    _syn_error = _syntax_precheck(modified_source, filepath)
    if _syn_error is not None:
        return MutationProbeOutcome(error=_syn_error)
    if test_map is None:
        test_map = build_mutation_test_mapping(skill_dir)
    test_files = _mapped_test_files(test_map, rel.replace(os.sep, '/'))
    bridge_outcome = _try_bridge_mutation(
        filepath, modified_source, timeout)
    if bridge_outcome is not None:
        return bridge_outcome
    return _copy_probe_run(
        rel, modified_source, skill_dir, timeout, test_files)
class _BatchJob(NamedTuple):
    mutants: list
    skill_dir: str
    test_timeout: int
def _chunk_mutants_by_file_group(all_mutants, skill_dir, test_timeout):
    file_groups: dict[str, list] = defaultdict(list)
    for m in all_mutants:
        file_groups[m['rel_path']].append(m)
    num_workers = max(1, min(os.cpu_count() or 4, 4, len(file_groups)))
    chunks = [[] for _ in range(num_workers)]
    for i, group in enumerate(file_groups.values()):
        chunks[i % num_workers].extend(group)
    jobs = [_BatchJob(chunk, skill_dir, test_timeout)
            for chunk in chunks if chunk]
    return num_workers, jobs
def _evaluate_worker(job: _BatchJob) -> list:
    try:
        return _evaluate_mutant_batch(
            job.mutants, job.skill_dir, job.test_timeout)
    except Exception as exc:
        _log.warning(
            "[TestQuality] 突变评估 worker 异常(降级不可判定): %s",
            exc, exc_info=True)
        return _all_survived(
            job.mutants, f"worker_exception:{type(exc).__name__}")
def _run_mutant_batches(jobs: list[_BatchJob], num_workers: int) -> list:
    if num_workers <= 1 or len(jobs) <= 1:
        return [r for job in jobs for r in _evaluate_worker(job)]
    with ThreadPoolExecutor(max_workers=num_workers) as executor:
        batch_results = list(executor.map(_evaluate_worker, jobs))
    return [r for batch in batch_results for r in batch]
def run_mutation_batch(mutants, skill_dir: str,
                       test_timeout: int) -> tuple[int, list]:
    num_workers, jobs = _chunk_mutants_by_file_group(
        mutants, skill_dir, test_timeout)
    results = _run_mutant_batches(jobs, num_workers)
    return min(num_workers, len(jobs)) or 1, results
@dataclass
class _SandboxContext:
    tmp_dir: str
    pkg_dst: str
    skill_dir: str
    env: dict
    timeout: int
    restore_failed: bool = False
def _mutant_result(mutant, killed: bool, error: str = "") -> dict:
    result = {'rel_path': mutant['rel_path'], 'line': mutant['line'],
              'killed': killed}
    if error:
        result['error'] = error
    return result
def _all_survived(mutants, error: str = "") -> list:
    return [_mutant_result(m, False, error) for m in mutants]
def _restore_group_source(group_mutants, tmp_dir, skill_dir) -> bool:
    _rel = group_mutants[0]['rel_path'] if group_mutants else None
    if not _rel:
        return True
    return _restore_mutant_file(
        _rel, os.path.join(sandbox_pkg_dst(tmp_dir, skill_dir), _rel),
        skill_dir, "批处理异常后恢复原文件失败(源被占用/删除)")
def _sandbox_env_base() -> dict[str, str]:
    env = subprocess_noartifact_env()
    env.pop("PYTEST_ADDOPTS", None)
    for key in SANDBOX_SKIP_ENV_VARS:
        env.pop(key, None)
    if SANDBOX_ENABLED:
        env.update(SANDBOX_ENV_VARS)
    return env
def _restore_mutant_file(rel_path, mutant_file, skill_dir, fail_msg) -> bool:
    try:
        shutil.copy2(os.path.join(skill_dir, rel_path), mutant_file)
        return True
    except OSError:
        _log.warning("%s: %s", fail_msg, rel_path, exc_info=True)
        return False
def _write_mutant(mutant, mutant_file) -> bool:
    try:
        os.makedirs(os.path.dirname(mutant_file), exist_ok=True)
        _write_source_text(mutant_file, mutant['mutated'])
        return True
    except (OSError, UnicodeError, LookupError) as e:
        _log.warning("[TestQuality] 突变体写入失败（标记未杀死）: %s: %s",
                       mutant['rel_path'], e)
        return False
def _evaluate_single_mutant(mutant, ctx: _SandboxContext) -> dict:
    mutant_file = os.path.join(ctx.pkg_dst, mutant['rel_path'])
    if not _write_mutant(mutant, mutant_file):
        restored = _restore_mutant_file(
            mutant['rel_path'], mutant_file, ctx.skill_dir,
            "写入失败后恢复原文件失败(源被占用/删除)")
        if not restored:
            ctx.restore_failed = True
        return _mutant_result(mutant, False, "mutant_write_failed")
    killed, error = _run_single_pytest(mutant['test_files'], ctx)
    restored = _restore_mutant_file(
        mutant['rel_path'], mutant_file, ctx.skill_dir,
        "恢复原始文件失败(源被占用/删除)")
    if not restored:
        ctx.restore_failed = True
    return _mutant_result(mutant, killed, error)
def _run_single_pytest(test_files, ctx: _SandboxContext) -> tuple[bool, str]:
    try:
        test_paths = [_sandbox_test_path(ctx.tmp_dir, ctx.pkg_dst, t)
                      for t in test_files]
    except (OSError, TypeError, ValueError) as e:
        _log.warning(
            "[TestQuality] 测试路径越出突变沙箱（不可判定）: %s", e)
        return False, "path_escape_inconclusive"
    cmd = ([sys.executable, '-m', 'pytest', '-x', '--tb=no',
            *_PYTEST_QUIET_ARGS] + test_paths)
    try:
        proc = _sp.run(
            cmd, capture_output=True, text=True, encoding='utf-8', errors='replace',
            timeout=ctx.timeout, cwd=ctx.tmp_dir, env=ctx.env, check=False
        )
        return proc_verdict(proc)
    except _sp.TimeoutExpired as _e:
        _log.warning("[TestQuality] 单突变体评估超时(标记未杀死): %s", _e, exc_info=True)
        return False, "mutant_timeout"
    except Exception as e:
        _log.warning("[TestQuality] 变异评估异常,标记未杀死: %s", e)
        return False, "mutant_run_exception"
def _evaluate_mutant_batch(mutants, skill_dir, timeout):
    sandbox = prepare_mutation_sandbox(skill_dir)
    if sandbox is None:
        return _all_survived(mutants, "sandbox_unavailable")
    tmp_dir, pkg_dst = sandbox
    try:
        ctx = _SandboxContext(
            tmp_dir=tmp_dir, pkg_dst=pkg_dst, skill_dir=skill_dir,
            env=_build_exec_env([tmp_dir, pkg_dst], pkg_dst, tmp_dir),
            timeout=timeout)
        return _dispatch_groups(mutants, ctx)
    finally:
        _discard_sandbox(tmp_dir)
def _baseline_group_error(test_files, ctx: _SandboxContext) -> str:
    killed, error = _run_single_pytest(test_files, ctx)
    if error:
        return f"baseline_{error}"
    return _BASELINE_FAILED_ERROR if killed else ""
def _group_mutant_path_error(group_mutants, ctx: _SandboxContext) -> str:
    rel_path = group_mutants[0]['rel_path']
    try:
        sandbox_path(ctx.skill_dir, rel_path)
        sandbox_path(ctx.pkg_dst, rel_path)
    except (OSError, TypeError, ValueError) as e:
        _log.warning(
            "[TestQuality] 突变体目标越出技能根/沙箱（不可判定）: %r: %s",
            rel_path, e)
        return "path_escape_inconclusive"
    for mutant in group_mutants:
        for test_file in _test_targets(mutant.get('test_files')):
            try:
                _sandbox_test_path(ctx.tmp_dir, ctx.pkg_dst, test_file)
            except (OSError, TypeError, ValueError) as e:
                _log.warning(
                    "[TestQuality] 测试路径越出突变沙箱（不可判定）: %r: %s",
                    test_file, e)
                return "path_escape_inconclusive"
    return ""
def _dispatch_groups(mutants, ctx: _SandboxContext) -> list:
    groups = defaultdict(list)
    for mutant in mutants:
        groups[mutant['rel_path']].append(mutant)
    grouped = list(groups.values())
    results = []
    for index, group_mutants in enumerate(grouped):
        baseline_error = (
            _group_mutant_path_error(group_mutants, ctx)
            or _baseline_group_error(group_mutants[0]['test_files'], ctx))
        if baseline_error:
            group_results = _all_survived(group_mutants, baseline_error)
        elif len(group_mutants) <= 1:
            group_results = [_evaluate_single_mutant(mutant, ctx)
                             for mutant in group_mutants]
        else:
            group_results = _run_grouped_mutants(group_mutants, ctx)
        results.extend(group_results)
        if ctx.restore_failed or any(
                r.get('error') == 'mutant_restore_failed'
                for r in group_results):
            remaining = [
                mutant for later_group in grouped[index + 1:]
                for mutant in later_group
            ]
            results.extend(_all_survived(
                remaining, 'mutant_restore_aborted'))
            break
    return results
def _batch_mutant_payload(group_mutants) -> str:
    return json.dumps([
        {
            'rel_path': m['rel_path'],
            'line': m['line'],
            'mutated': m['mutated'],
            'test_files': m['test_files'],
        }
        for m in group_mutants
    ])
def _render_batch_script(template: str, replacements: dict[str, str]) -> str:
    if not replacements:
        return template
    pattern = re.compile("|".join(
        re.escape(key) for key in sorted(replacements, key=len, reverse=True)))
    return pattern.sub(lambda m: replacements[m.group(0)], template)
def _build_batch_script(group_mutants, tmp_dir, skill_dir) -> str:
    return _render_batch_script(_BATCH_PROGRAM_TEMPLATE, {
        "__MUTANT_DATA__": repr(_batch_mutant_payload(group_mutants)),
        "__TMP_DIR__": repr(tmp_dir),
        "__PKG_NAME__": repr(sandbox_pkg_name(skill_dir)),
        "__SKILL_DIR__": repr(skill_dir),
        "__QUIET_ARGS__": repr(list(_PYTEST_QUIET_ARGS)),
    })
_BATCH_PROGRAM_TEMPLATE = r"""import sys, os, io, json, shutil, importlib, tokenize
detect_encoding = tokenize.detect_encoding

# 批处理：进程内 pytest 执行
MUTANT_DATA = json.loads(__MUTANT_DATA__)
TMP_DIR = __TMP_DIR__
PKG_NAME = __PKG_NAME__
SKILL_DIR = __SKILL_DIR__
PKG_DIR = os.path.join(TMP_DIR, PKG_NAME)
QUIET_ARGS = __QUIET_ARGS__
_SANDBOX_ROOT = os.path.normcase(os.path.abspath(TMP_DIR))

def _sandbox_test_path(rel_test):
    # 测试树在副本根（自定义容器）与包面副本（包内测试树）两处各有一份：
    # 固定拼副本根会让包内测试路径不存在，pytest 以用法错误退出。
    parts = [part for part in str(rel_test or '').replace(os.sep, '/').split('/')
             if part]
    if not parts or os.path.isabs(rel_test):
        raise ValueError('test path escapes sandbox: %r' % (rel_test,))
    try:
        sandbox_parts = _sandbox_segments(parts)
        candidate = os.path.join(TMP_DIR, *sandbox_parts)
        if not _is_under_sandbox(candidate):
            raise ValueError(candidate)
    except (OSError, TypeError, ValueError) as exc:
        raise ValueError(
            'test path escapes sandbox: %r' % (rel_test,)) from exc
    for base in (TMP_DIR, PKG_DIR):
        candidate = os.path.join(base, *sandbox_parts)
        if os.path.isfile(candidate):
            return candidate
    return os.path.join(TMP_DIR, *sandbox_parts)

def _is_under_sandbox(path):
    try:
        norm = os.path.normcase(os.path.abspath(path))
    except (OSError, ValueError):
        return False
    return norm == _SANDBOX_ROOT or norm.startswith(_SANDBOX_ROOT + os.sep)

def _sandbox_segments(parts):
    resolved = []
    for part in parts:
        if part in ('', '.'):
            continue
        if part == '..':
            if resolved:
                resolved.pop()
            else:
                raise ValueError('.. escapes sandbox')
        else:
            resolved.append(part)
    return resolved

def _sandbox_module_names():
    # 以导入来源而非模块名前缀识别缓存：测试辅助模块/conftest/测试包
    # 都可能持有被突变符号的旧绑定，必须一律随沙箱源码重导。
    names = set()
    for name, mod in list(sys.modules.items()):
        if mod is None:
            continue
        origins = []
        origin = getattr(mod, '__file__', None)
        if isinstance(origin, str) and origin:
            origins.append(origin)
        paths = getattr(mod, '__path__', None)
        if paths:
            try:
                origins.extend(str(p) for p in paths)
            except TypeError:
                pass
        if any(_is_under_sandbox(p) for p in origins):
            names.add(name)
    return names

results = []


class _MutationResultRecorder:
    # 记录 call 阶段真实断言失败数：setup/teardown/fixture 异常也计入
    # rc=1，但这类 error 没有评估到突变体。只认 call 阶段 failed，才能与
    # _interpret_test_outcome 的“无用例失败即不可判定”口径一致，避免
    # teardown error 被当成突变被杀死、把分数抬成假绿。
    def __init__(self):
        self.call_failed = 0
        self.call_passed = 0

    def pytest_runtest_logreport(self, report):
        if report.when != 'call':
            return
        if report.failed:
            self.call_failed += 1
        elif report.passed:
            self.call_passed += 1


try:
    import pytest
except ImportError:
    for m in MUTANT_DATA:
        results.append({'rel_path': m['rel_path'], 'line': m['line'],
                        'killed': False, 'error': 'pytest_unavailable'})
    print('BATCH_JSON:' + json.dumps(results))
    sys.exit(0)

def _write_mutant_source(path, text):
    # 与原文件同编码/同行尾写回：声明 `# coding: gbk` 的源被 UTF-8 覆盖后
    # 子进程按声明解码，变异体不可执行，整批判定降级为不可判定。
    try:
        with open(path, 'rb') as fh:
            raw = fh.read()
    except OSError:
        raw = b''
    try:
        encoding = detect_encoding(io.BytesIO(raw).readline)[0] or 'utf-8'
    except (SyntaxError, UnicodeDecodeError, LookupError):
        encoding = 'utf-8'
    if b'\r\n' in raw:
        newline = '\r\n'
    elif b'\r' in raw:
        newline = '\r'
    else:
        newline = '\n'
    body = text.replace('\r\n', '\n').replace('\r', '\n')
    with open(path, 'w', encoding=encoding, newline=newline) as f:
        f.write(body)

def _restore_source_or_abort(start_index, mutant_file):
    # 恢复失败时当前与后续样本均不可判定，并停止污染执行面。
    current = MUTANT_DATA[start_index]
    try:
        shutil.copy2(os.path.join(SKILL_DIR, current['rel_path']), mutant_file)
    except OSError:
        sys.stderr.write('mutant restore failed: %s\n' % current['rel_path'])
        for index in range(start_index, len(MUTANT_DATA)):
            pending = MUTANT_DATA[index]
            results.append({
                'rel_path': pending['rel_path'],
                'line': pending['line'],
                'killed': False,
                'error': ('mutant_restore_failed' if index == start_index
                          else 'mutant_restore_aborted'),
            })
        return False
    return True

for mutant_index, m in enumerate(MUTANT_DATA):
    mutant_file = os.path.join(PKG_DIR, m['rel_path'])
    # 写失败先恢复原文件再降级存活，防半写残留毒害同批。
    try:
        os.makedirs(os.path.dirname(mutant_file), exist_ok=True)
        _write_mutant_source(mutant_file, m['mutated'])
    except (OSError, UnicodeError, LookupError):
        sys.stderr.write('mutant write failed: %s\n' % m['rel_path'])
        if not _restore_source_or_abort(mutant_index, mutant_file):
            break
        results.append({'rel_path': m['rel_path'], 'line': m['line'],
                        'killed': False, 'error': 'mutant_write_failed'})
        continue

    rel_mod = os.path.splitext(m['rel_path'])[0].replace('/', '.')
    # 全链清除模块缓存：叶模块、祖先包、包名前缀与平铺名。只清叶模块不够——
    # 祖先包对象仍在 sys.modules 且持有旧子模块/旧再导出绑定，
    # `from pkg import name` 会直接复用旧绑定，使后续突变体假存活。
    rel_parts = rel_mod.split('.')
    rel_ancestors = ['.'.join(rel_parts[:i]) for i in range(1, len(rel_parts))]
    keys_to_remove = _sandbox_module_names()
    keys_to_remove.update(
        k for k in sys.modules
        if k == PKG_NAME or k.startswith(PKG_NAME + '.')
        or k == rel_mod or k.startswith(rel_mod + '.'))
    for _ancestor in rel_ancestors:
        keys_to_remove.update(
            k for k in sys.modules
            if k == _ancestor or k.startswith(_ancestor + '.'))
    for tf in m['test_files']:
        tf_mod = os.path.splitext(os.path.basename(tf))[0]
        # 测试模块双口径：tests 带 __init__.py 时以 tests.test_x 导入。
        tf_pkg = os.path.splitext(tf.replace('/', '.'))[0]
        keys_to_remove.update(
            k for k in sys.modules
            if k == tf_mod or k.startswith(tf_mod + '.')
            or k == tf_pkg or k.startswith(tf_pkg + '.'))
    for k in keys_to_remove:
        sys.modules.pop(k, None)
    importlib.invalidate_caches()

    try:
        test_paths = [_sandbox_test_path(t) for t in m['test_files']]
    except (OSError, TypeError, ValueError):
        if not _restore_source_or_abort(mutant_index, mutant_file):
            break
        results.append({'rel_path': m['rel_path'], 'line': m['line'],
                        'killed': False, 'error': 'path_escape_inconclusive'})
        continue
    # 仅 rc=1（用例失败）算杀死；收集错误/中断/内部错误（2/3/4）与未收集
    # 用例（5）说明测试未正常评估突变体，标记为不可判定而不是假杀死。
    recorder = _MutationResultRecorder()
    try:
        exit_code = int(pytest.main(
            test_paths + ['-x', '--tb=no', *QUIET_ARGS],
            plugins=[recorder]))
    except Exception:
        exit_code = -1
    if exit_code == 1 and recorder.call_failed > 0:
        killed, err = True, ''
    elif exit_code == 0 and recorder.call_passed > 0:
        killed, err = False, ''
    elif exit_code == 0:
        killed, err = False, 'no_tests_inconclusive'
    elif exit_code == 1:
        killed, err = False, 'pytest_exit_1_no_failed_inconclusive'
    else:
        killed, err = False, 'pytest_exit_%s_inconclusive' % exit_code

    # 恢复源与单体路径同口径：SKILL_DIR 实时源；失败则停止本批，
    # 防止上一条突变源码污染后续样本。
    if not _restore_source_or_abort(mutant_index, mutant_file):
        break

    results.append({
        'rel_path': m['rel_path'],
        'line': m['line'],
        'killed': killed,
        'error': err,
    })

print('BATCH_JSON:' + json.dumps(results))
"""
def _batch_results_complete(parsed: list, group_mutants: list) -> bool:
    if len(parsed) != len(group_mutants):
        return False
    expected = Counter((m['rel_path'], m['line']) for m in group_mutants)
    got: Counter = Counter()
    for item in parsed:
        if (not isinstance(item, dict)
                or type(item.get('killed')) is not bool
                or not isinstance(item.get('rel_path'), str)
                or type(item.get('line')) is not int):
            return False
        got[(item['rel_path'], item['line'])] += 1
    return got == expected
def _parse_batch_output(proc, group_mutants) -> list:
    stdout = getattr(proc, 'stdout', None) or ''
    stderr_tail = (getattr(proc, 'stderr', None) or '').strip()[-500:]
    if stderr_tail:
        _log.warning("[TestQuality] 突变批处理子进程 stderr: %s", stderr_tail)
    for line in reversed(stdout.split('\n')):
        if line.startswith('BATCH_JSON:'):
            try:
                parsed = json.loads(line[len('BATCH_JSON:'):])
            except (ValueError, TypeError) as e:
                _log.warning(
                    "[TestQuality] 突变批处理结果 JSON 解析失败(回退不可判定): %s", e)
                return _all_survived(group_mutants, "batch_output_unparsable")
            if not isinstance(parsed, list):
                _log.warning(
                    "[TestQuality] 突变批处理结果非列表(%s)，回退不可判定",
                    type(parsed).__name__)
                return _all_survived(group_mutants, "batch_output_invalid")
            if not _batch_results_complete(parsed, group_mutants):
                _log.warning(
                    "[TestQuality] 突变批处理结果与提交的突变体不匹配"
                    "（提交 %d 条 / 返回 %d 条），回退不可判定防分母缩水",
                    len(group_mutants), len(parsed))
                return _all_survived(
                    group_mutants, "batch_output_incomplete")
            return parsed
    _log.warning(
        "[TestQuality] 突变批处理输出缺失 BATCH_JSON(returncode=%s)，"
        "回退不可判定; stdout尾部: %s",
        getattr(proc, 'returncode', None), stdout.strip()[-300:])
    return _all_survived(group_mutants, "batch_output_missing")
def _run_grouped_mutants(group_mutants, ctx: _SandboxContext):
    batch_script = _build_batch_script(
        group_mutants, ctx.tmp_dir, ctx.skill_dir)
    cmd = [sys.executable, '-']
    try:
        proc = _sp.run(
            cmd, input=batch_script, capture_output=True, text=True,
            encoding='utf-8', errors='replace',
            timeout=ctx.timeout * len(group_mutants) + 10,
            cwd=ctx.tmp_dir, env=ctx.env, check=False
        )
        results = _parse_batch_output(proc, group_mutants)
        if any(str(r.get('error', '')).startswith('batch_output_')
               for r in results):
            restored = _restore_group_source(
                group_mutants, ctx.tmp_dir, ctx.skill_dir)
            if not restored:
                ctx.restore_failed = True
        return results
    except _sp.TimeoutExpired as _e:
        _log.warning("[TestQuality] 突变批执行超时(回退全部存活): %s", _e, exc_info=True)
        if not _restore_group_source(
                group_mutants, ctx.tmp_dir, ctx.skill_dir):
            ctx.restore_failed = True
        return _all_survived(group_mutants, 'batch_timeout')
    except Exception as e:
        _log.warning("[TestQuality] 变异批执行失败,标记未杀死: %s", e)
        if not _restore_group_source(
                group_mutants, ctx.tmp_dir, ctx.skill_dir):
            ctx.restore_failed = True
        return _all_survived(group_mutants, 'batch_run_exception')

from __future__ import annotations

import contextlib
import hashlib
import importlib.util
import logging
import os
import sys
import time
from dataclasses import MISSING, dataclass, field
from dataclasses import fields as dataclass_fields
from typing import Any, NoReturn

from jwsgj.diag_guard_state import (
    read_json_artifact,
    write_queue_json,
)
from jwsgj.diag_testing_coverage import (
    EFFECTIVE_LEVEL_DOMAIN,
    CoverageMap,
    ProjectAdapter,
    create_adapter,
    file_to_module_path,
    is_outside_root,
    resolve_project_path,
)
from jwsgj.diag_testing_mutation_runtime import set_mutation_test_bridge
from jwsgj.diag_testing_source import file_content_digest
from jwsgj.diag_types_normalize import integral_count, safe_float
from jwsgj.log_config import log_swallowed, write_module_run
from jwsgj.runtime_paths import (
    SOURCE_LAYOUT_ROOT_NAMES,
    source_import_roots,
)
from jwsgj.testsuite_registry import (
    RUN_STATUS_VALUES,
    TestMaturityLevel,
    TestMetadata,
    TestRegistry,
    assess_test_maturity,
    get_confidence_multiplier,
    get_test_maturity_report,
)
from jwsgj.testsuite_runner import (
    SelectiveTestRunner,
    TestRunResult,
    set_test_suite_bridge,
)

__all__ = [
    "LOW_QUALITY_TEST_PENALTY",
    "TEST_FAIL_BOOST",
    "TEST_PASS_WEAKEN",
    "TestDimensionScore",
    "TestDimensionScorer",
    "TestHealthMetrics",
    "TestSuiteBridge",
    "TestSuiteHealthMonitor",
    "assess_cv_maturity",
    "attach_test_health_metrics",
    "build_test_bridge",
    "execute_test_suggestions",
    "run_stage2b_test_bridge",
    "run_temp_regression_test",
    "suggest_test_coverage",
    "xv_test_cross_validation",
]
logger = logging.getLogger(__name__)
logger.addHandler(logging.NullHandler())
_LOG_MODULE = "testsuite_eval"
def _log_module_run(op: str, t0: float, **fields: Any) -> None:
    write_module_run(_LOG_MODULE, op,
                     duration_ms=(time.monotonic() - t0) * 1000.0, **fields)
_META_DEFAULTS: dict[str, Any] = {
    _f.name: _f.default for _f in dataclass_fields(TestMetadata)
    if _f.default is not MISSING
}
_COVERAGE_DEFAULTS: dict[str, Any] = {
    _f.name: _f.default for _f in dataclass_fields(CoverageMap)
    if _f.default is not MISSING
}
def _corrupt(path: str, detail: str, cause: BaseException | None = None) -> NoReturn:
    raise ValueError(f"bridge 快照结构损坏: {path} ({detail})") from cause
def _path_text(value: Any) -> str:
    try:
        raw = os.fspath(value)
    except (TypeError, ValueError):
        return ""
    return raw.strip() if isinstance(raw, str) else ""
def _snap_top_fields(data: Any, path: str) -> tuple[str, dict, dict]:
    try:
        project_root = data["project_root"]
        cm_data = data["coverage_map"]
        reg_data = data["test_registry"]
    except (KeyError, TypeError) as e:
        log_swallowed(__name__, e,
                     context=f'_snap_top_fields:{type(e).__name__}')
        _corrupt(path, str(e), e)
    if not isinstance(project_root, str) or not project_root:
        _corrupt(path, f"project_root 非 str: {type(project_root).__name__}")
    if not isinstance(cm_data, dict) or not isinstance(reg_data, dict):
        _corrupt(path, "coverage_map/test_registry 非 dict")
    return project_root, cm_data, reg_data
def _snap_field_mapping(
        cm_data: dict[str, Any], field: str, path: str) -> dict[str, list[str]]:
    value = cm_data.get(field, {})
    if not isinstance(value, dict):
        _corrupt(path, f"coverage_map.{field} 非 dict: {type(value).__name__}")
    for k, v in value.items():
        if not isinstance(v, list) or any(
                not isinstance(t, str) for t in v):
            _corrupt(path, f"coverage_map.{field}[{k!r}] 非字符串列表")
    return value
def _snap_non_negative_int(raw: Any, label: str, path: str) -> int:
    if isinstance(raw, bool):
        _corrupt(path, f"{label} 非负整数: {raw!r}")
    if isinstance(raw, float):
        if safe_float(raw, None) is None:
            _corrupt(path, f"{label} 非数值: {raw!r}")
        count = integral_count(raw)
        if count is None:
            _corrupt(path, f"{label} 非负整数: {raw!r}")
    else:
        try:
            count = int(raw)
        except (TypeError, ValueError, OverflowError) as e:
            log_swallowed(
                __name__, e,
                context=f'_snap_non_negative_int:{type(e).__name__}')
            _corrupt(path, f"{label} 非数值: {raw!r}", e)
    if count < 0:
        _corrupt(path, f"{label} 非负整数: {raw!r}")
    return count
def _snap_field_count(cm_data: dict[str, Any], field: str, path: str) -> int:
    return _snap_non_negative_int(
        cm_data.get(field, _COVERAGE_DEFAULTS[field]),
        f"coverage_map.{field}", path)
def _snap_field_level(
        cm_data: dict[str, Any], field: str, path: str) -> str:
    value = cm_data.get(field, _COVERAGE_DEFAULTS[field])
    if (not isinstance(value, str)
            or value not in EFFECTIVE_LEVEL_DOMAIN):
        _corrupt(path, f"coverage_map.{field} 非合法层级: {value!r}")
    return value
def _restore_registry_entries(
        reg_data: dict[str, Any], path: str,
        project_root: str) -> TestRegistry:
    registry = TestRegistry()
    for test_path, meta_dict in reg_data.items():
        if not isinstance(meta_dict, dict):
            _corrupt(
                path, f"test_registry[{test_path!r}] 非 dict: "
                      f"{type(meta_dict).__name__}")
        if not isinstance(test_path, str) or not test_path.strip():
            _corrupt(path, f"test_registry 条目路径非法: {test_path!r}")
        entry_path = resolve_project_path(test_path, project_root)
        meta = _restore_registry_entry(entry_path, meta_dict, path)
        registry.register(entry_path, meta)
        try:
            registry.update_run_result(
                entry_path, meta.last_run_status, meta.last_run_duration)
        except ValueError as e:
            _corrupt(path, f"测试条目 {test_path!r} 运行字段异常: {e}", e)
    return registry
def _snap_run_status(raw: Any) -> str:
    status = (_META_DEFAULTS["last_run_status"]
              if raw is None or raw == "" else raw)
    if not isinstance(status, str) or status not in RUN_STATUS_VALUES:
        raise ValueError(f"last_run_status 非合法运行状态: {raw!r}")
    return status
def _snap_optional_float(
        meta_dict: dict[str, Any], key: str, default: float) -> float:
    raw = meta_dict.get(key)
    if raw is None:
        return default
    if isinstance(raw, bool):
        raise TypeError(f"{key} 非数值: {raw!r}")
    return float(raw)
_SNAPSHOT_PREFIX = "test_suite_bridge_"
_SNAPSHOT_SUFFIX = ".json"
_SNAPSHOT_FILENAME = f"{_SNAPSHOT_PREFIX}snapshot{_SNAPSHOT_SUFFIX}"
def _snap_str_list(meta_dict: dict[str, Any], key: str) -> list[str]:
    raw = meta_dict.get(key)
    if isinstance(raw, list):
        return [item for item in raw if isinstance(item, str)]
    if isinstance(raw, int) and not isinstance(raw, bool):
        logger.debug(
            "[TestSuiteBridge] 快照字段 %s 为旧版计数形态(%d)，列表按空恢复",
            key, raw)
    elif raw is not None:
        logger.warning(
            "[TestSuiteBridge] 快照字段 %s 非字符串列表(%s)，忽略",
            key, type(raw).__name__)
    return []
def _validate_entry_metrics(
        meta: TestMetadata, test_path: str, path: str) -> None:
    duration = _finite_number(meta.last_run_duration)
    quality = _finite_number(meta.quality_score)
    if duration is None or quality is None:
        _corrupt(
            path,
            f"测试条目 {test_path!r} 字段非有限数值: "
            f"duration={meta.last_run_duration!r}, "
            f"quality={meta.quality_score!r}")
    if not 0.0 <= quality <= 1.0:
        _corrupt(
            path,
            f"测试条目 {test_path!r} quality_score 超出 [0, 1]: "
            f"{meta.quality_score!r}")
def _snap_entry_count(meta_dict: dict[str, Any], key: str, path: str) -> int:
    return _snap_non_negative_int(
        meta_dict.get(key, _META_DEFAULTS[key]), f"测试条目 {key}", path)
def _restore_registry_entry(test_path: str, meta_dict: dict[str, Any],
                            path: str) -> TestMetadata:
    try:
        meta = TestMetadata(
            path=test_path,
            test_count=_snap_entry_count(meta_dict, "test_count", path),
            framework=str(
                meta_dict.get("framework") or _META_DEFAULTS["framework"]),
            markers=_snap_str_list(meta_dict, "markers"),
            fixtures_used=_snap_str_list(meta_dict, "fixtures_used"),
            conftest_deps=_snap_str_list(meta_dict, "conftest_deps"),
            last_run_status=_snap_run_status(meta_dict.get("last_run_status")),
            last_run_duration=_snap_optional_float(
                meta_dict, "last_run_duration",
                _META_DEFAULTS["last_run_duration"]),
            quality_score=_snap_optional_float(
                meta_dict, "quality_score",
                _META_DEFAULTS["quality_score"]),
        )
    except (TypeError, ValueError, OverflowError) as e:
        log_swallowed(__name__, e,
                      context=f'_restore_registry_entry:{type(e).__name__}')
        _corrupt(path, f"测试条目 {test_path!r} 字段异常: {e}", e)
    _validate_entry_metrics(meta, test_path, path)
    return meta
_COVERAGE_SNAPSHOT_FIELDS: tuple[tuple[str, str], ...] = (
    ("by_filename", "mapping"),
    ("by_import", "mapping"),
    ("by_coverage", "mapping"),
    ("effective_level", "level"),
    ("total_source_files", "count"),
    ("total_test_files", "count"),
    ("covered_files", "count"),
)
_COVERAGE_FIELD_READERS = {
    "count": _snap_field_count,
    "level": _snap_field_level,
}
def _snap_field_path_mapping(
        cm_data: dict[str, Any], field: str, path: str,
        project_root: str) -> dict[str, list[str]]:
    raw = _snap_field_mapping(cm_data, field, path)
    restored: dict[str, list[str]] = {}
    for source, tests in raw.items():
        if not isinstance(source, str) or not source.strip():
            _corrupt(path, f"coverage_map.{field} 键非非空字符串: {source!r}")
        restored[resolve_project_path(source, project_root)] = [
            resolve_project_path(test, project_root) for test in tests]
    return restored
def _restore_coverage_map(
        cm_data: dict[str, Any], path: str,
        project_root: str) -> CoverageMap:
    cm = CoverageMap(**{
        field: (_snap_field_path_mapping(
                    cm_data, field, path, project_root)
                if kind == "mapping"
                else _COVERAGE_FIELD_READERS[kind](cm_data, field, path))
        for field, kind in _COVERAGE_SNAPSHOT_FIELDS
    })
    if cm.covered_files > cm.total_source_files:
        _corrupt(
            path,
            "coverage_map.covered_files 不得大于 total_source_files: "
            f"{cm.covered_files} > {cm.total_source_files}")
    cm.build_reverse_index()
    return cm
def _ensure_adapter_root(adapter: ProjectAdapter | None, project_root: str,
                         root_label: str) -> None:
    if (adapter is not None
            and os.path.normcase(os.path.abspath(adapter.root))
            != os.path.normcase(os.path.abspath(project_root))):
        raise ValueError(
            f"adapter 根目录 {adapter.root} 与 {root_label} {project_root} 不一致"
        )
_SNAPSHOT_FILE_SET_FIELDS = ("source_files", "test_files")
def _snapshot_file_identity(path: str, project_root: str) -> str:
    path = os.fspath(path)
    anchored = path if os.path.isabs(path) else os.path.join(project_root, path)
    return os.path.normcase(os.path.abspath(os.path.normpath(anchored)))
def _new_snapshot_file_set(
        project_root: str, source_files: list[str], test_files: list[str],
) -> dict[str, list[str]]:
    return {
        "source_files": sorted({
            _snapshot_file_identity(path, project_root) for path in source_files}),
        "test_files": sorted({
            _snapshot_file_identity(path, project_root) for path in test_files}),
    }
def _snapshot_file_fingerprint(file_set: dict[str, list[str]]) -> str:
    paths = sorted({
        path for field_name in _SNAPSHOT_FILE_SET_FIELDS
        for path in file_set.get(field_name, [])
    })
    signature: list[tuple[str, str]] = []
    for path in paths:
        try:
            digest = file_content_digest(path)
        except OSError as exc:
            log_swallowed(__name__, exc, context="_snapshot_file_fingerprint:OSError")
            return ""
        signature.append((path, digest))
    return hashlib.sha256(repr(signature).encode("utf-8")).hexdigest()
def _restore_snapshot_file_set(
        data: dict[str, Any], project_root: str, path: str,
) -> dict[str, list[str]]:
    raw = data.get("file_set")
    if not raw:
        return {}
    if not isinstance(raw, dict):
        _corrupt(path, f"file_set 非 dict: {type(raw).__name__}")
    restored: dict[str, list[str]] = {}
    for field_name in _SNAPSHOT_FILE_SET_FIELDS:
        values = raw.get(field_name)
        if (not isinstance(values, list)
                or any(not isinstance(value, str) or not value
                       for value in values)):
            _corrupt(path, f"file_set.{field_name} 非字符串列表")
        restored[field_name] = sorted({
            _snapshot_file_identity(value, project_root) for value in values})
    return restored
@dataclass
class TestSuiteBridge:
    __test__ = False
    coverage_map: CoverageMap
    test_registry: TestRegistry
    runner: SelectiveTestRunner
    project_root: str
    adapter: ProjectAdapter
    file_set: dict[str, list[str]] = field(default_factory=dict)
    file_fingerprint: str = ""
    def save(self, path: str) -> None:
        write_queue_json(path, self._snapshot_payload())
        logger.info("[TestSuiteBridge] 状态已保存: %s", path)
    def _snapshot_payload(self) -> dict[str, Any]:
        return {
            "project_root": self.project_root,
            "coverage_map": {
                field: getattr(self.coverage_map, field)
                for field, _kind in _COVERAGE_SNAPSHOT_FIELDS
            },
            "test_registry": {
                str(meta.path): {
                    **meta.to_dict(),
                    "last_run_duration": meta.last_run_duration,
                    "quality_score": meta.quality_score,
                }
                for meta in self.test_registry.entries.values()
            },
            "file_set": {
                field_name: list(self.file_set.get(field_name, []))
                for field_name in _SNAPSHOT_FILE_SET_FIELDS
            },
            "file_fingerprint": self.file_fingerprint,
        }
    @classmethod
    def load(
        cls,
        path: str,
        adapter: ProjectAdapter | None = None,
        test_timeout: int | None = None,
        mutation_timeout: int | None = None,
    ) -> TestSuiteBridge:
        if not os.path.isfile(path):
            raise FileNotFoundError(f"bridge 快照不存在: {path}")
        data, _status, _detail = read_json_artifact(path)
        if _status == "missing":
            raise FileNotFoundError(f"bridge 快照不存在: {path}")
        if _status != "ok":
            _corrupt(path, f"JSON 读取失败: {_detail or _status}")
        project_root, cm_data, reg_data = _snap_top_fields(data, path)
        project_root = os.path.abspath(project_root)
        file_set = _restore_snapshot_file_set(data, project_root, path)
        file_fingerprint = data.get("file_fingerprint", "")
        if not isinstance(file_fingerprint, str):
            _corrupt(path, "file_fingerprint 非 str")
        _ensure_adapter_root(adapter, project_root, "快照 project_root")
        if adapter is None:
            adapter = create_adapter(project_root)
        cm = _restore_coverage_map(cm_data, path, project_root)
        registry = _restore_registry_entries(reg_data, path, project_root)
        registry.update_coverage_links(cm)
        registry.compute_stats()
        logger.info(
            "[TestSuiteBridge] 快照恢复: %d 源文件, %d 测试文件, level=%s",
            cm.total_source_files, cm.total_test_files, cm.effective_level,
        )
        return cls._assemble(
            project_root, adapter, cm, registry,
            test_timeout, mutation_timeout, file_set=file_set,
            file_fingerprint=file_fingerprint)
    @classmethod
    def load_latest(
        cls,
        directory: str,
        adapter: ProjectAdapter | None = None,
        test_timeout: int | None = None,
        mutation_timeout: int | None = None,
    ) -> TestSuiteBridge | None:
        if not os.path.isdir(directory):
            return None
        candidates = [
            os.path.join(directory, name)
            for name in sorted(os.listdir(directory))
            if (name.startswith(_SNAPSHOT_PREFIX)
                and name.endswith(_SNAPSHOT_SUFFIX)
                and os.path.isfile(os.path.join(directory, name)))
        ]
        stamped: list[tuple[float, str]] = []
        for cand in candidates:
            try:
                stamped.append((os.path.getmtime(cand), cand))
            except OSError:
                logger.debug("[TestSuiteBridge] 快照 mtime 读取失败，跳过: %s", cand)
        if not stamped:
            return None
        latest = max(stamped)[1]
        return cls.load(
            latest,
            adapter=adapter,
            test_timeout=test_timeout,
            mutation_timeout=mutation_timeout,
        )
    @classmethod
    def build(
        cls,
        project_root: str,
        adapter: ProjectAdapter | None = None,
        run_coverage: bool = False,
        coverage_timeout: int | None = None,
        test_timeout: int | None = None,
        mutation_timeout: int | None = None,
    ) -> TestSuiteBridge:
        root_text = _path_text(project_root)
        if not root_text:
            raise ValueError(
                "TestSuiteBridge.build: project_root 为空或非路径入参"
                f"（{type(project_root).__name__}），拒绝按进程 cwd 构建")
        project_root = os.path.abspath(root_text)
        _ensure_adapter_root(adapter, project_root, "project_root")
        if adapter is None:
            adapter = create_adapter(project_root)
        source_files = adapter.get_source_files()
        test_files = adapter.get_test_files()
        logger.info(
            "[TestSuiteBridge] 构建: %d 源文件, %d 测试文件, adapter=%s",
            len(source_files), len(test_files), type(adapter).__name__,
        )
        coverage_map = CoverageMap.build(
            source_files=source_files,
            test_files=test_files,
            project_root=project_root,
            run_coverage=run_coverage,
            coverage_timeout=coverage_timeout,
        )
        test_registry = TestRegistry.build(
            test_files=test_files,
            coverage_map=coverage_map,
            project_root=project_root,
        )
        file_set = _new_snapshot_file_set(
            project_root, source_files, test_files)
        file_fingerprint = _snapshot_file_fingerprint(file_set)
        return cls._assemble(
            project_root, adapter, coverage_map, test_registry,
            test_timeout, mutation_timeout, file_set=file_set,
            file_fingerprint=file_fingerprint)
    @classmethod
    def _assemble(
        cls,
        project_root: str,
        adapter: ProjectAdapter,
        coverage_map: CoverageMap,
        test_registry: TestRegistry,
        test_timeout: int | None,
        mutation_timeout: int | None,
        file_set: dict[str, list[str]] | None = None,
        file_fingerprint: str = "",
    ) -> TestSuiteBridge:
        runner = SelectiveTestRunner(
            coverage_map=coverage_map,
            test_registry=test_registry,
            project_root=project_root,
            test_timeout=test_timeout,
            mutation_timeout=mutation_timeout,
        )
        return cls(
            coverage_map=coverage_map,
            test_registry=test_registry,
            runner=runner,
            project_root=project_root,
            adapter=adapter,
            file_set=file_set if file_set is not None else {},
            file_fingerprint=file_fingerprint,
        )
_UNMEASURED_SCORE: float = -1.0
@dataclass
class TestHealthMetrics:
    __test__ = False
    total_files: int = 0
    total_tests: int = 0
    flaky_tests: list[str] = field(default_factory=list)
    slow_tests: list[str] = field(default_factory=list)
    pollution_tests: list[str] = field(default_factory=list)
    orphan_tests: list[str] = field(default_factory=list)
    duplicate_tests: list[str] = field(default_factory=list)
    avg_quality: float = _UNMEASURED_SCORE
    health_score: float = _UNMEASURED_SCORE
    def to_dict(self) -> dict[str, Any]:
        return {
            "total_files": self.total_files,
            "total_tests": self.total_tests,
            "flaky_count": len(self.flaky_tests),
            "slow_count": len(self.slow_tests),
            "pollution_count": len(self.pollution_tests),
            "orphan_count": len(self.orphan_tests),
            "duplicate_count": len(self.duplicate_tests),
            "avg_quality": round(self.avg_quality, 3),
            "health_score": round(self.health_score, 3),
        }
_POLLUTION_QUALITY_THRESHOLD = 0.3
class TestSuiteHealthMonitor:
    __test__ = False
    SLOW_THRESHOLD = 10.0
    def __init__(self, registry: TestRegistry):
        self.registry = registry
    def _classify_entries(self, unstable_paths: set[str],
                          metrics: TestHealthMetrics) -> None:
        for meta in self.registry.entries.values():
            path = meta.path
            if meta.last_run_duration > self.SLOW_THRESHOLD:
                metrics.slow_tests.append(path)
            if not meta.covers_source:
                metrics.orphan_tests.append(path)
            if meta.quality_score < _POLLUTION_QUALITY_THRESHOLD:
                metrics.pollution_tests.append(path)
            if path in unstable_paths and not _is_low_quality(meta):
                metrics.flaky_tests.append(path)
    @staticmethod
    def _detect_duplicate_tests(
            entries: dict[str, Any]) -> list[str]:
        duplicates: list[str] = []
        seen_signatures: dict[str, str] = {}
        for meta in entries.values():
            path = meta.path
            covers = tuple(sorted(meta.covers_source))
            if not covers:
                continue
            if meta.test_count <= 0:
                continue
            sig = f"{meta.test_count}:{meta.framework}:{covers}"
            if sig in seen_signatures:
                original = seen_signatures[sig]
                if original not in duplicates:
                    duplicates.append(original)
                if path not in duplicates:
                    duplicates.append(path)
            else:
                seen_signatures[sig] = path
        return duplicates
    def analyze(self) -> TestHealthMetrics:
        _t0 = time.monotonic()
        metrics = TestHealthMetrics()
        metrics.total_files = len(self.registry.entries)
        if not self.registry.entries:
            _log_module_run(
                "TestSuiteHealthMonitor.analyze", _t0,
                total_files=0, total_tests=0,
                health_score=_UNMEASURED_SCORE)
            return metrics
        self.registry.compute_stats()
        metrics.total_tests = self.registry.total_tests
        metrics.avg_quality = self.registry.average_quality
        unstable_paths = {
            m.path
            for m in (self.registry.get_by_status("failed")
                      + self.registry.get_by_status("error"))
        }
        self._classify_entries(unstable_paths, metrics)
        metrics.duplicate_tests = self._detect_duplicate_tests(
            self.registry.entries)
        total_issues = (
            len(metrics.flaky_tests) * 3 +
            len(metrics.slow_tests) * 2 +
            len(metrics.pollution_tests) * 1 +
            len(metrics.orphan_tests) * 1 +
            len(metrics.duplicate_tests) * 1
        )
        max_issues = max(metrics.total_files, 1)
        metrics.health_score = max(0.0, 1.0 - total_issues / max_issues * 0.5)
        _log_module_run(
            "TestSuiteHealthMonitor.analyze", _t0,
            total_files=metrics.total_files,
            total_tests=metrics.total_tests,
            health_score=round(metrics.health_score, 3))
        return metrics
_W_COVERAGE = 0.15
_W_MUTATION = 0.10
_W_REGRESSION = 0.15
_W_QUALITY = 0.10
_W_NEW_TESTS = 0.05
@dataclass
class TestDimensionScore:
    __test__ = False
    coverage_change: float = 0.0
    mutation_score: float = 0.0
    regression_pass_rate: float = 0.0
    quality_trend: float = 0.0
    new_tests_added: int = 0
    overall_score: float = 0.0
    mutation_measured: bool = False
    regression_measured: bool = False
    def to_dict(self) -> dict[str, Any]:
        return {
            "coverage_change": round(self.coverage_change, 4),
            "mutation_score": round(self.mutation_score, 4),
            "regression_pass_rate": round(self.regression_pass_rate, 4),
            "quality_trend": round(self.quality_trend, 4),
            "new_tests_added": self.new_tests_added,
            "overall_score": round(self.overall_score, 2),
            "mutation_measured": self.mutation_measured,
            "regression_measured": self.regression_measured,
            "weights": {
                "coverage": _W_COVERAGE,
                "mutation": _W_MUTATION,
                "regression": _W_REGRESSION,
                "quality": _W_QUALITY,
                "new_tests": _W_NEW_TESTS,
            },
        }
def _finite_number(value) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    return safe_float(value, None)
def _mutation_survival_rate(mutation_results: list[dict]) -> float | None:
    total_mutants = 0
    killed_mutants = 0
    for r in mutation_results:
        if not isinstance(r, dict):
            continue
        total = _finite_number(r.get("total", 0))
        killed = _finite_number(r.get("killed", 0))
        if total is None or killed is None:
            continue
        total = max(0.0, total)
        total_mutants += total
        killed_mutants += min(max(0.0, killed), total)
    if total_mutants > 0:
        return _clamp(1.0 - killed_mutants / total_mutants, 0.0, 1.0)
    return None
def _registry_has_run_data(registry) -> bool:
    return any(
        meta.last_run_status not in _UNRUN_STATUSES
        for meta in getattr(registry, "entries", {}).values())
def _compute_regression_pass_rate(regression_results: list | None,
                                  registry) -> float | None:
    valid_results = [r for r in regression_results or ()
                     if isinstance(r, TestRunResult)
                     and r.status not in _UNRUN_STATUSES]
    if valid_results:
        passed = sum(bool(r.passed) for r in valid_results)
        return passed / len(valid_results)
    return registry.pass_rate if _registry_has_run_data(registry) else None
def _baseline_delta(post_value: float, pre_value: float | None) -> float:
    pre_value = _finite_number(pre_value)
    if pre_value is not None:
        return post_value - pre_value
    return post_value
def _normalize_new_test_count(new_test_count: int | None) -> int:
    count_num = _finite_number(new_test_count)
    count = integral_count(count_num) if count_num is not None else None
    if count is None or count < 0:
        if new_test_count is not None:
            logger.warning(
                "[TestDimensionScorer] new_test_count 须为非负整数 (%r)，按 0 计",
                new_test_count)
        return 0
    return count
def _clamp(value: float, lo: float, hi: float) -> float:
    return max(lo, min(hi, value))
def _weighted_overall_score(score: TestDimensionScore) -> float:
    mutation_measured = score.mutation_measured
    regression_measured = score.regression_measured
    weighted: list[tuple[float, float]] = [
        (_clamp(score.coverage_change, -1.0, 1.0) * 100, _W_COVERAGE),
        (_clamp(score.quality_trend, -1.0, 1.0) * 100, _W_QUALITY),
        (_clamp(score.new_tests_added, 0, 10) / 10.0 * 100, _W_NEW_TESTS),
    ]
    if regression_measured:
        weighted.append((
            _clamp(score.regression_pass_rate, 0.0, 1.0) * 100,
            _W_REGRESSION))
    if mutation_measured:
        weighted.append((
            (1.0 - _clamp(score.mutation_score, 0.0, 1.0)) * 100,
            _W_MUTATION))
    total_weight = sum(weight for _value, weight in weighted)
    return _clamp(
        sum(value * weight for value, weight in weighted) / total_weight,
        0.0, 100.0)
class TestDimensionScorer:
    __test__ = False
    def __init__(self, bridge: TestSuiteBridge):
        self.bridge = bridge
    def score(
        self,
        pre_coverage: float | None = None,
        mutation_results: list[dict] | None = None,
        regression_results: list[TestRunResult] | None = None,
        pre_quality: float | None = None,
        new_test_count: int = 0,
    ) -> TestDimensionScore:
        _t0 = time.monotonic()
        score = TestDimensionScore()
        post_coverage = self.bridge.coverage_map.coverage_ratio()
        score.coverage_change = _baseline_delta(post_coverage, pre_coverage)
        mutation_measured = False
        if mutation_results:
            survival = _mutation_survival_rate(mutation_results)
            if survival is not None:
                score.mutation_score = survival
                mutation_measured = True
        regression_rate = _compute_regression_pass_rate(
            regression_results, self.bridge.test_registry)
        regression_measured = regression_rate is not None
        score.regression_pass_rate = (
            regression_rate if regression_rate is not None else 0.0)
        post_quality = self.bridge.test_registry.average_quality
        score.quality_trend = _baseline_delta(post_quality, pre_quality)
        score.new_tests_added = _normalize_new_test_count(new_test_count)
        score.mutation_measured = mutation_measured
        score.regression_measured = regression_measured
        score.overall_score = _weighted_overall_score(score)
        _log_module_run(
            "TestDimensionScorer.score", _t0,
            overall_score=round(score.overall_score, 2),
            regression_pass_rate=round(score.regression_pass_rate, 4))
        return score
def attach_test_health_metrics(
        bridge: Any, result: dict[str, Any]) -> None:
    try:
        if bridge is not None and _bridge_has_test_files(bridge):
            health_monitor = TestSuiteHealthMonitor(
                registry=bridge.test_registry,
            )
            health_metrics = health_monitor.analyze()
            result["test_health_metrics"] = health_metrics.to_dict()
            logger.info("[TestHealth] 测试健康: score=%.3f, flaky=%d, slow=%d, orphan=%d",
                        health_metrics.health_score,
                        len(health_metrics.flaky_tests),
                        len(health_metrics.slow_tests),
                        len(health_metrics.orphan_tests))
            test_score = TestDimensionScorer(bridge).score()
            result["test_dimension_score"] = test_score.to_dict()
            logger.info("[TestHealth] 测试维度评分: overall=%.2f",
                        test_score.overall_score)
    except Exception as tsb_err:
        logger.warning("[TestHealth] TestSuiteBridge 评分跳过: %s", tsb_err)
TEST_FAIL_BOOST = 1.2
TEST_PASS_WEAKEN = 0.85
LOW_QUALITY_TEST_PENALTY = 0.9
_DEFAULT_CONFIDENCE = 1.0
_CONFIDENCE_FLOOR = 0.1
_CONFIDENCE_CEILING = 1.5
_LOW_QUALITY_SCORE_THRESHOLD = 0.5
def _is_low_quality(meta) -> bool:
    return meta is not None and meta.quality_score < _LOW_QUALITY_SCORE_THRESHOLD
def _count_low_quality_tests(covering_tests: list[str],
                             registry: TestRegistry) -> int:
    return sum(
        1 for tf in covering_tests if _is_low_quality(registry.get(tf)))
def _low_quality_majority(low_quality_count: int, total: int) -> bool:
    return low_quality_count > total / 2
_FINDING_FIELD_ALIASES: dict[str, tuple[str, ...]] = {
    "file": ("file", "filepath", "path", "filename", "source_file",
             "rel_path"),
    "rule_id": ("rule_id", "type", "rule", "check_id", "id", "category",
                "code"),
    "severity": ("severity", "level", "priority", "impact"),
}
def _finding_field_text(finding: dict[str, Any], field: str,
                        default: str = "") -> str:
    for key in _FINDING_FIELD_ALIASES[field]:
        value = finding.get(key)
        if isinstance(value, os.PathLike):
            try:
                value = os.fspath(value)
            except TypeError as _e:
                log_swallowed(
                    __name__, _e,
                    context=f'_finding_field_text:{field}:{type(_e).__name__}')
                continue
        if isinstance(value, str) and value:
            return value
    return default
def _anchored_source_path(source_file: Any, project_root: str) -> str:
    if not isinstance(source_file, str) or not source_file:
        return ""
    if os.path.isabs(source_file):
        return os.path.normpath(source_file)
    return os.path.normpath(os.path.join(project_root, source_file))
def _path_within_root(path: str, project_root: str) -> bool:
    try:
        root = os.path.realpath(os.path.abspath(project_root))
        candidate = os.path.realpath(os.path.abspath(path))
        common = os.path.commonpath([root, candidate])
    except (OSError, TypeError, ValueError):
        return False
    return os.path.normcase(common) == os.path.normcase(root)
def _lookup_covering_tests(bridge: TestSuiteBridge, source_file: str,
                           anchored_file: str) -> list[str]:
    candidates = [os.path.normpath(source_file), os.path.normpath(anchored_file)]
    if os.path.isabs(anchored_file):
        try:
            relative = os.path.relpath(anchored_file, bridge.project_root)
        except ValueError as _e:
            log_swallowed(
                __name__, _e,
                context=f'_lookup_covering_tests:{type(_e).__name__}')
        else:
            if not is_outside_root(relative):
                candidates.append(os.path.normpath(relative))
    seen: set[str] = set()
    for candidate in candidates:
        identity = os.path.normcase(candidate)
        if identity in seen:
            continue
        seen.add(identity)
        covering_tests = bridge.coverage_map.get_tests_for(candidate)
        if covering_tests:
            return covering_tests
    return []
def _log_xv_run(_t0: float, findings: list[dict] | None, mode: str) -> None:
    _log_module_run("xv_test_cross_validation", _t0,
                    findings=len(findings) if findings else 0, mode=mode)
def xv_test_cross_validation(
    findings: list[dict],
    bridge: TestSuiteBridge | None,
) -> list[dict]:
    _t0 = time.monotonic()
    if not findings or bridge is None:
        _log_xv_run(_t0, findings, "passthrough")
        return findings
    if not _bridge_has_test_files(bridge):
        _mark_findings_without_tests(findings, bridge.project_root)
        _log_xv_run(_t0, findings, "no_tests")
        return findings
    for finding in findings:
        if not isinstance(finding, dict):
            continue
        _adjust_finding_confidence(finding, bridge)
    _log_xv_run(_t0, findings, "cross_validated")
    return findings
def _mark_findings_without_tests(findings: list[dict],
                                 project_root: str) -> None:
    for finding in findings:
        if not isinstance(finding, dict):
            continue
        _normalize_confidence_inplace(finding)
        source_file = _finding_field_text(finding, "file")
        if not source_file:
            continue
        anchored_file = _anchored_source_path(source_file, project_root)
        if anchored_file and os.path.isdir(anchored_file):
            finding["xv_signal"] = "directory_level_finding"
        elif "xv_signal" not in finding:
            finding["xv_signal"] = "no_test_coverage"
def _normalize_confidence_inplace(finding: dict[str, Any]) -> None:
    raw = finding.get("confidence", _DEFAULT_CONFIDENCE)
    value = _finite_number(raw)
    if value is None:
        logger.warning(
            "[XV] finding confidence 非数值 (%r)，归一为中性值 %.1f",
            raw, _DEFAULT_CONFIDENCE)
        value = _DEFAULT_CONFIDENCE
    elif not _CONFIDENCE_FLOOR <= value <= _CONFIDENCE_CEILING:
        logger.warning(
            "[XV] finding confidence 越界 (%r)，收敛到 [%.1f, %.1f]",
            raw, _CONFIDENCE_FLOOR, _CONFIDENCE_CEILING)
    finding["confidence"] = _clamp(
        value, _CONFIDENCE_FLOOR, _CONFIDENCE_CEILING)
_FAILED_RUN_STATUSES = ("failed", "error")
_UNRUN_STATUSES = frozenset({"not_run", "skipped"})
def _classify_covering_tests(
        covering_tests: list[str],
        registry: TestRegistry) -> tuple[list[str], list[str], list[str]]:
    failed_tests: list[str] = []
    passed_tests: list[str] = []
    low_quality_tests: list[str] = []
    for tf in covering_tests:
        meta = registry.get(tf)
        if meta is None:
            continue
        if meta.last_run_status in _FAILED_RUN_STATUSES:
            failed_tests.append(tf)
        elif meta.last_run_status == "passed":
            passed_tests.append(tf)
        if _is_low_quality(meta):
            low_quality_tests.append(tf)
    return failed_tests, passed_tests, low_quality_tests
def _apply_test_evidence(finding: dict[str, Any],
                         failed_tests: list[str],
                         passed_tests: list[str],
                         low_quality_tests: list[str],
                         covering_tests: list[str]) -> None:
    confidence = _clamp(
        finding.get("confidence", _DEFAULT_CONFIDENCE),
        _CONFIDENCE_FLOOR, _CONFIDENCE_CEILING)
    if failed_tests:
        confidence *= TEST_FAIL_BOOST
        finding["xv_signal"] = "test_failure_confirms"
        finding["xv_test_detail"] = f"{len(failed_tests)}/{len(covering_tests)} covering tests failed"
    else:
        confidence *= TEST_PASS_WEAKEN
        finding["xv_signal"] = "test_pass_weakens"
        finding["xv_test_detail"] = f"{len(passed_tests)}/{len(covering_tests)} covering tests passed"
    if _low_quality_majority(len(low_quality_tests), len(covering_tests)):
        confidence *= LOW_QUALITY_TEST_PENALTY
        finding["xv_test_quality_warning"] = True
    finding["confidence"] = round(
        _clamp(confidence, _CONFIDENCE_FLOOR, _CONFIDENCE_CEILING), 3)
def _adjust_finding_confidence(
        finding: dict[str, Any], bridge: TestSuiteBridge) -> None:
    _normalize_confidence_inplace(finding)
    source_file = _finding_field_text(finding, "file")
    if not source_file:
        return
    anchored_file = _anchored_source_path(source_file, bridge.project_root)
    if os.path.isdir(anchored_file):
        finding["xv_signal"] = "directory_level_finding"
        return
    covering_tests = _lookup_covering_tests(bridge, source_file, anchored_file)
    if not covering_tests:
        finding["xv_signal"] = "no_test_coverage"
        return
    failed_tests, passed_tests, low_quality_tests = _classify_covering_tests(
        covering_tests, bridge.test_registry)
    if not failed_tests and not passed_tests:
        finding["xv_signal"] = "test_not_run"
        return
    _apply_test_evidence(finding, failed_tests, passed_tests,
                         low_quality_tests, covering_tests)
def _resolve_suggestion_target(finding: object, seen_files: set[str],
                               project_root: str) -> str | None:
    if not isinstance(finding, dict):
        return None
    source_file = _finding_field_text(finding, "file")
    if not source_file:
        return None
    anchored_file = _anchored_source_path(source_file, project_root)
    if not _path_within_root(anchored_file, project_root):
        return None
    if os.path.isdir(anchored_file):
        return None
    source_file_norm = os.path.normpath(source_file)
    dedup_key = os.path.normcase(anchored_file)
    if dedup_key in seen_files:
        return None
    seen_files.add(dedup_key)
    return source_file_norm
def _append_coverage_suggestion(suggestions: list[dict],
                                source_file_norm: str,
                                finding: dict[str, Any],
                                bridge: TestSuiteBridge) -> None:
    anchored_file = _anchored_source_path(
        source_file_norm, bridge.project_root)
    covering_tests = _lookup_covering_tests(
        bridge, source_file_norm, anchored_file)
    rule_id = _finding_field_text(finding, "rule_id", "unknown")
    severity = _finding_field_text(finding, "severity", "medium")
    if not covering_tests:
        suggestions.append({
            "file": source_file_norm,
            "rule_id": rule_id,
            "severity": "high",
            "suggestion": (
                f"文件 {os.path.basename(source_file_norm)} 无测试覆盖，"
                f"诊断发现规则 {rule_id}（{severity}），"
                f"建议补充单元测试覆盖该文件"
            ),
            "action": "add_test",
            "template": "run_temp_regression_test",
        })
        return
    low_quality_count = _count_low_quality_tests(
        covering_tests, bridge.test_registry)
    if _low_quality_majority(low_quality_count, len(covering_tests)):
        suggestions.append({
            "file": source_file_norm,
            "rule_id": rule_id,
            "severity": "medium",
            "suggestion": (
                f"文件 {os.path.basename(source_file_norm)} 有 {len(covering_tests)} 个测试文件，"
                f"但 {low_quality_count} 个质量较低，建议增强测试断言密度"
            ),
            "action": "enhance_test",
            "template": None,
        })
def suggest_test_coverage(
    findings: list[dict],
    bridge: TestSuiteBridge | None,
) -> list[dict]:
    _t0 = time.monotonic()
    suggestions: list[dict] = []
    if not findings or bridge is None:
        _log_module_run("suggest_test_coverage", _t0,
                        suggestions=0, mode="passthrough")
        return suggestions
    seen_files: set[str] = set()
    for finding in findings:
        source_file_norm = _resolve_suggestion_target(
            finding, seen_files, bridge.project_root)
        if source_file_norm is None:
            continue
        _append_coverage_suggestion(
            suggestions, source_file_norm, finding, bridge)
    _log_module_run("suggest_test_coverage", _t0,
                    suggestions=len(suggestions))
    return suggestions
def _execution_result(source_file: str, executed: bool, status: str,
                      error_message: str = "",
                      passed: bool | None = None) -> dict:
    result = {
        "file": source_file,
        "action": "add_test",
        "executed": executed,
        "status": status,
    }
    if passed is not None:
        result["passed"] = passed
    result["error_message"] = error_message
    return result
def _is_dotted_python_name(name: str) -> bool:
    parts = name.split(".")
    return bool(name) and all(part.isidentifier() for part in parts)
def _strip_layout_root_prefix(mod_path: str, project_root: str) -> str:
    text = str(mod_path or '')
    head, sep, tail = text.partition('.')
    if not sep or not tail or head not in SOURCE_LAYOUT_ROOT_NAMES:
        return text
    if os.path.isfile(os.path.join(project_root, head, '__init__.py')):
        return text
    return tail
def _resolve_regression_mod(
    source_file: str,
    project_root: str,
) -> tuple[str, str | None]:
    mod_path = file_to_module_path(source_file, project_root)
    if not mod_path:
        mod_path = os.path.splitext(os.path.basename(source_file))[0]
        return mod_path, "file_to_module_path 未解析出模块名，回退 basename"
    stripped = _strip_layout_root_prefix(mod_path, project_root)
    if stripped != mod_path:
        return stripped, None
    return mod_path, None
def _project_top_level_modules(project_root: str) -> set[str]:
    names: set[str] = set()
    for root in (project_root, *source_import_roots(project_root)):
        try:
            entries = os.listdir(root)
        except OSError:
            continue
        for entry in entries:
            path = os.path.join(root, entry)
            if os.path.isdir(path):
                name = entry
            elif entry.endswith(".py") and entry != "__init__.py":
                name = entry[:-3]
            else:
                continue
            if name.isidentifier():
                names.add(name)
    return names
def _module_import_root(mod_path: str, source_file: str) -> str:
    parts = mod_path.split(".")
    depth = (len(parts) if os.path.basename(source_file) == "__init__.py"
             else len(parts) - 1)
    root = os.path.dirname(os.path.abspath(source_file))
    for _ in range(max(0, depth)):
        parent = os.path.dirname(root)
        if parent == root:
            return ""
        root = parent
    return root
def _ensure_loaded_module_source(mod, source_file: str, mod_path: str) -> None:
    loaded_file = getattr(mod, "__file__", None)
    if not isinstance(loaded_file, str) or not loaded_file:
        raise ImportError(f"{mod_path} 已加载模块缺少源码路径")
    if (os.path.normcase(os.path.realpath(loaded_file))
            != os.path.normcase(os.path.realpath(source_file))):
        raise ImportError(
            f"{mod_path} 导入来源 {loaded_file!r} 与目标源码 {source_file!r} 不一致")
def _load_module_from_disk(
        mod_path: str, source_file: str, project_root: str = ""):
    spec = importlib.util.spec_from_file_location(mod_path, source_file)
    if spec is None or spec.loader is None:
        raise ImportError(
            f"无法为 {source_file} 构建加载 spec"
            f"（无受支持后缀或不可识别的模块源）")
    mod = importlib.util.module_from_spec(spec)
    _missing = object()
    previous_modules = sys.modules.copy()
    project_names = _project_top_level_modules(project_root)
    project_names.add(mod_path.partition(".")[0])
    for name in tuple(sys.modules):
        if name.partition(".")[0] in project_names:
            sys.modules.pop(name, None)
    try:
        parent_name = mod_path.rpartition(".")[0]
        if parent_name:
            importlib.import_module(parent_name)
            loaded = sys.modules.get(mod_path)
            if loaded is not None:
                _ensure_loaded_module_source(loaded, source_file, mod_path)
                return loaded
        sys.modules[mod_path] = mod
        spec.loader.exec_module(mod)
        return mod
    finally:
        for name in tuple(sys.modules):
            if name not in previous_modules:
                sys.modules.pop(name, None)
        for name, previous in previous_modules.items():
            if sys.modules.get(name, _missing) is not previous:
                sys.modules[name] = previous
def _check_function_member(mod, mod_path: str,
                            function_name: str | None,
                            errors: list[str]) -> None:
    if not function_name:
        return
    func = getattr(mod, function_name, None)
    if func is None:
        errors.append(f"{function_name} not found in {mod_path}")
    elif not callable(func):
        errors.append(f"{function_name} is not callable in {mod_path}")
def _check_all_exports(mod, mod_path: str, errors: list[str]) -> None:
    missing = object()
    exported = getattr(mod, "__all__", missing)
    if exported is missing:
        return
    if not isinstance(exported, (list, tuple)):
        errors.append(
            f"{mod_path}: __all__ declaration is not a list/tuple: "
            f"{type(exported).__name__}")
        return
    for name in exported:
        if not isinstance(name, str):
            errors.append(
                f"{mod_path}: __all__ contains non-str entry: {name!r}")
            continue
        if not hasattr(mod, name):
            errors.append(f"{mod_path}: {name} in __all__ but not defined")
def _verify_module_members(mod, mod_path: str,
                           function_name: str | None) -> list[str]:
    errors: list[str] = []
    try:
        _check_function_member(mod, mod_path, function_name, errors)
        _check_all_exports(mod, mod_path, errors)
    except OSError:
        raise
    except Exception as exc:
        log_swallowed(
            __name__, exc,
            context=f'_verify_module_members:{type(exc).__name__}')
        errors.append(f"验证 {mod_path} 时属性访问异常: {exc}")
    return errors
def _reject_invalid_module_name(mod_path: str, source_file: str,
                                start_time: float) -> TestRunResult:
    logger.warning("[TempRegression] mod_path 含非法字符: %s", mod_path)
    message = (
        f"临时回归测试失败: 模块名 {mod_path!r} 不是合法 Python 标识符，"
        f"无法按模块名加载 {os.path.basename(source_file)!r} 执行导入验证")
    return _log_and_build_failure(
        source_file, start_time, "failed", message,
        reason="invalid_module_name")
def _log_and_build_failure(source_file: str, start_time: float,
                            failure_status: str,
                            failure_message: str,
                            **log_fields: Any) -> TestRunResult:
    _log_module_run(
        "run_temp_regression_test", start_time, outcome="failed",
        source=os.path.basename(source_file), passed=False,
        status=failure_status, **log_fields)
    return TestRunResult(
        passed=False, status=failure_status,
        duration=time.monotonic() - start_time,
        ran_tests=[source_file],
        error_message=failure_message,
    )
@contextlib.contextmanager
def _injected_project_sys_path(project_root: str):
    previous_path = sys.path.copy()
    sys.path.insert(0, project_root)
    try:
        yield
    finally:
        sys.path[:] = previous_path
def _source_layout_import_root(source_file: str, project_root: str) -> str:
    for import_root in source_import_roots(project_root):
        if os.path.isfile(os.path.join(import_root, '__init__.py')):
            continue
        try:
            relative = os.path.relpath(source_file, import_root)
        except (OSError, ValueError):
            continue
        if not is_outside_root(relative):
            return import_root
    return ""
def _execute_and_collect(
        mod_path: str, source_file: str, function_name: str | None,
        project_root: str = "") -> tuple[str | None, list[str], str]:
    try:
        mod = _load_module_from_disk(mod_path, source_file, project_root)
        return None, _verify_module_members(mod, mod_path, function_name), ""
    except OSError as exc:
        log_swallowed(
            __name__, exc,
            context=f'run_temp_regression_test:{type(exc).__name__}')
        return "error", [], str(exc)[:200]
    except SystemExit as exc:
        log_swallowed(
            __name__, exc,
            context=f'run_temp_regression_test:{type(exc).__name__}')
        return "failed", [], (
            f"临时回归测试失败: 模块 {mod_path} 导入期终止进程"
            f"（SystemExit code={exc.code!r}），无法完成成员验证")
    except Exception as exc:
        log_swallowed(
            __name__, exc,
            context=f'run_temp_regression_test:{type(exc).__name__}')
        return "failed", [], f"临时回归测试失败: 模块 {mod_path} 导入失败: {exc}"
def _assemble_verified_result(source_file: str, start_time: float,
                              errors: list[str]) -> TestRunResult:
    elapsed = time.monotonic() - start_time
    _passed = not errors
    _log_module_run(
        "run_temp_regression_test", start_time,
        outcome="ok" if _passed else "failed",
        source=os.path.basename(source_file), passed=_passed,
        status="failed" if errors else "passed",
        errors=len(errors))
    if errors:
        return TestRunResult(
            passed=False, status="failed", duration=elapsed,
            output="; ".join(errors)[:2000],
            ran_tests=[source_file],
            error_message=f"临时回归测试失败: {'; '.join(errors)[:200]}",
        )
    return TestRunResult(
        passed=True, status="passed", duration=elapsed,
        ran_tests=[source_file],
    )
def run_temp_regression_test(
    source_file: str,
    project_root: str,
    function_name: str | None = None,
) -> TestRunResult:
    start_time = time.monotonic()
    root_text = _path_text(project_root)
    source_text = _path_text(source_file)
    if not root_text:
        return _log_and_build_failure(
            source_text, start_time, "failed",
            "临时回归测试失败: 项目根为空或非路径入参"
            f"（{type(project_root).__name__}），拒绝按进程 cwd 解析源文件",
            reason="invalid_project_root")
    if not source_text:
        return _log_and_build_failure(
            "", start_time, "failed",
            "临时回归测试失败: 源文件为空或非路径入参"
            f"（{type(source_file).__name__}）",
            reason="invalid_source_file")
    project_root = os.path.abspath(root_text)
    source_file = os.path.abspath(
        resolve_project_path(source_text, project_root))
    if not _path_within_root(source_file, project_root):
        return _log_and_build_failure(
            source_file, start_time, "failed",
            f"临时回归测试失败: 源文件越出项目根，拒绝导入执行: {source_file}",
            reason="outside_project_root")
    mod_path, fallback_reason = _resolve_regression_mod(source_file, project_root)
    if fallback_reason:
        logger.debug("[TempRegression] %s: %s", source_file, fallback_reason)
    if not _is_dotted_python_name(mod_path):
        return _reject_invalid_module_name(mod_path, source_file, start_time)
    if function_name is not None and (
            not isinstance(function_name, str)
            or (function_name != "" and not function_name.isidentifier())):
        logger.warning("[TempRegression] function_name 含非法字符: %r",
                       function_name)
        return _log_and_build_failure(
            source_file, start_time, "failed",
            f"临时回归测试失败: function_name {function_name!r} "
            "不是合法 Python 标识符",
            reason="invalid_function_name")
    with contextlib.ExitStack() as stack:
        stack.enter_context(_injected_project_sys_path(project_root))
        src_root = _source_layout_import_root(source_file, project_root)
        if src_root:
            stack.enter_context(_injected_project_sys_path(src_root))
        import_root = _module_import_root(mod_path, source_file)
        if import_root:
            stack.enter_context(_injected_project_sys_path(import_root))
        failure_status, errors, failure_message = _execute_and_collect(
            mod_path, source_file, function_name, project_root)
    if failure_status is not None:
        return _log_and_build_failure(
            source_file, start_time, failure_status, failure_message)
    return _assemble_verified_result(source_file, start_time, errors)
def _execute_single_suggestion(
        sug: dict[str, Any], project_root: str) -> dict[str, Any]:
    source_file = _anchored_source_path(
        _finding_field_text(sug, "file"), project_root)
    if not source_file or not os.path.isfile(source_file):
        return _execution_result(source_file, False, "skipped",
                                 "source file not found")
    if not _path_within_root(source_file, project_root):
        return _execution_result(source_file, False, "skipped",
                                 "source file outside project root")
    try:
        tr = run_temp_regression_test(source_file, project_root)
    except (OSError, ValueError) as e:
        logger.warning("[TempRegression] 临时回归测试执行异常: %s", e, exc_info=True)
        return _execution_result(source_file, False, "error", str(e)[:200])
    return _execution_result(source_file, True, tr.status,
                             tr.error_message, tr.passed)
_DEFAULT_MAX_EXECUTE = 5
def _normalize_max_execute(max_execute: Any) -> int:
    if not isinstance(max_execute, bool):
        try:
            return max(0, int(max_execute))
        except (TypeError, ValueError, OverflowError) as _swallow_e:
            log_swallowed(
                __name__, _swallow_e,
                context=f'_normalize_max_execute:{type(_swallow_e).__name__}')
    logger.warning(
        "[TempRegression] max_execute 非数值 (%r)，回退默认 %d",
        max_execute, _DEFAULT_MAX_EXECUTE)
    return _DEFAULT_MAX_EXECUTE
def _select_executable_suggestions(suggestions: list[dict]) -> list[dict]:
    executable = [
        s for s in suggestions
        if isinstance(s, dict) and s.get("action") == "add_test"
    ]
    sev_order = {"high": 0, "medium": 1, "low": 2}
    executable.sort(key=lambda s: sev_order.get(str(s.get("severity", "low")), 9))
    return executable
def execute_test_suggestions(
    suggestions: list[dict],
    project_root: str,
    max_execute: int = _DEFAULT_MAX_EXECUTE,
) -> list[dict]:
    _t0 = time.monotonic()
    results: list[dict] = []
    root_text = _path_text(project_root)
    if not suggestions or not root_text:
        _log_module_run("execute_test_suggestions", _t0,
                        executed=0, skipped=0, total=0, mode="passthrough")
        return results
    project_root = os.path.abspath(root_text)
    executable = _select_executable_suggestions(suggestions)
    budget = _normalize_max_execute(max_execute)
    for sug in executable[:budget]:
        results.append(
            _execute_single_suggestion(sug, project_root))
    executed = sum(1 for r in results if r.get("executed"))
    _log_module_run("execute_test_suggestions", _t0,
                    executed=executed,
                    skipped=len(results) - executed,
                    total=len(results))
    return results
def assess_cv_maturity(skill_dir: str, cv,
                       result: dict[str, Any]) -> None:
    try:
        _maturity_level = assess_test_maturity(skill_dir)
        if not isinstance(_maturity_level, TestMaturityLevel):
            logger.warning(
                "[Stage2b] 测试成熟度等级非法(%s: %r)，跳过成熟度装配",
                type(_maturity_level).__name__, _maturity_level)
            return
        _maturity_mult = get_confidence_multiplier(_maturity_level)
        _maturity_report = get_test_maturity_report(skill_dir)
        cv._test_maturity_multiplier = _maturity_mult
        cv._test_maturity_level = _maturity_level.name
        result["test_maturity"] = _maturity_report
        logger.info("[Stage2b] 测试成熟度: %s (乘数=%.2f, 活跃规则=%d, 兜底规则=%d, 跳过规则=%d)",
                    _maturity_level.name, _maturity_mult,
                    len(_maturity_report.get("active_rules", [])),
                    len(_maturity_report.get("fallback_rules", [])),
                    len(_maturity_report.get("skipped_rules", [])))
    except Exception as _mat_err:
        logger.warning("[Stage2b] 测试成熟度评估跳过: %s", _mat_err)
def run_stage2b_test_bridge(
        test_bridge, temp_dir: str, cv_report: dict[str, Any],
        result: dict[str, Any]) -> None:
    try:
        bridge = test_bridge
        if not _bridge_has_test_files(bridge):
            return
        _root = getattr(bridge, "project_root", "")
        project_root = _root if isinstance(_root, str) and _root else temp_dir
        _raw_findings = cv_report.get("confirmed_findings")
        confirmed_findings = (
            [entry for entry in _raw_findings if isinstance(entry, dict)]
            if isinstance(_raw_findings, list) else [])
        if confirmed_findings:
            xv_test_cross_validation(confirmed_findings, bridge)
            logger.info("[Stage2b] TestSuiteBridge XV: %d findings enhanced", len(confirmed_findings))
        _emit_test_suggestions(project_root, result, confirmed_findings,
                               bridge)
        _save_bridge_snapshot(bridge, temp_dir, "[Stage2b]")
    except Exception as tsb_err:
        logger.warning("[Stage2b] TestSuiteBridge 集成跳过: %s", tsb_err)
def _bridge_has_test_files(bridge) -> bool:
    cov_map = getattr(bridge, "coverage_map", None)
    total = getattr(cov_map, "total_test_files", 0)
    return isinstance(total, int) and not isinstance(total, bool) and total > 0
def _emit_test_suggestions(
        project_root: str, result: dict[str, Any],
        confirmed_findings: list[dict], bridge: Any) -> None:
    test_suggestions = suggest_test_coverage(confirmed_findings, bridge)
    if not test_suggestions:
        return
    result["test_coverage_suggestions"] = test_suggestions
    logger.info("[Stage2b] 测试覆盖建议: %d 条", len(test_suggestions))
    try:
        exec_results = execute_test_suggestions(test_suggestions, project_root)
        if exec_results:
            result["temp_regression_results"] = exec_results
            logger.info("[Stage2b] 临时回归测试执行: %d 项", len(exec_results))
    except Exception as exec_err:
        logger.warning("[Stage2b] 临时回归测试执行跳过: %s", exec_err)
def _save_bridge_snapshot(bridge: TestSuiteBridge, temp_dir: Any,
                         log_prefix: str) -> None:
    snapshot_dir = _path_text(temp_dir)
    if not snapshot_dir:
        logger.debug("%s temp_dir 为空，bridge 快照不落盘", log_prefix)
        return
    bridge.save(os.path.join(snapshot_dir, _SNAPSHOT_FILENAME))
def build_test_bridge(skill_dir: str, temp_dir: str, adapter=None) -> TestSuiteBridge | None:
    root_text = _path_text(skill_dir)
    if not root_text or not os.path.isdir(root_text):
        logger.warning("[FullPipeline] TestSuiteBridge 项目根无效(降级): %r",
                       skill_dir)
        _clear_bridge_slots()
        return None
    project_root = os.path.abspath(root_text)
    snapshot = _try_load_bridge_snapshot(temp_dir, adapter)
    if snapshot is not None:
        if _snapshot_root_is_foreign(snapshot, project_root):
            logger.info("[FullPipeline] bridge 快照属于其他项目根(%s)，放弃复用",
                        getattr(snapshot, "project_root", ""))
        else:
            return _bind_bridges(snapshot, "复用快照")
    try:
        bridge = TestSuiteBridge.build(project_root, adapter=adapter)
        _bind_bridges(bridge, "构建完成")
        try:
            _save_bridge_snapshot(bridge, temp_dir, "[FullPipeline]")
        except Exception as _bs_err:
            logger.debug("[FullPipeline] bridge 快照即时落盘失败(不阻断): %s",
                         _bs_err)
        return bridge
    except Exception as e:
        logger.warning("[FullPipeline] TestSuiteBridge 构建失败(降级): %s", e)
        _clear_bridge_slots()
        return None
def _snapshot_root_is_foreign(snapshot, project_root: Any) -> bool:
    snapshot_root = getattr(snapshot, "project_root", "")
    if not isinstance(snapshot_root, str) or not snapshot_root:
        return False
    if not isinstance(project_root, str) or not project_root:
        return False
    return (os.path.normcase(os.path.abspath(snapshot_root))
            != os.path.normcase(os.path.abspath(project_root)))
def _clear_bridge_slots() -> None:
    set_test_suite_bridge(None)
    set_mutation_test_bridge(None)
def _bind_bridges(bridge: TestSuiteBridge, action: str) -> TestSuiteBridge:
    set_test_suite_bridge(bridge)
    set_mutation_test_bridge(bridge)
    cov = bridge.coverage_map
    logger.info(
        "[FullPipeline] TestSuiteBridge %s: %d源文件, %d测试文件, level=%s",
        action, cov.total_source_files, cov.total_test_files,
        cov.effective_level)
    return bridge
def _snapshot_reuse_blocker(adapter, snapshot: TestSuiteBridge) -> str:
    current_adapter = adapter if adapter is not None else snapshot.adapter
    if current_adapter is None:
        return "缺少适配器，无法校验当前文件集"
    current_file_set = _new_snapshot_file_set(
        snapshot.project_root,
        current_adapter.get_source_files(),
        current_adapter.get_test_files(),
    )
    if snapshot.file_set != current_file_set:
        return "与当前文件集不一致"
    if not snapshot.file_fingerprint:
        return "缺少文件指纹，无法确认内容新鲜度"
    if snapshot.file_fingerprint != _snapshot_file_fingerprint(
            current_file_set):
        return "与当前文件内容状态不一致"
    return ""
def _try_load_bridge_snapshot(temp_dir: str, adapter=None) -> TestSuiteBridge | None:
    try:
        snapshot = TestSuiteBridge.load_latest(temp_dir, adapter=adapter)
    except Exception as e:
        logger.debug("[FullPipeline] bridge 快照加载失败(忽略): %s", e)
        return None
    if snapshot is None:
        return None
    try:
        _blocker = _snapshot_reuse_blocker(adapter, snapshot)
    except Exception as e:
        logger.debug("[FullPipeline] bridge 快照一致性校验失败(忽略): %s", e)
        return None
    if _blocker:
        logger.info("[FullPipeline] bridge 快照%s，放弃复用", _blocker)
        return None
    return snapshot

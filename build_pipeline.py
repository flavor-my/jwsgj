from __future__ import annotations

import logging
import os
from abc import (
    ABC,
    abstractmethod,
)
from collections import deque
from collections.abc import (
    Callable,
    Iterable,
    Iterator,
    Mapping,
)
from concurrent.futures import (
    ThreadPoolExecutor,
    as_completed,
)
from dataclasses import (
    dataclass,
    field,
)
from typing import (
    Any,
    Self,
)

from jwsgj.build_module_topology import (
    ArchitectureCheckStage as _ArchitectureCheckStage,
)
from jwsgj.build_preflight_guard import (
    check_cie_antipatterns,
    check_frontmatter,
    check_fupan_hook,
    check_security,
)
from jwsgj.diag_self_check import (
    check_python_deps,
    check_system_tools,
)
from jwsgj.diag_shared_source_core import read_source
from jwsgj.diag_types_defs import ContractViolationError
from jwsgj.diag_types_normalize import normalize_passed
from jwsgj.diag_types_vocab import RULE_MISSING_ANNOTATIONS
from jwsgj.log_config import log_swallowed
from jwsgj.refactor_api_contract import InfraContractStage
from jwsgj.runtime_scope import (
    iter_py_files,
)
from jwsgj.runtime_scope import (
    verify_isolated_import as _verify_isolated_import,
)
from jwsgj.skill_audit_rules import resolve_target_document
from jwsgj.skill_scan_kernels import (
    scan_python_quality_file,
    scan_python_security_file,
)

logger = logging.getLogger(__name__)
__all__ = [
    'CompositeSkill',
    'ExecuteStage',
    'LoadStage',
    'MetaOrchestrator',
    'PipelineResult',
    'PipelineStage',
    'PostVerifyStage',
    'PreFlightStage',
    'QualityGateStage',
    'SecurityScanStage',
    'SkillComposer',
    'SkillPipeline',
    'ValidationResult',
    'compose_skill',
    'create_skill_pipeline',
    'orchestrate_build',
    'self_test',
    'validate_meta_skill',
]
class PipelineStage(ABC):
    def __init__(self, name: str, description: str = "") -> None:
        self.name = name
        self.description = description
        self.result: dict[str, Any] | None = None
    @abstractmethod
    def run(self, context: dict[str, Any]) -> dict[str, Any]:
        pass
class ExecuteStage(PipelineStage):
    def __init__(self, name: str = "execute",
                 skill_name: str | None = None,
                 skill_dir: str | None = None) -> None:
        super().__init__(
            name,
            "Import skill package from its file location to verify importability")
        self.skill_name = skill_name
        self.skill_dir = skill_dir
    def run(self, context: dict[str, Any]) -> dict[str, Any]:
        skill_dir = self.skill_dir or context.get("skill_dir", "")
        skill_name = self.skill_name or context.get("skill_name", "")
        output = context.get("output", {})
        errors: list[str] = []
        warnings_list: list[str] = []
        if skill_dir and skill_name:
            output, failures = _verify_isolated_import(skill_dir, skill_name)
            errors = [f"ExecuteStage import failed: {failure}"
                      for failure in failures]
        else:
            warnings_list.append("ExecuteStage: no skill_dir/skill_name, passthrough mode")
        result = {"passed": not errors, "stage": self.name, "output": output}
        if errors:
            result["errors"] = errors
        if warnings_list:
            result["warnings"] = warnings_list
        return result
def _failure_messages(value: Any, field_name: str) -> list[Any]:
    if value is None:
        return []
    if isinstance(value, str):
        return [value] if value.strip() else []
    if isinstance(value, (list, tuple)):
        return list(value)
    return [
        (f"{field_name} has invalid type {type(value).__name__}; "
         "expected string or list/tuple")
    ]
class PostVerifyStage(PipelineStage):
    def __init__(self, name: str = "post_verify",
                 skill_name: str | None = None) -> None:
        super().__init__(
            name, "Normalize upstream stage result into verify payload")
        self.skill_name = skill_name
    def run(self, context: dict[str, Any]) -> dict[str, Any]:
        skill_name = self.skill_name or context.get("skill_name", "")
        results = context.get("results")
        if not isinstance(results, dict):
            return {
                "passed": False,
                "output": {},
                "errors": [],
                "error": (
                    f"results is not a dict "
                    f"(got {type(results).__name__}: {results!r:.200})"),
                "skill_name": skill_name,
                "stage": self.name,
            }
        passed = normalize_passed(results.get("passed"))
        output = results.get("output", {})
        errors = _failure_messages(results.get("errors"), "errors")
        failure = _stage_failure_evidence(results)
        if failure:
            passed = False
            if failure not in _non_blank_texts(errors):
                errors.append(failure)
        return {
            "passed": passed,
            "output": output,
            "errors": errors,
            "skill_name": skill_name,
            "stage": self.name,
        }
class SecurityScanStage(PipelineStage):
    def __init__(self, name: str = "security_scan",
                 skill_dir: str | None = None) -> None:
        super().__init__(name, "Pre-execution security scan")
        self.skill_dir = skill_dir
    def run(self, context: dict[str, Any]) -> dict[str, Any]:
        issues: list[str] = []
        scan_error_messages: list[str] = []
        skill_dir = self.skill_dir or context.get("skill_dir", "")
        if skill_dir and not os.path.isdir(skill_dir):
            issues.append(
                f"安全扫描: skill_dir 不存在或不是目录: {skill_dir}")
        elif skill_dir:
            try:
                for fpath in iter_py_files(skill_dir):
                    try:
                        issues.extend(scan_python_security_file(fpath))
                    except Exception as exc:  # noqa: BLE001
                        logger.debug("安全扫描单文件检查失败 %s: %s",
                                     os.path.basename(fpath), exc)
                        scan_error_messages.append(
                            f"Security scan error (file skipped): "
                            f"{os.path.basename(fpath)}: {exc}")
            except Exception as exc:  # noqa: BLE001
                logger.warning("安全扫描文件枚举失败: %s", exc)
                scan_error_messages.append(
                    f"Security scan error (enumeration): {exc}")
        errors = issues + scan_error_messages
        result = {"passed": not errors, "stage": self.name,
                  "issues": issues, "warnings": list(scan_error_messages)}
        if errors:
            result["errors"] = errors
        return result
def _check_md_hard_constraints(md_content: str, errors: list[str]) -> None:
    for check, label in (
        (check_frontmatter, "frontmatter"),
        (check_cie_antipatterns, "cie_antipatterns"),
        (check_fupan_hook, "fupan_hook"),
    ):
        try:
            check(md_content)
        except ContractViolationError as ce:
            logger.debug("SKILL.md %s 约束违规转结构化错误: %s", label, ce)
            errors.append(
                f"Preflight constraint violation in SKILL.md ({label}): {ce}")
class PreFlightStage(PipelineStage):
    def __init__(self, name: str = "pre_flight",
                 required_deps: dict | None = None,
                 skill_dir: str | None = None) -> None:
        super().__init__(
            name, "Check dependency availability and security constraints")
        self.required_deps = (
            required_deps if required_deps is not None else {})
        self.skill_dir = skill_dir
    def run(self, context: dict[str, Any]) -> dict[str, Any]:
        errors: list[str] = []
        warnings_list: list[str] = []
        python_deps, system_tools = self._normalize_required_deps(errors)
        self._check_missing_requirements(
            check_python_deps, python_deps, "Python package", errors)
        self._check_missing_requirements(
            check_system_tools, system_tools, "system tool", errors)
        skill_dir = self.skill_dir or context.get("skill_dir", "")
        target_declared = self.skill_dir is not None or "skill_dir" in context
        if not skill_dir:
            if target_declared:
                errors.append("PreFlightStage: skill_dir 必须为非空目录路径")
        elif not os.path.isdir(skill_dir):
            errors.append(
                f"PreFlightStage: skill_dir 不存在或不是目录: {skill_dir}")
        elif skill_dir:
            self._check_skill_md(skill_dir, errors)
            self._scan_py_files(skill_dir, errors, warnings_list)
        return {"passed": not errors, "stage": self.name,
                "errors": errors, "warnings": warnings_list}
    def _normalize_required_deps(
            self, errors: list[str]) -> tuple[list, list]:
        deps = self._coerce_required_deps(errors)
        return (self._flatten_dep_values(deps.get("python") or ()),
                self._flatten_dep_values(deps.get("system") or ()))
    def _coerce_required_deps(self, errors: list[str]) -> dict:
        deps = self.required_deps
        if isinstance(deps, (list, tuple, set, frozenset)):
            return {"python": list(deps)}
        if isinstance(deps, str):
            return {"python": [deps]}
        if isinstance(deps, Mapping):
            return dict(deps)
        errors.append(
            "Invalid required_deps: unsupported type "
            f"{type(deps).__name__} (expected dict/list/str)")
        logger.warning("PreFlightStage: required_deps 形态不支持（%s）",
                       type(deps).__name__)
        return {}
    @staticmethod
    def _flatten_dep_values(values: Any) -> list:
        if isinstance(values, dict):
            return [item for items in values.values()
                    for item in (list(items)
                                 if isinstance(items, (list, tuple, set,
                                                       frozenset))
                                 else [items])]
        if isinstance(values, (list, tuple, set, frozenset)):
            return list(values)
        return [values]
    @staticmethod
    def _check_missing_requirements(
            checker: Callable[[list], dict], requirements: list,
            requirement_kind: str, errors: list[str]) -> None:
        if not requirements:
            return
        for name, available in checker(requirements).items():
            if not available:
                errors.append(f"Missing {requirement_kind}: {name}")
    def _check_skill_md(self, skill_dir: str, errors: list[str]) -> None:
        skill_md = os.path.join(skill_dir, "SKILL.md")
        if not os.path.exists(skill_md):
            return
        md_content = self._read_md_content(skill_md, errors)
        if md_content is None:
            return
        try:
            check_security(md_content, filepath=skill_md)
        except ContractViolationError as ce:
            logger.debug("SKILL.md 安全违规转结构化错误: %s", ce)
            errors.append(f"Security violation in SKILL.md: {ce}")
        _check_md_hard_constraints(md_content, errors)
    @staticmethod
    def _read_md_content(skill_md: str, errors: list[str]) -> str | None:
        try:
            with open(skill_md, encoding="utf-8-sig") as fh:
                return fh.read()
        except FileNotFoundError:
            return None
        except (OSError, UnicodeDecodeError) as exc:
            log_swallowed(__name__, exc,
                          context=f'PreFlightStage._read_md_content'
                                  f':{type(exc).__name__}')
            errors.append(f"SKILL.md unreadable: {exc}")
            return None
    def _scan_py_files(self, skill_dir: str, errors: list[str],
                       warnings_list: list[str]) -> None:
        try:
            for py_file in iter_py_files(skill_dir):
                self._check_py_source(py_file, errors, warnings_list)
        except Exception as exc:  # noqa: BLE001
            logger.warning("PreFlightStage: 文件枚举失败: %s", exc)
            errors.append(f"PreFlightStage: 文件枚举失败: {exc}")
            warnings_list.append(f"PreFlightStage enumeration skipped: {exc}")
    @staticmethod
    def _check_py_source(py_file: str, errors: list[str],
                         warnings_list: list[str]) -> None:
        py_content = read_source(py_file)
        if py_content is None:
            logger.warning("PreFlightStage: 单文件读取失败: %s", py_file)
            errors.append(
                f"Unreadable file (security scan skipped): "
                f"{os.path.basename(py_file)}")
            warnings_list.append(
                f"Unreadable file skipped: {os.path.basename(py_file)}")
            return
        if not py_content.strip():
            return
        try:
            check_security(py_content, filepath=py_file)
        except ContractViolationError as ce:
            logger.debug(".py 安全违规转结构化错误: %s", ce)
            errors.append(
                f"Security violation in {os.path.basename(py_file)}: {ce}")
class LoadStage(PipelineStage):
    def __init__(self, name: str = "load", skill_dir: str | None = None) -> None:
        super().__init__(name, "Read target document content")
        self.skill_dir = skill_dir
    def run(self, context: dict[str, Any]) -> dict[str, Any]:
        skill_dir = self.skill_dir or context.get("skill_dir", "")
        if not skill_dir:
            return {"passed": True, "stage": self.name, "skill_md": None,
                    "warnings": ["LoadStage: no skill_dir, passthrough mode"]}
        if not os.path.isdir(skill_dir):
            error = f"LoadStage: skill_dir 不存在或不是目录: {skill_dir}"
            return {"passed": False, "stage": self.name, "skill_md": None,
                    "errors": [error], "error": error}
        skill_doc = os.path.join(skill_dir, "SKILL.md")
        if os.path.exists(skill_doc) and not os.path.isfile(skill_doc):
            error = "LoadStage: SKILL.md unreadable (not a regular file)"
            return {"passed": False, "stage": self.name, "skill_md": None,
                    "errors": [error], "error": error}
        doc = resolve_target_document(skill_dir)
        if doc.path is None:
            error = "LoadStage: target document not found (SKILL.md/README/pyproject)"
            return {"passed": False, "stage": self.name, "skill_md": None,
                    "errors": [error], "error": error}
        if doc.read_failed:
            error = f"LoadStage: {doc.path.name} unreadable"
            return {"passed": False, "stage": self.name, "skill_md": None,
                    "errors": [error], "error": error}
        return {"passed": True, "stage": self.name, "skill_md": doc.text,
                "doc_path": str(doc.path), "doc_role": doc.doc_role}
@dataclass
class _StageCollectors:
    issues: list
    warnings: list
    errors: list
    metrics: dict[str, int]
    def record_scan_error(self, message: str) -> None:
        self.metrics["scan_errors"] = self.metrics.get("scan_errors", 0) + 1
        self.errors.append(message)
        self.warnings.append(message)
class QualityGateStage(PipelineStage):
    def _scan_files(self, py_files: list[str],
                    collectors: _StageCollectors) -> None:
        collectors.metrics["files_checked"] = len(py_files)
        for py_file in py_files:
            try:
                finding = scan_python_quality_file(py_file)
            except Exception as exc:  # noqa: BLE001
                logger.debug("质量门禁单文件检查失败 %s: %s", os.path.basename(py_file), exc)
                collectors.record_scan_error(
                    f"Quality gate error (file skipped): {os.path.basename(py_file)}: {exc}")
                continue
            if finding is None:
                collectors.record_scan_error(
                    f"Quality gate error (unreadable): {os.path.basename(py_file)}")
                continue
            try:
                issues, warnings, delta = finding
            except (TypeError, ValueError) as exc:
                collectors.record_scan_error(
                    f"Quality gate error (invalid result): "
                    f"{os.path.basename(py_file)}: {exc}")
                continue
            if not isinstance(issues, (list, tuple)) \
                    or not isinstance(warnings, (list, tuple)):
                collectors.record_scan_error(
                    f"Quality gate error (invalid result shape): "
                    f"{os.path.basename(py_file)}")
                continue
            collectors.issues.extend(issues)
            collectors.warnings.extend(warnings)
            if not isinstance(delta, Mapping):
                collectors.record_scan_error(
                    f"Quality gate error (invalid metrics): "
                    f"{os.path.basename(py_file)}")
                continue
            if not all(
                    isinstance(key, str) and key
                    and isinstance(value, int) and not isinstance(value, bool)
                    and value >= 0
                    for key, value in delta.items()):
                collectors.record_scan_error(
                    f"Quality gate error (invalid metric values): "
                    f"{os.path.basename(py_file)}")
                continue
            for key, value in delta.items():
                collectors.metrics[key] = collectors.metrics.get(key, 0) + value
    def __init__(self, name: str = "quality_gate",
                 skill_dir: str | None = None) -> None:
        super().__init__(
            name,
            "Verify code quality: anti-patterns, exceptions, security, types",
        )
        self.skill_dir = skill_dir
    def _result(self, collectors: _StageCollectors,
                passed: bool) -> dict[str, Any]:
        return {
            "passed": passed,
            "issues": collectors.issues,
            "warnings": collectors.warnings,
            "errors": collectors.errors,
            "metrics": collectors.metrics,
            "stage": self.name,
        }
    def _enumerate_py_files(self, skill_dir: str,
                            collectors: _StageCollectors) -> list[str]:
        try:
            return list(iter_py_files(skill_dir))
        except Exception as exc:  # noqa: BLE001
            logger.debug("质量门禁文件枚举失败: %s", exc)
            collectors.record_scan_error(f"Quality gate error (skipped): {exc}")
            return []
    def run(self, context: dict[str, Any]) -> dict[str, Any]:
        collectors = _StageCollectors(
            issues=[],
            warnings=[],
            errors=[],
            metrics={
                "files_checked": 0,
                "anti_patterns": 0,
                "bare_excepts": 0,
                RULE_MISSING_ANNOTATIONS: 0,
                "dangerous_calls": 0,
                "scan_errors": 0,
            },
        )
        skill_dir = self.skill_dir or context.get("skill_dir", "")
        if not skill_dir:
            return self._result(collectors, True)
        if not os.path.isdir(skill_dir):
            collectors.issues.append(
                f"Quality gate: skill_dir 不存在或不是目录: {skill_dir}")
            collectors.metrics["invalid_skill_dir"] = 1
            return self._result(collectors, False)
        py_files = self._enumerate_py_files(skill_dir, collectors)
        self._scan_files(py_files, collectors)
        return self._result(
            collectors,
            not collectors.issues and not collectors.metrics["scan_errors"],
        )
def _normalize_stage_result(stage_result: Any, stage_name: str) -> dict[str, Any]:
    if isinstance(stage_result, dict):
        normalized = dict(stage_result)
        normalized.setdefault("stage", stage_name)
        return normalized
    if isinstance(stage_result, bool):
        return {"passed": stage_result, "stage": stage_name}
    return {
        "passed": False,
        "stage": stage_name,
        "output": stage_result,
        "error": (
            f"{stage_name} returned invalid result type "
            f"{type(stage_result).__name__}; expected dict or bool"),
    }
def _extract_stage_error(stage_result: dict[str, Any], stage_name: str) -> str:
    err = stage_result.get("error")
    if err is not None and str(err).strip():
        return str(err)
    errs = stage_result.get("errors")
    texts = _non_blank_texts(_failure_messages(errs, "errors"))
    if texts:
        return "; ".join(texts)
    issues = stage_result.get("issues")
    texts = _non_blank_texts(_failure_messages(issues, "issues"))
    if texts:
        head = "; ".join(texts[:3])
        rest = len(texts) - 3
        return f"{head} (+{rest} more)" if rest > 0 else head
    return f"{stage_name} failed"
def _safe_fire_callback(callback: Callable | None, *args: Any) -> None:
    if callback is None:
        return
    try:
        callback(*args)
    except Exception:
        logger.warning("阶段完成回调异常（已隔离，不影响流水线）", exc_info=True)
def _store_stage_result(ctx: dict[str, Any], stage_name: str,
                        stage_result: dict[str, Any]) -> None:
    ctx[f"stage_result:{stage_name}"] = stage_result
    ctx["results"] = stage_result
def _absorb_warnings(bucket: list, stage_result: dict[str, Any]) -> None:
    warnings_val = stage_result.get("warnings")
    if isinstance(warnings_val, (list, tuple)):
        bucket.extend(warnings_val)
def _absorb_metrics(bucket: dict[str, float], stage_result: dict[str, Any]) -> None:
    metrics_val = stage_result.get("metrics")
    if isinstance(metrics_val, dict):
        bucket.update(metrics_val)
def _mark_stage_failed(result: dict[str, Any], stage_name: str,
                       stage_result: dict[str, Any]) -> None:
    result["passed"] = False
    result["errors"].append(_extract_stage_error(stage_result, stage_name))
def _run_one_stage(executor: Any, stage_name: str,
                   ctx: dict[str, Any]) -> tuple[dict[str, Any], Exception | None]:
    try:
        return _invoke_stage(executor, stage_name, ctx), None
    except Exception as exc:  # noqa: BLE001
        log_swallowed(__name__, exc,
                      context=f'_run_one_stage:{type(exc).__name__}')
        return {"passed": False, "stage": stage_name,
                "error": str(exc)}, exc
def _stage_failure_logger(scope: str) -> Callable[[str, Exception], None]:
    def _log(stage_name: str, exc: Exception) -> None:
        logger.debug("阶段异常转结构化错误并中断%s: %s: %s",
                     scope, stage_name, exc)
    return _log
_LOG_PIPELINE_STAGE_FAILURE = _stage_failure_logger("流水线")
_LOG_ORCHESTRATOR_STAGE_FAILURE = _stage_failure_logger("编排")
def _default_task_id() -> str:
    return f"task_{os.getpid()}_{os.urandom(6).hex()}"
def _new_run_result(task_id: str, **extra: Any) -> dict[str, Any]:
    result: dict[str, Any] = {
        "task_id": task_id,
        "passed": True,
        "stages": {},
        "errors": [],
        "warnings": [],
    }
    result.update(extra)
    return result
def _resolve_stage_name(stage: Any) -> str:
    return (getattr(stage, 'name', None)
            or getattr(stage, '__name__', None)
            or str(stage))
def _writeback_stage_result(stage: Any, stage_result: dict[str, Any]) -> None:
    try:
        stage.result = stage_result
    except Exception as exc:  # noqa: BLE001
        logger.debug("阶段对象不支持 result 回写（%s），跳过: %s",
                     type(stage).__name__, exc)
def _invoke_stage(executor: Any, stage_name: str, ctx: dict[str, Any]) -> dict[str, Any]:
    if executor is None:
        return {
            "passed": False,
            "stage": stage_name,
            "error": f"no executor registered for stage '{stage_name}'",
        }
    if hasattr(executor, "run"):
        return _normalize_stage_result(executor.run(ctx), stage_name)
    if callable(executor):
        return _normalize_stage_result(executor(ctx), stage_name)
    return {
        "passed": False,
        "stage": stage_name,
        "error": (
            f"stage '{stage_name}' executor is not callable "
            f"({type(executor).__name__})"),
    }
_FAILED_STAGE_STATUSES: frozenset[str] = frozenset({
    "failed", "failure", "error", "blocked", "aborted",
    "cancelled", "canceled", "timeout",
})
def _non_blank_texts(values: Iterable) -> list[str]:
    return [text for text in (str(item) for item in values) if text.strip()]
def _first_text_evidence(values: Any, field_name: str) -> str:
    texts = _non_blank_texts(_failure_messages(values, field_name))
    return texts[0] if texts else ""
def _stage_failure_evidence(stage_result: dict[str, Any]) -> str:
    err = stage_result.get("error")
    if err is not None and str(err).strip():
        return str(err)
    for key in ("errors", "issues"):
        evidence = _first_text_evidence(stage_result.get(key), key)
        if evidence:
            return evidence
    status = str(stage_result.get("status") or "").strip().lower()
    return f"status={status}" if status in _FAILED_STAGE_STATUSES else ""
def _evaluate_stage_result(
        stage_result: dict[str, Any]) -> tuple[bool, str]:
    evidence = _stage_failure_evidence(stage_result)
    if "passed" in stage_result:
        verdict = normalize_passed(stage_result.get("passed"))
    else:
        verdict = not evidence
    return verdict and not evidence, evidence
def _stage_error_messages(stage_result: dict[str, Any]) -> list[Any]:
    return (
        _failure_messages(stage_result.get("error"), "error")
        + _failure_messages(stage_result.get("errors"), "errors")
    )
def _run_stage_step(
    executor: Any,
    stage_name: str,
    ctx: dict[str, Any],
    result: dict[str, Any],
    on_stage_complete: Callable | None,
    log_failure: Callable[[str, Exception], None],
    callback_subject: Any = None,
    metrics_bucket: dict[str, float] | None = None,
    writeback: bool = False,
) -> bool:
    stage_result, exc = _run_one_stage(executor, stage_name, ctx)
    result["stages"][stage_name] = stage_result
    if writeback:
        _writeback_stage_result(executor, stage_result)
    subject = stage_name if callback_subject is None else callback_subject
    if exc is not None:
        log_failure(stage_name, exc)
        result["passed"] = False
        result["errors"].append(
            f"{stage_name}: {str(exc) or type(exc).__name__}")
        _safe_fire_callback(on_stage_complete, subject, stage_result)
        return False
    _store_stage_result(ctx, stage_name, stage_result)
    _verdict, _evidence = _evaluate_stage_result(stage_result)
    _absorb_warnings(result["warnings"], stage_result)
    if metrics_bucket is not None:
        _absorb_metrics(metrics_bucket, stage_result)
    if not _verdict:
        _record = (stage_result
                   if stage_result.get("error") or stage_result.get("errors")
                   else {**stage_result, "error": _evidence})
        _mark_stage_failed(result, stage_name, _record)
        _safe_fire_callback(on_stage_complete, subject, stage_result)
        return False
    _safe_fire_callback(on_stage_complete, subject, stage_result)
    return True
def _run_stage_sequence(
    stage_names: list[str],
    stages: dict[str, Any],
    ctx: dict[str, Any],
    result: dict[str, Any],
    on_stage_complete: Callable[[str, dict[str, Any]], None] | None,
    log_failure: Callable[[str, Exception], None],
) -> None:
    for stage_name in stage_names:
        if not _run_stage_step(
                stages.get(stage_name), stage_name, ctx, result,
                on_stage_complete, log_failure, callback_subject=stage_name):
            break
class PipelineResult:
    def __init__(self) -> None:
        self.passed = True
        self.stages: dict[str, dict[str, Any]] = {}
        self.errors: list = []
        self.warnings: list = []
        self.metrics: dict[str, float] = {}
    def to_dict(self) -> dict[str, Any]:
        return {
            "passed": self.passed,
            "stages": self.stages,
            "errors": self.errors,
            "warnings": self.warnings,
            "metrics": self.metrics,
        }
class SkillPipeline:
    def __init__(self) -> None:
        self.stages: list = []
        self._on_stage_complete: Callable | None = self._default_stage_callback
    def add_stage(self, stage: PipelineStage | Callable[[dict[str, Any]], Any]) -> SkillPipeline:
        stage_name = _resolve_stage_name(stage)
        if any(_resolve_stage_name(existing) == stage_name
               for existing in self.stages):
            logger.warning(
                "[SkillPipeline] Stage '%s' re-registered, 聚合结果将被后者覆盖",
                stage_name)
        self.stages.append(stage)
        return self
    def on_stage_complete(self, callback: Callable) -> SkillPipeline:
        self._on_stage_complete = callback
        return self
    def _default_stage_callback(self, stage: Any, result: Any) -> None:
        stage_name = _resolve_stage_name(stage)
        passed = (_evaluate_stage_result(result)[0]
                  if isinstance(result, dict) else True)
        status = "PASSED" if passed else "FAILED"
        logger.info("[Pipeline] Stage '%s' %s", stage_name, status)
    def run(self, context: dict[str, Any]) -> PipelineResult:
        result = PipelineResult()
        aggregate: dict[str, Any] = {
            "passed": True,
            "stages": result.stages,
            "errors": result.errors,
            "warnings": result.warnings,
        }
        for stage in self.stages:
            stage_name = _resolve_stage_name(stage)
            keep_going = _run_stage_step(
                stage, stage_name, context, aggregate,
                self._on_stage_complete, _LOG_PIPELINE_STAGE_FAILURE,
                callback_subject=stage, metrics_bucket=result.metrics,
                writeback=True)
            if not keep_going:
                break
        result.passed = aggregate["passed"]
        return result
class MetaOrchestrator:
    def __init__(self) -> None:
        self._stage_order: list[str] = []
        self._stages: dict[str, Any] = {}
        self._on_stage_complete: Callable | None = None
    def on_stage_complete(self, callback: Callable) -> MetaOrchestrator:
        self._on_stage_complete = callback
        return self
    def add_stage(self, name: str, executor: Any = None) -> MetaOrchestrator:
        if name not in self._stage_order:
            self._stage_order.append(name)
        if executor is not None:
            if name in self._stages:
                logger.warning(
                    "[MetaOrchestrator] Stage '%s' re-registered, executor replaced",
                    name)
            self._stages[name] = executor
        return self
    def remove_stage(self, name: str) -> MetaOrchestrator:
        if name in self._stage_order:
            self._stage_order.remove(name)
            self._stages.pop(name, None)
            logger.info("[MetaOrchestrator] Removed stage: %s", name)
        else:
            logger.warning("[MetaOrchestrator] Stage '%s' not found, cannot remove", name)
        return self
    def run(self, **kwargs: Any) -> dict:
        task_id = kwargs.get("task_id") or _default_task_id()
        kwargs["task_id"] = task_id
        result = _new_run_result(task_id)
        _run_stage_sequence(
            self._stage_order, self._stages, kwargs, result,
            self._on_stage_complete, _LOG_ORCHESTRATOR_STAGE_FAILURE,
        )
        return result
    def run_parallel(self, parallel_stages: list[list[str]] | None = None, **kwargs: Any) -> dict:
        task_id = kwargs.get("task_id") or _default_task_id()
        kwargs["task_id"] = task_id
        result = _new_run_result(
            task_id, groups={}, mode="parallel")
        if parallel_stages is None:
            parallel_stages = [list(self._stage_order)]
        self._execute_groups(parallel_stages, kwargs, result)
        self._flatten_group_stages(result, parallel_stages)
        return result
    def _execute_groups(self, parallel_stages: list[list[str]],
                        kwargs: dict[str, Any], result: dict[str, Any]) -> None:
        max_workers = min(len(parallel_stages), 4) if parallel_stages else 1
        with ThreadPoolExecutor(max_workers=max_workers) as pool:
            pending: dict[Any, str] = {}
            for index, group in enumerate(parallel_stages):
                group_name = f"group_{index}"
                pending[pool.submit(
                    self._run_group, group_name, group, kwargs)] = group_name
            for future in as_completed(pending):
                self._record_group_outcome(future, pending[future], result)
    def _run_group(self, group_name: str, stage_names: list[str],
                   kwargs: dict[str, Any]) -> dict:
        group_result: dict[str, Any] = {
            "group": group_name,
            "passed": True,
            "stages": {},
            "errors": [],
            "warnings": [],
        }
        _run_stage_sequence(
            stage_names, self._stages, dict(kwargs), group_result,
            self._on_stage_complete,
            lambda stage_name, exc: logger.warning(
                "[MetaOrchestrator:run_parallel] Group %s stage %s failed: %s",
                group_name, stage_name, exc),
        )
        return group_result
    @staticmethod
    def _record_group_outcome(future: Any, group_name: str,
                              result: dict[str, Any]) -> None:
        try:
            group_result = future.result()
            result["groups"][group_name] = group_result
            result["warnings"].extend(group_result.get("warnings", []))
            if not group_result["passed"]:
                result["passed"] = False
                result["errors"].extend(group_result["errors"])
        except Exception as exc:
            logger.exception("[MetaOrchestrator:run_parallel] Group %s raised",
                             group_name)
            result["passed"] = False
            result["errors"].append(f"{group_name}: {exc}")
    @staticmethod
    def _flatten_group_stages(result: dict[str, Any],
                              parallel_stages: list[list[str]]) -> None:
        for index in range(len(parallel_stages)):
            gname = f"group_{index}"
            group_stages = result["groups"].get(gname, {}).get("stages", {})
            for sname, sres in group_stages.items():
                if sname in result["stages"]:
                    base_key = f"{gname}:{sname}"
                    disambig = base_key
                    suffix = 2
                    while disambig in result["stages"]:
                        disambig = f"{base_key}#{suffix}"
                        suffix += 1
                    result["stages"][disambig] = sres
                    result["warnings"].append(
                        f"stages 顶层视图同名阶段冲突消歧: {sname} -> {disambig}")
                else:
                    result["stages"][sname] = sres
def orchestrate_build(skill_name: str, stages: list | None = None, **kwargs: Any) -> dict:
    orchestrator = MetaOrchestrator()
    kwargs.setdefault("skill_name", skill_name)
    if stages:
        for stage in stages:
            if not isinstance(stage, dict) or "name" not in stage:
                raise ValueError(
                    f"stages 元素须为含 'name' 键的 dict，实际: {stage!r}")
            stage_name = stage["name"]
            if not isinstance(stage_name, str) or not stage_name.strip():
                raise ValueError(
                    f"stages 元素 name 须为非空字符串，实际: {stage_name!r}")
            orchestrator.add_stage(stage_name, stage.get("executor"))
    return orchestrator.run(**kwargs)
_DEFAULT_TIMEOUT = 600
_MAX_TIMEOUT = 1800
_MAX_STAGES = 5
def _normalized_budget(value: Any, default: int) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        return default
    return value if value > 0 else default
@dataclass
class ValidationResult:
    errors: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    suggestions: list[str] = field(default_factory=list)
    @property
    def is_valid(self) -> bool:
        return not self.errors
    def add_error(self, msg: str) -> None:
        self.errors.append(msg)
    def add_warning(self, msg: str) -> None:
        self.warnings.append(msg)
    def add_suggestion(self, msg: str) -> None:
        self.suggestions.append(msg)
def _type_error(result: ValidationResult, label: str, *values: Any) -> None:
    actual = "/".join(type(value).__name__ for value in values)
    result.add_error(f"{label} 类型错误（{actual}），应为字符串")
def _validate_stage_entry(stage: Any, i: int, stage_names: set[str],
                          sub_skills: set[str], result: ValidationResult) -> None:
    if not isinstance(stage, dict):
        result.add_error(f"阶段[{i}] 非 dict 形态({type(stage).__name__})，跳过校验")
        return
    name = stage.get("name", "")
    if not name:
        result.add_error(f"阶段[{i}] 缺少 name 字段")
        return
    if not isinstance(name, str):
        _type_error(result, f"阶段[{i}] name", name)
        return
    if not name.strip():
        result.add_error(f"阶段[{i}] name 必须为非空字符串")
        return
    if name in stage_names:
        result.add_error(f"阶段名重复: {name}")
    stage_names.add(name)
    sub_skill = stage.get("sub_skill", "")
    if not sub_skill or (isinstance(sub_skill, str) and not sub_skill.strip()):
        result.add_warning(f"阶段 '{name}' 未指定子Skill")
    elif not isinstance(sub_skill, str):
        _type_error(result, f"阶段 '{name}' sub_skill", sub_skill)
    else:
        sub_skills.add(sub_skill)
    _warn_missing_optional_fields(stage, name, result)
def _warn_missing_optional_fields(stage: dict, name: str,
                                  result: ValidationResult) -> None:
    for key, label in (
        ("description", "描述"),
        ("trigger_condition", "触发条件"),
        ("completion_condition", "完成条件"),
    ):
        if not stage.get(key):
            result.add_warning(f"阶段 '{name}' 缺少{label}")
def _validate_stages(stages: Any, result: ValidationResult) -> tuple[set[str], set[str]]:
    stage_names = set()
    sub_skills = set()
    for i, stage in enumerate(stages):
        _validate_stage_entry(stage, i, stage_names, sub_skills, result)
    if len(stage_names) < 2:
        result.add_error("Meta Skill 至少需要 2 个阶段")
    return stage_names, sub_skills
def _validate_transition_entry(trans: Any, i: int, stage_names: set[str],
                              result: ValidationResult) -> tuple[str, str] | None:
    if not isinstance(trans, dict):
        result.add_error(f"转换规则[{i}] 非 dict 形态({type(trans).__name__})，跳过校验")
        return None
    frm = trans.get("from_stage", "")
    to = trans.get("to_stage", "")
    if not frm:
        result.add_error(f"转换规则[{i}] 缺少 from_stage")
        return None
    if not to:
        result.add_error(f"转换规则[{i}] 缺少 to_stage")
        return None
    if not (isinstance(frm, str) and isinstance(to, str)):
        _type_error(result, f"转换规则[{i}] from_stage/to_stage", frm, to)
        return None
    unknown = {frm, to} - stage_names
    for name in sorted(unknown):
        result.add_error(f"转换规则引用未知阶段: {name}")
    return None if unknown else (frm, to)
def _validate_transitions(transitions: Any, stage_names: set[str],
                           result: ValidationResult) -> list[dict]:
    from_stages, to_stages = set(), set()
    valid: list[dict] = []
    for i, trans in enumerate(transitions):
        pair = _validate_transition_entry(trans, i, stage_names, result)
        if pair is None:
            continue
        from_stages.add(pair[0])
        to_stages.add(pair[1])
        valid.append(trans)
    multi_stage = len(stage_names) > 1
    for name in sorted(stage_names):
        if multi_stage and name not in to_stages:
            result.add_warning(f"阶段 '{name}' 无入度(可能是起始阶段)")
        if multi_stage and name not in from_stages:
            result.add_warning(f"阶段 '{name}' 无出度(可能是终止阶段)")
    return valid
def _validate_route_entry(route: Any, i: int, sub_skills: set[str],
                         result: ValidationResult) -> None:
    if not isinstance(route, dict):
        result.add_error(f"路由[{i}] 非 dict 形态({type(route).__name__})，跳过校验")
        return
    target = route.get("target_skill", "")
    if not target or (isinstance(target, str) and not target.strip()):
        result.add_error(f"路由[{i}] 缺少 target_skill")
    elif not isinstance(target, str):
        _type_error(result, f"路由[{i}] target_skill", target)
    elif target not in sub_skills:
        result.add_warning(f"路由[{i}] 目标Skill '{target}' 不在阶段定义的子Skill中")
    if not route.get("trigger_condition"):
        result.add_warning(f"路由[{i}] 缺少触发条件")
def _validate_routes(routes: Any, sub_skills: set[str], result: ValidationResult) -> None:
    for i, route in enumerate(routes):
        _validate_route_entry(route, i, sub_skills, result)
def _validate_best_practices(stages: Any, result: ValidationResult,
                             max_stages: int,
                             max_timeout_seconds: int) -> None:
    if len(stages) > max_stages:
        result.add_suggestion(
            f"阶段数 > {max_stages},考虑合并简单阶段或拆分为多个 Meta Skill")
    for stage in stages:
        if not isinstance(stage, dict):
            continue
        timeout = stage.get("timeout_seconds", _DEFAULT_TIMEOUT)
        if (isinstance(timeout, (int, float)) and not isinstance(timeout, bool)
                and timeout > max_timeout_seconds):
            result.add_suggestion(
                f"阶段 '{stage.get('name')}' 超时 {timeout}s > "
                f"{max_timeout_seconds // 60}min,考虑拆分")
def validate_meta_skill(
    stages: list[dict],
    transitions: list[dict],
    routes: list[dict] | None = None,
    *,
    max_stages: int = _MAX_STAGES,
    max_timeout_seconds: int = _MAX_TIMEOUT,
) -> ValidationResult:
    result = ValidationResult()
    max_stages = _normalized_budget(max_stages, _MAX_STAGES)
    max_timeout_seconds = _normalized_budget(
        max_timeout_seconds, _MAX_TIMEOUT)
    routes = [] if routes is None else routes
    stages = _normalize_list_input(stages, "stages", result)
    transitions = _normalize_list_input(transitions, "transitions", result)
    routes = _normalize_list_input(routes, "routes", result)
    stage_names, sub_skills = _validate_stages(stages, result)
    valid_transitions = _validate_transitions(transitions, stage_names, result)
    cycle = _detect_cycle(stage_names, valid_transitions)
    if cycle:
        result.add_error(f"检测到循环依赖: {' -> '.join(cycle)}")
    reachable = _find_reachable(stage_names, valid_transitions)
    for ds in sorted(stage_names - reachable):
        result.add_error(f"死阶段(不可达): {ds}")
    _validate_routes(routes, sub_skills, result)
    _validate_best_practices(stages, result, max_stages=max_stages,
                             max_timeout_seconds=max_timeout_seconds)
    return result
def _normalize_list_input(value: Any, label: str,
                          result: ValidationResult) -> list:
    if isinstance(value, list):
        return value
    result.add_error(f"{label} 必须为列表(实际 {type(value).__name__})")
    return []
def _build_graph(stage_names: set[str], transitions: list[dict]) -> tuple[dict[str, list[str]], dict[str, int]]:
    graph = {name: [] for name in stage_names}
    in_degree = dict.fromkeys(stage_names, 0)
    for t in transitions:
        if not isinstance(t, dict):
            continue
        frm = t.get("from_stage", "")
        to = t.get("to_stage", "")
        if frm in graph and to in graph:
            graph[frm].append(to)
            in_degree[to] += 1
    return graph, in_degree
def _reconstruct_cycle(parent: dict, node: str, nb: str) -> list[str]:
    if node == nb:
        return [node, node]
    cycle = [nb, node]
    curr = node
    while curr in parent and parent[curr] != nb:
        curr = parent[curr]
        cycle.append(curr)
    cycle.append(nb)
    cycle.reverse()
    return cycle
_DFS_WHITE, _DFS_GRAY, _DFS_BLACK = 0, 1, 2
def _detect_cycle(stage_names: set[str], transitions: list[dict]) -> list[str]:
    graph, _ = _build_graph(stage_names, transitions)
    color = dict.fromkeys(stage_names, _DFS_WHITE)
    parent: dict[str, str] = {}
    for name in sorted(stage_names):
        if color[name] != _DFS_WHITE:
            continue
        color[name] = _DFS_GRAY
        frames: list[tuple[str, Iterator[str]]] = [(name, iter(graph[name]))]
        while frames:
            node, neighbors = frames[-1]
            descended = False
            for nb in neighbors:
                if color[nb] == _DFS_GRAY:
                    return _reconstruct_cycle(parent, node, nb)
                if color[nb] == _DFS_WHITE:
                    parent[nb] = node
                    color[nb] = _DFS_GRAY
                    frames.append((nb, iter(graph[nb])))
                    descended = True
                    break
            if not descended:
                frames.pop()
                color[node] = _DFS_BLACK
    return []
def _find_reachable(stage_names: set[str], transitions: list[dict]) -> set[str]:
    if not stage_names:
        return set()
    graph, in_degree = _build_graph(stage_names, transitions)
    start_nodes = [n for n, d in in_degree.items() if d == 0]
    if not start_nodes:
        return set(stage_names)
    visited = set()
    queue = deque(start_nodes)
    while queue:
        node = queue.popleft()
        if node in visited:
            continue
        visited.add(node)
        queue.extend(neighbor for neighbor in graph.get(node, [])
                     if neighbor not in visited)
    return visited
@dataclass
class CompositeSkill:
    name: str
    description: str
    steps: list
    composition_type: str = "serial"
    metadata: dict = field(default_factory=lambda: {
        "version": "1.0.0",
        "created": "",
        "atomic_skills": [],
    })
class SkillComposer:
    def __init__(self: Self, name: str = "") -> None:
        self.name = name
        self.atomic_skills: dict = {}
    def register_atomic(self: Self, name: str, skill_def: dict) -> SkillComposer:
        if not isinstance(name, str) or not name.strip():
            logger.warning(
                "[SkillComposer] register_atomic 跳过无效技能名: %r", name)
            return self
        if not isinstance(skill_def, dict):
            logger.warning("[SkillComposer] register_atomic 跳过非 dict 技能定义: %r", skill_def)
            return self
        self.atomic_skills[name] = skill_def
        return self
    def register(self: Self, name: str, level: int, desc: str, deps: list | None = None) -> SkillComposer:
        return self.register_atomic(name, {
            "name": name, "level": level, "description": desc,
            "dependencies": deps or [],
        })
    def _dependency_names(self: Self, name: str) -> list:
        skill = self.atomic_skills.get(name)
        if not isinstance(skill, dict):
            return []
        raw_dependencies = skill.get("dependencies")
        if isinstance(raw_dependencies, str):
            candidates = [raw_dependencies]
        elif isinstance(raw_dependencies, (set, frozenset)):
            candidates = sorted(raw_dependencies, key=repr)
        elif isinstance(raw_dependencies, (list, tuple)):
            candidates = list(raw_dependencies)
        else:
            return []
        dependencies: list = []
        for dependency in candidates:
            if isinstance(dependency, str) and dependency.strip():
                dependencies.append(dependency)
            else:
                logger.warning(
                    "[SkillComposer] 跳过非法依赖项 %r（技能 %s）",
                    dependency, name)
        return dependencies
    def _order_serial_dependencies(self: Self, names: list) -> list:
        selected = set(names)
        ordered: list = []
        completed: set = set()
        pending = list(dict.fromkeys(names))
        dependency_map = {
            name: self._dependency_names(name) for name in pending}
        while pending:
            for name in pending:
                dependencies = [
                    dependency for dependency in dependency_map.get(name, ())
                    if dependency in selected
                ]
                if all(dependency in completed for dependency in dependencies):
                    ordered.append(name)
                    completed.add(name)
                    break
            else:
                raise ValueError(
                    "串行组合存在循环依赖: " + ", ".join(pending))
            pending = [name for name in pending if name not in completed]
        return ordered
    def _compose(self: Self, names: list, composition_type: str) -> CompositeSkill:
        missing = [n for n in names
                   if not isinstance(n, str) or n not in self.atomic_skills]
        if missing:
            logger.warning("[SkillComposer] %s组合跳过未注册技能: %s",
                         composition_type, missing)
        included = list(dict.fromkeys(
            n for n in names if isinstance(n, str) and n in self.atomic_skills))
        if composition_type == "serial":
            included = self._order_serial_dependencies(included)
        steps = [self.atomic_skills[n] for n in included]
        composed = CompositeSkill(
            name=self.name, description=f"{composition_type} composition",
            steps=steps, composition_type=composition_type,
        )
        composed.metadata["atomic_skills"] = included
        return composed
    def compose_serial(self: Self, names: list) -> CompositeSkill:
        return self._compose(names, "serial")
    def compose_parallel(self: Self, names: list) -> CompositeSkill:
        return self._compose(names, "parallel")
    def deprecate(self: Self, name: str, reason: str = "") -> None:
        if not isinstance(name, str) or not name.strip():
            logger.warning("[SkillComposer] deprecate 跳过无效技能名: %r", name)
            return
        if name in self.atomic_skills:
            self.atomic_skills[name]["deprecated"] = True
            self.atomic_skills[name]["deprecate_reason"] = reason
            return
        logger.warning("[SkillComposer] deprecate 跳过未注册技能: %s", name)
    def merge(self: Self, name_a: str, name_b: str, new_name: str) -> None:
        names = (name_a, name_b, new_name)
        if not all(isinstance(name, str) and name.strip() for name in names):
            logger.warning("[SkillComposer] merge 跳过无效技能名: %r", names)
            return
        missing = [n for n in (name_a, name_b) if n not in self.atomic_skills]
        if missing:
            logger.warning("[SkillComposer] merge 跳过未注册来源技能: %s", missing)
            return
        if new_name in self.atomic_skills and new_name not in (name_a, name_b):
            logger.warning(
                "[SkillComposer] merge 跳过会覆盖已有技能的目标名: %s", new_name)
            return
        internal_names = (name_a, name_b, new_name)
        dependencies = list(dict.fromkeys(
            dependency
            for source_name in (name_a, name_b)
            for dependency in self._dependency_names(source_name)
            if dependency not in internal_names
        ))
        levels = [self.atomic_skills[name].get("level")
                  for name in (name_a, name_b)]
        numeric_levels = [level for level in levels
                          if isinstance(level, int) and not isinstance(level, bool)]
        self.atomic_skills[new_name] = {
            "name": new_name,
            "merged_from": [name_a, name_b],
            "description": f"Merged: {name_a} + {name_b}",
            "level": max(numeric_levels, default=0),
            "dependencies": dependencies,
        }
def _register_composable_skills(composer: SkillComposer, skills: list) -> None:
    for skill in (skills or []):
        if not isinstance(skill, dict):
            logger.warning("[SkillComposer] compose_skill 跳过非 dict 技能条目: %r", skill)
            continue
        skill_name = skill.get("name")
        if not skill_name:
            logger.warning("[SkillComposer] compose_skill 跳过缺 name 键的技能条目: %r", skill)
            continue
        composer.register_atomic(skill_name, skill)
def compose_skill(skills: list, mode: str = "serial", name: str = "composed") -> CompositeSkill:
    composer = SkillComposer(name)
    _register_composable_skills(composer, skills)
    if mode not in ("serial", "parallel"):
        logger.warning("[SkillComposer] compose_skill 未知组合模式 %r，按 serial 回退", mode)
        mode = "serial"
    compose = composer.compose_parallel if mode == "parallel" else composer.compose_serial
    return compose(list(composer.atomic_skills))
def _assert_selftest_registration(cur: SkillComposer) -> None:
    cur.register("file_rw", 1, "read/write local files")
    cur.register("text_proc", 1, "string and text ops", ["file_rw"])
    cur.register("data_viz", 2, "generate charts", ["file_rw"])
    cur.register("report_gen", 3, "generate full Excel reports", ["data_viz", "text_proc"])
    if len(cur.atomic_skills) != 4:
        raise RuntimeError("注册后原子技能数应为 4")
def _assert_selftest_deprecation(cur: SkillComposer) -> None:
    cur.deprecate("text_proc", "replaced by higher-level skill")
    if cur.atomic_skills["text_proc"].get("deprecated") is not True:
        raise RuntimeError("弃用标记未写入")
def _assert_selftest_merge(cur: SkillComposer) -> None:
    cur.merge("file_rw", "data_viz", "file_and_viz")
    merged = cur.atomic_skills.get("file_and_viz")
    if merged is None:
        raise RuntimeError("合并技能未生成")
    if merged.get("merged_from") != ["file_rw", "data_viz"]:
        raise RuntimeError("合并来源记录不符")
def _assert_selftest_composition(cur: SkillComposer) -> None:
    composed = cur.compose_serial(["file_rw", "data_viz"])
    if composed.composition_type != "serial":
        raise RuntimeError("组合类型不符")
    if len(composed.steps) != 2:
        raise RuntimeError("组合步骤数不符")
def self_test() -> bool:
    cur = SkillComposer()
    _assert_selftest_registration(cur)
    _assert_selftest_deprecation(cur)
    _assert_selftest_merge(cur)
    _assert_selftest_composition(cur)
    return True
def create_skill_pipeline(skill_dir: str, skill_name: str | None = None,
                          required_deps: dict | None = None,
                          architecture_check: bool = True,
                          quality_gate: bool = True) -> SkillPipeline:
    pipeline = SkillPipeline()
    pipeline.add_stage(PreFlightStage(
        required_deps=required_deps, skill_dir=skill_dir))
    pipeline.add_stage(SecurityScanStage(skill_dir=skill_dir))
    if architecture_check:
        pipeline.add_stage(_ArchitectureCheckStage(skill_dir=skill_dir))
        pipeline.add_stage(InfraContractStage(skill_dir=skill_dir))
    pipeline.add_stage(LoadStage(skill_dir=skill_dir))
    pipeline.add_stage(ExecuteStage(
        skill_name=skill_name, skill_dir=skill_dir))
    pipeline.add_stage(PostVerifyStage(skill_name=skill_name))
    if quality_gate:
        pipeline.add_stage(QualityGateStage(skill_dir=skill_dir))
    return pipeline
def _run_guarded(label: str, runner: Callable[[], dict[str, Any]]) -> tuple[dict[str, Any], str | None]:
    try:
        return runner(), None
    except Exception as exc:  # noqa: BLE001
        detail = str(exc) or type(exc).__name__
        logger.warning("quick_quality_enforce: %s异常: %s", label, detail)
        return {"error": detail, "passed": False}, detail
def _run_quality_gate(skill_dir: str) -> tuple[dict[str, Any], str | None]:
    def _check() -> dict[str, Any]:
        qg = QualityGateStage(skill_dir=skill_dir).run(
            {"skill_dir": skill_dir})
        return {
            "passed": (normalize_passed(qg.get("passed", False))
                       and not _stage_failure_evidence(qg)),
            "issues": qg.get("issues", []),
            "warnings": qg.get("warnings", []),
            "errors": _stage_error_messages(qg),
            "metrics": qg.get("metrics", {}),
        }
    return _run_guarded("质量门禁", _check)
def _run_architecture_check(skill_dir: str) -> tuple[dict[str, Any], str | None]:
    def _check() -> dict[str, Any]:
        arch = _ArchitectureCheckStage(skill_dir=skill_dir).run(
            {"skill_dir": skill_dir})
        contract = InfraContractStage(skill_dir=skill_dir).run(
            {"skill_dir": skill_dir})
        return {
            "passed": all(
                normalize_passed(payload.get("passed", False))
                and not _stage_failure_evidence(payload)
                for payload in (arch, contract)
            ),
            "issues": (list(arch.get("issues", []))
                       + list(contract.get("issues", []))),
            "warnings": (list(arch.get("warnings", []))
                         + list(contract.get("warnings", []))),
            "errors": (_stage_error_messages(arch)
                       + _stage_error_messages(contract)),
        }
    return _run_guarded("架构检查", _check)

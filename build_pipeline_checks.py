from __future__ import annotations

import ast
import copy
import hashlib
import inspect
import keyword
import logging
import os
import sys
import time
from collections.abc import (
    Callable,
    Iterable,
    Iterator,
    Mapping,
)
from concurrent.futures import ProcessPoolExecutor
from dataclasses import (
    dataclass,
    fields,
    is_dataclass,
    replace,
)
from enum import Enum
from pathlib import Path
from types import SimpleNamespace
from typing import (
    Any,
    Self,
)

from jwsgj.ai_review_item_plan import enqueue_plan_items
from jwsgj.build_pipeline import (
    SecurityScanStage,
    _normalized_budget,
    _run_architecture_check,
    _run_guarded,
    _run_quality_gate,
)
from jwsgj.diag_detector_assembly import (
    DiagnoseGate,
    GateScanCache,
    _gate_issue_row,
)
from jwsgj.diag_security_diagnoser import (
    DiagOptions,
    get_diagnoser,
)
from jwsgj.diag_shared_source_core import (
    line_start_offset,
    read_source,
)
from jwsgj.diag_shared_source_scan import (
    inline_suppressed_at,
    is_suppressed,
    parse_suppressions,
)
from jwsgj.diag_types_normalize import normalize_passed
from jwsgj.diag_types_vocab import (
    DiagnoseSeverity,
    Severity,
)
from jwsgj.engine_b1_cohesion import CohesionAnalyzer
from jwsgj.fp_rules_judge import (
    annotate_findings_with_fp_evidence,
    is_fp_rule,
    is_static_fp_rule,
)
from jwsgj.log_config import (
    collect_and_reset_degraded,
    degraded_section,
    log_swallowed,
    mark_section_degraded,
    perf_trace,
    write_audit,
)
from jwsgj.runtime_scope import (
    PY_SUFFIXES,
    is_test_file_path,
    keep_inventory_dir,
)
from jwsgj.shared_cache import SharedCache
from jwsgj.skill_audit_rules import (
    P_SEVERITY_MAP,
    SecurityIssue,
    SecurityReport,
    acquire_scan_cache,
    check_skill_packaging_quality,
    check_supply_chain,
    check_supply_chain_hardening,
    collect_delivery_issues,
    deduplicate_security_findings,
    file_compiles_strict,
    iter_scan_scope_files,
    join_issue_location,
    normalize_issue_line,
    normalize_issue_severity,
    normalize_issue_suggestion,
    read_scan_source_tree,
    resolve_target_document,
    split_issue_location,
)
from jwsgj.skill_scan_kernels import (
    SkillSecurityScanner,
    scan_document_assets,
)

logger = logging.getLogger(__name__)
__all__ = [
    'ConstraintBudgets',
    'ConstraintDimension',
    'ConstraintEngine',
    'HardConstraint',
    'consume_security_gate_findings',
    'diag_skill_security',
    'enqueue_security_fixes',
    'format_security_report',
    'quick_quality_enforce',
    'quick_security_scan',
    'run_security_detection',
    'scan_security_gate',
]
def quick_security_scan(skill_dir: str) -> dict[str, Any]:
    payload = _normalize_path_payload(skill_dir)
    if not _is_audit_target_payload(payload):
        _invalid = f"安全扫描: skill_dir 无效载荷: {skill_dir!r}"
        return {"passed": False, "stage": "security_scan",
                "issues": [_invalid], "errors": [_invalid],
                "warnings": []}
    return SecurityScanStage(skill_dir=payload).run({"skill_dir": payload})
_AI_QUALITY_FIX_INSTRUCTION = (
    "逐项审核 quality/architecture 的 issues 与 warnings；修复类问题"
    "审核通过后直接修改源码（备份→改→compile+import 验证→回归），"
    "一律根因修复、禁止补丁方式修复（吞异常遮蔽/调用点特判豁免/"
    "副本对冲/宽捕获重试/表层归一等症状压制形态一律打回重写，"
    "与当前项目写盘门禁的同口径要求一致），"
    "结构性调整经目标项目自身的重构执行入口落盘，"
    "不通过项按理由驳回"
)
class ConstraintDimension(Enum):
    COMPLETENESS = "completeness"
    ACCURACY = "accuracy"
    EXECUTABILITY = "executability"
    NORMATIVITY = "normativity"
    PERFORMANCE = "performance"
    ROBUSTNESS = "robustness"
    EFFICIENCY = "efficiency"
    MIGRABILITY = "migratability"
@dataclass(frozen=True)
class HardConstraint:
    dimension: ConstraintDimension
    name: str
    check: Callable[[Any], bool]
    error_message: str
    repair: Callable[[Any], Any] | None = None
    def _attempt_repair(self: Self, subject: Any) -> tuple[Any, bool]:
        if self.repair is None:
            return subject, False
        try:
            return self.repair(subject), True
        except Exception as e:  # noqa: BLE001
            logger.warning("自动修复失败(%s): %s", self.name, e)
            return subject, False
    def _safe_check(self: Self, subject: Any, phase: str) -> bool:
        try:
            return bool(self.check(subject))
        except Exception as e:  # noqa: BLE001
            logger.warning("[Constraint] %s评估异常,视为未通过: %s (%s)",
                           phase, e, self.name)
            return False
    def evaluate_and_repair(self: Self, subject: Any) -> tuple[Any, bool, dict[str, Any] | None]:
        if self._safe_check(subject, "约束"):
            return subject, False, None
        if self.repair is None:
            return subject, True, None
        repaired, repaired_ok = self._attempt_repair(subject)
        if not repaired_ok:
            return subject, True, None
        if not self._safe_check(repaired, "修复后"):
            return subject, True, None
        record = {"name": self.name, "dimension": self.dimension.value,
                  "repaired": True}
        return repaired, False, record
def _get_attr_or_key(subject: Any, key: str, default: Any = None) -> Any:
    if isinstance(subject, Mapping):
        value = subject.get(key, default)
    else:
        value = getattr(subject, key, default)
    return default if value is None else value
def _get_text(subject: Any, key: str, default: str = "") -> str:
    value = _get_attr_or_key(subject, key, default)
    if isinstance(value, str):
        return value
    if not value:
        return default
    try:
        return str(value)
    except Exception as e:  # noqa: BLE001
        logger.debug("_get_text: 字段 %s 字符串化失败，按缺省值降级: %s", key, e)
        return default
def _file_paths(subject: Any) -> list:
    files = _get_attr_or_key(subject, "files", [])
    if isinstance(files, (str, bytes)):
        return [files] if files else []
    if isinstance(files, Mapping):
        return [files] if files else []
    if isinstance(files, Iterable):
        return list(files)
    return [files] if files else []
def _path_basename(path: str) -> str:
    return path.replace("\\", "/").rsplit("/", 1)[-1]
def _replace_field(subject: Any, key: str, value: Any) -> Any:
    if isinstance(subject, Mapping):
        updated = dict(subject)
        updated[key] = value
        return updated
    try:
        if is_dataclass(subject) and not isinstance(subject, type) and \
                key in {item.name for item in fields(subject)}:
            return replace(subject, **{key: value})
    except Exception as e:  # noqa: BLE001
        logger.debug("_replace_field: dataclass 替换失败，尝试属性写入: %s", e)
    try:
        clone = copy.copy(subject)
        setattr(clone, key, value)
        return clone
    except Exception as e:  # noqa: BLE001
        logger.warning("_replace_field: 对象字段 %s 不可写，原样返回: %s", key, e)
        return subject
_DOC_CARRIER_NAMES = frozenset({
    "skill.md", "readme.md", "readme.rst", "readme.txt", "readme",
    "pyproject.toml", "setup.py", "setup.cfg"})
_DESC_MATCH_CHARS, _MAX_FILES = 500, 300
_DESCRIPTION_MIN_CHARS = 10
_MAX_PY_FILE_BYTES, _MAX_DESCRIPTION_CHARS = 200_000, 2000
@dataclass(frozen=True)
class ConstraintBudgets:
    description_chars: int = _DESC_MATCH_CHARS
    max_files: int = _MAX_FILES
    max_file_bytes: int = _MAX_PY_FILE_BYTES
    max_description_chars: int = _MAX_DESCRIPTION_CHARS
_DEFAULT_CONSTRAINT_BUDGETS = ConstraintBudgets()
def _check_description_matches_files(
        subject: Any, max_chars: int) -> bool:
    description = _get_text(subject, "description")
    if len(description) <= _normalized_budget(
            max_chars, _DEFAULT_CONSTRAINT_BUDGETS.description_chars):
        return True
    target_name = _get_text(subject, "name").strip()
    if not target_name:
        return False
    needle = target_name.lower().replace("-", "_")
    for item in _file_paths(subject):
        if not isinstance(item, str):
            continue
        normalized = item.replace("\\", "/").lower().replace("-", "_")
        if needle in normalized:
            return True
        if _path_basename(item).lower() in _DOC_CARRIER_NAMES:
            return True
    return False
def _check_no_large_files(subject: Any,
                          max_bytes: int) -> bool:
    limit = _normalized_budget(
        max_bytes, _DEFAULT_CONSTRAINT_BUDGETS.max_file_bytes)
    for f in _file_paths(subject):
        if not isinstance(f, str) or not f.lower().endswith(".py"):
            continue
        if not os.path.exists(f):
            continue
        try:
            if os.path.getsize(f) > limit:
                return False
        except OSError as e:
            logger.warning("_check_no_large_files: 文件大小不可测跳过: %s (%s)", f, e)
    return True
def _check_has_entry_document(subject: Any) -> bool:
    return any(isinstance(f, str)
               and _path_basename(f).lower() in _DOC_CARRIER_NAMES
               for f in _file_paths(subject))
def _file_identity(item: Any) -> Any:
    return item if isinstance(item, str) else repr(item)
def _check_no_duplicate_files(subject: Any) -> bool:
    keys = [_file_identity(item) for item in _file_paths(subject)]
    return len(set(keys)) == len(keys)
def _dedup_file_paths(subject: Any) -> Any:
    unique: list = []
    seen: set = set()
    for item in _file_paths(subject):
        key = _file_identity(item)
        if key in seen:
            continue
        seen.add(key)
        unique.append(item)
    return _replace_field(subject, "files", unique)
def _check_name_is_identifier(subject: Any) -> bool:
    name = _get_text(subject, "name")
    return name.isidentifier() and not keyword.iskeyword(name)
class ConstraintEngine:
    def __init__(self: Self,
                 budgets: ConstraintBudgets | None = None) -> None:
        if budgets is None:
            raw = _DEFAULT_CONSTRAINT_BUDGETS
        elif isinstance(budgets, ConstraintBudgets):
            raw = budgets
        else:
            raise TypeError(
                "budgets 必须是 ConstraintBudgets 或 None，"
                f"实际为 {type(budgets).__name__}")
        defaults = _DEFAULT_CONSTRAINT_BUDGETS
        self.budgets = ConstraintBudgets(
            description_chars=_normalized_budget(
                raw.description_chars, defaults.description_chars),
            max_files=_normalized_budget(raw.max_files, defaults.max_files),
            max_file_bytes=_normalized_budget(
                raw.max_file_bytes, defaults.max_file_bytes),
            max_description_chars=_normalized_budget(
                raw.max_description_chars, defaults.max_description_chars),
        )
        self._constraints: list[HardConstraint] = []
        self._dimension_defaults: dict[ConstraintDimension, list[HardConstraint]] = {}
        self._build_default_constraints()
        for dim in self._dimension_defaults:
            self.add_dimension_constraints(dim)
    def _check_python_syntax(self: Self, subject: Any) -> bool:
        files = _file_paths(subject)
        if not files:
            return True
        for fpath in files:
            if not (isinstance(fpath, str) and fpath.lower().endswith(".py")):
                continue
            source = read_source(fpath)
            if source is None:
                logger.warning("_check_python_syntax: %s 不可读,判为语法约束未通过", fpath)
                return False
            try:
                compile(source, fpath, "exec")
            except (SyntaxError, ValueError, RecursionError, MemoryError) as e:
                logger.warning("_check_python_syntax: %s 语法/编码错误: %s", fpath, e)
                return False
        return True
    def _build_default_constraints(self: Self) -> None:
        self._dimension_defaults = {
            ConstraintDimension.COMPLETENESS: self._defaults_completeness(),
            ConstraintDimension.NORMATIVITY: self._defaults_normativity(),
            ConstraintDimension.ROBUSTNESS: self._defaults_robustness(),
            ConstraintDimension.EXECUTABILITY: self._defaults_executability(),
            ConstraintDimension.ACCURACY: self._defaults_accuracy(),
            ConstraintDimension.PERFORMANCE: self._defaults_performance(),
            ConstraintDimension.EFFICIENCY: self._defaults_efficiency(),
            ConstraintDimension.MIGRABILITY: self._defaults_migratability(),
        }
    def _defaults_completeness(self: Self) -> list[HardConstraint]:
        return [
            HardConstraint(
                dimension=ConstraintDimension.COMPLETENESS,
                name="skill_name_present",
                check=lambda s: bool(_get_text(s, "name").strip()),
                error_message="目标名称不可为空",
                repair=lambda s: _replace_field(
                    s, "name", _get_text(s, "name").strip() or "unnamed-skill"),
            ),
            HardConstraint(
                dimension=ConstraintDimension.COMPLETENESS,
                name="description_present",
                check=lambda s: len(
                    _get_text(s, "description").strip()) >= _DESCRIPTION_MIN_CHARS,
                error_message=f"目标描述必须不少于{_DESCRIPTION_MIN_CHARS}字符",
                repair=lambda s: _replace_field(
                    s, "description",
                    (_get_text(s, "description").strip()
                     + "（功能描述待补充）").ljust(
                        _DESCRIPTION_MIN_CHARS, "。")),
            ),
        ]
    def _defaults_normativity(self: Self) -> list[HardConstraint]:
        return [
            HardConstraint(
                dimension=ConstraintDimension.NORMATIVITY,
                name="has_entry_document",
                check=_check_has_entry_document,
                error_message=("目标缺少入口文档：技能需 SKILL.md，"
                               "Python 项目需 pyproject/setup.cfg/setup.py/README"),
            ),
            HardConstraint(
                dimension=ConstraintDimension.NORMATIVITY,
                name="name_no_spaces",
                check=lambda s: " " not in _get_text(s, "name"),
                error_message="目标名称不可包含空格",
                repair=lambda s: _replace_field(
                    s, "name", _get_text(s, "name").replace(" ", "-")),
            ),
        ]
    def _defaults_robustness(self: Self) -> list[HardConstraint]:  # jwsgj:suppress IA-03 dead_stub — 该维度无硬约束：根包/扁平模块/scripts/src/PEP 420 均为有效布局
        return []
    def _defaults_executability(self: Self) -> list[HardConstraint]:
        return [
            HardConstraint(
                dimension=ConstraintDimension.EXECUTABILITY,
                name="python_syntax_valid",
                check=self._check_python_syntax,
                error_message="所有 .py 文件必须通过语法检查",
            ),
        ]
    def _defaults_accuracy(self: Self) -> list[HardConstraint]:
        return [
            HardConstraint(
                dimension=ConstraintDimension.ACCURACY,
                name="description_matches_files",
                check=lambda s: _check_description_matches_files(
                    s, self.budgets.description_chars),
                error_message=("描述过长或与实现/文档不匹配,"
                               "可能存在描述与实现不一致"),
            ),
            HardConstraint(
                dimension=ConstraintDimension.ACCURACY,
                name="no_duplicate_module_names",
                check=_check_no_duplicate_files,
                error_message="文件列表中存在重复模块名",
                repair=_dedup_file_paths,
            ),
        ]
    def _defaults_performance(self: Self) -> list[HardConstraint]:
        return [
            HardConstraint(
                dimension=ConstraintDimension.PERFORMANCE,
                name="file_count_reasonable",
                check=lambda s: len(_file_paths(s)) <= self.budgets.max_files,
                error_message=(f"文件数超过{self.budgets.max_files},"
                               "可能影响加载性能"),
            ),
            HardConstraint(
                dimension=ConstraintDimension.PERFORMANCE,
                name="no_large_files",
                check=lambda s: _check_no_large_files(
                    s, self.budgets.max_file_bytes),
                error_message=(f"存在超过{self.budgets.max_file_bytes // 1024}KB"
                               "的Python文件,可能影响解析性能"),
            ),
        ]
    def _defaults_efficiency(self: Self) -> list[HardConstraint]:
        return [
            HardConstraint(
                dimension=ConstraintDimension.EFFICIENCY,
                name="description_under_budget",
                check=lambda s: (len(_get_text(s, "description"))
                                 <= self.budgets.max_description_chars),
                error_message=(f"描述超过{self.budgets.max_description_chars}"
                               "字符,超出Token预算"),
                repair=lambda s: _replace_field(
                    s, "description",
                    _get_text(s, "description")[:self.budgets.max_description_chars]),
            ),
        ]
    def _defaults_migratability(self: Self) -> list[HardConstraint]:
        return [
            HardConstraint(
                dimension=ConstraintDimension.MIGRABILITY,
                name="has_version_field",
                check=lambda s: bool(_get_text(s, "version").strip()),
                error_message="目标缺少版本号,影响迁移兼容性",
                repair=lambda s: _replace_field(s, "version", "0.1.0"),
            ),
            HardConstraint(
                dimension=ConstraintDimension.MIGRABILITY,
                name="name_is_valid_identifier",
                check=_check_name_is_identifier,
                error_message="目标名称不是有效的Python标识符,影响迁移",
                repair=lambda s: _replace_field(
                    s, "name",
                    _get_text(s, "name").replace("-", "_").replace(" ", "_")),
            ),
        ]
    def add_dimension_constraints(self: Self, dimension: ConstraintDimension) -> Self:
        existing = {(c.dimension, c.name) for c in self._constraints}
        for constraint in self._dimension_defaults.get(dimension, []):
            key = (constraint.dimension, constraint.name)
            if key not in existing:
                self._constraints.append(constraint)
                existing.add(key)
        return self
    def enforce_constraints(self: Self, subject: Any) -> tuple[Any, list[dict[str, Any]]]:
        repair_records: list[dict[str, Any]] = []
        files = _get_attr_or_key(subject, "files")
        if isinstance(files, Iterator):
            subject = _replace_field(subject, "files", list(files))
        for constraint in self._constraints:
            subject, still_fails, record = constraint.evaluate_and_repair(subject)
            if record is not None:
                repair_records.append(record)
            if still_fails:
                repair_records.append({
                    "name": constraint.name,
                    "dimension": constraint.dimension.value,
                    "repaired": False,
                    "error": constraint.error_message,
                })
                if constraint.repair is None:
                    logger.warning("约束 '%s' 未通过且不可自动修复: %s",
                                   constraint.name, constraint.error_message)
                else:
                    logger.warning("约束 '%s' 修复后仍失败: %s",
                                   constraint.name, constraint.error_message)
        final_failures = {
            (constraint.dimension.value, constraint.name): constraint
            for constraint in self._constraints
            if not constraint._safe_check(subject, "最终复核")
        }
        finalized_records: list[dict[str, Any]] = []
        recorded_failures: set[tuple[str, str]] = set()
        for record in repair_records:
            key = (str(record.get("dimension")), str(record.get("name")))
            if record.get("repaired") is False:
                if key not in final_failures:
                    continue
                recorded_failures.add(key)
            elif key in final_failures:
                # 该约束的修复被后续约束改回失败：丢弃"已修复"记录，
                # 由下方最终复核统一补一条失败记录，避免同一约束自相矛盾。
                continue
            finalized_records.append(record)
        for key, constraint in final_failures.items():
            if key in recorded_failures:
                continue
            finalized_records.append({
                "name": constraint.name,
                "dimension": constraint.dimension.value,
                "repaired": False,
                "error": constraint.error_message,
            })
            if constraint.repair is None:
                logger.warning("约束 '%s' 最终复核未通过且不可自动修复: %s",
                               constraint.name, constraint.error_message)
            else:
                logger.warning("约束 '%s' 最终状态被后续修复破坏: %s",
                               constraint.name, constraint.error_message)
        return subject, finalized_records
def _collect_contract_profile(skill_dir: str) -> dict[str, Any]:
    profile: dict[str, Any] = {
        "skill_dir": skill_dir,
        "name": os.path.basename(os.path.normpath(skill_dir)),
        "description": "",
        "version": "",
        "files": [],
    }
    doc = resolve_target_document(skill_dir)
    profile["doc_role"] = doc.doc_role
    if doc.name:
        profile["name"] = doc.name
    if doc.description:
        profile["description"] = doc.description
    if doc.version:
        profile["version"] = doc.version
    files_inventory: list[str] = []
    inventory_errors: list[OSError] = []
    for _root, _dirs, _fnames in os.walk(
            skill_dir, onerror=inventory_errors.append):
        _dirs[:] = [d for d in _dirs if keep_inventory_dir(d)]
        files_inventory.extend(
            os.path.join(_root, _fn) for _fn in _fnames)
    if inventory_errors:
        raise inventory_errors[0]
    profile["files"] = files_inventory
    return profile
def _run_contract_check(
        skill_dir: str,
        budgets: ConstraintBudgets | None = None,
) -> tuple[dict[str, Any], str | None]:
    def _enforce() -> dict[str, Any]:
        profile = _collect_contract_profile(skill_dir)
        _repaired, repair_records = ConstraintEngine(
            budgets=budgets).enforce_constraints(profile)
        unresolved = [
            record for record in repair_records
            if record.get("repaired") is False
        ]
        return {
            "repair_records": repair_records,
            "passed": not unresolved,
            "unresolved_count": len(unresolved),
        }
    return _run_guarded("契约引擎", _enforce)
def _apply_stage_status(result: dict[str, Any], payload: dict[str, Any],
                        error: str | None, fail_status: str | None) -> None:
    # 任一阶段异常都意味着结果不完整：无论此前是否已有阶段判失败，
    # 状态都必须升级为 partial，否则后续阶段异常会被先前的 *_issues 状态遮蔽。
    if error:
        if result["status"] != "partial":
            result["status"] = "partial"
    elif (fail_status and not normalize_passed(payload.get("passed", False))
          and result["status"] == "ok"):
        result["status"] = fail_status
def quick_quality_enforce(skill_dir: str,
                          budgets: ConstraintBudgets | None = None) -> dict:
    payload = _normalize_path_payload(skill_dir)
    if not _is_audit_target_payload(payload):
        logger.warning('quick_quality_enforce: skill_dir 无效载荷 %r，返回显式错误结果',
                       skill_dir)
        return {
            "status": "invalid_target", "skill_dir": payload,
            "contract": {}, "quality": {}, "architecture": {},
            "passed": False, "error": f"技能目录无效: {skill_dir!r}",
            "ai_execution": {
                "next_action": "review_and_execute_quality_fixes",
                "instruction": _AI_QUALITY_FIX_INSTRUCTION,
            },
        }
    result: dict[str, Any] = {
        "status": "ok", "skill_dir": payload,
        "contract": {}, "quality": {}, "architecture": {},
    }
    contract_runner = (
        _run_contract_check if budgets is None
        else lambda path: _run_contract_check(path, budgets))
    for key, runner, fail_status in (
        ("contract", contract_runner, "contract_issues"),
        ("quality", _run_quality_gate, "quality_issues"),
        ("architecture", _run_architecture_check, "architecture_issues"),
    ):
        result[key], error = runner(payload)
        _apply_stage_status(result, result[key], error, fail_status)
    result["passed"] = all(
        normalize_passed(result[key].get("passed"))
        for key in ("contract", "quality", "architecture")
    )
    result["ai_execution"] = {
        "next_action": "review_and_execute_quality_fixes",
        "instruction": _AI_QUALITY_FIX_INSTRUCTION,
    }
    return result
_DEFAULT_P_LABEL = 'P2'
_UNKNOWN_RULE_ID = 'unknown'
_SEV_TO_P_MAP = {sev: p for p, sev in P_SEVERITY_MAP.items()}
_SEV_TO_P_MAP[Severity.INFO] = 'P4'
_P_TO_SEV_MAP = {p: sev for sev, p in _SEV_TO_P_MAP.items()}
_SEV_TO_RANK = {Severity.CRITICAL: 'CRITICAL', Severity.HIGH: 'HIGH'}
def _skill_finding_to_issue_pair(
        finding: dict) -> tuple[SecurityIssue, SimpleNamespace]:
    _ln_ss = normalize_issue_line(finding.get('line'))
    _sev_ss = finding.get('severity') or _DEFAULT_P_LABEL
    _rid_ss = finding.get('rule_id') or _UNKNOWN_RULE_ID
    _msg_ss = finding.get('message') or ''
    _sug_ss = finding.get('suggestion') or ''
    _file_ss = finding.get('file') or ''
    _severity = normalize_issue_severity(_sev_ss)
    issue = SecurityIssue(
        severity=_severity,
        category='技能安全-' + _rid_ss, description=_msg_ss,
        location=join_issue_location(str(_file_ss), _ln_ss), recommendation=_sug_ss)
    gate_ns = SimpleNamespace(
        is_false_positive=False,
        severity=_severity.name,
        category=SimpleNamespace(value=_rid_ss), cwe_id='',
        confidence=1.0, source='', sink=_rid_ss, suggestion=_sug_ss,
        line=_ln_ss, file=_file_ss)
    return issue, gate_ns
def _sec_skill_sec_scan(sp: Path, report: SecurityReport, gate: DiagnoseGate,
                        cache=None) -> None:
    with degraded_section('技能安全专项'):
        skill_sec_findings = SkillSecurityScanner(cache=cache).scan_skill(str(sp))
        _skill_sec_for_gate = []
        for finding in skill_sec_findings:
            issue, gate_ns = _skill_finding_to_issue_pair(finding)
            report.issues.append(issue)
            _skill_sec_for_gate.append(gate_ns)
        if _skill_sec_for_gate:
            consume_security_gate_findings(
                _skill_sec_for_gate, report, gate, sp)
def _layer1_issue(finding, cat_name: str, py_file: Path) -> SecurityIssue:
    _sugg = normalize_issue_suggestion(finding.suggestion)
    _ln1 = normalize_issue_line(finding.line)
    _sink1 = (finding.sink if isinstance(finding.sink, str) and finding.sink
              else 'unknown')
    return SecurityIssue(
        severity=normalize_issue_severity(finding.severity),
        category=f"安全检测-{cat_name}",
        description=f'{_sink1} at {py_file.name}:{_ln1}: {_sugg[:80]}',
        location=join_issue_location(str(py_file), _ln1),
        recommendation=_sugg)
def _sec_layer1_collect_findings(diagnoser, py_file: Path,
                                 code: str, tree,
                                 report: SecurityReport,
                                 raw_findings: list) -> None:
    result = diagnoser.diag(code, filepath=str(py_file), tree=tree,
                            options=DiagOptions(enable_symbolic=False,
                                                enable_cfg_du=False,
                                                include_extras=False))
    for finding in result.get('findings', []):
        _cat_name = (finding.category.value
                     if hasattr(finding.category, 'value')
                     else str(finding.category))
        if _layer1_finding_exempt(py_file, _cat_name, finding, code):
            continue
        raw_findings.append(finding)
        report.issues.append(_layer1_issue(finding, _cat_name, py_file))
_LAYER1_TEST_EXEMPT_CATEGORIES = frozenset({'hardcoded_secret', 'sql_injection'})
def _layer1_finding_exempt(py_file: Path, cat_name: str, finding,
                           code: str = '') -> bool:
    if (is_test_file_path(str(py_file))
            and cat_name in _LAYER1_TEST_EXEMPT_CATEGORIES):
        return True
    if code:
        _ln = normalize_issue_line(finding.line)
        if inline_suppressed_at(code, line_start_offset(code, _ln), cat_name):
            logger.info('[SUPPRESSED-INLINE] 安全检测-%s 行内抑制: %s:%s',
                      cat_name, py_file, _ln)
            return True
    return False
def _scan_layer1_security(sp: Path, report: SecurityReport,
                         cache=None) -> tuple[list, dict[str, str]]:
    _layer1_raw_findings: list = []
    _layer1_sources: dict[str, str] = {}
    with degraded_section('层1扫描'):
        diagnoser = get_diagnoser()
        for py_file in iter_scan_scope_files(sp, PY_SUFFIXES):
            try:
                code, _tree = read_scan_source_tree(py_file, cache)
                _layer1_sources[str(py_file)] = code
                _sec_layer1_collect_findings(
                    diagnoser, py_file, code, _tree, report,
                    _layer1_raw_findings)
            except Exception as _e:  # noqa: BLE001
                logger.warning('diag_skill_security: 跳过不可读文件 %s: %s', py_file, _e)
                mark_section_degraded('层1文件跳过')
    return _layer1_raw_findings, _layer1_sources
def _annotate_fp_evidence(_layer1_raw_findings: list,
                          _layer1_sources: dict[str, str]) -> None:
    if not _layer1_raw_findings:
        return
    with degraded_section('误报标注'):
        annotated = annotate_findings_with_fp_evidence(
            _layer1_raw_findings, source_map=_layer1_sources)
        if annotated:
            logger.info('安全审计: %d/%d 条检测发现带高置信误报证据(fp_evidence)',
                      annotated, len(_layer1_raw_findings))
def _p_level_findings(data) -> list:
    if not isinstance(data, dict):
        raise TypeError(
            f'P级扫描载荷必须为 dict，实际为 {type(data).__name__}')
    if data.get('status') == 'error':
        detail = str(data.get('message') or data.get('error') or '未知扫描错误')
        raise RuntimeError(f'P级扫描失败: {detail}')
    payload = data.get('data')
    if not isinstance(payload, dict):
        raise TypeError('P级扫描载荷缺少 dict 类型 data')
    findings = payload.get('findings')
    if not isinstance(findings, list):
        raise TypeError('P级扫描载荷缺少 list 类型 data.findings')
    valid = [finding for finding in findings if isinstance(finding, dict)]
    if len(valid) != len(findings):
        raise TypeError(
            f'P级扫描发现含 {len(findings) - len(valid)} 个非 dict 条目')
    return valid
def _p_finding_issue(finding: dict, prefix: str) -> SecurityIssue:
    _sev = normalize_issue_severity(finding.get('severity'))
    _rule = finding.get('rule_id') or _UNKNOWN_RULE_ID
    _line = normalize_issue_line(finding.get('line'))
    _file = str(finding.get('file') or '')
    return SecurityIssue(
        severity=_sev, category=f'{prefix}-{_rule}',
        description=str(finding.get('message') or ''),
        location=join_issue_location(_file, _line),
        recommendation=str(finding.get('suggestion') or ''))
def _run_p_level_stage(report: SecurityReport, label: str, loader) -> None:
    with degraded_section(label):
        for _finding in _p_level_findings(loader()):
            report.issues.append(_p_finding_issue(_finding, label))
def _scan_supply_chain_dimensions(sp: Path, report: SecurityReport,
                                  cache=None) -> None:
    with degraded_section('供应链四维'):
        sc_report = check_supply_chain(str(sp), cache=cache)
        report.issues.extend(sc_report.all_issues())
        if sc_report.scan_errors:
            mark_section_degraded('供应链四维扫描不完整')
        for error in sc_report.scan_errors:
            report.issues.append(SecurityIssue(
                severity=Severity.CRITICAL,
                category='供应链安全-扫描不完整',
                description=f'供应链安全扫描不完整: {error}',
                location=str(sp),
                recommendation='修复扫描错误后重新执行完整供应链安全审计'))
def _sec_detect_stage(sp: Path, report: SecurityReport, cache) -> list:
    _layer1_raw_findings, _layer1_sources = _scan_layer1_security(
        sp, report, cache=cache)
    _annotate_fp_evidence(_layer1_raw_findings, _layer1_sources)
    with degraded_section('文档资产扫描'):
        scan_document_assets(sp, report)
    _run_p_level_stage(
        report, '技能包装',
        lambda: check_skill_packaging_quality(str(sp)))
    _run_p_level_stage(
        report, '供应链加固',
        lambda: check_supply_chain_hardening(str(sp), cache=cache))
    _scan_supply_chain_dimensions(sp, report, cache=cache)
    return _layer1_raw_findings
def _detector_registration_snapshot(gate: DiagnoseGate | None = None) -> tuple:
    active_gate = gate if gate is not None else DiagnoseGate()
    detectors = active_gate._detectors
    return tuple(
        (check_id,
         getattr(detector, '__module__', type(detector).__module__),
         getattr(detector, '__qualname__', type(detector).__qualname__))
        for check_id, detector in sorted(detectors.items()))
def _gate_rules_key(gate: DiagnoseGate | None = None) -> str:
    try:
        active_gate = gate if gate is not None else DiagnoseGate()
        _self_module = sys.modules.get(DiagnoseGate.__module__)
        _mods = {
            module.__name__: module
            for module in (_self_module, *active_gate.detector_modules())
            if module is not None
        }
        _registration = _detector_registration_snapshot(active_gate)
        if not _mods or not _registration:
            return 'unversioned'
        _src = repr(_registration) + ''.join(
            inspect.getsource(_mods[name]) for name in sorted(_mods))
        return hashlib.sha256(_src.encode('utf-8')).hexdigest()
    except Exception:
        logger.debug('规则指纹计算失败，降级 unversioned（将触发全量重扫）',
                   exc_info=True)
        return 'unversioned'
def _gate_issues_from_scan(gate: DiagnoseGate, code: str, tree, py_file: Path,
                           rel: str, content_hash: str, cache: dict) -> list:
    gate_result = gate.check(code, filepath=str(py_file), tree=tree)
    raw_issues = [i for i in gate_result.issues if _is_blocking_issue(i)]
    if any(issue.check_id == 'GATE-DEGRADED' for issue in raw_issues):
        cache.pop(rel, None)
    else:
        GateScanCache.store(cache, rel, content_hash, raw_issues)
    return raw_issues
def _is_blocking_issue(issue) -> bool:
    return issue.severity in (DiagnoseSeverity.BLOCK, DiagnoseSeverity.ERROR)
def _append_gate_issue(report: SecurityReport, severity, category: str,
                       headline: str, message, location: str,
                       suggestion) -> None:
    report.issues.append(SecurityIssue(
        severity=severity, category=category,
        description=f'{headline}: {message}',
        location=location, recommendation=suggestion))
def _gate_error_suppressed(sp: Path, category: str, file_path: Path,
                           location: str) -> bool:
    if is_test_file_path(str(file_path)):
        return True
    if is_static_fp_rule(category, skill_dir=str(sp),
                         file_path=str(file_path)) \
            or is_fp_rule(str(sp), category):
        logger.info('[SecAudit] FP固化规则过滤门禁错误: %s %s', category, location)
        return True
    return False
def _emit_gate_issue(report: SecurityReport, issue, py_file: Path,
                     sp: Path) -> None:
    _loc = join_issue_location(str(py_file), normalize_issue_line(issue.line))
    if issue.severity == DiagnoseSeverity.BLOCK:
        if issue.check_id == 'D29' and file_compiles_strict(py_file):
            logger.warning('[SecAudit] D29 瞬时半写误报过滤: %s 首读语法错误，复读解析通过', py_file.name)
            return
        _append_gate_issue(report, Severity.CRITICAL,
                           f'门禁阻断-{issue.check_id}', '门禁阻断',
                           issue.message, _loc, issue.suggestion)
    elif issue.severity == DiagnoseSeverity.ERROR:
        _cat = f'门禁错误-{issue.check_id}'
        if (issue.check_id != 'GATE-DEGRADED'
                and _gate_error_suppressed(sp, _cat, py_file, _loc)):
            return
        _append_gate_issue(report, Severity.HIGH, _cat, '门禁错误',
                           issue.message, _loc, issue.suggestion)
def _gate_scan_file(py_file: Path, sp: Path, gate: DiagnoseGate, cache,
                    file_cache: dict, report: SecurityReport,
                    seen: set[str]) -> bool:
    code, _tree = read_scan_source_tree(py_file, cache)
    _rel = str(py_file.relative_to(sp))
    _hash = hashlib.sha256(code.encode('utf-8')).hexdigest()
    seen.add(_rel)
    _raw = GateScanCache.issues_for(file_cache, _rel, _hash)
    _dirty = _raw is None
    if _dirty:
        _raw = _gate_issues_from_scan(
            gate, code, _tree, py_file, _rel, _hash, file_cache)
    _suppressions = parse_suppressions(code)
    for issue in _raw:
        if _suppressions and is_suppressed(
                _suppressions, normalize_issue_line(issue.line),
                issue.check_id):
            logger.info('[SecAudit] 行内抑制过滤门禁错误: %s %s %s',
                      issue.check_id, py_file.name, issue.line)
            continue
        _emit_gate_issue(report, issue, py_file, sp)
    return _dirty
def _scan_gate_files(sp: Path, gate: DiagnoseGate, cache,
                     file_cache: dict, report: SecurityReport,
                     seen: set[str]) -> bool:
    dirty = False
    for py_file in iter_scan_scope_files(sp, PY_SUFFIXES):
        try:
            dirty |= _gate_scan_file(
                py_file, sp, gate, cache, file_cache, report, seen)
        except Exception as _e:  # noqa: BLE001
            logger.warning(
                'diag_skill_security: 跳过不可读文件(门禁) %s: %s', py_file, _e)
            try:
                _rel = str(py_file.relative_to(sp))
            except ValueError:
                _rel = str(py_file)
            if file_cache.pop(_rel, None) is not None:
                dirty = True
            mark_section_degraded('门禁文件跳过')
            continue
    return dirty
def _clear_gate_exempt(gate: Any) -> None:
    try:
        gate.d01_cycle_exempt = set()
    except Exception as exc:
        logger.warning(
            '[SecAudit] 门禁豁免集无法清空（%s），该 gate 实例不可复用: %s',
            type(gate).__name__, exc)
        raise RuntimeError(
            '门禁豁免集无法清空，禁止携带旧豁免继续安全扫描') from exc
def inject_d01_cycle_exempt(skill_dir, gate, cache=None) -> set:
    try:
        _exempt = CohesionAnalyzer(
            str(skill_dir), cache=cache).cycle_exempt_lazy_edges()
        gate.d01_cycle_exempt = _exempt
        if _exempt:
            logger.info('[SecAudit] D01 环断路器豁免: %d 条 lazy 边（组合图 SCC 内）',
                      len(_exempt))
        return _exempt
    except Exception:
        _clear_gate_exempt(gate)
        logger.warning('[SecAudit] D01 环断路器豁免计算失败，退回全量严格判定',
                     exc_info=True)
        return set()
_GATE_WORKER_GATE = None


def _gate_worker_init(cycle_exempt: Iterable[tuple] = ()) -> None:
    global _GATE_WORKER_GATE
    _GATE_WORKER_GATE = DiagnoseGate()
    _GATE_WORKER_GATE.d01_cycle_exempt = set(cycle_exempt)


def _gate_worker_scan(args: tuple) -> tuple | None:
    """进程池工作单元：扫描单文件并返回可序列化的门禁结果行。

    源码文本由父进程统一读取（走 SharedCache 归一化），子进程只做纯计算：
    否则子进程直读原始字节会与父进程的归一化文本产生不同哈希，缓存永远不命中。
    """
    rel, path, code = args
    gate = _GATE_WORKER_GATE
    if gate is None or not isinstance(code, str):
        return None
    try:
        tree = ast.parse(code)
    except (SyntaxError, ValueError, RecursionError):
        tree = None
    try:
        result = gate.check(code, filepath=str(path), tree=tree)
    except Exception:  # noqa: BLE001 —— 子进程异常降级为未命中，由串行通道重算
        return None
    rows = [_gate_issue_row(issue)
            for issue in result.issues if _is_blocking_issue(issue)]
    return rel, rows


def _gate_parallel_workers() -> int:
    if os.environ.get('JWSGJ_GATE_SERIAL', '').strip() == '1':
        return 0
    if 'pytest' in sys.modules or 'py.test' in sys.modules:
        return 0
    try:
        cpu = os.cpu_count() or 1
    except Exception:  # noqa: BLE001 —— 平台查询失败时退回串行
        return 0
    if cpu < 4:
        return 0
    return max(2, min(8, cpu - 1))


def _parallel_prefill_gate_cache(
        sp: Path, file_cache: dict, source_cache=None,
        cycle_exempt: Iterable[tuple] | None = None) -> bool:
    """并行预填门禁扫描缓存（476 文件 × 99 检测器的最优加速手段）。

    每个文件的门禁扫描彼此独立且为纯 CPU 计算，串行时单文件约 3.8s；
    这里用进程池按文件并行，结果写回同一份缓存，串行通道随后全部命中。
    任何异常（无法 pickle、子进程崩溃、平台限制）都降级为串行，不影响结论。
    """
    workers = _gate_parallel_workers()
    if workers <= 0:
        return False
    try:
        files = list(iter_scan_scope_files(sp, PY_SUFFIXES))
    except (OSError, ValueError):
        return False
    if len(files) < 8:
        return False
    tasks: list[tuple] = []
    hashes: dict[str, str] = {}
    for path in files:
        try:
            code, _tree = read_scan_source_tree(path, source_cache)
        except (OSError, ValueError, SyntaxError, RecursionError):
            continue
        if not isinstance(code, str):
            continue
        rel = str(path.relative_to(sp))
        content_hash = hashlib.sha256(code.encode('utf-8')).hexdigest()
        cached = file_cache.get(rel)
        if isinstance(cached, dict) and cached.get('hash') == content_hash:
            continue
        hashes[rel] = content_hash
        tasks.append((rel, str(path), code))
    if len(tasks) < 8:
        return False
    dirty = False
    try:
        with ProcessPoolExecutor(
                max_workers=workers,
                initializer=_gate_worker_init,
                initargs=(tuple(cycle_exempt or ()),)) as pool:
            for outcome in pool.map(_gate_worker_scan, tasks,
                                    chunksize=4):
                if not outcome:
                    continue
                rel, rows = outcome
                if any(row.get('check_id') in {'D29', 'GATE-DEGRADED'}
                       for row in rows):
                    file_cache.pop(rel, None)
                    continue
                file_cache[rel] = {'hash': hashes[rel], 'issues': rows}
                dirty = True
        logger.info('[SecAudit] 门禁并行预扫描完成: %d 文件 × %d 进程',
                    len(tasks), workers)
    except Exception as _par_err:  # noqa: BLE001 —— 并行失败降级串行，不改变结论
        logger.warning('[SecAudit] 门禁并行预扫描不可用，退回串行: %s',
                       _par_err)
        return False
    return dirty


def scan_security_gate(sp: Path, report: SecurityReport, gate: DiagnoseGate,
                       cache=None) -> None:
    with degraded_section('门禁扫描'):
        _cycle_exempt = inject_d01_cycle_exempt(sp, gate, cache=cache)
        _store = GateScanCache(
            str(sp), _cycle_exempt,
            rules_key_provider=lambda: _gate_rules_key(gate))
        _cache = _store.load()
        _seen: set[str] = set()
        _prefilled = _parallel_prefill_gate_cache(
            sp, _cache, cache, cycle_exempt=_cycle_exempt)
        _cache_dirty = _scan_gate_files(
            sp, gate, cache, _cache, report, _seen) or _prefilled
        _cache_dirty = GateScanCache.prune(_cache, _seen) or _cache_dirty
        if _cache_dirty:
            _store.save(_cache)
def consume_security_gate_findings(_layer1_raw_findings: list,
                                    report: SecurityReport,
                                    gate: DiagnoseGate, sp: Path) -> None:
    if not _layer1_raw_findings:
        return
    with degraded_section('门禁消费'):
        _reported = _reported_security_keys(report)
        sec_gate_result = gate.check_security_findings(_layer1_raw_findings)
        for issue in sec_gate_result.issues:
            _emit_gate_finding(report, issue, sp, _reported)
        if sec_gate_result.block_count > 0:
            logger.warning('安全门禁阻断 %d 项安全发现', sec_gate_result.block_count)
def _reported_security_keys(report: SecurityReport) -> set:
    _reported: set = set()
    for _iss in report.issues:
        if not isinstance(_iss.category, str):
            continue
        if _iss.category.startswith(('安全检测-', '技能安全-')):
            if not isinstance(_iss.location, str):
                continue
            _f, _l = split_issue_location(_iss.location)
            _rule = _iss.category.split('-', 1)[1]
            _reported.add((_f, _l, _rule))
    return _reported
def _emit_gate_finding(report: SecurityReport, issue, sp: Path,
                       reported: set) -> None:
    _details = getattr(issue, 'details', {})
    if not isinstance(_details, dict):
        _details = {}
    _file = str(_details.get('file') or sp)
    _line = normalize_issue_line(getattr(issue, 'line', 0))
    _loc = join_issue_location(_file, _line)
    _reported_key = (_file, _line, str(_details.get('category') or 'unknown'))
    if _reported_key in reported:
        return
    if issue.severity == DiagnoseSeverity.BLOCK:
        _append_gate_issue(report, Severity.CRITICAL,
                           f'安全门禁阻断-{issue.check_id}', '安全门禁阻断',
                           issue.message, _loc, issue.suggestion)
        reported.add(_reported_key)
        return
    if issue.severity != DiagnoseSeverity.ERROR:
        return
    _cat = f'安全门禁错误-{issue.check_id}'
    if _gate_error_suppressed(sp, _cat, Path(_file), _loc):
        return
    _append_gate_issue(report, Severity.HIGH, _cat, '安全门禁错误',
                       issue.message, _loc, issue.suggestion)
    reported.add(_reported_key)
def _sec_gate_stage(sp: Path, report: SecurityReport, cache,
                    layer1_raw: list) -> DiagnoseGate:
    gate = DiagnoseGate()
    scan_security_gate(sp, report, gate, cache=cache)
    consume_security_gate_findings(layer1_raw, report, gate, sp)
    return gate
def _sec_ops_stage(sp: Path, report: SecurityReport, gate: DiagnoseGate,
                    cache) -> None:
    collect_delivery_issues(sp, report, cache=cache)
    _sec_skill_sec_scan(sp, report, gate, cache=cache)
def run_security_detection(sp: Path, report: SecurityReport,
                           cache=None) -> None:
    _layer1_raw = _sec_detect_stage(sp, report, cache)
    gate = _sec_gate_stage(sp, report, cache, _layer1_raw)
    _sec_ops_stage(sp, report, gate, cache)
def _issue_finding_fields(issue: SecurityIssue) -> dict:
    _loc_file, _loc_line = split_issue_location(issue.location)
    return {'rule_id': issue.category, 'file': _loc_file, 'line': _loc_line,
            'message': issue.description, 'suggestion': issue.recommendation}
def _p_label_to_severity(label: Any) -> Severity:
    severity = _P_TO_SEV_MAP.get(label) if isinstance(label, str) else None
    return severity if severity is not None else normalize_issue_severity(label)
def _finding_to_issue(finding: dict) -> SecurityIssue:
    return SecurityIssue(
        severity=_p_label_to_severity(
            finding.get('severity', _DEFAULT_P_LABEL)),
        category=finding.get('rule_id', ''),
        description=finding.get('message', ''),
        location=join_issue_location(str(finding.get('file', '')),
                                normalize_issue_line(finding.get('line'))),
        recommendation=finding.get('suggestion', ''))
def _finding_rows(issues, severity_labels: dict, default=None) -> list[dict]:
    rows: list[dict] = []
    for issue in issues:
        label = severity_labels.get(
            normalize_issue_severity(issue.severity), default)
        if label is None:
            continue
        row = _issue_finding_fields(issue)
        row['severity'] = label
        rows.append(row)
    return rows
def _sec_dedup(report: SecurityReport) -> None:
    with degraded_section('安全去重'):
        rows = _finding_rows(report.issues, _SEV_TO_P_MAP, _DEFAULT_P_LABEL)
        deduped = deduplicate_security_findings(rows)
        if deduped and len(deduped) < len(rows):
            report.issues = [_finding_to_issue(d) for d in deduped]
            logger.info('安全发现去重: %d -> %d', len(rows), len(deduped))
def _group_issues_by_severity(issues) -> dict:
    grouped: dict = {}
    for issue in issues:
        grouped.setdefault(
            normalize_issue_severity(issue.severity), []).append(issue)
    return grouped
def _top_severity_issues(issues) -> tuple[list, list]:
    grouped = _group_issues_by_severity(issues)
    return grouped.get(Severity.CRITICAL, []), grouped.get(Severity.HIGH, [])
def _sec_finalize(report: SecurityReport) -> None:
    grouped = _group_issues_by_severity(report.issues)
    critical_count = len(grouped.get(Severity.CRITICAL, []))
    high_count = len(grouped.get(Severity.HIGH, []))
    medium_count = len(grouped.get(Severity.MEDIUM, []))
    if critical_count > 0:
        report.risk_level = 'critical'
        report.passed = False
    elif high_count > 0:
        report.risk_level = 'high'
        report.passed = False
    elif medium_count > 0:
        report.risk_level = 'medium'
        report.passed = True
    else:
        report.risk_level = 'low'
        report.passed = True
def _sec_enqueue_ai_review(sp: Path, report: SecurityReport) -> None:
    with degraded_section('AI审核入队'):
        items = _finding_rows(report.issues, _SEV_TO_RANK)
        if items:
            _enqueued = enqueue_security_fixes(str(sp), items)
            if (isinstance(_enqueued, dict)
                    and _enqueued.get('status') == 'error'):
                logger.warning('安全发现入队失败: %s',
                             _enqueued.get('error', 'unknown'))
                mark_section_degraded('AI审核入队')
def _sec_audit_log(sp: Path, report: SecurityReport) -> None:
    try:
        critical_issues, high_issues = _top_severity_issues(report.issues)
        if critical_issues or high_issues:
            write_audit('security_finding', skill_dir=str(sp),
                        risk_level=report.risk_level,
                        total_issues=len(report.issues),
                        critical_count=len(critical_issues),
                        high_count=len(high_issues),
                        findings=[{'category': i.category,
                                    'location': i.location,
                                    'description': str(i.description)[:200]}
                                   for i in (critical_issues + high_issues)[:20]])
        write_audit('security_scan_complete', skill_dir=str(sp),
                    risk_level=report.risk_level, passed=report.passed,
                    total_issues=len(report.issues))
    except Exception:
        logger.debug('write_audit failed for security findings', exc_info=True)
def _sec_perf_trace(sp: Path, report: SecurityReport,
                    scan_start: float | None) -> None:
    if scan_start is None:
        return
    try:
        perf_trace('security_scan',
                   int((time.monotonic() - scan_start) * 1000),
                   skill_dir=str(sp), finding_count=len(report.issues))
    except Exception:
        logger.debug('perf_trace failed for security scan', exc_info=True)
def _invalid_audit_report(skill_name: str, skill_path: str) -> SecurityReport:
    report = SecurityReport(skill_name=skill_name, skill_path=skill_path)
    report.passed = False
    report.risk_level = 'unknown'
    return report
def _normalize_path_payload(value) -> str:
    if isinstance(value, os.PathLike):
        try:
            value = os.fspath(value)
        except TypeError as _swallow_e:
            log_swallowed(__name__, _swallow_e,
                          context=f'_normalize_path_payload'
                                  f':{type(_swallow_e).__name__}')
            return ''
    if isinstance(value, str):
        stripped = value.strip()
        return stripped or value
    return ''
def _is_audit_target_payload(payload: str) -> bool:
    if not isinstance(payload, str) or not payload.strip():
        return False
    try:
        return os.path.normpath(payload) != os.curdir
    except (OSError, ValueError):
        return False
def _resolve_audit_target(skill_dir):
    payload = _normalize_path_payload(skill_dir)
    if not _is_audit_target_payload(payload):
        logger.warning('diag_skill_security: skill_dir 无效载荷 %r，'
                     '返回显式错误报告', skill_dir)
        return None, _invalid_audit_report('(未知)', payload)
    try:
        sp = Path(payload)
        exists = sp.exists()
        is_dir = sp.is_dir()
    except (OSError, ValueError) as exc:
        logger.warning('diag_skill_security: 路径无法解析 %r: %s，'
                     '返回显式错误报告', payload, exc)
        return None, _invalid_audit_report('(未知)', payload)
    if not exists:
        logger.warning('diag_skill_security: 目录不存在 %s，返回显式错误报告', sp)
        return None, _invalid_audit_report(sp.name, str(sp))
    if not is_dir:
        logger.warning('diag_skill_security: 技能根不是目录 %s，返回显式错误报告', sp)
        return None, _invalid_audit_report(sp.name, str(sp))
    return sp, None
def _attach_degraded_layers(report: SecurityReport, layers: dict) -> None:
    if not layers:
        return
    try:
        current = getattr(report, 'degraded_layers', None)
        merged = dict(current) if isinstance(current, Mapping) else {}
        for section, count in layers.items():
            merged[section] = merged.get(section, 0) + count
        report.degraded_layers = merged  # type: ignore[attr-defined]
    except Exception:
        logger.debug('attach degraded_layers failed', exc_info=True)
def _sec_converge_stage(sp: Path, report: SecurityReport,
                        scan_start: float) -> None:
    _sec_dedup(report)
    _scan_degraded = collect_and_reset_degraded()
    _attach_degraded_layers(report, _scan_degraded)
    if _scan_degraded and not any(
            issue.category == '安全审计-主流程异常' for issue in report.issues):
        detail = ', '.join(
            f'{section}({count})'
            for section, count in sorted(_scan_degraded.items()))
        report.issues.append(SecurityIssue(
            severity=Severity.CRITICAL,
            category='安全审计-扫描不完整',
            description=f'安全检测阶段降级，扫描结果不完整: {detail}',
            location=str(sp),
            recommendation='修复降级阶段后重新执行完整安全扫描'))
    _sec_finalize(report)
    _sec_enqueue_ai_review(sp, report)
    _sec_audit_log(sp, report)
    _sec_perf_trace(sp, report, scan_start)
    _attach_degraded_layers(report, collect_and_reset_degraded())
def diag_skill_security(skill_dir: str,
                        cache: SharedCache | None=None) -> SecurityReport:
    _scan_start = time.monotonic()
    sp, invalid = _resolve_audit_target(skill_dir)
    if invalid is not None:
        return invalid
    logger.info('diag_skill_security 开始: 技能目录=%s', sp)
    report = SecurityReport(skill_name=sp.name, skill_path=str(sp))
    collect_and_reset_degraded()
    _scan_failed = False
    try:
        cache = acquire_scan_cache(sp, cache,
                                   who="安全审计 diag_skill_security")
        run_security_detection(sp, report, cache=cache)
    except Exception as exc:
        _scan_failed = True
        logger.exception('diag_skill_security 主流程异常，按审计失败收口')
        mark_section_degraded('安全检测主流程')
        report.issues.append(SecurityIssue(
            severity=Severity.CRITICAL,
            category='安全审计-主流程异常',
            description=(f'安全检测主流程异常: '
                         f'{type(exc).__name__}: {exc}'),
            location=str(sp),
            recommendation='修复异常后重新扫描；本次结果按失败处理'))
    _sec_converge_stage(sp, report, _scan_start)
    if _scan_failed:
        report.passed = False
        report.risk_level = 'critical'
    logger.info(
        'diag_skill_security 完成: 风险=%s, 通过=%s, 问题数=%d, 耗时=%.0fms',
        report.risk_level, report.passed, len(report.issues),
        (time.monotonic() - _scan_start) * 1000,
    )
    return report
def format_security_report(report: SecurityReport) -> str:
    risk_level = str(report.risk_level or 'unknown').upper()
    lines = ['=' * 60, f'技能安全诊断: {report.skill_name}', '=' * 60,
             f'路径: {report.skill_path}',
             f'风险等级: {risk_level}',
             f"通过: {('是' if report.passed else '否')}",
             f'问题数: {len(report.issues)}', '']
    if report.issues:
        by_severity = _group_issues_by_severity(report.issues)
        for sev in [Severity.CRITICAL, Severity.HIGH, Severity.MEDIUM,
                    Severity.LOW, Severity.INFO]:
            if sev in by_severity:
                lines.append(f'--- {sev.value.upper()} ({len(by_severity[sev])}个) ---')
                for issue in by_severity[sev]:
                    lines.append(f'  [{issue.category}] {issue.description}')
                    lines.append(f'    位置: {issue.location}')
                    lines.append(f'    建议: {issue.recommendation}')
                    lines.append('')
    lines.append('=' * 60)
    return '\n'.join(lines)
def enqueue_security_fixes(skill_dir: str, items: list[dict]) -> dict:
    try:
        return enqueue_plan_items(
            skill_dir, "_security_fix_plan.json", "SEC", items)
    except Exception as e:  # noqa: BLE001
        logger.warning('enqueue_security_fixes failed: %s', e)
        return {'status': 'error', 'enqueued': 0, 'total': 0, 'error': str(e)}

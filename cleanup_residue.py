from __future__ import annotations

import itertools
import logging
import math
import os
import re
import shutil
import time
from collections import Counter
from dataclasses import dataclass, field
from enum import Enum
from typing import Any

from jwsgj.ai_review_item_channels import normalize_cleanup_reviews
from jwsgj.ai_review_item_plan import (
    _required_plan_lock,
    cleanup_operation,
    find_pending_entry,
    is_pending_plan,
    load_pending_security_plan,
    needs_fixed_source,
    pending_review_count,
    provided_source,
    prune_consumed_items,
    resolve_security_plan,
)
from jwsgj.build_safe_write import BACKUP_RETENTION_DAYS
from jwsgj.cleanup_artifacts import (
    classify_prune_target,
    is_unregistered_jinhua_artifact,
    is_unregistered_jinhua_dir,
    scan_unregistered_jinhua_artifacts,
    scan_unregistered_jinhua_dirs,
    scan_unscoped_jinhua_entries,
)
from jwsgj.diag_guard_io import (
    check_path_traversal,
    fs_path_text,
    safe_delete,
)
from jwsgj.diag_guard_state import (
    read_json_artifact,
    read_queue_json,
    write_queue_json,
)
from jwsgj.diag_symbol_surface import scan_broken_imports
from jwsgj.diag_types_normalize import (
    as_dict,
    as_item_list,
    as_list,
    as_str,
    dict_or_empty,
    drop_scalar_items,
    normalize_confidence,
    normalize_file_ref,
    normalize_line_no,
    str_or,
)
from jwsgj.diag_types_vocab import (
    DIAG_REPORT_DIRNAME,
    FMT_DATETIME_ISO,
)
from jwsgj.fix_safety_gate import (
    apply_security_write,
    apply_verified_write,
)
from jwsgj.fp_rules_judge import DEFAULT_SEVERITY
from jwsgj.html_report_stage_doc import normalize_skill_key
from jwsgj.runtime_paths import (
    EVOLUTION_STATE_SECTIONS,
    get_backup_base,
    get_html_report_base,
    get_jinhua_dir,
    get_temp_dir,
    json_artifact_path,
    json_root_dir,
)
from jwsgj.runtime_scope import (
    PACKAGE_EXCLUDE_FILE_NAMES,
    PROTECTED_CORE_FILES,
    RUNTIME_DIR_NAME,
    SKILL_PACKAGE_ALLOWED_HIDDEN,
    expand_git_bash_path,
    import_key,
    is_backup_snapshot_dir,
    is_package_excluded_file,
    is_unregistered_package_root_file,
    normalize_skill_dir,
    py_stem,
)

logger = logging.getLogger(__name__)
logger.info("cleanup_residue 清理域（判定 + 识别 + 待审登记 + 审核执行：删除/源码改写 + "
            "级联复核）已加载")
__all__ = [
    "CLEANABLE_ROOT_DIR_NAMES",
    "CLEANABLE_ROOT_DIR_PREFIXES",
    "CLEANABLE_ROOT_FILES",
    "JINHUA_PROHIBITED_RESIDUE",
    "MAX_CLEANUP_PLANS",
    "PROTECTED_RESIDUE_TARGETS",
    "REPORT_ARTIFACT_KEEP",
    "TS_SUFFIX_RE",
    "SafetyAction",
    "SafetyCheck",
    "SafetyGate",
    "apply_cleanup_fix",
    "apply_cleanup_verdict",
    "apply_security_verdict",
    "apply_temp_cleanup",
    "check_locator_scope_integrity",
    "cleanup_after_diagnosis",
    "cleanup_plan_path",
    "collect_cleanup_reviews",
    "default_ai_review",
    "enqueue_cleanup_plan",
    "enqueue_temp_cleanup",
    "is_absent_releasable_target",
    "is_cleanable_path",
    "is_jinhua_prohibited_target",
    "is_jinhua_unregistered_dir_target",
    "is_jinhua_unregistered_file_target",
    "is_skill_root_backup_target",
    "is_skill_root_temp_target",
    "list_pending_cleanup_reviews",
    "purge_skill_root_temp",
    "read_cleanup_plan",
    "reject_cleanup_plan",
    "scan_jinhua_residue",
    "scan_post_cleanup_dangling",
    "scan_skill_root_hygiene",
    "scan_temp_residue",
    "skill_root_real",
    "to_queue_priority",
    "write_cleanup_plan",
]
CLEANABLE_ROOT_FILES = frozenset()
# 时间戳后缀不强制下划线：中文名口径（诊断A20261121104830438）直接拼接，
# 旧英文前缀（diag_stage_20261121104830438）仍能匹配。
TS_SUFFIX_RE = re.compile(
    r"(\d{17}|\d{8}_\d{9}|\d{8}_\d{6}|\d{8}-\d{6})$")
def _is_timestamp_name(name: str) -> bool:
    return bool(TS_SUFFIX_RE.search(os.path.splitext(name)[0]))
def _is_timestamp_file(path: str, name: str,
                       allow_absent: bool = False) -> bool:
    return (_is_timestamp_name(name)
            and (allow_absent or os.path.isfile(path)))
REPORT_ARTIFACT_KEEP = 3
_DEFAULT_BACKUP_RETENTION_DAYS = float(BACKUP_RETENTION_DAYS)
_DEFAULT_SNAPSHOT_KEEP = 3
_STALE_TMP_DIR_AGE_DAYS = 1.0
PROTECTED_RESIDUE_TARGETS = {
    "_state",
    "_reports",
    "_anchor",
    "evolution_state.json",
    "evolution_events.jsonl",
    "retrospective_report.json",
    "lifecycle_state",
    "fp_rules.json",
    "fp_suppression.json",
    "fp_tracker.json",
    "fp_tracker_rules.json",
    "_fixer_experiences.json",
    "_human_confirmations.json",
    "evidence_weights.json",
    "_solidify_ssot.json",
    "_hallucination_registry.json",
    "consumption_state.json",
    "warning_history.json",
    "_version_history.json",
    "trigger_keywords_custom.json",
    "zero_backlog_ledger.jsonl",
    "ai_review_verdicts.jsonl",
    "cv_conclusion_history.jsonl",
    "_cleanup_ai_plan.json",
    "_ai_fix_plan.json",
    "_ai_adjustment_plan.json",
    "_treatment_state.json",
    "_mutation_cache",
    "log",
    "coverage-coord",
    "sec_gate_scan_cache",
}
_PROTECTED_RESIDUE_NORMCASE = frozenset(
    os.path.normcase(name) for name in PROTECTED_RESIDUE_TARGETS)
def _is_protected_residue_name(name: Any) -> bool:
    return (isinstance(name, str)
            and os.path.normcase(name) in _PROTECTED_RESIDUE_NORMCASE)
_JINHUA_STATE_MIGRATION_NAMES = frozenset({
    *EVOLUTION_STATE_SECTIONS.values(),
    "memory_injection_receipt.jsonl",
})
JINHUA_PROHIBITED_RESIDUE = frozenset({
    "audit_register.jsonl",
    "evolution_state.json.correction-bak",
    "enhancement_log.json",
    "enhancement_log.json.correction-bak",
    "feedback_history.json",
    "method_adjustments.json",
    "_growth_history.json",
    "log_finding_closure.json",
    "_enhancement_snapshots.json",
    "_coordinator_state.json",
    "_ai_approved_adjustments.json",
    "_threshold_adjustment_history.json",
    "_template_meta.json",
    "code_feedback_log.json",
    "memory_injection_receipt.jsonl",
    "threshold_history.json",
    "domains",
})
CLEANABLE_ROOT_DIR_PREFIXES = ("tmp",)
CLEANABLE_ROOT_DIR_NAMES = {"test_tmp"}
_DELETE_TEMP_OPERATION = "delete_temp_residue"
_LEGACY_REPORT_DIR_NAMES = tuple(
    dict.fromkeys((DIAG_REPORT_DIRNAME, "report_34")))
_DEFAULT_CLEANUP_OPERATION = "cleanup"
SKILL_ROOT_POLLUTION_DIRS = frozenset({
    ".pytest_cache", "__pycache__", ".ruff_cache", ".mypy_cache", "htmlcov",
})
_AGENT_SKILL_POLLUTION_DIRS = frozenset({".analysis"})
SKILL_ROOT_POLLUTION_FILES = PACKAGE_EXCLUDE_FILE_NAMES
SKILL_ROOT_POLLUTION_WALK_SKIP = frozenset({
    ".git", ".hg", ".svn",
    "venv", ".venv", "env", ".env", "node_modules", "site-packages",
    ".tox", ".nox", ".eggs", "__pypackages__", "build", "dist",
})
def _is_agent_skill_root(root_real: str) -> bool:
    return bool(root_real) and os.path.isfile(
        os.path.join(root_real, "SKILL.md"))
def skill_root_real(skill_dir) -> str | None:
    path = fs_path_text(skill_dir)
    if not path.strip():
        return None
    return os.path.realpath(normalize_skill_dir(path))
def _html_root_real() -> str | None:
    try:
        return os.path.realpath(get_html_report_base())
    except (RuntimeError, ValueError) as _e:
        logger.debug("htm 落点解析失败（按非 htm 域处理）: %s", _e)
        return None
def _path_key(path: str) -> str:
    return os.path.normcase(os.path.normpath(path))
def _same_path(first: str, second: str) -> bool:
    return _path_key(first) == _path_key(second)
def _covers_path(parent: str, child: str) -> bool:
    if not parent or not child:
        return False
    parent_key = _path_key(parent)
    child_key = _path_key(child)
    try:
        return os.path.commonpath((parent_key, child_key)) == parent_key
    except (OSError, ValueError, TypeError):
        return False
def _direct_child_name(root_real: str, target_real: str) -> str | None:
    if (not root_real or not _covers_path(root_real, target_real)
            or _same_path(root_real, target_real)):
        return None
    try:
        rel = os.path.relpath(target_real, root_real)
    except (OSError, ValueError, TypeError):
        return None
    if not rel or rel == os.curdir or os.sep in rel:
        return None
    return rel
def _htm_artifact_boundary_reason(target_real: str) -> str:
    leaf = os.path.basename(target_real)
    return (f"htm/ 阶段产物由 cleanup_artifacts 成对回收，"
            f"本清理通道不单独删除: {leaf}")
_EXISTENCE_PREDICATES: dict[str, Any] = {
    "file": os.path.isfile,
    "dir": os.path.isdir,
}
def _exists_as(target_real: str, kind: str = "") -> bool:
    return _EXISTENCE_PREDICATES.get(kind, os.path.exists)(target_real)
_OUT_OF_TEMP_FAMILIES: tuple[tuple[str, Any, str], ...] = (
    ("jinhua_prohibited",
     lambda sd, target, _td, _aa: is_jinhua_prohibited_target(sd, target), ""),
    ("jinhua_unregistered_file",
     lambda sd, target, _td, _aa: is_jinhua_unregistered_file_target(sd, target),
     "file"),
    ("jinhua_unregistered_dir",
     lambda sd, target, _td, aa: is_jinhua_unregistered_dir_target(
         sd, target, allow_absent=aa), "dir"),
    ("skill_root_temp",
     lambda sd, target, td, _aa: is_skill_root_temp_target(sd, target, td), ""),
    ("skill_root_backup",
     lambda sd, target, _td, _aa: is_skill_root_backup_target(sd, target), "dir"),
    ("skill_root_pollution",
     lambda sd, target, _td, aa: is_skill_root_pollution_target(
         sd, target, allow_absent=aa), ""),
    ("htm_artifact",
     lambda _sd, target, _td, _aa: _is_htm_report_target(target), "htm"),
)
def _out_of_temp_family(skill_dir: str, target_real: str,
                        temp_dir_real: str = "", *,
                        allow_absent: bool = False) -> tuple[str, str]:
    skill_dir = normalize_skill_dir(skill_dir)
    for family, hit, kind in _OUT_OF_TEMP_FAMILIES:
        if hit(skill_dir, target_real, temp_dir_real, allow_absent):
            return family, kind
    return "", ""
_FAMILY_KIND_LABELS = {"file": "文件", "dir": "目录", "": "现存条目"}
def _release_out_of_temp_specials(skill_dir: str, target_real: str,
                                   temp_dir: str) -> tuple[bool, str] | None:
    family, kind = _out_of_temp_family(skill_dir, target_real, temp_dir)
    if not family:
        return None
    if kind == "htm":
        return False, _htm_artifact_boundary_reason(target_real)
    if _exists_as(target_real, kind):
        return True, ""
    label = _FAMILY_KIND_LABELS.get(kind, "现存条目")
    return False, f"命中域外{family}族，但目标不是可清理的{label}"
def _release_coverage_layer(parts: list[str], target_real: str,
                            allow_absent: bool = False
                            ) -> tuple[bool, str] | None:
    if (len(parts) == 2 and parts[0] == "coverage"
            and parts[1].startswith("snapshot_") and parts[1].endswith(".json")
            and (allow_absent or os.path.isfile(target_real))):
        return True, ""
    return None
def _release_temp_layers(parts: list[str], target_real: str,
                         rel: str, allow_absent: bool = False
                         ) -> tuple[bool, str]:
    if any(_is_protected_residue_name(p) for p in parts):
        return False, f"目标命中保护白名单: {'/'.join(parts)}"
    if len(parts) == 1:
        return _release_root_level(parts, target_real, allow_absent)
    _coverage_verdict = _release_coverage_layer(
        parts, target_real, allow_absent)
    if _coverage_verdict is not None:
        return _coverage_verdict
    if parts[0] in _LEGACY_REPORT_DIR_NAMES:
        return _release_report_layer(parts, target_real, allow_absent)
    if len(parts) >= 2 and parts[0] == "mutation":
        return _release_mutation_layer(parts, target_real, allow_absent)
    return False, f"路径层级/类型不支持自动清理: {rel}"
def is_cleanable_path(skill_dir: str, target: str) -> tuple[bool, str]:
    if not target:
        return False, "目标路径为空"
    try:
        temp_dir = os.path.realpath(get_temp_dir(skill_dir))
    except (RuntimeError, ValueError, OSError) as _e:
        logger.warning("[CleanupBridge] Temp 归口不可解析，拒绝清理: %s", _e)
        return False, f"Temp 归口不可解析: {_e}"
    target_real = os.path.realpath(expand_git_bash_path(target))
    if _same_path(target_real, temp_dir):
        return False, "禁止删除 Temp 根目录本身"
    if _covers_path(target_real, temp_dir):
        return False, "禁止删除 Temp 根目录的上级目录（会连带删除活跃归口）"
    rel = ""
    parts: list[str] = []
    if _covers_path(temp_dir, target_real):
        rel = os.path.relpath(target_real, temp_dir)
        parts = [p for p in rel.split(os.sep) if p]
        if any(_is_protected_residue_name(p) for p in parts):
            return False, f"目标命中保护白名单: {'/'.join(parts)}"
    verdict = _release_out_of_temp_specials(skill_dir, target_real, temp_dir)
    if verdict is not None:
        return verdict
    _json_verdict = _release_json_artifact(skill_dir, target_real)
    if _json_verdict is not None:
        return _json_verdict
    if not parts:
        return False, "目标不在 Temp 目录内（拒绝路径穿越）"
    return _release_temp_layers(parts, target_real, rel)
def _release_json_artifact(
        skill_dir: str, target_real: str,
        allow_absent: bool = False,
) -> tuple[bool, str] | None:
    try:
        root = os.path.realpath(json_root_dir(skill_dir))
    except (RuntimeError, ValueError, OSError) as _e:
        logger.debug("zhenduan 落点解析失败（按非 JSON 域处理）: %s", _e)
        return None
    if not root or not _covers_path(root, target_real):
        return None
    if _same_path(target_real, root):
        return False, "禁止删除 zhenduan 根目录本身"
    rel = os.path.relpath(target_real, root)
    parts = [p for p in rel.split(os.sep) if p]
    if not parts:
        return False, "禁止删除 zhenduan 根目录本身"
    leaf = parts[-1]
    if len(parts) > 2:
        return False, f"zhenduan/ 层级越界（仅根级/命名空间两级）: {rel}"
    if not leaf.lower().endswith(".json"):
        return False, f"zhenduan/ 下非 JSON 产物 {leaf}，不可自动清理"
    if not _is_timestamp_name(leaf):
        return False, f"zhenduan/ 下非时间戳产物 {leaf}，不可自动清理"
    if not os.path.isfile(target_real):
        if allow_absent:
            return True, ""
        return False, f"zhenduan/ 下时间戳产物已不存在 {leaf}"
    html_root = _html_root_real()
    if not html_root:
        return False, (f"zhenduan/ 快照同名 HTML 不可核验，"
                       f"不得单独清理: {leaf}")
    companion = os.path.join(html_root, os.path.splitext(leaf)[0] + ".html")
    if os.path.isfile(companion):
        return False, (f"zhenduan/ 快照仍有同名 HTML，须由 "
                       f"cleanup_artifacts 成对回收: {leaf}")
    try:
        payload, status, error = read_json_artifact(
            target_real, propagate_io=True)
    except OSError as exc:
        return False, f"zhenduan/ 快照归属读取失败: {exc}"
    if status != "ok" or not isinstance(payload, dict):
        return False, f"zhenduan/ 快照归属不可验证: {error or status}"
    owner = payload.get("skill_dir")
    if not isinstance(owner, str) or not owner.strip():
        return False, f"zhenduan/ 快照缺少 skill_dir 归属: {leaf}"
    if normalize_skill_key(owner) != normalize_skill_key(skill_dir):
        return False, f"zhenduan/ 快照归属其他技能，拒绝跨技能清理: {leaf}"
    return True, ""
def _is_cleanable_root_file(name: str) -> bool:
    if name in CLEANABLE_ROOT_FILES:
        return True
    if name.startswith("f2_mutbak_"):
        return True
    return _is_timestamp_name(name)
def _is_cleanable_root_dir(name: str) -> bool:
    return (name in CLEANABLE_ROOT_DIR_NAMES
            or name.startswith(CLEANABLE_ROOT_DIR_PREFIXES)
            or name.startswith("_backup_"))
def _release_root_level(parts: list[str], target_real: str,
                        allow_absent: bool = False) -> tuple[bool, str]:
    name = parts[0]
    if ((allow_absent or os.path.isfile(target_real))
            and _is_cleanable_root_file(name)):
        return True, ""
    if ((allow_absent or os.path.isdir(target_real))
            and _is_cleanable_root_dir(name)):
        return True, ""
    return False, f"Temp 根级文件 {parts[0]} 不在可自动清理名单"
def _release_report_layer(parts: list[str], target_real: str,
                          allow_absent: bool = False) -> tuple[bool, str]:
    if len(parts) == 2 or (len(parts) == 3
                           and parts[1] in ("html", "_intermediate")):
        leaf = parts[-1]
        if _is_timestamp_file(target_real, leaf, allow_absent):
            return True, ""
        return False, f"{parts[0]}/ 下非时间戳产物 {leaf}，不可自动清理"
    return False, (f"{parts[0]}/ 层级越界 "
                   f"（仅根级/html/_intermediate 三层）: {'/'.join(parts)}")
def _release_mutation_layer(parts: list[str], target_real: str,
                            allow_absent: bool = False) -> tuple[bool, str]:
    if (parts[1].startswith("mut_") and len(parts) == 2
            and (allow_absent or os.path.isdir(target_real))):
        return True, ""
    if parts[1].startswith("mut_"):
        return False, ("变异测试副本仅支持整目录清理（整个 mut_* 目录），"
                       "当前目标不是可直接清理的 mut_* 目录")
    return False, f"mutation/ 下 {parts[1]} 非 mut_ 前缀，不可自动清理"
def _jinhua_real(skill_dir: str, action: str) -> str | None:
    try:
        return os.path.realpath(get_jinhua_dir(normalize_skill_dir(skill_dir)))
    except (RuntimeError, ValueError, OSError) as _e:
        logger.debug("[CleanupBridge] jinhua 归口不可用（%s降级不放行）: "
                     "%s: %s", action, skill_dir, _e)
        return None
def is_jinhua_prohibited_target(skill_dir: str, target_real: str) -> bool:
    jinhua_real = _jinhua_real(skill_dir, "禁产目标判定")
    if jinhua_real is None:
        return False
    name = _direct_child_name(jinhua_real, target_real)
    return (name in JINHUA_PROHIBITED_RESIDUE
            and name not in _JINHUA_STATE_MIGRATION_NAMES)
def _file_shaped_name(name: str) -> bool:
    return bool(os.path.splitext(str(name or ''))[1])
def is_jinhua_unregistered_file_target(skill_dir: str, target_real: str) -> bool:
    jinhua_real = _jinhua_real(skill_dir, "未登记文件判定")
    if jinhua_real is None:
        return False
    target_real = os.path.realpath(expand_git_bash_path(target_real))
    if os.path.basename(target_real) in JINHUA_PROHIBITED_RESIDUE:
        return False
    exists = os.path.exists(target_real)
    if exists and not os.path.isfile(target_real):
        return False
    try:
        relative = os.path.relpath(target_real, jinhua_real)
    except ValueError:  # jwsgj:silent-ok 纯值降级：入参不可解析时返回安全默认值，无副作用可留痕
        return False
    if not exists and not _file_shaped_name(os.path.basename(relative)):
        return False
    return is_unregistered_jinhua_artifact(skill_dir, relative)
def is_jinhua_unregistered_dir_target(
        skill_dir: str, target_real: str, *,
        allow_absent: bool = False) -> bool:
    jinhua_real = _jinhua_real(skill_dir, "未登记目录判定")
    if jinhua_real is None:
        return False
    name = _direct_child_name(jinhua_real, target_real)
    if not name:
        return False
    return is_unregistered_jinhua_dir(
        skill_dir, name, allow_absent=allow_absent)
def is_skill_root_temp_target(skill_dir: str, target_real: str,
                               temp_dir_real: str = "") -> bool:
    root_real = skill_root_real(skill_dir)
    if root_real is None:
        return False
    if not temp_dir_real:
        try:
            temp_dir_real = os.path.realpath(get_temp_dir(skill_dir))
        except (RuntimeError, ValueError, OSError) as _e:
            logger.warning(
                "[CleanupBridge] Temp 归口不可解析"
                "（技能根 Temp 判定降级不放行）: %s", _e)
            return False
    if _covers_path(temp_dir_real, target_real):
        return False
    temp_child = os.path.join(root_real, RUNTIME_DIR_NAME)
    if _same_path(target_real, temp_child):
        return False
    name = _direct_child_name(temp_child, target_real)
    if name is None:
        return False
    return not _is_protected_residue_name(name)
def is_skill_root_backup_target(skill_dir: str, target_real: str) -> bool:
    root_real = skill_root_real(skill_dir)
    if root_real is None:
        return False
    rel = _direct_child_name(root_real, target_real)
    if rel is None or not is_backup_snapshot_dir(rel):
        return False
    temp_child = os.path.join(root_real, RUNTIME_DIR_NAME)
    return not _covers_path(temp_child, target_real)
def is_skill_root_pollution_name(name: str, *,
                                 agent_skill: bool = False) -> bool:
    if not name:
        return False
    if name in SKILL_ROOT_POLLUTION_DIRS:
        return True
    if not agent_skill:
        return name == ".coverage" or name.endswith(".pyc")
    if (name in _AGENT_SKILL_POLLUTION_DIRS
            or name in SKILL_ROOT_POLLUTION_FILES):
        return True
    if name.startswith(".") and name not in SKILL_PACKAGE_ALLOWED_HIDDEN:
        return True
    return is_package_excluded_file(name)
def is_skill_root_pollution_target(
        skill_dir: str, target_real: str, *,
        allow_absent: bool = False) -> bool:
    root_real = skill_root_real(skill_dir)
    if root_real is None:
        return False
    if _same_path(target_real, root_real) or not _covers_path(root_real, target_real):
        return False
    name = os.path.basename(target_real)
    agent_skill = _is_agent_skill_root(root_real)
    if (agent_skill
            and _direct_child_name(root_real, target_real) is not None
            and (allow_absent or os.path.isfile(target_real))
            and is_unregistered_package_root_file(name)):
        return True
    return is_skill_root_pollution_name(name, agent_skill=agent_skill)
def _skill_root_hygiene_hit(name: str, path: str,
                            root_real: str) -> str | None:
    if name in ("jinhua", "log"):
        return None
    agent_skill = _is_agent_skill_root(root_real)
    if not os.path.isdir(path):
        if is_skill_root_pollution_name(name, agent_skill=agent_skill):
            return name
        return (name if agent_skill and is_unregistered_package_root_file(name)
                else None)
    if name == RUNTIME_DIR_NAME:
        try:
            count = len(os.listdir(path))
        except OSError as _e:
            logger.debug("Temp 条目统计失败（跳过）: %s: %s", path, _e)
            return None
        return (f"{RUNTIME_DIR_NAME}/（{count} 项运行态产物）"
                if count else None)
    if (is_skill_root_pollution_name(name, agent_skill=agent_skill)
            and name != "__pycache__"):
        return f"{name}/"
    return None
def scan_skill_root_hygiene(skill_dir: str) -> list[str]:
    root_real = skill_root_real(skill_dir)
    if root_real is None or not os.path.isdir(root_real):
        return []
    hits: list[str] = []
    try:
        names = sorted(os.listdir(root_real))
    except OSError as _e:
        logger.debug("技能根卫生检查跳过（不可读）: %s: %s", root_real, _e)
        return []
    for name in names:
        hit = _skill_root_hygiene_hit(
            name, os.path.join(root_real, name), root_real)
        if hit is not None:
            hits.append(hit)
    return hits
def _on_pollution_walk_error(error: OSError) -> None:
    logger.warning("[CleanupBridge] 技能包目录枚举失败，已跳过: %s", error)
def _walk_skill_root_pollution(root_real: str):
    root_norm = os.path.normpath(root_real)
    agent_skill = _is_agent_skill_root(root_real)
    for cur, dirs, files in os.walk(root_real,
                                   onerror=_on_pollution_walk_error):
        at_root = os.path.normpath(cur) == root_norm
        for _d in list(dirs):
            if _d in SKILL_ROOT_POLLUTION_WALK_SKIP:
                dirs.remove(_d)
                continue
            if is_skill_root_pollution_name(_d, agent_skill=agent_skill):
                yield os.path.join(cur, _d), _d
                dirs.remove(_d)
        for _f in files:
            if (is_skill_root_pollution_name(_f, agent_skill=agent_skill)
                    or (agent_skill and at_root
                        and is_unregistered_package_root_file(_f))):
                yield os.path.join(cur, _f), _f
def _skill_root_pollution_item(path: str, name: str) -> dict:
    if is_unregistered_package_root_file(name):
        desc = (f"技能包根级未登记文件: {name}（重构暂存块/迁移产物/"
                f"临时 dump，无消费方）")
        sugg = ("确认内容已合并回模块或已过期后回收（回收站可恢复）；"
                "暂存件应落会话工作空间 Temp，不得写回技能包根")
    else:
        desc = (f"技能包内运行态缓存/产物: {name}（验证与运行不得写回被"
                f"治理技能包）")
        sugg = ("删除前确认无引用；建议验证命令带 "
                "PYTHONDONTWRITEBYTECODE=1 与 -p no:cacheprovider，"
                "经 AI 审核后回收（回收站可恢复）")
    return _mk_item(path, "skill_root_pollution", desc,
                    suggestion=sugg, severity="P2")
def _scan_skill_root_pollution(skill_dir: str, items: list[dict]) -> None:
    root_real = skill_root_real(skill_dir)
    if root_real is None:
        return
    for _p, _name in _walk_skill_root_pollution(root_real):
        if not is_skill_root_pollution_target(skill_dir, os.path.realpath(_p)):
            continue
        items.append(_skill_root_pollution_item(_p, _name))
def _is_htm_report_target(target_real: str) -> bool:
    htm_real = _html_root_real()
    if htm_real is None or _same_path(target_real, htm_real):
        return False
    return _covers_path(htm_real, target_real)
def _is_absent_htm_artifact(target_real: str) -> bool:
    htm_real = _html_root_real()
    if htm_real is None:
        return False
    leaf = _direct_child_name(htm_real, target_real)
    if leaf is None:
        return False
    return leaf.lower().endswith(".html") and _is_timestamp_name(leaf)
def is_absent_releasable_target(skill_dir: str, target_real: str,
                                temp_dir_real: str = "") -> bool:
    if not target_real:
        return False
    if not temp_dir_real:
        try:
            temp_dir_real = os.path.realpath(get_temp_dir(skill_dir))
        except (RuntimeError, ValueError, OSError) as _e:
            logger.warning(
                "[CleanupBridge] Temp 归口不可解析，按不可释放处理: %s", _e)
            return False
    target_real = os.path.realpath(expand_git_bash_path(target_real))
    if _same_path(target_real, temp_dir_real) or _covers_path(target_real, temp_dir_real):
        return False
    if _covers_path(temp_dir_real, target_real):
        rel = os.path.relpath(target_real, temp_dir_real)
        parts = [part for part in rel.split(os.sep) if part]
        allowed, _reason = _release_temp_layers(
            parts, target_real, rel, allow_absent=True)
        return allowed
    family, _kind = _out_of_temp_family(
        skill_dir, target_real, temp_dir_real, allow_absent=True)
    if family and family != "htm_artifact":
        return True
    json_verdict = _release_json_artifact(
        skill_dir, target_real, allow_absent=True)
    if json_verdict is not None:
        return json_verdict[0]
    return _is_absent_htm_artifact(target_real)
def _mk_item(file_path: str, category: str, description: str,
             suggestion: str = "",
             severity: str = DEFAULT_SEVERITY) -> dict:
    return {
        "file_path": file_path,
        "line": 0,
        "category": category,
        "operation": _DELETE_TEMP_OPERATION,
        "description": description,
        "suggestion": suggestion or "该临时产物消费完成后无后续引用，经 AI 审核后可删除",
        "confidence": 1.0,
        "severity": severity,
    }
def _is_non_negative_finite(value) -> bool:
    return (isinstance(value, (int, float)) and not isinstance(value, bool)
            and (not isinstance(value, float) or math.isfinite(value))
            and value >= 0)
def _norm_scan_param(value, default, *, label: str, transform):
    if _is_non_negative_finite(value):
        return transform(value)
    logger.warning("[CleanupBridge] %s参数脏值 %r，已归默认 %s",
                   label, value, default)
    return default
def _norm_scan_keep(value, default: int) -> int:
    return _norm_scan_param(
        value, default, label="扫描份数", transform=math.ceil)
def _norm_enqueue_quota(value) -> int:
    if value is None:
        return _DEFAULT_MAX_ENQUEUE_ITEMS
    if isinstance(value, bool):
        logger.warning(
            "[CleanupBridge] 入队配额为布尔值 %r（语义不明），已归默认 %d",
            value, _DEFAULT_MAX_ENQUEUE_ITEMS)
        return _DEFAULT_MAX_ENQUEUE_ITEMS
    if isinstance(value, str):
        try:
            value = int(value.strip())
        except ValueError:
            logger.warning(
                "[CleanupBridge] 入队配额非数字 %r，已归默认 %d",
                value, _DEFAULT_MAX_ENQUEUE_ITEMS)
            return _DEFAULT_MAX_ENQUEUE_ITEMS
    if isinstance(value, float) and not math.isfinite(value):
        logger.warning(
            "[CleanupBridge] 入队配额非有限值 %r，已归默认 %d",
            value, _DEFAULT_MAX_ENQUEUE_ITEMS)
        return _DEFAULT_MAX_ENQUEUE_ITEMS
    if _is_non_negative_finite(value) and value == 0:
        return 0
    normalized = normalize_line_no(value)
    if normalized <= 0:
        logger.warning(
            "[CleanupBridge] 入队配额非正数 %r，已归默认 %d",
            value, _DEFAULT_MAX_ENQUEUE_ITEMS)
        return _DEFAULT_MAX_ENQUEUE_ITEMS
    return normalized
def _newest_first(paths: list[str]) -> list[str] | None:
    try:
        return sorted(
            paths,
            key=lambda path: (os.path.getmtime(path), os.path.normcase(path)),
            reverse=True,
        )
    except OSError as e:
        logger.debug("文件状态探测失败（跳过）: %s", e)
        return None
def _safe_listdir(dirpath: str) -> list[str]:
    try:
        return os.listdir(dirpath)
    except OSError as e:
        logger.debug("目录列举失败（跳过）: %s: %s", dirpath, e)
        return []
def _append_ts_rotation_items(files: list[str], report_keep: int,
                              items: list[dict], label: str, rel_base: str) -> None:
    groups: dict[tuple[str, str], list[str]] = {}
    for fp in files:
        key = _ts_group_key(fp)
        if key is not None:
            groups.setdefault(key, []).append(fp)
    for (prefix, _ext), paths in sorted(groups.items()):
        if len(paths) > report_keep:
            _append_rotation_overflow(
                paths, report_keep, items, label, rel_base, prefix)
def _ts_group_key(fp: str) -> tuple[str, str] | None:
    stem, ext = os.path.splitext(os.path.basename(fp))
    match = TS_SUFFIX_RE.search(stem)
    if match is None:
        return None
    return stem[:match.start()], ext
def _append_rotation_overflow(
        paths: list[str], report_keep: int, items: list[dict],
        label: str, rel_base: str, prefix: str) -> None:
    ordered = _newest_first(paths)
    if ordered is None:
        return
    items.extend(_mk_item(
        path, "stale_report_artifact",
        f"超量{label}（{prefix}* 保留最近{report_keep}份）: "
        f"{rel_base}{os.path.basename(path)}",
        severity="P3",
    ) for path in ordered[report_keep:])
def _list_files_of(dirpath: str) -> list[str]:
    return [os.path.join(dirpath, n) for n in _safe_listdir(dirpath)
            if os.path.isfile(os.path.join(dirpath, n))]
def scan_temp_residue(skill_dir: str,
                      backup_retention_days: float = _DEFAULT_BACKUP_RETENTION_DAYS,
                      snapshot_keep: int = _DEFAULT_SNAPSHOT_KEEP,
                      report_keep: int = REPORT_ARTIFACT_KEEP) -> list[dict]:
    try:
        temp_dir = get_temp_dir(skill_dir)
    except (RuntimeError, ValueError, OSError) as _e:
        logger.warning("[CleanupBridge] Temp 归口不可解析，扫描降级空: %s", _e)
        return []
    backup_retention_days = _norm_scan_param(
        backup_retention_days, _DEFAULT_BACKUP_RETENTION_DAYS,
        label="保留窗口", transform=lambda value: value)
    snapshot_keep = _norm_scan_keep(snapshot_keep, _DEFAULT_SNAPSHOT_KEEP)
    report_keep = _norm_scan_keep(report_keep, REPORT_ARTIFACT_KEEP)
    items: list[dict] = []
    now = time.time()
    _scan_mutation_residue(temp_dir, now, items)
    _scan_root_marker_files(temp_dir, items)
    _scan_expired_backups(temp_dir, backup_retention_days, now, items)
    _scan_coverage_snapshots(temp_dir, snapshot_keep, items)
    _scan_named_root_dirs(temp_dir, now, items)
    _scan_tmp_prefix_dirs(temp_dir, now, items)
    _scan_report_rotation(temp_dir, report_keep, items)
    _scan_root_ts_rotation(temp_dir, report_keep, items)
    _scan_skill_root_temp_residue(skill_dir, temp_dir, items)
    _scan_skill_root_backup_residue(skill_dir, items, temp_dir)
    _scan_skill_root_pollution(skill_dir, items)
    return items
def _scan_mutation_residue(temp_dir: str, now: float,
                           items: list[dict]) -> None:
    mutation_dir = os.path.join(temp_dir, "mutation")
    if not os.path.isdir(mutation_dir):
        return
    for name in sorted(_safe_listdir(mutation_dir)):
        p = os.path.join(mutation_dir, name)
        if not (os.path.isdir(p) and name.startswith("mut_")):
            continue
        age_s = _tmp_dir_activity_age_seconds(p, now)
        if age_s is None or age_s / 86400.0 < _STALE_TMP_DIR_AGE_DAYS:
            continue
        items.append(_mk_item(
            p, "mutation_residue",
            f"变异测试临时副本残留目录: mutation/{name}"
            f"（最后活动 {age_s / 3600.0:.0f} 小时前，该次变异测试已完成）",
            severity="P3",
        ))
def _scan_root_marker_files(temp_dir: str, items: list[dict]) -> None:
    for fname in sorted(CLEANABLE_ROOT_FILES):
        p = os.path.join(temp_dir, fname)
        if os.path.isfile(p):
            items.append(_mk_item(
                p, "root_marker_residue",
                f"已登记的临时标记文件: {fname}（消费完成后无业务价值）",
                severity="P3",
            ))
def _entry_age_seconds(path: str, now: float) -> float | None:
    try:
        return now - os.path.getmtime(path)
    except OSError as e:
        logger.debug("文件状态探测失败（跳过）: %s: %s", path, e)
        return None
def _raise_walk_error(error: OSError) -> None:
    raise error
def _tmp_dir_activity_age_seconds(path: str, now: float) -> float | None:
    try:
        latest = os.path.getmtime(path)
        root_age = now - latest
        if root_age / 86400.0 < _STALE_TMP_DIR_AGE_DAYS:
            return root_age
        for current, dirs, files in os.walk(path, onerror=_raise_walk_error):
            for name in itertools.chain(dirs, files):
                latest = max(
                    latest, os.path.getmtime(os.path.join(current, name)))
    except OSError as e:
        logger.debug("临时目录活动探测失败（不判定为残留）: %s: %s", path, e)
        return None
    return now - latest
def _is_expired_entry(path: str, now: float, retention_days: float) -> bool:
    age_s = _entry_age_seconds(path, now)
    return age_s is not None and age_s / 86400.0 >= retention_days
def _scan_expired_backups(temp_dir: str, backup_retention_days: float,
                          now: float, items: list[dict]) -> None:
    root_listing = _safe_listdir(temp_dir)
    for name in sorted(root_listing):
        p = os.path.join(temp_dir, name)
        if not os.path.isdir(p) or not name.startswith("_backup_"):
            continue
        if _is_expired_entry(p, now, backup_retention_days):
            items.append(_mk_item(
                p, "expired_backup",
                f"超过保留窗口({backup_retention_days}天)的备份目录: {name}",
                suggestion="请先确认相关修改已稳定无需回滚后再清理",
                severity="P2",
            ))
    _scan_f2_recovery_dumps(temp_dir, root_listing, backup_retention_days,
                            now, items)
def _scan_f2_recovery_dumps(temp_dir: str, root_listing: list[str],
                            backup_retention_days: float, now: float,
                            items: list[dict]) -> None:
    for name in sorted(root_listing):
        p = os.path.join(temp_dir, name)
        if not name.startswith("f2_mutbak_") or not os.path.isfile(p):
            continue
        if _is_expired_entry(p, now, backup_retention_days):
            items.append(_mk_item(
                p, "expired_f2_recovery_dump",
                f"超过保留窗口({backup_retention_days}天)的F2应急恢复转储: {name}",
                suggestion="确认对应源文件已人工恢复后可清理",
                severity="P3",
            ))
def _coverage_snapshot_paths(cov_dir: str) -> list[str]:
    return [
        p for p in _list_files_of(cov_dir)
        if os.path.basename(p).startswith("snapshot_")
        and os.path.basename(p).endswith(".json")
    ]
def _scan_coverage_snapshots(temp_dir: str, snapshot_keep: int,
                             items: list[dict]) -> None:
    cov_dir = os.path.join(temp_dir, "coverage")
    if not os.path.isdir(cov_dir):
        return
    snapshots = _coverage_snapshot_paths(cov_dir)
    if len(snapshots) <= snapshot_keep:
        return
    ordered = _newest_first(snapshots)
    if ordered is None:
        return
    items.extend(_mk_item(
        p, "stale_coverage_snapshot",
        f"超量覆盖率快照（保留最近{snapshot_keep}份）: coverage/{os.path.basename(p)}",
        severity="P3",
    ) for p in ordered[snapshot_keep:])
def _scan_named_root_dirs(temp_dir: str, now: float,
                          items: list[dict]) -> None:
    silence_hours = _STALE_TMP_DIR_AGE_DAYS * 24.0
    for name in sorted(CLEANABLE_ROOT_DIR_NAMES):
        dpath = os.path.join(temp_dir, name)
        if not os.path.isdir(dpath):
            continue
        age_s = _tmp_dir_activity_age_seconds(dpath, now)
        if age_s is None or age_s / 3600.0 < silence_hours:
            continue
        items.append(_mk_item(
            dpath, "stale_test_tmp",
            f"超{silence_hours:.0f}h未更新的测试临时目录: {name}"
            f"（最后活动 {age_s / 3600.0:.0f} 小时前）",
            severity="P3",
        ))
def _scan_tmp_prefix_dirs(temp_dir: str, now: float,
                          items: list[dict]) -> None:
    for name in sorted(_safe_listdir(temp_dir)):
        if (not name.startswith(CLEANABLE_ROOT_DIR_PREFIXES)
                or _is_protected_residue_name(name)):
            continue
        p = os.path.join(temp_dir, name)
        if not os.path.isdir(p):
            continue
        age_s = _tmp_dir_activity_age_seconds(p, now)
        if age_s is None or age_s / 86400.0 < _STALE_TMP_DIR_AGE_DAYS:
            continue
        items.append(_mk_item(
            p, "tmp_dir_residue",
            f"Temp 根级临时目录残留: {name}"
            f"（tempfile.mkdtemp 未清理，最后活动 {age_s / 3600.0:.0f} 小时前）",
            severity="P3",
        ))
def _scan_report_rotation(temp_dir: str, report_keep: int,
                          items: list[dict]) -> None:
    for report_name in _LEGACY_REPORT_DIR_NAMES:
        report_dir = os.path.join(temp_dir, report_name)
        if not os.path.isdir(report_dir):
            continue
        for sub in ("", "html", "_intermediate"):
            scan_dir = os.path.join(report_dir, sub) if sub else report_dir
            if not os.path.isdir(scan_dir):
                continue
            rel_base = f"{report_name}/" + (f"{sub}/" if sub else "")
            _append_ts_rotation_items(
                _list_files_of(scan_dir), report_keep, items,
                label="诊断报告时间戳产物", rel_base=rel_base)
def _scan_root_ts_rotation(temp_dir: str, report_keep: int,
                           items: list[dict]) -> None:
    candidates = [
        p for p in _list_files_of(temp_dir)
        if not os.path.basename(p).startswith("f2_mutbak_")
        and classify_prune_target(os.path.basename(p)) is None
    ]
    _append_ts_rotation_items(
        candidates, report_keep, items,
        label="时间戳产物", rel_base="")
def _skill_root_residue_item(path: str, name: str, category: str,
                             contract: str) -> dict:
    return _mk_item(
        path, category,
        f"技能根违规残留: {name}（{contract}，该条目系绕过归口的历史手工残留）",
        suggestion="备份类残留建议先迁移至会话工作空间 Temp/_backups/ 归口；"
                   "确认无需回滚后经 AI 审核删除（回收站可恢复）",
        severity="P2")
def _scan_skill_root_temp_residue(skill_dir, temp_dir: str,
                                  items: list[dict]) -> None:
    root_real = skill_root_real(skill_dir)
    if root_real is None:
        return
    _skill_root_temp = os.path.join(root_real, RUNTIME_DIR_NAME)
    if not os.path.isdir(_skill_root_temp):
        return
    temp_real = os.path.realpath(temp_dir)
    for _name in sorted(_safe_listdir(_skill_root_temp)):
        _p = os.path.join(_skill_root_temp, _name)
        _target_real = os.path.realpath(_p)
        if (_covers_path(_target_real, temp_real)
                or _covers_path(temp_real, _target_real)):
            continue
        if not os.path.exists(_target_real):
            continue
        if not is_skill_root_temp_target(skill_dir, _target_real, temp_real):
            continue
        items.append(_skill_root_residue_item(
            _p, _name, "skill_root_temp_residue",
            "Temp 治理契约：产物落点只能是会话工作空间"))
def _scan_skill_root_backup_residue(skill_dir, items: list[dict],
                                    temp_dir: str = "") -> None:
    root_real = skill_root_real(skill_dir)
    if root_real is None:
        return
    temp_real = os.path.realpath(temp_dir) if temp_dir else ""
    for _name in sorted(_safe_listdir(root_real)):
        _p = _backup_residue_dir(skill_dir, root_real, _name, temp_real)
        if _p is None:
            continue
        items.append(_skill_root_residue_item(
            _p, _name, "skill_root_backup_residue",
            "备份治理契约：备份文件只能是会话工作空间路径"))
def _backup_residue_dir(
        skill_dir: str, skill_root_real: str, name: str,
        temp_dir_real: str) -> str | None:
    if not is_backup_snapshot_dir(name):
        return None
    path = os.path.join(skill_root_real, name)
    if not os.path.isdir(path):
        return None
    target_real = os.path.realpath(path)
    if temp_dir_real and (_covers_path(target_real, temp_dir_real)
                          or _covers_path(temp_dir_real, target_real)):
        return None
    if not is_skill_root_backup_target(skill_dir, target_real):
        return None
    return path
def check_locator_scope_integrity(skill_dir: str) -> dict:
    """定位类账本条目作用域完整性门禁（只读，不进入删除流水线）。

    共享账本里项目内相对定位键无归属会在所有项目上生效，属于跨项目误抑制
    隐患；该门禁只报告待回填条目，不把整份账本当成可删残留。
    """
    try:
        sd = fs_path_text(skill_dir)
    except (TypeError, ValueError):
        sd = ""
    if not sd.strip():
        return {"passed": True, "skipped": True, "unscoped_count": 0,
                "items": [], "reason": "missing_skill_dir"}
    items = scan_unscoped_jinhua_entries(sd)
    return {
        "passed": not items,
        "skipped": False,
        "unscoped_count": len(items),
        "items": items,
    }


def scan_jinhua_residue(skill_dir: str) -> list[dict]:
    jinhua_dir = _jinhua_real(skill_dir, "禁产残留扫描")
    if jinhua_dir is None:
        return []
    items = _scan_jinhua_prohibited_files(jinhua_dir)
    items.extend(_scan_jinhua_unregistered_files(skill_dir, jinhua_dir))
    items.extend(_scan_jinhua_unregistered_dirs(skill_dir, jinhua_dir))
    return items
def _scan_jinhua_prohibited_files(jinhua_dir: str) -> list[dict]:
    items: list[dict] = []
    for name in sorted(JINHUA_PROHIBITED_RESIDUE
                       - _JINHUA_STATE_MIGRATION_NAMES):
        p = os.path.join(jinhua_dir, name)
        if os.path.isfile(p):
            items.append(_mk_item(
                p, "jinhua_zero_consumption_residue",
                f"jinhua/ 零消费禁产登记残留: {name}（SKILL.md 禁止的"
                f"会话手写登记文件，零产生代码零消费代码，跨会话登记"
                f"唯一通道为记忆系统）",
                suggestion="该登记文件无任何代码下游消费，经 AI 审核后可删除",
                severity="P2",
            ))
    return items
def _scan_jinhua_unregistered_files(skill_dir: str,
                                    jinhua_dir: str) -> list[dict]:
    items: list[dict] = []
    unregistered_dirs = {
        os.path.normcase(name) for name in scan_unregistered_jinhua_dirs(skill_dir)
    }
    for relative in scan_unregistered_jinhua_artifacts(skill_dir):
        parts = os.path.normpath(relative).split(os.sep)
        if os.path.normcase(parts[0]) in unregistered_dirs:
            continue
        if len(parts) == 1 and parts[0] in JINHUA_PROHIBITED_RESIDUE:
            continue
        path = os.path.join(jinhua_dir, relative)
        if not os.path.isfile(path):
            continue
        items.append(_mk_item(
            path, "jinhua_unregistered_file_residue",
            f"jinhua/ 未登记长期消费文件: {relative}（没有已登记的"
            "持久化边界和反哺进化消费方）",
            suggestion="先迁往本次任务工作空间保留证据；确认无消费方后"
                       "再经 AI 审核回收，禁止继续写入 jinhua",
            severity="P2",
        ))
    return items
def _scan_jinhua_unregistered_dirs(skill_dir: str,
                                   jinhua_dir: str) -> list[dict]:
    items: list[dict] = []
    for name in scan_unregistered_jinhua_dirs(skill_dir):
        p = os.path.join(jinhua_dir, name)
        if not os.path.isdir(p):
            continue
        items.append(_mk_item(
            p, "jinhua_one_time_dir_residue",
            f"jinhua/ 未登记目录: {name}（非跨会话长期消费资产，"
            f"典型为一次性 merge 快照/临时备份，不应占用长期归口）",
            suggestion="先迁往会话工作空间 Temp/_backups/ 归口；"
                       "确认无需回滚后经 AI 审核回收",
            severity="P2",
        ))
    return items
def _scan_residue_items(skill_dir: str) -> list[dict]:
    return scan_temp_residue(skill_dir) + scan_jinhua_residue(skill_dir)
def _iter_pending_plans(plan: dict):
    return (p for p in (plan.get("plans") or []) if is_pending_plan(p))
def _find_pending_cleanup_plan(plan: dict, plan_id: str) -> dict | None:
    plans = (plan.get("plans") if isinstance(plan, dict) else None) or []
    return find_pending_entry(plans, "plan_id", plan_id)
def _cleanup_safety_block(target: dict) -> dict | None:
    gate = target.get("safety_gate")
    if not isinstance(gate, dict) or gate.get("action") != SafetyAction.BLOCK.value:
        return None
    reason = str_or(gate.get("reason")).strip() or "命中禁止清理规则"
    return {"status": "rejected", "reason": f"安全门禁禁止清理: {reason}",
            "next_action": "reject_or_revise_cleanup_plan"}
def _mark_cleanup_entry_resolved(target: dict, description: str) -> None:
    target["status"] = "resolved"
    target["applied"] = True
    target["applied_at"] = time.strftime(FMT_DATETIME_ISO)
    target["description_used"] = str_or(description)
def _plan_target_path(skill_dir: str, raw_file) -> str | None:
    if not isinstance(raw_file, str) or not raw_file.strip():
        return None
    raw_file = expand_git_bash_path(raw_file.strip())
    return os.path.normpath(os.path.join(normalize_skill_dir(skill_dir),
                                         raw_file))
_PLAN_WRITE_ERRORS = (OSError, RuntimeError, ValueError, TypeError)
def _persist_cleanup_plan(skill_dir: str, plan: dict, fail_label: str) -> dict | None:
    try:
        write_cleanup_plan(skill_dir, plan)
    except _PLAN_WRITE_ERRORS as e:
        logger.warning("[CleanupBridge] %s（plan 未消费，可重试）: %s",
                       fail_label, e, exc_info=True)
        return {"status": "error",
                "reason": f"{fail_label}（plan 未消费，可重试）: {e}"}
    return None
def _cleanup_apply_hint(operation: str, has_fixed_source: bool) -> str:
    if operation == _DELETE_TEMP_OPERATION:
        return ("run_next_ai_review(skill_dir, review_id=CLEAN-xxx, "
                "assessment={'verdict':'approve'})  # 删除类残留方案无需源码，"
                "审核通过即进入回收站删除")
    if has_fixed_source:
        return ("run_next_ai_review(skill_dir, review_id=CLEAN-xxx, "
                "fixed_source=plan['fixed_source'])  # 队列已携带可直接执行的源码")
    return ("run_next_ai_review(skill_dir, review_id=CLEAN-xxx, "
            "fixed_source=<修复后源码全文>)")
def _cleanup_review_view(p: dict) -> dict:
    _fs = str_or(p.get("fixed_source", ""))
    _has_fs = bool(_fs.strip())
    _operation = str_or(p.get("operation", ""))
    _is_delete = _operation == _DELETE_TEMP_OPERATION
    _requires_fs = not _is_delete and not _has_fs
    return {
        "channel": "cleanup",
        "review_id": str_or(p.get("plan_id", "")),
        "target": str_or(p.get("target", "")),
        "rule_id": (str_or(p.get("category", ""))
                    or str_or(p.get("operation", ""))),
        "file_path": str_or(p.get("file", "")),
        "line": normalize_line_no(p.get("line")),
        "severity": str_or(p.get("severity", "")) or DEFAULT_SEVERITY,
        "strategy": _operation or _DEFAULT_CLEANUP_OPERATION,
        "description": (str_or(p.get("description", ""))
                        or str_or(p.get("suggestion", ""))),
        "confidence": normalize_confidence(p.get("confidence")),
        "suggested_value": str_or(p.get("suggestion", "")),
        "source": str_or(p.get("source", "")),
        "requires_fixed_source": _requires_fs,
        "fixed_source": _fs if (_has_fs and not _is_delete) else "",
        "safety_gate": dict_or_empty(p.get("safety_gate", {})),
        "apply_hint": _cleanup_apply_hint(_operation, _has_fs),
        "plan": p,
    }
def list_pending_cleanup_reviews(skill_dir: str) -> list[dict]:
    plan = read_cleanup_plan(skill_dir, for_update=True)
    reviews = [_cleanup_review_view(p) for p in _iter_pending_plans(plan)]
    logger.debug("[CleanupBridge] 待审核清理方案: %d", len(reviews))
    return reviews
def collect_cleanup_reviews(skill_dir: str) -> list[dict]:
    try:
        skill_dir = normalize_skill_dir(skill_dir)
        items = list_pending_cleanup_reviews(skill_dir)
    except Exception as e:
        logger.warning("[AIReview] 清理方案收集失败: %s", e, exc_info=True)
        raise
    return normalize_cleanup_reviews(items, skill_dir)
def _count_pending_cleanup_reviews(skill_dir: str) -> int:
    pending = pending_review_count(
        read_cleanup_plan(skill_dir, for_update=True).get("plans"))
    logger.debug("[CleanupBridge] 待审核清理方案: %d", pending)
    return pending
def reject_cleanup_plan(skill_dir: str, plan_id: str, reason: str = "") -> dict:
    try:
        with _required_plan_lock(cleanup_plan_path(skill_dir)):
            plan = read_cleanup_plan(skill_dir, for_update=True)
            target = _find_pending_cleanup_plan(plan, plan_id)
            if target is None:
                return {"status": "error",
                        "reason": f"未找到待审核清理方案 plan_id={plan_id}"}
            target["status"] = "rejected"
            target["applied"] = False
            target["rejected_at"] = time.strftime(FMT_DATETIME_ISO)
            target["rejection_reason"] = str_or(reason).strip() or "AI 审核否决"
            error = _persist_cleanup_plan(skill_dir, plan, "否决标记落盘失败")
            if error is not None:
                return error
    except _PLAN_WRITE_ERRORS as exc:
        logger.warning("[CleanupBridge] 否决标记落盘失败（plan 未消费，可重试）: %s",
                       exc, exc_info=True)
        return {"status": "error",
                "reason": f"否决标记落盘失败（plan 未消费，可重试）: {exc}",
                "review_retained": True,
                "next_action": "retry_plan_resolution"}
    logger.info("[CleanupBridge] 清理方案已否决: %s（原因: %s）", plan_id,
                target["rejection_reason"])
    return {"status": "rejected", "review_id": plan_id,
            "reason": target["rejection_reason"]}
def apply_cleanup_verdict(sd: str, review: dict, fixed_source: str,
                          approved: bool) -> dict:
    _review = review if isinstance(review, dict) else {}
    _plan = as_dict(_review.get("plan"))
    _plan_id = as_str(_review.get("review_id"))
    if not approved:
        return reject_cleanup_plan(sd, _plan_id, reason="AI 审核否决清理方案")
    if cleanup_operation(_review, _plan) == _DELETE_TEMP_OPERATION:
        return apply_temp_cleanup(sd, _plan_id)
    _source = (provided_source(fixed_source)
               or provided_source(_plan.get("fixed_source")))
    return apply_cleanup_fix(sd, _plan_id, _source,
                             as_str(_review.get("description")))
def apply_security_verdict(sd: str, review: dict, fixed_source: str,
                           approved: bool) -> dict:
    review = review if isinstance(review, dict) else {}
    _plan_id = review.get("review_id")
    try:
        plan = load_pending_security_plan(sd, _plan_id)
    except (OSError, RuntimeError, ValueError, TypeError) as exc:
        logger.warning(
            "[AIReview] 安全计划 %s 读取失败，保留待审可重试: %s",
            _plan_id, exc, exc_info=True)
        return {
            "status": "error",
            "reason": f"安全计划读取失败: {exc}",
            "review_retained": True,
            "next_action": "retry_review",
        }
    if plan is None:
        return {"status": "already_absent", "reason": "计划不存在或已消费"}
    def _finish(status: str, reason: str = "") -> dict:
        try:
            resolved = resolve_security_plan(sd, _plan_id, status)
        except (OSError, RuntimeError, ValueError, TypeError) as exc:
            logger.warning(
                "[AIReview] 安全计划 %s 终态落盘失败，保留待审可重试: %s",
                _plan_id, exc, exc_info=True)
            return {
                "status": "error",
                "reason": f"安全计划终态落盘失败（原操作: {status}）: {exc}",
                "operation_status": status,
                "review_retained": True,
                "next_action": "retry_plan_resolution",
            }
        if not resolved:
            logger.warning(
                "[AIReview] 安全计划 %s 终态未消费，可能已被其他执行者处理",
                _plan_id)
            return {
                "status": "error",
                "reason": "安全计划终态未消费，可能已被其他执行者处理",
                "operation_status": status,
                "next_action": "reload_security_plan",
            }
        return {"status": status, "reason": reason}
    def _retain(status: str, reason: str = "") -> dict:
        logger.warning("[AIReview] 安全计划 %s 执行未完成(%s)，保留待审可重试: %s",
                     _plan_id, status, reason)
        return {"status": status, "reason": reason,
                "review_retained": True,
                "next_action": "resubmit_fixed_source"}
    if not approved:
        return _finish("rejected", "AI 判定为误报或不采纳")
    if not provided_source(fixed_source):
        return needs_fixed_source("安全")
    target, _target_reason = _sec_resolve_target(sd, plan)
    if _target_reason is not None:
        return _finish("rejected", _target_reason)
    _outcome = apply_security_write(sd, target, fixed_source)
    if _outcome.status != "applied":
        _retained = _retain(_outcome.status, _outcome.reason)
        if _outcome.detail is not None:
            _retained["targeted_regression"] = _outcome.detail
        return _retained
    _result = _finish("applied", _outcome.reason)
    if _outcome.detail is not None:
        _result["targeted_regression"] = _outcome.detail
    return _result
def _sec_resolve_target(sd: str, plan: dict) -> tuple[str, str | None]:
    root_real = skill_root_real(sd)
    if root_real is None:
        return "", "技能根目录无效"
    rel = plan.get("file") or plan.get("file_path") or ""
    if not isinstance(rel, str):
        rel = ""
    rel = rel.strip()
    if not rel:
        return "", "目标文件越界（不在技能根目录内）"
    target = os.path.realpath(os.path.join(root_real, rel))
    _within, _why = check_path_traversal(root_real, target)
    if not _within:
        logger.warning("[AIReview] 安全计划目标越界拦截: %s (%s)", target, _why)
        return "", "目标文件越界（不在技能根目录内）"
    if not os.path.isfile(target):
        return "", "目标文件不存在或已被修复"
    return target, None
def _empty_residue_result(
        skill_dir: str, scanned: int, *, dry_run: bool | None = None) -> dict:
    try:
        _pending = _count_pending_cleanup_reviews(skill_dir)
    except (RuntimeError, ValueError, OSError) as _e:
        logger.warning("[CleanupBridge] 待审核方案存储不可解析"
                       "（计数按未知降级）: %s", _e)
        result = {
            "status": "degraded",
            "scanned": scanned,
            "enqueued": 0,
            "total_pending": 0,
            "pending_unresolved": True,
            "next_action": "resolve_plan_store",
            "reason": "待审核方案存储不可解析，计数按未知处理",
        }
    else:
        result = {
            "status": "ok",
            "scanned": scanned,
            "enqueued": 0,
            "total_pending": _pending,
            "next_action": "run_next_ai_review" if _pending else "none",
        }
    if dry_run is not None:
        result["dry_run"] = dry_run
        try:
            result["plan_file"] = cleanup_plan_path(skill_dir)
        except (RuntimeError, ValueError, OSError) as _e:
            logger.debug("[CleanupBridge] 方案落点不可解析: %s", _e)
            result["plan_file"] = ""
    return result
SKILL_ROOT_TEMP_QUARANTINE = "skill_root_temp_quarantine"
_QUARANTINE_TS_FMT = "%Y%m%d_%H%M%S"
def _skill_root_temp_path(skill_dir: str) -> tuple[str | None, str]:
    try:
        root_real = skill_root_real(skill_dir)
        if root_real is None:
            return None, "技能根目录无效"
        skill_temp = os.path.join(root_real, RUNTIME_DIR_NAME)
        if os.path.lexists(skill_temp):
            resolved = os.path.realpath(skill_temp)
            lexical = os.path.abspath(skill_temp)
            if not _same_path(resolved, lexical):
                reason = "技能根 Temp 是链接/联接，拒绝迁移根外条目"
                logger.warning("[SkillRootTemp] %s: %s -> %s",
                               reason, skill_temp, resolved)
                return None, reason
        return skill_temp, ""
    except (OSError, RuntimeError, ValueError, TypeError) as _e:
        logger.warning("[SkillRootTemp] 技能根不可解析（跳过自愈）: %s", _e,
                       exc_info=True)
        return None, f"技能根不可解析: {_e}"
def _skill_temp_overlap_reason(skill_temp_real: str, skill_dir: str) -> str:
    try:
        workspace_temp = os.path.realpath(get_temp_dir(skill_dir))
    except (RuntimeError, ValueError, OSError) as _e:
        logger.warning("[SkillRootTemp] 会话产物根不可解析（保留证据不搬运）: %s",
                       _e, exc_info=True)
        return f"会话产物根不可解析（保留证据不搬运）: {_e}"
    if (_covers_path(skill_temp_real, workspace_temp)
            or _covers_path(workspace_temp, skill_temp_real)):
        return ("技能根 Temp 即会话产物根（测试隔离或技能根自身"
                "工作空间），不搬运")
    return ""
def _quarantine_dir(skill_dir: str) -> str:
    base = os.path.join(get_backup_base(skill_dir), SKILL_ROOT_TEMP_QUARANTINE)
    os.makedirs(base, exist_ok=True)
    stamp = time.strftime(_QUARANTINE_TS_FMT)
    candidate, seq = os.path.join(base, stamp), 1
    while True:
        try:
            os.makedirs(candidate, exist_ok=False)
        except FileExistsError:
            seq += 1
            candidate = os.path.join(base, f"{stamp}_{seq}")
            continue
        return candidate
def _reclaim_empty_dir(path: str) -> bool:
    try:
        if not os.path.isdir(path) or os.listdir(path):
            return False
        if safe_delete(path):
            return True
    except OSError as _e:
        logger.debug("[SkillRootTemp] 空目录回收异常（保留）: %s: %s", path, _e)
    logger.warning("[SkillRootTemp] 空 Temp 目录回收失败（保留空目录）: %s", path)
    return False
def _move_entry_into(src: str, dst_dir: str) -> bool:
    try:
        shutil.move(src, os.path.join(dst_dir, os.path.basename(src)))
        return True
    except (OSError, shutil.Error) as _e:
        logger.warning("[SkillRootTemp] 条目归口迁移失败，保留原状 %s: %s",
                       src, _e)
        return False
def purge_skill_root_temp(skill_dir: str, *, dry_run: bool = False) -> dict:
    summary: dict[str, Any] = {
        "status": "clean", "skill_root_temp": "", "quarantine": "",
        "moved": [], "kept": [], "reclaimed": False, "reason": "",
    }
    skill_temp, reason = _skill_root_temp_path(skill_dir)
    if skill_temp is None:
        summary.update(status="skipped", reason=reason)
        return summary
    summary["skill_root_temp"] = skill_temp
    if not os.path.isdir(skill_temp):
        return summary
    overlap = _skill_temp_overlap_reason(os.path.realpath(skill_temp), skill_dir)
    if overlap:
        summary.update(status="skipped", reason=overlap)
        return summary
    try:
        entries = sorted(os.listdir(skill_temp))
    except OSError as _e:
        logger.warning("[SkillRootTemp] 技能根 Temp 列举失败（原状保留）: %s",
                       _e, exc_info=True)
        summary.update(status="failed", reason=f"技能根 Temp 列举失败: {_e}")
        return summary
    movable = [name for name in entries
               if not _is_protected_residue_name(name)]
    summary["kept"] = [name for name in entries
                       if _is_protected_residue_name(name)]
    if not movable:
        summary["reason"] = "无条目可迁移（受保护白名单原状保留）"
        return summary
    if dry_run:
        summary.update(status="dry_run", moved=movable)
        return summary
    try:
        quarantine = _quarantine_dir(skill_dir)
    except (OSError, RuntimeError, ValueError) as _e:
        logger.warning("[SkillRootTemp] 隔离区不可用（原状保留）: %s", _e,
                       exc_info=True)
        summary.update(status="failed", reason=f"隔离区不可用: {_e}")
        return summary
    summary["quarantine"] = quarantine
    moved = [name for name in movable
             if _move_entry_into(os.path.join(skill_temp, name), quarantine)]
    failed = [name for name in movable if name not in set(moved)]
    summary["moved"] = moved
    summary["kept"] = [*summary["kept"], *failed]
    summary["reclaimed"] = _reclaim_empty_dir(skill_temp)
    if moved and not failed:
        summary["status"] = "migrated"
    elif moved:
        summary.update(status="partial",
                       reason=f"{len(failed)} 项迁移失败，已原状保留")
    else:
        summary.update(status="failed", reason="全部条目迁移失败（原状保留）")
    if moved:
        logger.info("[SkillRootTemp] 技能根 Temp 归口迁移 %d 项 → %s",
                    len(moved), quarantine)
    return summary
def _purge_skill_root_temp_quiet(skill_dir: str) -> dict:
    try:
        return purge_skill_root_temp(skill_dir)
    except Exception as _e:
        logger.warning("[SkillRootTemp] 技能根 Temp 自愈异常（已忽略）: %s",
                       _e, exc_info=True)
        return {"status": "ignored", "reason": str(_e),
                "moved": [], "kept": [], "reclaimed": False}
def cleanup_after_diagnosis(skill_dir: str) -> dict:
    try:
        purged = _purge_skill_root_temp_quiet(skill_dir)
        items = _scan_residue_items(skill_dir)
        if not items:
            return {**_empty_residue_result(skill_dir, 0),
                    "skill_root_temp": purged}
        res = enqueue_cleanup_plan(skill_dir, items, source="cleanup_after_diagnosis")
        logger.info("[CleanupBridge] 诊断后残留清理（Temp + jinhua 禁产登记）: "
                    "识别 %d 项，新增入队 %d 条", len(items),
                    res.get("enqueued", 0))
        return {"status": "ok", "scanned": len(items), **res,
                "skill_root_temp": purged}
    except Exception as e:
        logger.warning("诊断后Temp清理异常（已忽略）: %s", e, exc_info=True)
        return {"status": "ignored", "scanned": 0, "enqueued": 0, "error": str(e)}
def enqueue_temp_cleanup(skill_dir: str, dry_run: bool = True) -> dict:
    items = _scan_residue_items(skill_dir)
    if dry_run or not items:
        return _empty_residue_result(skill_dir, len(items), dry_run=dry_run)
    res = enqueue_cleanup_plan(skill_dir, items, source="temp_cleaner")
    return {"scanned": len(items), "dry_run": dry_run, **res}
def _resolved_cleanup_followup(skill_dir: str) -> dict:
    try:
        remaining = _count_pending_cleanup_reviews(skill_dir)
    except (RuntimeError, ValueError, OSError) as _e:
        logger.warning("[CleanupBridge] 操作已完成，待审核计数读取失败"
                       "（需重载确认）: %s", _e, exc_info=True)
        return {"remaining": None, "pending_unresolved": True,
                "next_action": "reload_cleanup_plan",
                "plan_count_error": str(_e)}
    return {"remaining": remaining,
            "next_action": ("run_next_ai_review"
                            if remaining > 0 else "all_reviews_done")}
def _finalize_and_dequeue(skill_dir: str, plan_id: str, *,
                          status: str, reason: str,
                          resolved_note: str, fail_prefix: str) -> dict:
    try:
        with _required_plan_lock(cleanup_plan_path(skill_dir)):
            plan = read_cleanup_plan(skill_dir, for_update=True)
            target = _find_pending_cleanup_plan(plan, plan_id)
            if target is None:
                return {"status": "error",
                        "reason": ("原清理计划已不存在或已被其他执行者消费: "
                                   f"plan_id={plan_id}"),
                        "next_action": "reload_cleanup_plan"}
            _mark_cleanup_entry_resolved(target, resolved_note)
            error = _persist_cleanup_plan(skill_dir, plan, fail_prefix)
            if error is not None:
                return error
    except _PLAN_WRITE_ERRORS as exc:
        logger.warning("[CleanupBridge] %s: %s", fail_prefix, exc, exc_info=True)
        return {"status": "error", "reason": f"{fail_prefix}: {exc}",
                "review_retained": True,
                "next_action": "retry_plan_resolution"}
    followup = _resolved_cleanup_followup(skill_dir)
    return {"status": status, "reason": reason, **followup}
def _consume_invalid_plan(skill_dir: str, plan_id: str) -> dict:
    result = _finalize_and_dequeue(
        skill_dir, plan_id,
        status="invalid_plan_consumed",
        reason="清理方案缺少有效目标路径（file 字段缺失/为空），已收口出队",
        resolved_note="清理方案缺少有效目标路径（脏数据收口）",
        fail_prefix="脏 plan 已标记收口但落盘失败")
    if result["status"] != "error":
        logger.warning(
            "[CleanupBridge] 清理方案缺少有效目标路径（已收口出队）: "
            "plan_id=%s", plan_id)
    return result
def _resolve_absent_target(skill_dir: str, file_path: str,
                           plan_id: str) -> dict:
    target_real = os.path.realpath(file_path)
    if not is_absent_releasable_target(skill_dir, target_real):
        logger.warning("[CleanupBridge] 清理目标越界拒绝 %s", file_path)
        return {"status": "rejected",
                "reason": "安全校验未通过: 目标不在可清理边界内（Temp 归口/"
                          "jinhua/技能根残留/htm，拒绝路径穿越）"}
    result = _finalize_and_dequeue(
        skill_dir, plan_id,
        status="already_absent",
        reason=f"目标已不存在: {file_path}",
        resolved_note="目标已不存在，标记完成",
        fail_prefix="目标已不存在标记完成，但落盘失败")
    if result["status"] != "error":
        logger.info("[CleanupBridge] Temp 残留目标已不存在（收口出队）: "
                    "%s，剩余待审核 %s", file_path,
                    "未知" if result["remaining"] is None
                    else result["remaining"])
    return result
def _delete_target(file_path: str) -> dict | None:
    try:
        if not safe_delete(file_path):
            raise OSError("回收站删除被拒绝（非 Windows 平台或 Shell API 失败）")
    except OSError as e:
        logger.warning("[CleanupBridge] 删除失败 %s: %s", file_path, e)
        return {"status": "failed", "reason": f"删除失败: {e}"}
    return None
def _guarded_delete(skill_dir: str, file_path: str) -> dict | None:
    ok, reason = is_cleanable_path(skill_dir, file_path)
    if not ok:
        logger.warning("[CleanupBridge] 清理目标安全校验拒绝 %s: %s",
                       file_path, reason)
        return {"status": "rejected", "reason": f"安全校验未通过: {reason}"}
    return _delete_target(file_path)
def _target_path_for_delete(skill_dir: str, target: dict,
                           plan_id: str) -> str | dict:
    blocked = _cleanup_safety_block(target)
    if blocked is not None:
        return blocked
    file_path = _plan_target_path(skill_dir, target.get("file"))
    if file_path is None:
        return _consume_invalid_plan(skill_dir, plan_id)
    if not os.path.lexists(file_path):
        return _resolve_absent_target(skill_dir, file_path, plan_id)
    return file_path
def apply_temp_cleanup(skill_dir: str, plan_id: str) -> dict:
    if not plan_id:
        return {"status": "error", "reason": "缺少 plan_id"}
    # 校验、删除与消费必须是同一队列临界区；否则两个审核执行者会
    # 同时基于 pending_review 快照删除，后者直到删除后才发觉计划已消费。
    with _required_plan_lock(cleanup_plan_path(skill_dir)):
        plan = read_cleanup_plan(skill_dir)
        target = _find_pending_cleanup_plan(plan, plan_id)
        if target is None:
            return {"status": "error",
                    "reason": f"未找到待审核清理方案 plan_id={plan_id}"}
        file_path = _target_path_for_delete(skill_dir, target, plan_id)
        if isinstance(file_path, dict):
            return file_path
        failed = _guarded_delete(skill_dir, file_path)
        if failed is not None:
            return failed
        result = _finalize_and_dequeue(
            skill_dir, plan_id,
            status="approved_removed",
            reason=f"已删除残留: {file_path}",
            resolved_note="AI 审核后清理残留",
            fail_prefix="残留已删除但方案消费落盘失败")
    if result["status"] != "error":
        logger.info("[CleanupBridge] 残留已清理: %s（%s），剩余待审核 %s",
                    plan_id, file_path,
                    "未知" if result["remaining"] is None
                    else result["remaining"])
    return result
def _locate_cleanup_target(skill_dir: str,
                            plan_id: str) -> tuple[dict, dict, str, dict | None]:
    plan = read_cleanup_plan(skill_dir)
    target = _find_pending_cleanup_plan(plan, plan_id)
    if target is None:
        return {}, {}, "", {"status": "error",
                            "reason": f"未找到待审核清理方案 plan_id={plan_id}"}
    blocked = _cleanup_safety_block(target)
    if blocked is not None:
        return {}, {}, "", blocked
    file_path = _plan_target_path(skill_dir, target.get("file"))
    if file_path is None:
        return {}, {}, "", _consume_invalid_plan(skill_dir, plan_id)
    root_real = skill_root_real(skill_dir)
    file_real = os.path.realpath(file_path)
    if not root_real or not _covers_path(root_real, file_real):
        logger.warning(
            "[CleanupBridge] 清理写盘目标越界拒绝: plan_id=%s target=%s root=%s",
            plan_id, file_real, root_real)
        return {}, {}, "", {"status": "rejected",
                            "reason": "安全校验未通过: 清理写盘目标不在技能根内"
                                      "（拒绝路径穿越）"}
    if not os.path.lexists(file_path):
        return {}, {}, "", _finalize_and_dequeue(
            skill_dir, plan_id,
            status="already_absent",
            reason=f"目标已不存在: {file_real}",
            resolved_note="目标已不存在，标记完成",
            fail_prefix="目标已不存在标记完成，但落盘失败")
    if not os.path.isfile(file_real):
        logger.warning(
            "[CleanupBridge] 清理写盘目标非普通文件拒绝: plan_id=%s target=%s",
            plan_id, file_real)
        return {}, {}, "", {"status": "rejected",
                            "reason": "安全校验未通过: 清理写盘目标不是普通文件"}
    return plan, target, file_real, None
def _consume_cleanup_plan(skill_dir: str, plan: dict, target: dict,
                          description: str) -> dict | None:
    _mark_cleanup_entry_resolved(
        target, str_or(description).strip() or "AI 审核后手动清理")
    return _persist_cleanup_plan(skill_dir, plan, "方案消费落盘失败")
def _finalize_cleanup_success(skill_dir: str, plan: dict, target: dict,
                              description: str, file_path: str,
                              regression_result: dict) -> dict:
    cascade = _cascade_after_cleanup(skill_dir, file_path)
    try:
        with _required_plan_lock(cleanup_plan_path(skill_dir)):
            plan = read_cleanup_plan(skill_dir, for_update=True)
            target = _find_pending_cleanup_plan(
                plan, str_or(target.get("plan_id")))
            if target is None:
                error = {
                    "status": "error",
                    "reason": "原清理计划已不存在或已被其他执行者消费",
                    "next_action": "reload_cleanup_plan",
                }
            else:
                error = _consume_cleanup_plan(
                    skill_dir, plan, target, description)
    except _PLAN_WRITE_ERRORS as exc:
        logger.warning(
            "[CleanupBridge] 源码已写成功，但清理队列重读失败: %s",
            exc, exc_info=True)
        error = {
            "status": "error",
            "reason": f"清理队列重读失败，原操作待确认: {exc}",
            "review_retained": True,
            "next_action": "retry_plan_resolution",
        }
    if error is not None:
        error["cascade"] = cascade
        error["targeted_regression"] = regression_result
        return error
    followup = _resolved_cleanup_followup(skill_dir)
    logger.info("[CleanupBridge] 清理方案已应用: %s (%s)，剩余待审核 %s",
                target.get("plan_id", ""), file_path,
                "未知" if followup["remaining"] is None
                else followup["remaining"])
    return {
        "status": "approved_fixed",
        "reason": f"清理方案已应用: {file_path}",
        "cascade": cascade,
        "targeted_regression": regression_result,
        **followup,
    }
def apply_cleanup_fix(skill_dir: str, plan_id: str, fixed_source: str,
                      description: str = "") -> dict:
    skill_dir = normalize_skill_dir(skill_dir)
    if not isinstance(fixed_source, str) or not fixed_source.strip():
        return {"status": "needs_fixed_source",
                "reason": "清理修复需要 AI 提供 fixed_source（修复后源码全文）"}
    # 与删除通道共用同一队列临界区，防止同一计划在消费前被重复写盘。
    # locked_artifact 可重入，最终消费及级联入队仍沿用原有内层锁。
    with _required_plan_lock(cleanup_plan_path(skill_dir)):
        plan, target, file_path, error = _locate_cleanup_target(skill_dir, plan_id)
        if error is not None:
            return error
        regression_result, error = apply_verified_write(
            skill_dir, file_path, fixed_source)
        if error is not None:
            return error
        return _finalize_cleanup_success(
            skill_dir, plan, target, description, file_path, regression_result)
def _cascade_result(status: str, *, reason: str | None = None,
                    total_broken: int = 0, candidates: int = 0,
                    enqueued: int = 0, plan_file: str = "",
                    next_action: str = "") -> dict:
    out = {"status": status, "total_broken": total_broken,
           "cascade_candidates": candidates, "cascade_enqueued": enqueued,
           "plan_file": plan_file, "next_action": next_action}
    if reason is not None:
        out["reason"] = reason
    return out
def _read_broken_imports(skill_dir: str) -> tuple[list, dict, dict | None]:
    try:
        result = scan_broken_imports(skill_dir)
    except Exception as e:
        logger.warning("[CleanupBridge] 级联悬空引用扫描失败: %s", e, exc_info=True)
        return [], {}, _cascade_result("error", reason=str(e))
    if not isinstance(result, dict):
        logger.warning("[CleanupBridge] 悬空扫描返回非 dict 类型: %r", type(result))
        return [], {}, _cascade_result(
            "error", reason=f"悬空扫描返回非 dict: {type(result).__name__}")
    broken = result.get("broken_imports") or []
    if not isinstance(broken, list):
        reason = (f"broken_imports 非列表形态({type(broken).__name__})，"
                  "无法确认级联断链")
        logger.warning("[CleanupBridge] %s", reason)
        return [], {}, _cascade_result("error", reason=reason)
    if result.get("status") == "partial":
        skipped = result.get("skipped_files") or []
        skipped_names = ", ".join(
            str(item.get("file", "")) for item in skipped[:3]
            if isinstance(item, dict))
        reason = (f"悬空扫描不完整：{len(skipped)} 个源文件未能解析"
                  f"（{skipped_names or '未知文件'}），无法确认级联断链已归零")
        logger.warning("[CleanupBridge] %s", reason)
        return [], result, _cascade_result(
            "error", reason=reason,
            total_broken=result.get("total_broken", len(broken)))
    return broken, result, None
def _enqueue_dangling(skill_dir: str, items: list, source: str,
                      total_broken: int, candidate_count: int) -> dict:
    try:
        enq = enqueue_cleanup_plan(skill_dir, items, source=source)
        if not isinstance(enq, dict):
            logger.warning("[CleanupBridge] 入队返回非 dict 类型: %r", type(enq))
            return _cascade_result(
                "error",
                reason=("级联检测完成但入队返回非 dict（候选未入队，可重试）: "
                        f"{type(enq).__name__}"),
                total_broken=total_broken,
                candidates=candidate_count)
    except Exception as e:
        logger.warning("[CleanupBridge] 级联悬空引用入队失败（可重试）: %s", e, exc_info=True)
        return _cascade_result(
            "error",
            reason=f"级联检测完成但入队失败（候选未入队，可重试）: {e}",
            total_broken=total_broken,
            candidates=candidate_count)
    enqueued = enq.get("enqueued", 0)
    if as_str(enq.get("status")) in {"failed", "error", "degraded"}:
        reason = as_str(enq.get("error") or enq.get("reason") or "")
        return _cascade_result(
            "error",
            reason=("级联检测完成但入队失败（候选未入队，可重试）"
                    + (f": {reason}" if reason else "")),
            total_broken=total_broken,
            candidates=candidate_count)
    logger.info("[CleanupBridge] 级联悬空检测: 检出 %d 项, 已入队 %d 项待 AI 审核",
                candidate_count, enqueued)
    return _cascade_result(
        "ok", total_broken=total_broken, candidates=candidate_count,
        enqueued=enqueued,
        plan_file=enq.get("plan_file", ""),
        next_action=enq.get("next_action", ""))
def _cascade_after_cleanup(skill_dir: str, file_path: str) -> dict:
    try:
        return scan_post_cleanup_dangling(skill_dir, [file_path])
    except Exception as e:  # noqa: BLE001
        logger.warning("[CleanupBridge] 级联悬空引用检测失败(不阻断): %s", e)
        return _cascade_result("error", reason=str(e))
_DANGLING_SEVERITY_CONFIDENCE = {"HIGH": 0.9, "MEDIUM": 0.7, "LOW": 0.5}
def _changed_module_identity(
        root_real: str, root_package: str,
        changed: Any) -> tuple[set[str], set[str]]:
    if not isinstance(changed, str) or not changed:
        return set(), set()
    candidate = (changed if os.path.isabs(changed)
                 else os.path.join(root_real, changed))
    path_real = os.path.realpath(candidate)
    basename = os.path.basename(path_real)
    stem = py_stem(basename)
    if stem == basename or not _covers_path(root_real, path_real):
        return set(), set()
    parts = os.path.relpath(path_real, root_real).split(os.sep)
    if basename.lower() == "__init__.py":
        parts = parts[:-1]
    else:
        parts[-1] = stem
    part_variants = [parts]
    if parts and parts[0] == "src":
        part_variants.append(parts[1:])
    qualified_names: set[str] = set()
    bare_names: set[str] = set()
    for variant in part_variants:
        if variant:
            qualified_names.add(".".join(variant))
        if root_package:
            qualified_names.add(".".join([root_package, *variant]))
        if len(variant) == 1:
            bare_names.add(variant[0])
    return qualified_names, bare_names
def _normalize_changed_files(changed_files) -> list | None:
    if changed_files is None:
        return None
    if isinstance(changed_files, (str, os.PathLike)):
        path = fs_path_text(changed_files)
        return [path] if path else []
    if isinstance(changed_files, (list, tuple, set, frozenset)):
        normalized: list[str] = []
        for item in changed_files:
            path = (fs_path_text(item)
                    if isinstance(item, (str, os.PathLike)) else "")
            if path:
                normalized.append(path)
            else:
                logger.warning(
                    "[CleanupBridge] changed_files 含非路径元素(%s)，已跳过: %r",
                    type(item).__name__, item)
        return normalized
    logger.warning(
        "[CleanupBridge] changed_files 非路径集合形态(%s)，按无匹配收口: %r",
        type(changed_files).__name__, changed_files)
    return []
def _changed_module_identities(
        skill_dir: str, changed_files) -> tuple[set[str], set[str]]:
    root_real = skill_root_real(skill_dir)
    if not root_real:
        return set(), set()
    root_package = import_key(os.path.basename(root_real))
    qualified_names: set[str] = set()
    bare_names: set[str] = set()
    for changed in _normalize_changed_files(changed_files) or []:
        names, bare = _changed_module_identity(
            root_real, root_package, changed)
        qualified_names.update(names)
        bare_names.update(bare)
    return qualified_names, bare_names
_RELATIVE_IMPORT_STMT_RE = re.compile(
    r"^\s*from\s+(\.+)(\w+(?:\.\w+)*)?\s+import\s+(.+?)\s*$")
_ABSOLUTE_IMPORT_STMT_RE = re.compile(
    r"^\s*from\s+(\w+(?:\.\w+)*)\s+import\s+(.+?)\s*$")
def _imported_symbol_names(aliases: str) -> list[str]:
    names = []
    for alias in aliases.split(","):
        fields = alias.strip().split()
        alias_name = fields[0] if fields else ""
        if re.fullmatch(r"\w+", alias_name):
            names.append(alias_name)
    return names
def _relative_cascade_targets(root_real: str, item: dict) -> set[str]:
    stmt = str_or(item.get("import_stmt", ""))
    match = _RELATIVE_IMPORT_STMT_RE.match(stmt)
    if match is None:
        return set()
    level = len(match.group(1))
    module = match.group(2) or ""
    importer = str_or(item.get("file", ""))
    if not importer:
        return set()
    importer_path = (importer if os.path.isabs(importer)
                     else os.path.join(root_real, importer))
    rel = os.path.relpath(os.path.realpath(importer_path), root_real)
    parts = [part for part in rel.replace("\\", "/").split("/")[:-1]
             if part]
    keep = len(parts) - (level - 1)
    if keep < 0:
        return set()
    base = parts[:keep]
    if base and base[0] == "src":
        base = base[1:]
    module_parts = tuple(module.split(".")) if module else ()
    imported_from = (*base, *module_parts)
    targets = {".".join(imported_from)} if imported_from else set()
    if not imported_from:
        root_package = import_key(os.path.basename(root_real))
        if root_package:
            targets.add(root_package)
    for alias_name in _imported_symbol_names(match.group(3)):
        targets.add(".".join((*imported_from, alias_name)))
    return targets
def _absolute_cascade_targets(item: dict) -> set[str]:
    stmt = str_or(item.get("import_stmt", ""))
    match = _ABSOLUTE_IMPORT_STMT_RE.match(stmt)
    if match is None:
        return set()
    imported_from = match.group(1)
    return {f"{imported_from}.{alias_name}"
            for alias_name in _imported_symbol_names(match.group(2))}
def _filter_cascade_broken(broken: list, changed_files,
                           skill_dir: str = "") -> list:
    qualified_names, bare_names = _changed_module_identities(
        skill_dir, changed_files)
    root_real = skill_root_real(skill_dir)
    matched = []
    for item in broken:
        if not isinstance(item, dict):
            continue
        target = str_or(item.get("target_module", "")).lstrip(".")
        if item.get("is_relative"):
            if (root_real and target
                    and _relative_cascade_targets(root_real, item)
                    & qualified_names):
                matched.append(item)
            continue
        if (target in qualified_names or target in bare_names
                or _absolute_cascade_targets(item) & qualified_names):
            matched.append(item)
    return matched
def _build_dangling_items(broken: list) -> list[dict]:
    items = []
    for b in broken:
        if not isinstance(b, dict):
            continue
        import_stmt = str_or(b.get("import_stmt", ""))
        target_module = str_or(b.get("target_module", ""))
        has_severity = "severity" in b
        severity = str_or(b.get("severity", "MEDIUM"))
        severity_key = severity.strip().upper()
        items.append({
            "file_path": str_or(b.get("file", "")),
            "line": normalize_line_no(b.get("line", 0)),
            "category": "dangling_import",
            "operation": "remove_dangling_import",
            "description": (
                f"清理级联悬空引用: {import_stmt} "
                f"(目标 {target_module} 不存在)"
            ),
            "suggestion": (str_or(b.get("suggestion", ""))
                           or "移除该 import 或改为仍存在的符号"),
            "severity": (to_queue_priority(severity) if has_severity
                         else DEFAULT_SEVERITY),
            "confidence": _DANGLING_SEVERITY_CONFIDENCE.get(
                severity_key, 0.6),
        })
    return items
def scan_post_cleanup_dangling(skill_dir: str,
                               changed_files: list[str] | None = None,
                               source: str = "post_cleanup_cascade") -> dict:
    skill_dir = normalize_skill_dir(skill_dir)
    if (changed_files is not None
            and not isinstance(changed_files,
                               (str, os.PathLike, list, tuple, set,
                                frozenset))):
        reason = ("changed_files 非路径集合形态"
                  f"({type(changed_files).__name__})，无法确认级联范围")
        logger.warning("[CleanupBridge] %s: %r", reason, changed_files)
        return _cascade_result("error", reason=reason)
    raw_changed = changed_files
    changed_files = _normalize_changed_files(changed_files)
    if raw_changed and changed_files == []:
        reason = ("changed_files 无可解析路径（全部为非路径元素），"
                  "无法确认级联范围")
        logger.warning("[CleanupBridge] %s: %r", reason, raw_changed)
        return _cascade_result("error", reason=reason)
    broken, result, error = _read_broken_imports(skill_dir)
    if error is not None:
        return error
    if changed_files is not None:
        broken = _filter_cascade_broken(broken, changed_files, skill_dir)
    if not broken:
        logger.info("[CleanupBridge] 级联悬空检测: 无新增悬空引用, 全库断链=%s",
                    result.get("total_broken", 0))
        return _cascade_result(
            "ok", total_broken=result.get("total_broken", 0),
            candidates=0, enqueued=0, plan_file="", next_action="")
    items = _build_dangling_items(broken)
    return _enqueue_dangling(skill_dir, items, source,
                             result.get("total_broken", 0), len(items))
MAX_CLEANUP_PLANS = 100
_DEFAULT_MAX_ENQUEUE_ITEMS = 200
_CLEANUP_PLAN_FILENAME = "_cleanup_ai_plan.json"
def cleanup_plan_path(skill_dir: str) -> str:
    return json_artifact_path(skill_dir, _CLEANUP_PLAN_FILENAME)
def _empty_cleanup_plan() -> dict:
    return {"_meta": {"total": 0, "generated": ""}, "plans": []}
def read_cleanup_plan(skill_dir: str, *, for_update: bool = False) -> dict:
    plan_path = cleanup_plan_path(skill_dir)
    if for_update:
        data, kind, error = read_json_artifact(plan_path, propagate_io=True)
        if kind == "missing":
            data = _empty_cleanup_plan()
        elif kind != "ok":
            raise ValueError(f"清理队列读取失败: {error}")
        if not isinstance(data, dict):
            raise ValueError("清理队列顶层必须是键值映射")
        if "plans" in data and not isinstance(data["plans"], list):
            raise ValueError("清理队列 plans 必须是列表")
    else:
        data = read_queue_json(plan_path, _empty_cleanup_plan())
    if not isinstance(data.get("plans"), list):
        data["plans"] = []
    if not isinstance(data.get("_meta"), dict):
        data["_meta"] = {}
    return data
def write_cleanup_plan(skill_dir: str, data: dict) -> None:
    if not isinstance(data, dict):
        logger.warning("[CleanupBridge] 清理方案写盘入参非 dict（%s），"
                       "已拒绝写盘", type(data).__name__)
        return
    plans = prune_consumed_items(
        as_list(data.get("plans")), MAX_CLEANUP_PLANS,
        preserve_order=True)
    data["plans"] = plans
    meta = data.get("_meta")
    if not isinstance(meta, dict):
        meta = {}
        data["_meta"] = meta
    meta["total"] = len(plans)
    meta["pending"] = pending_review_count(plans)
    write_queue_json(cleanup_plan_path(skill_dir), data)
_PLAN_SEQ = itertools.count(1)
def _first_truthy(*candidates: Any, default: Any = None) -> Any:
    for candidate in candidates:
        if candidate:
            return candidate
    return default
def _extract_item(item: Any) -> dict:
    if isinstance(item, dict):
        extracted = dict(item)
        extracted.update(_extract_spec_fields(extracted.get))
        return extracted
    return _extract_spec_fields(
        lambda key, default=None: getattr(item, key, default))
_ITEM_FIELD_SPECS: tuple = (
    ("file_path", ("file_path", "file"), normalize_file_ref, "", True),
    ("line", ("line", "lineno"), normalize_line_no, 0, True),
    ("category", ("category",), str_or, "", True),
    ("operation", ("operation", "action", "kind"),
     lambda value: str_or(value) or _DEFAULT_CLEANUP_OPERATION, "", True),
    ("description", ("description", "message"), str_or, "", True),
    ("suggestion", ("suggestion", "reason"), str_or, "", True),
    ("confidence", ("confidence",), normalize_confidence, None, False),
    ("severity", ("severity",),
     lambda value: str_or(value) or DEFAULT_SEVERITY, "", True),
    ("line_count", ("line_count", "lines"), None, 0, True),
    ("end_line", ("end_line", "end_lineno"), None, 0, True),
    ("symbol", ("symbol", "func_name"), str_or, "", True),
    ("fixed_source", ("fixed_source",), str_or, "", True),
)
def _extract_spec_fields(get_value) -> dict:
    out = {}
    for key, aliases, norm, default, coalesce in _ITEM_FIELD_SPECS:
        if coalesce:
            raw = _first_truthy(
                *(get_value(alias, None) for alias in aliases), default=default)
        else:
            raw = get_value(key, None)
        out[key] = norm(raw) if norm is not None else raw
    return out
def _is_positive_number(value: Any) -> bool:
    return _is_non_negative_finite(value) and value > 0
def _estimate_lines_to_remove(d: dict) -> int:
    for _key in ("line_count", "lines", "lines_span", "size_lines"):
        _v = d.get(_key)
        if _is_positive_number(_v):
            return math.ceil(_v)
    _end = d.get("end_line")
    _start = d.get("line", 0)
    if _is_positive_number(_end) and _is_positive_number(_start) and _end >= _start:
        return math.ceil(_end - _start + 1)
    return 0
def _cleanup_idem_key(d: dict) -> tuple:
    return (
        d["file_path"],
        d["line"],
        d["description"] or d["operation"] or d["category"],
    )
def _dedupe_cleanup_pairs(extracted, existing_keys: set,
                          max_items: int) -> list:
    new_pairs = []
    for item in extracted:
        if len(new_pairs) >= max_items:
            break
        key = _cleanup_idem_key(item)
        if key in existing_keys:
            continue
        existing_keys.add(key)
        new_pairs.append((key, item))
    return new_pairs
def _has_item_identity(item: dict) -> bool:
    return bool(item["file_path"] or item["line"] or item["description"]
                or item["category"] or item["symbol"])
def _extract_new_cleanup_pairs(items, existing_keys: set,
                               max_items: int) -> list:
    items = as_item_list(items, log_tag="[CleanupBridge]")
    raw_items = drop_scalar_items(items, log_tag="[CleanupBridge]")
    extracted: list[dict] = []
    for raw in raw_items:
        try:
            item = _extract_item(raw)
        except Exception as _e:  # noqa: BLE001 — 单条脏载荷不得击穿整批入队
            logger.warning("[CleanupBridge] 清理条目字段读取失败（已跳过）: "
                           "%s: %r", _e, raw)
            continue
        if not _has_item_identity(item):
            logger.warning("[CleanupBridge] 跳过无可定位身份的清理条目: %r",
                           raw)
            continue
        extracted.append(item)
    return _dedupe_cleanup_pairs(
        extracted, existing_keys, _norm_enqueue_quota(max_items))
def _cleanup_plan_id() -> str:
    stamp = time.strftime('%Y%m%d%H%M%S')
    return f"CLEAN-{stamp}-{os.getpid()}-{next(_PLAN_SEQ):04d}"
_DELETE_LIKE_OPS: tuple[str, ...] = ("delete", "remove")
def _is_delete_like_item(item: dict) -> bool:
    op = str(item.get("operation", "") or "").strip().lower()
    return op.startswith(_DELETE_LIKE_OPS)
def _gate_check(gate: SafetyGate, item: dict, file_path: str,
                batch_files: list, root_dir: str) -> SafetyCheck:
    lines = _estimate_lines_to_remove(item)
    whole_entry_delete = (_is_delete_like_item(item)
                          and _estimate_lines_to_remove(item) == 0)
    affected = ([file_path] if whole_entry_delete and file_path
                else batch_files)
    verdict = gate.check(file_path, lines, affected,
                         item.get("symbol", ""), root_dir=root_dir)
    if (lines != 0
            or not _is_delete_like_item(item)
            or verdict.action in (SafetyAction.BLOCK,
                                  SafetyAction.REQUIRE_CONFIRM)):
        return verdict
    logger.warning(
        "[SafetyGate] 删除类操作未携带删除范围，按未知影响升级为待确认: %s %s",
        item.get("operation", ""), file_path or item.get("category", ""))
    return SafetyCheck(
        action=SafetyAction.REQUIRE_CONFIRM,
        reason="删除类操作未提供删除行数范围（缺 line_count/end_line），"
               "无法评估影响面，须人工确认",
        risk_level="medium",
        blast_radius=0,
        affected_files=[file_path] if file_path else [],
    )
def _cleanup_plan_entry(
    item: dict, gate: SafetyGate, batch_files: list, source: str,
    skill_dir: str,
) -> dict:
    file_path = item["file_path"]
    line = item["line"]
    description = item["description"]
    return {
        "plan_id": _cleanup_plan_id(),
        "target": (os.path.basename(file_path) if file_path
                   else item["category"]),
        "file": file_path,
        "line": line,
        "operation": item["operation"],
        "category": item["category"],
        "description": description,
        "suggestion": item["suggestion"],
        "confidence": item["confidence"],
        "severity": item["severity"],
        "safety_gate": _gate_check(
            gate, item, file_path, batch_files, root_dir=skill_dir).to_dict(),
        "fixed_source": item.get("fixed_source", ""),
        "source": source,
        "status": "pending_review",
        "created": time.strftime(FMT_DATETIME_ISO),
    }
def _build_cleanup_plan_entries(new_pairs: list, source: str,
                                skill_dir: str = "") -> list:
    gate = SafetyGate()
    batch_files = sorted({item.get("file_path", "") for _, item in new_pairs} - {""})
    return [
        _cleanup_plan_entry(item, gate, batch_files, source, skill_dir)
        for _key, item in new_pairs
    ]
def _write_cleanup_entries(
    plan: dict,
    existing: list,
    new_plans: list,
    existing_pending: list,
    source: str,
    skill_dir: str,
) -> None:
    plan["plans"] = existing + new_plans
    plan["_meta"] = {"generated": time.strftime(FMT_DATETIME_ISO)}
    write_cleanup_plan(skill_dir, plan)
    logger.info(
        "[CleanupBridge] 入队 %d 条清理方案（来源=%s），待审核总数=%d",
        len(new_plans),
        source or "unknown",
        len(existing_pending) + len(new_plans),
    )
def _cleanup_enqueue_summary(
    existing_pending: list, new_plans: list, skill_dir: str
) -> dict:
    total_pending = len(existing_pending) + len(new_plans)
    actions = Counter(
        p.get("safety_gate", {}).get("action") for p in new_plans
    )
    return {
        "enqueued": len(new_plans),
        "total_pending": total_pending,
        "next_action": "run_next_ai_review" if total_pending else "none",
        "plan_file": cleanup_plan_path(skill_dir),
        "blocked_items": actions.get("block", 0),
        "require_confirm_items": actions.get("require_confirm", 0),
    }
_SEVERITY_TO_PRIORITY = {
    "critical": "P0",
    "high": "P1",
    "medium": "P2",
    "warning": "P2",
    "low": "P3",
    "info": "P3",
}
_PRIORITY_VALUES = frozenset(("P0", "P1", "P2", "P3"))
def to_queue_priority(severity: Any) -> str:
    normalized = severity.strip() if isinstance(severity, str) else ""
    lowered = normalized.lower()
    if lowered in _SEVERITY_TO_PRIORITY:
        return _SEVERITY_TO_PRIORITY[lowered]
    priority = normalized.upper()
    return priority if priority in _PRIORITY_VALUES else "P3"
_AI_REVIEW_ENQUEUE_FALLBACK = {
    "status": "failed",
    "enqueued": 0,
    "total_pending": 0,
    "next_action": "retry_enqueue",
}
def default_ai_review(error: str) -> dict[str, Any]:
    result = dict(_AI_REVIEW_ENQUEUE_FALLBACK)
    result["error"] = error
    return result
def enqueue_cleanup_plan(
    skill_dir: str, items: list, source: str = "",
    max_items: int = _DEFAULT_MAX_ENQUEUE_ITEMS,
) -> dict:
    try:
        with _required_plan_lock(cleanup_plan_path(skill_dir)):
            plan = read_cleanup_plan(skill_dir, for_update=True)
            existing = plan.get("plans") or []
            existing_pending = [p for p in existing if is_pending_plan(p)]
            existing_keys = {
                _cleanup_idem_key(_extract_item(p)) for p in existing_pending
            }
            new_pairs = _extract_new_cleanup_pairs(
                items, existing_keys, max_items)
            new_plans = _build_cleanup_plan_entries(
                new_pairs, source, skill_dir)
            if new_plans:
                _write_cleanup_entries(
                    plan, existing, new_plans, existing_pending, source, skill_dir)
            return _cleanup_enqueue_summary(
                existing_pending, new_plans, skill_dir)
    except _PLAN_WRITE_ERRORS as e:
        logger.warning("[CleanupBridge] 清理队列读改写失败，入队未确认: %s",
                       e, exc_info=True)
        result = default_ai_review(f"清理队列读改写失败，入队未确认: {e}")
        result["review_retained"] = True
        return result
_PROTECTED_CORE_NORMCASE: frozenset[str] = frozenset(
    os.path.normcase(name) for name in PROTECTED_CORE_FILES)
class SafetyAction(str, Enum):
    ALLOW = "allow"
    WARN = "warn"
    BLOCK = "block"
    REQUIRE_CONFIRM = "require_confirm"
@dataclass
class SafetyCheck:
    action: SafetyAction = SafetyAction.ALLOW
    reason: str = ""
    risk_level: str = "low"
    blast_radius: int = 0
    affected_files: list[str] = field(default_factory=list)
    def to_dict(self) -> dict[str, Any]:
        return {
            "action": self.action.value,
            "reason": self.reason,
            "risk_level": self.risk_level,
            "blast_radius": self.blast_radius,
            "affected_files": list(self.affected_files),
        }
@dataclass(frozen=True)
class _GateRequest:
    file_path: str
    symbol_name: str
    lines_to_remove: int
    affected_files: list[str]
    root_dir: str = ""
    @property
    def basename(self) -> str:
        return os.path.basename(self.file_path) if self.file_path else ""
    @property
    def single_file(self) -> list[str]:
        return [self.file_path] if self.file_path else []
def _dedupe_affected_files(affected_files: list) -> list:
    out: list[str] = []
    seen: set[str] = set()
    for f in affected_files:
        if not isinstance(f, str) or not f:
            continue
        key = os.path.normcase(os.path.normpath(f))
        if key in seen:
            continue
        seen.add(key)
        out.append(f)
    return out
class SafetyGate:
    MAX_LINES_NO_CONFIRM = 100
    MAX_LINES_BLOCK = 500
    MAX_FILES_NO_CONFIRM = 5
    MAX_FILES_BLOCK = 20
    def __init__(self) -> None:
        self._blocked_count: int = 0
        self._confirmed_count: int = 0
    @property
    def blocked_count(self) -> int:
        return self._blocked_count
    @property
    def confirmed_count(self) -> int:
        return self._confirmed_count
    def check(
        self,
        file_path: str,
        lines_to_remove: int = 0,
        affected_files: list[str] | None = None,
        symbol_name: str = "",
        root_dir: str = "",
    ) -> SafetyCheck:
        req = self._normalize_check_inputs(
            file_path, lines_to_remove, affected_files, symbol_name, root_dir)
        for rule in (self._check_protected_core, self._check_blast_lines,
                     self._check_blast_files, self._check_confirm_lines,
                     self._check_confirm_files, self._check_public_api):
            verdict = rule(req)
            if verdict is not None:
                self._record(verdict.action)
                return verdict
        return self._make_check(
            SafetyAction.ALLOW, "", "low", req, req.affected_files)
    @staticmethod
    def _normalize_check_inputs(
        file_path: str,
        lines_to_remove: int,
        affected_files: list[str] | None,
        symbol_name: str,
        root_dir: str = "",
    ) -> _GateRequest:
        if not isinstance(affected_files, list):
            affected_files = as_item_list(
                affected_files, log_tag="[SafetyGate]")
        return _GateRequest(
            file_path=normalize_file_ref(file_path),
            symbol_name=normalize_file_ref(symbol_name),
            lines_to_remove=(math.ceil(lines_to_remove)
                             if _is_non_negative_finite(lines_to_remove)
                             else normalize_line_no(lines_to_remove)),
            affected_files=_dedupe_affected_files(affected_files),
            root_dir=normalize_file_ref(root_dir),
        )
    def _record(self, action: SafetyAction) -> None:
        if action is SafetyAction.BLOCK:
            self._blocked_count += 1
        elif action is SafetyAction.REQUIRE_CONFIRM:
            self._confirmed_count += 1
    @staticmethod
    def _make_check(action: SafetyAction, reason: str, risk_level: str,
                    req: _GateRequest, affected_files: list[str]) -> SafetyCheck:
        return SafetyCheck(
            action=action, reason=reason, risk_level=risk_level,
            blast_radius=req.lines_to_remove, affected_files=affected_files,
        )
    def _is_root_level(self, req: _GateRequest) -> bool:
        root = os.path.realpath(req.root_dir)
        path = req.file_path
        if not os.path.isabs(path):
            path = os.path.join(root, path)
        return (os.path.normcase(os.path.dirname(os.path.realpath(path)))
                == os.path.normcase(root))
    def _check_protected_core(self, req: _GateRequest) -> SafetyCheck | None:
        if os.path.normcase(req.basename) not in _PROTECTED_CORE_NORMCASE:
            return None
        if req.root_dir and not self._is_root_level(req):
            return None
        return self._make_check(
            SafetyAction.BLOCK,
            f"核心文件 '{req.basename}' 受保护，禁止清理",
            "critical", req, req.single_file)
    def _threshold_check(self, req: _GateRequest, *, value: int, limit: int,
                         action: SafetyAction, risk: str, reason: str,
                         files: list[str]) -> SafetyCheck | None:
        if value <= limit:
            return None
        return self._make_check(action, reason, risk, req, files)
    def _check_blast_lines(self, req: _GateRequest) -> SafetyCheck | None:
        return self._threshold_check(
            req, value=req.lines_to_remove, limit=self.MAX_LINES_BLOCK,
            action=SafetyAction.BLOCK, risk="critical",
            reason=(f"单项删除 {req.lines_to_remove} 行"
                    f"超过上限 {self.MAX_LINES_BLOCK}"),
            files=req.single_file)
    def _check_blast_files(self, req: _GateRequest) -> SafetyCheck | None:
        return self._threshold_check(
            req, value=len(req.affected_files), limit=self.MAX_FILES_BLOCK,
            action=SafetyAction.BLOCK, risk="high",
            reason=(f"批次影响 {len(req.affected_files)} 个文件"
                    f"超过上限 {self.MAX_FILES_BLOCK}"),
            files=req.affected_files)
    def _check_confirm_lines(self, req: _GateRequest) -> SafetyCheck | None:
        return self._threshold_check(
            req, value=req.lines_to_remove, limit=self.MAX_LINES_NO_CONFIRM,
            action=SafetyAction.REQUIRE_CONFIRM, risk="medium",
            reason=f"单项删除 {req.lines_to_remove} 行代码，建议确认",
            files=req.single_file)
    def _check_confirm_files(self, req: _GateRequest) -> SafetyCheck | None:
        return self._threshold_check(
            req, value=len(req.affected_files), limit=self.MAX_FILES_NO_CONFIRM,
            action=SafetyAction.REQUIRE_CONFIRM, risk="medium",
            reason=f"批次影响 {len(req.affected_files)} 个文件，建议确认",
            files=req.affected_files)
    def _check_public_api(self, req: _GateRequest) -> SafetyCheck | None:
        if not req.symbol_name or req.symbol_name.startswith("_"):
            return None
        return self._make_check(
            SafetyAction.WARN,
            f"删除公开 API '{req.symbol_name}'，确认未被外部引用",
            "low", req, req.single_file)

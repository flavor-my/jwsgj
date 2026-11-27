from __future__ import annotations

import hashlib
import logging
import math
import os
import re
import shutil
import tempfile
import threading
import time
from collections.abc import Callable
from dataclasses import (
    dataclass,
    field,
)
from datetime import datetime
from difflib import unified_diff
from enum import Enum
from pathlib import Path
from typing import (
    Any,
    Self,
)

from jwsgj.build_discover_sixdim import (
    enhance_content_six_dim,
    enhance_proposal_file_six_dim,
)
from jwsgj.build_skill_md_generate import (
    build_refactor_content,
    improve_description_from_issues,
)
from jwsgj.build_text_frontmatter import extract_frontmatter_fields
from jwsgj.build_text_scoring import (
    fix_upload_violation_descs,
    normalize_suggestion_text,
)
from jwsgj.diag_guard_io import (
    guarded_open,
    normalize_out_path,
    normalize_path_arg,
    resolve_skill_dir,
    two_level_rmtree,
    two_level_unlink,
)
from jwsgj.diag_types_defs import (
    ContractViolationError,
    DocQualityReport,
    DocRefactorPlan,
)
from jwsgj.html_render_pipeline import emit_step_html
from jwsgj.log_config import (
    log_swallowed,
    write_module_run,
)
from jwsgj.runtime_paths import (
    get_backup_base,
    get_workspace_output_dir,
    sanitize_skill_name,
)
from jwsgj.shared_cache import ensure_entry_warmed
from jwsgj.skill_doc_diagnoser import (
    SkillDocDiagnoser,
    get_doc_diagnoser,
    validate_refactor_content,
)

__all__ = [
    'REGRESSION_THRESHOLD',
    'EvolutionLaws',
    'LawCheckResult',
    'LawViolation',
    'PreEvolutionSnapshot',
    'SelfCorrectingEvolver',
    'SkillDocRefactorer',
    'ViolationSeverity',
    'apply_refactored_doc',
    'as_dict',
    'backup_source_for_apply',
    'capture_guard_snapshot',
    'compose_refactor_document',
    'detect_regression',
    'fill_evolution_guard',
    'get_refactorer',
    'get_self_correcting_evolver',
    'is_numeric_score',
    'read_refactor_source',
    'read_utf8_text',
    'refactor_skill_doc',
    'resolve_proposal_path',
    'restore_backup_bytes',
    'result_from_defaults',
    'rollback_after_regression',
    'run_save_evolution_guard',
    'write_proposal_text',
]
_log = logging.getLogger(__name__)
REGRESSION_THRESHOLD = 0.01
_UTF8_BOM_TEXT = "\ufeff"
_APPLY_BACKUP_SUBDIR = "apply_md"
_APPLY_BACKUP_PREFIX = "backup_apply_"
_APPLY_BACKUP_KEEP = 5
_APPLY_OUTCOME_BY_STATUS: dict[str, str] = {
    "ok": "ok",
    "rolled_back": "degraded",
    "rejected": "degraded",
    "unverified": "degraded",
}
def _as_list(value: Any) -> list | tuple:
    return value if isinstance(value, (list, tuple)) else []
def _as_str(value: Any) -> str:
    return value if isinstance(value, str) else ""
def _normalized_newlines(text: str) -> str:
    return text.replace("\r\n", "\n").replace("\r", "\n")
def read_utf8_text(path: str) -> str:
    with open(path, encoding="utf-8-sig") as fh:
        return fh.read()
def _apply_result(
        status: str, detail: str, *,
        applied: bool = False,
        backup_path: str | None = None,
        score_before: float | None = None,
        score_after: float | None = None,
        **extra: Any,
) -> dict[str, Any]:
    result: dict[str, Any] = {
        "status": status,
        "applied": applied,
        "backup_path": backup_path,
        "score_before": score_before,
        "score_after": score_after,
        "detail": detail,
    }
    result.update(extra)
    return result
def _apply_outcome(status: Any) -> str:
    return _APPLY_OUTCOME_BY_STATUS.get(status, "error")
def _refactor_outcome(status: Any, apply_status: Any) -> str:
    outcome = _apply_outcome(status)
    if outcome != "ok":
        return outcome
    if apply_status in (None, "ok"):
        return "ok"
    if apply_status in ("skipped_regression", "skipped_unverified"):
        return "degraded"
    return _apply_outcome(apply_status)
def _discard_generated_path(path: str) -> bool:
    try:
        if os.path.isdir(path) and not os.path.islink(path):
            return bool(two_level_rmtree(path))
        return bool(two_level_unlink(path))
    except Exception as _e:  # noqa: BLE001 — 清理失败仅降级，不得阻断调用方
        log_swallowed(__name__, _e, context='_discard_generated_path:Exception')
        return False
def _path_identity_key(path: str) -> str:
    return os.path.normcase(os.path.realpath(path))
def _safe_isfile(path: Any) -> bool:
    try:
        return os.path.isfile(path)
    except (OSError, ValueError, TypeError):
        return False
def _path_identity_digest(path: str) -> str:
    return hashlib.sha256(
        _path_identity_key(path).encode("utf-8")).hexdigest()[:12]
def _apply_backup_root(md_path: str) -> str:
    return os.path.join(
        get_backup_base(), _APPLY_BACKUP_SUBDIR, _path_identity_digest(md_path))
def _backup_dir_mtime(path: str) -> float:
    try:
        return os.path.getmtime(path)
    except OSError as _e:
        log_swallowed(__name__, _e, context='_backup_dir_mtime:OSError')
        return 0.0
def _list_apply_backup_dirs(base: str) -> list[str]:
    try:
        entries = os.listdir(base)
    except OSError as _e:
        _log.warning("_list_apply_backup_dirs: 备份目录枚举失败(不阻断): %s", _e)
        return []
    return [
        os.path.join(base, entry) for entry in entries
        if entry.startswith(_APPLY_BACKUP_PREFIX)
        and os.path.isdir(os.path.join(base, entry))]
def _prune_apply_backups(md_path: str, *, keep: int = _APPLY_BACKUP_KEEP,
                         exclude: str | None = None) -> None:
    try:
        base = os.path.normpath(_apply_backup_root(md_path))
    except (RuntimeError, ValueError) as _e:
        _log.warning("_prune_apply_backups: 备份归口不可解析(跳过裁剪): %s", _e)
        return
    if not os.path.isdir(base):
        return
    entries = _list_apply_backup_dirs(base)
    if exclude:
        _ex = _path_identity_key(exclude)
        entries = [p for p in entries
                   if _path_identity_key(p) != _ex]
    entries.sort(key=lambda path: (_backup_dir_mtime(path), path))
    _budget = keep - 1 if exclude else keep
    prune_count = max(0, len(entries) - _budget)
    for old_dir in entries[:prune_count]:
        if not _discard_generated_path(old_dir):
            _log.warning("_prune_apply_backups: 旧备份删除失败(不阻断): %s", old_dir)
def restore_backup_bytes(md_path: str, backup_path: str,
                          *, stage: str = "rollback_apply",
                          include_suffix: bool = False) -> str | None:
    md_path = normalize_path_arg(md_path)
    backup_path = normalize_path_arg(backup_path)
    if not isinstance(md_path, str) or not md_path.strip():
        return f"源文档路径无效: {type(md_path).__name__}"
    if not isinstance(backup_path, str) or not backup_path.strip():
        return f"备份路径无效: {type(backup_path).__name__}"
    try:
        _atomic_replace_via_tmp(
            md_path, stage,
            lambda tmp_path: shutil.copyfile(backup_path, tmp_path),
            include_suffix=include_suffix)
    except (OSError, ValueError) as _e:
        log_swallowed(__name__, _e, context='restore_backup_bytes:OSError')
        return str(_e)
    return None
def rollback_after_regression(md_path: str, backup_path: str,
                               score_before: float,
                               score_after: float | None,
                               *, evolution_guard: dict[str, Any] | None = None,
                               reason_prefix: str = "score_regression",
                               ) -> dict[str, Any]:
    err = restore_backup_bytes(md_path, backup_path)
    reason = ("验证失败" if score_after is None
              or reason_prefix == "post_write_verification"
              else "overall_score 退化")
    failed = err is not None
    score_delta = (round(score_after - score_before, 1)
                   if score_after is not None else None)
    if evolution_guard is not None:
        evolution_guard["rolled_back"] = not failed
        evolution_guard["rollback_failed"] = failed
        evolution_guard["rollback_reason"] = (
            f"{reason_prefix}_restore_failed" if failed
            else f"{reason_prefix}_auto_restore")
    detail = (f"采纳后{reason}且回滚失败，请从备份人工恢复: "
              f"{backup_path}（{err}）" if failed
              else f"采纳后 {reason}，源文件已回滚")
    if failed:
        _log.error("apply_refactored_doc: %s", detail)
    else:
        _log.warning("apply_refactored_doc: %s", detail)
    return _apply_result(
        "rollback_failed" if failed else "rolled_back", detail,
        applied=failed,
        backup_path=backup_path, score_before=score_before,
        score_after=score_after, score_delta=score_delta,
        evolution_guard=evolution_guard)
def _create_apply_backup(md_path: str) -> tuple[str | None, str | None]:
    try:
        base_dir = _apply_backup_root(md_path)
    except (RuntimeError, ValueError) as _e:
        log_swallowed(__name__, _e, context='_create_apply_backup:RuntimeError+')
        return None, f"备份归口不可解析，拒绝写盘: {_e}"
    try:
        os.makedirs(base_dir, exist_ok=True)
        backup_dir = tempfile.mkdtemp(
            prefix=_APPLY_BACKUP_PREFIX, dir=base_dir)
    except OSError as _e:
        log_swallowed(__name__, _e, context='_create_apply_backup:OSError')
        return None, f"备份目录创建失败，拒绝写盘: {_e}"
    backup_path = os.path.join(backup_dir, os.path.basename(md_path))
    try:
        shutil.copyfile(md_path, backup_path)
    except OSError as _e:
        if not _discard_generated_path(backup_dir):
            _log.warning("apply_refactored_doc: 空备份目录清理失败(不阻断): %s", backup_dir)
        return None, f"备份失败，拒绝写盘: {_e}"
    _prune_apply_backups(exclude=backup_dir, md_path=md_path)
    return backup_path, None
def backup_source_for_apply(md_path: str) -> tuple[str | None, dict[str, Any] | None]:
    md_path = normalize_path_arg(md_path)
    if not isinstance(md_path, str) or not md_path.strip():
        return None, _apply_result(
            "error", f"源文档路径无效，拒绝写盘: {type(md_path).__name__}")
    backup_path, _err = _create_apply_backup(md_path)
    if _err is not None:
        return None, _apply_result("error", _err)
    return backup_path, None
def _finite_float_or_none(value: Any) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    try:
        number = float(value)
    except OverflowError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_finite_float_or_none:OverflowError')
        return None
    return number if math.isfinite(number) else None
def _uv000_issue(report: Any) -> Any | None:
    issues = getattr(report, "issues", None)
    if not isinstance(issues, (list, tuple)):
        return None
    return next(
        (issue for issue in issues
         if getattr(issue, "rule_id", "") == "UV-000"),
        None)
def is_numeric_score(value: Any) -> bool:
    return _finite_float_or_none(value) is not None
def _content_hash(text: str) -> str:
    return hashlib.md5(
        text.encode("utf-8"), usedforsecurity=False).hexdigest()[:12]
def _append_capped(items: list[Any], item: Any, limit: int) -> None:
    items.append(item)
    if len(items) > limit:
        del items[:len(items) - limit]
class ViolationSeverity(Enum):
    INFO = "info"
    WARNING = "warning"
    ERROR = "error"
    CRITICAL = "critical"
@dataclass
class LawViolation:
    law_name: str
    severity: ViolationSeverity
    message: str
    details: dict = field(default_factory=dict)
@dataclass
class LawCheckResult:
    passed: bool
    violations: list[LawViolation] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
class EvolutionLaws:
    _MAX_CONVERGENCE_STEPS = 50
    _STAGNATION_WINDOW = 5
    _STAGNATION_SPREAD_RATIO = 0.01
    def check_evolution_safety(
        self: Self, original: dict, candidate: dict) -> LawCheckResult:
        original = as_dict(original)
        candidate = as_dict(candidate)
        violations: list[LawViolation] = []
        warnings: list[str] = []
        if candidate.get("rollback_available") is not True:
            violations.append(LawViolation(
                law_name="可逆进化定律",
                severity=ViolationSeverity.ERROR,
                message="候选进化不可回滚，违反可逆进化定律",
                details={"rollback_available": False},
            ))
        if not candidate.get("evidence"):
            warnings.append("候选进化缺少经验证据驱动")
        orig_text = _as_str(original.get("text", ""))
        cand_text = _as_str(candidate.get("text", ""))
        if orig_text == cand_text:
            warnings.append("候选文本与原始文本相同，无实际进化")
        if orig_text and not cand_text:
            violations.append(LawViolation(
                law_name="经验驱动定律",
                severity=ViolationSeverity.CRITICAL,
                message="候选文本为空，可能导致功能丢失",
                details={"original_length": len(orig_text), "candidate_length": 0},
            ))
        return LawCheckResult(passed=not violations, violations=violations, warnings=warnings)
    def _recent_numeric_scores(self: Self, history: list) -> list:
        if len(history) < self._STAGNATION_WINDOW:
            return []
        return [v for v in history[-self._STAGNATION_WINDOW:] if is_numeric_score(v)]
    def check_convergence(self: Self, history: list) -> LawCheckResult:
        history = _as_list(history)
        violations: list[LawViolation] = []
        warnings: list[str] = []
        if len(history) > self._MAX_CONVERGENCE_STEPS:
            violations.append(LawViolation(
                law_name="收敛性保证定律",
                severity=ViolationSeverity.ERROR,
                message=(f"连续进化 {len(history)} 步未收敛" f"（超过最大步数 {self._MAX_CONVERGENCE_STEPS}）"),
                details={"steps": len(history), "max": self._MAX_CONVERGENCE_STEPS},
            ))
        recent = self._recent_numeric_scores(history)
        if len(recent) >= 2:
            spread = max(recent) - min(recent)
            _spread_ref = abs(max(recent))
            if (spread == 0
                    or (_spread_ref > 0 and spread < _spread_ref * self._STAGNATION_SPREAD_RATIO)):
                warnings.append(
                    f"最近{self._STAGNATION_WINDOW}步评分变化<"
                    f"{self._STAGNATION_SPREAD_RATIO:.0%}，可能停滞")
        return LawCheckResult(passed=not violations, violations=violations, warnings=warnings)
@dataclass
class PreEvolutionSnapshot:
    skill_name: str = ""
    skill_dir: str = ""
    content: str = ""
    score: float = 0.0
    metadata: dict = field(default_factory=dict)
    content_hash: str = ""
    def __post_init__(self: Self) -> None:
        self.metadata = dict(self.metadata) if isinstance(self.metadata, dict) else {}
        if isinstance(self.content, str) and not self.content_hash:
            self.content_hash = _content_hash(self.content)
_SECTION_FEATURE_PAIRS: tuple[tuple[str, str, str], ...] = (
    ("##", "新增章节", "删除章节"),
    ("```", "新增代码示例", "删除代码示例"),
)
_KEYWORD_FEATURES: tuple[tuple[tuple[str, ...], str], ...] = (
    (("keywords:", "trigger"), "优化触发词"),
    (("description:",), "更新描述"),
)
def _diff_line_stats(diff: list[str]) -> tuple[int, int, str, str]:
    additions = 0
    deletions = 0
    added_parts: list[str] = []
    removed_parts: list[str] = []
    for line in diff[2:]:
        if line.startswith("+"):
            additions += 1
            added_parts.append(line[1:])
        elif line.startswith("-"):
            deletions += 1
            removed_parts.append(line[1:])
    return additions, deletions, "".join(added_parts), "".join(removed_parts)
def _section_feature_reason(token: str, add_reason: str, del_reason: str,
                            added_text: str, removed_text: str) -> str:
    if token in added_text and token not in removed_text:
        return add_reason
    if token in removed_text and token not in added_text:
        return del_reason
    return ""
def _feature_reasons(added_text: str, removed_text: str) -> list[str]:
    reasons: list[str] = []
    for token, add_reason, del_reason in _SECTION_FEATURE_PAIRS:
        reason = _section_feature_reason(token, add_reason, del_reason, added_text, removed_text)
        if reason:
            reasons.append(reason)
    _added_low = added_text.lower()
    for tokens, label in _KEYWORD_FEATURES:
        if any(t in _added_low for t in tokens):
            reasons.append(label)
    return reasons
@dataclass
class _EvolutionState:
    skill_name: str
    skill_dir: str
    pre_content: str
    evolved_content: str
    restore_fn: Callable[[], None] | None
    pre_score: float
    post_score: float
def _normalized_skill_dir(skill_dir: Any) -> str:
    if not isinstance(skill_dir, str) or not skill_dir.strip():
        return ""
    try:
        return _path_identity_key(skill_dir)
    except (OSError, ValueError) as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc, context='_normalized_skill_dir:OSError')
        return skill_dir
def _stagnation_key(skill_name: str, skill_dir: str | None) -> str:
    if skill_dir is None:
        return skill_name
    return f"{skill_name}\0{_normalized_skill_dir(skill_dir)}"
def _rollback_target_path(
        snapshot: PreEvolutionSnapshot,
) -> Path | None:
    metadata = (snapshot.metadata if isinstance(snapshot.metadata, dict) else {})
    bound_path = metadata.get("_rollback_target_path")
    if isinstance(bound_path, str) and bound_path:
        return Path(bound_path)
    md_path = metadata.get("md_path")
    if isinstance(md_path, str) and md_path:
        return Path(md_path)
    if isinstance(snapshot.skill_dir, str) and snapshot.skill_dir:
        return Path(snapshot.skill_dir) / "SKILL.md"
    return None
def _snapshot_skill_dir(snapshot: PreEvolutionSnapshot) -> str:
    metadata = snapshot.metadata if isinstance(snapshot.metadata, dict) else {}
    bound_dir = metadata.get("_snapshot_skill_dir")
    if isinstance(bound_dir, str) and bound_dir:
        return bound_dir
    return snapshot.skill_dir if isinstance(snapshot.skill_dir, str) else ""
_UTF8_BOM = b"\xef\xbb\xbf"
def _raw_payload_for_snapshot(target_path: str,
                              content: str) -> dict[str, Any]:
    try:
        raw = Path(target_path).read_bytes()
    except OSError as _e:
        log_swallowed(__name__, _e, context='_raw_payload_for_snapshot:OSError')
        return {}
    try:
        raw_text = raw.decode("utf-8-sig")
    except UnicodeDecodeError as _e:
        log_swallowed(__name__, _e, context='_raw_payload_for_snapshot:UnicodeDecodeError')
        return {}
    if _normalized_newlines(raw_text) != _normalized_newlines(content):
        return {}
    return {"raw_text": raw_text, "raw_bom": raw.startswith(_UTF8_BOM)}
def _attach_raw_payload(snapshot: PreEvolutionSnapshot) -> None:
    content = snapshot.content
    if not isinstance(content, str):
        return
    target_path = _rollback_target_path(snapshot)
    if target_path is None:
        return
    bound_target = Path(os.path.abspath(str(target_path)))
    snapshot.metadata["_rollback_target_path"] = str(bound_target)
    if isinstance(snapshot.skill_dir, str) and snapshot.skill_dir:
        snapshot.metadata["_snapshot_skill_dir"] = os.path.abspath(snapshot.skill_dir)
    snapshot.metadata.update(
        _raw_payload_for_snapshot(str(bound_target), content))
def _rollback_raw_payload(
        target_snapshot: PreEvolutionSnapshot,
) -> tuple[str | None, bool]:
    metadata = (target_snapshot.metadata if isinstance(target_snapshot.metadata, dict) else {})
    raw_text = metadata.get("raw_text")
    if not isinstance(raw_text, str):
        return None, False
    if _normalized_newlines(raw_text) != _normalized_newlines(target_snapshot.content):
        return None, False
    return raw_text, bool(metadata.get("raw_bom"))
def _write_rollback_file(tmp_path: str, content: str,
                         raw_text: str | None, had_bom: bool) -> None:
    if raw_text is not None:
        with guarded_open(tmp_path, "w", encoding="utf-8", newline="") as f:
            f.write((_UTF8_BOM_TEXT if had_bom else "") + raw_text)
        return
    with guarded_open(tmp_path, "w", encoding="utf-8", newline="\n") as f:
        f.write(content)
def _write_rollback_content(
        target_snapshot: PreEvolutionSnapshot,
) -> tuple[str | None, bool]:
    skill_path = _rollback_target_path(target_snapshot)
    if skill_path is None:
        return "no_rollback_target", False
    tmp_path = (f"{skill_path}.tmp_rollback." f"{os.getpid()}.{threading.get_ident()}")
    raw_text, had_bom = _rollback_raw_payload(target_snapshot)
    try:
        _write_rollback_file(tmp_path, target_snapshot.content, raw_text, had_bom)
        os.replace(tmp_path, str(skill_path))
        _log.info(
            "[SelfCorrecting][%s] 回滚成功: 恢复 %d 字符到 %s",
            target_snapshot.skill_name,
            len(target_snapshot.content), skill_path,
        )
        return None, True
    except (OSError, ValueError, ContractViolationError) as e:
        _log.error("[SelfCorrecting][%s] 回滚写入失败: %s",
                   target_snapshot.skill_name, e, exc_info=True)
        if not _discard_generated_path(tmp_path):
            _log.debug("[SelfCorrecting][%s] 回滚临时文件清理失败: %s",
                       target_snapshot.skill_name, tmp_path)
        return "rollback_write_failed", False
def _guarded_score_call(
        score_fn: Callable[[str], float],
        text: str,
        skill_name: str,
        phase: str,
) -> tuple[float | None, str | None]:
    try:
        score = score_fn(text)
    except Exception as e:  # noqa: BLE001
        _log.error("[SelfCorrecting][%s] %s异常: %s", skill_name, phase, e, exc_info=True)
        return None, f"score_fn_error: {e}"
    if not is_numeric_score(score):
        _log.error("[SelfCorrecting][%s] %s返回不可判定评分"
                   "（非数值或非有限）: %s",
                   skill_name, phase, type(score).__name__)
        return None, (f"score_fn_error: 返回值须为有限数值，" f"实际 {type(score).__name__}")
    return score, None
def _failure_result(
        reason: str,
        *,
        score_before: float | None = None,
        score_after: float | None = None,
        rollback_info: dict[str, Any] | None = None,
) -> dict[str, Any]:
    result: dict[str, Any] = {
        "success": False,
        "reason": reason,
        "rolled_back": bool(rollback_info and rollback_info.get("rolled_back")),
        "score_before": score_before,
        "score_after": score_after,
    }
    if rollback_info is not None:
        result["rollback_info"] = rollback_info
    return result
def _run_evolve_fn(
        evolve_fn: Callable[[str], str],
        pre_content: str,
        skill_name: str,
        pre_score: float | None,
) -> tuple[str | None, dict | None]:
    try:
        evolved_content = evolve_fn(pre_content)
    except Exception as e:  # noqa: BLE001
        _log.error("[SelfCorrecting][%s] 进化函数异常: %s", skill_name, e, exc_info=True)
        return None, _failure_result(f"evolve_fn_error: {e}", score_before=pre_score)
    if not isinstance(evolved_content, str):
        _log.error("[SelfCorrecting][%s] 进化函数返回非 str: %s",
                   skill_name, type(evolved_content).__name__)
        return None, _failure_result(
            (f"evolve_fn_error: 返回值须为 str，" f"实际 {type(evolved_content).__name__}"),
            score_before=pre_score)
    return evolved_content, None
def _restore_quietly(
        restore_fn: Callable[[], None] | None,
        skill_name: str,
) -> str | None:
    if restore_fn:
        try:
            restore_fn()
        except Exception as e:  # noqa: BLE001
            _log.error("[SelfCorrecting][%s] restore_fn 异常: %s", skill_name, e, exc_info=True)
            return str(e)
    return None
def _normalize_pre_content(pre_content: Any, skill_name: str) -> str:
    if isinstance(pre_content, str):
        return pre_content
    _log.warning(
        "[SelfCorrecting][%s] evolve_with_rollback 收到非 str 进化前文本"
        "（归一为空串）: %s",
        skill_name, type(pre_content).__name__)
    return ""
def _check_convergence_warn(
        laws: EvolutionLaws,
        score_history: list[float],
) -> None:
    try:
        conv_result = laws.check_convergence(score_history)
        for v in conv_result.violations:
            _log.warning("[EvolutionLaw] convergence: %s", v.message)
        for warn in conv_result.warnings:
            _log.warning("[EvolutionLaw] convergence: %s", warn)
    except Exception as e:  # noqa: BLE001 — 收敛检查是观测步骤，不得中断进化
        _log.warning("[EvolutionLaw] convergence check failed: %s", e)
def _inject_exploration(text: str) -> str:
    exploration_marker = (
        f"\n\n<!-- exploration-injection {datetime.now().strftime('%Y%m%d')} -->\n"
        "<!-- Auto-Exploration: 停滞突破注入 -->\n"
    )
    if "exploration-injection" in text:
        return text
    return text.rstrip() + exploration_marker
def _delta_exceeds(score_before: float, score_after: float,
                   threshold: float) -> bool:
    return round(score_before - score_after, 9) > threshold
def detect_regression(
        score_before: Any, score_after: Any, threshold: float) -> bool:
    if not (is_numeric_score(score_before) and is_numeric_score(score_after)):
        _log.warning(
            "[SelfCorrecting] 退化检测收到不可判定评分（非数值或非有限，"
            "无法判定退化，按未退化处理）: before=%s, after=%s",
            type(score_before).__name__, type(score_after).__name__)
        return False
    regression = _delta_exceeds(float(score_before), float(score_after),
                                threshold)
    if regression:
        _log.warning(
            "[SelfCorrecting] 评分退化: %.3f → %.3f (delta=%.3f)",
            score_before, score_after, score_before - score_after,
        )
    return regression
class SelfCorrectingEvolver:
    STAGNATION_HASH_THRESHOLD = 3
    REGRESSION_THRESHOLD = REGRESSION_THRESHOLD
    _MAX_SNAPSHOTS = 50
    _MAX_CORRECTION_LOGS = 200
    _MAX_SCORE_HISTORY = 100
    _MAX_STAGNATION_KEYS = 50
    def __init__(self: Self) -> None:
        self.snapshots: list[PreEvolutionSnapshot] = []
        self._correction_logs: list[dict[str, Any]] = []
        self._stagnation_counter: dict[str, int] = {}
        self.evolution_laws: EvolutionLaws = EvolutionLaws()
        self._score_history: list[float] = []
    def capture_snapshot(
        self: Self,
        skill_name: str,
        skill_dir: str,
        content: str,
        score: float = 0.0,
        metadata: dict | None = None,
    ) -> PreEvolutionSnapshot:
        snapshot = PreEvolutionSnapshot(
            skill_name=skill_name,
            skill_dir=skill_dir,
            content=content,
            score=score,
            metadata=metadata if isinstance(metadata, dict) else {},
        )
        _attach_raw_payload(snapshot)
        _append_capped(self.snapshots, snapshot, self._MAX_SNAPSHOTS)
        _log.info(
            "[SelfCorrecting][%s] 快照已捕获: score=%s, hash=%s",
            skill_name,
            f"{score:.3f}" if is_numeric_score(score) else score,
            snapshot.content_hash,
        )
        return snapshot
    def _append_correction_log(self: Self, entry: dict[str, Any]) -> None:
        _append_capped(self._correction_logs, entry, self._MAX_CORRECTION_LOGS)
    def _bump_stagnation(self: Self, skill_name: str, value: int) -> None:
        if (skill_name not in self._stagnation_counter
                and len(self._stagnation_counter) >= self._MAX_STAGNATION_KEYS):
            evicted = min(self._stagnation_counter,
                          key=self._stagnation_counter.get)
            del self._stagnation_counter[evicted]
        self._stagnation_counter[skill_name] = value
    def _find_latest_snapshot(
            self: Self, skill_name: str,
            skill_dir: str | None = None) -> PreEvolutionSnapshot | None:
        expected_dir = (_normalized_skill_dir(skill_dir) if skill_dir is not None else None)
        for snap in reversed(self.snapshots):
            if snap.skill_name != skill_name:
                continue
            if (expected_dir is not None
                    and _normalized_skill_dir(_snapshot_skill_dir(snap)) != expected_dir):
                continue
            return snap
        return None
    def _rollback_payload(
            self: Self,
            skill_name: str,
            *,
            rolled_back: bool = False,
            reason: str | None = None,
            restored_content_length: int = 0,
            snapshot_hash: str = "",
    ) -> dict[str, Any]:
        return {
            "rolled_back": rolled_back,
            "reason": reason,
            "skill_name": skill_name,
            "restored_content_length": restored_content_length,
            "snapshot_hash": snapshot_hash,
        }
    def auto_rollback(self: Self, skill_name: str,
                      skill_dir: str | None = None) -> dict[str, Any]:
        target_snapshot = self._find_latest_snapshot(skill_name, skill_dir)
        if target_snapshot is None:
            _log.warning("[SelfCorrecting][%s] 无可用快照，回滚失败", skill_name)
            return self._rollback_payload(skill_name, reason="no_snapshot_available")
        restored = False
        _content = target_snapshot.content
        _content_ok = isinstance(_content, str)
        if not _content_ok:
            rollback_reason: str | None = "invalid_snapshot_content"
        elif _rollback_target_path(target_snapshot) is None:
            rollback_reason = "no_rollback_target"
        else:
            rollback_reason, restored = _write_rollback_content(target_snapshot)
        self._append_correction_log({
            "skill_name": skill_name,
            "timestamp": datetime.now().isoformat(),
            "action": "auto_rollback",
            "restored": restored,
            "snapshot_hash": target_snapshot.content_hash,
            "snapshot_score": target_snapshot.score,
        })
        return self._rollback_payload(
            skill_name, rolled_back=restored, reason=rollback_reason,
            restored_content_length=(
                len(_content) if (restored and _content_ok) else 0),
            snapshot_hash=target_snapshot.content_hash)
    def detect_regression(self: Self, score_before: Any,
                          score_after: Any) -> bool:
        return detect_regression(score_before, score_after, self.REGRESSION_THRESHOLD)
    def _update_stagnation(self: Self, skill_name: str,
                           current_hash: str,
                           skill_dir: str | None = None) -> tuple[int, int, bool]:
        counter_key = _stagnation_key(skill_name, skill_dir)
        prev_count = self._stagnation_counter.get(counter_key, 0)
        matched_snap = self._find_latest_snapshot(skill_name, skill_dir)
        if matched_snap is not None and matched_snap.content_hash == current_hash:
            self._bump_stagnation(counter_key, prev_count + 1)
            current_count = self._stagnation_counter[counter_key]
            return (prev_count, current_count, current_count >= self.STAGNATION_HASH_THRESHOLD)
        self._bump_stagnation(counter_key, 0)
        return prev_count, 0, False
    def auto_break_stagnation(
        self: Self, skill_name: str, evolved_text: str,
        skill_dir: str | None = None,
    ) -> tuple[str, dict[str, Any]]:
        if not isinstance(evolved_text, str):
            _log.warning("[SelfCorrecting][%s] auto_break_stagnation "
                         "收到非 str 文本: %s",
                         skill_name, type(evolved_text).__name__)
            return "", {
                "injected": False, "strategy": "invalid_text",
                "invalid_text": True,
                "stagnation_count": self._stagnation_counter.get(
                    _stagnation_key(skill_name, skill_dir), 0)}
        current_hash = _content_hash(evolved_text)
        prev_count, current_count, is_stagnant = self._update_stagnation(skill_name, current_hash, skill_dir)
        if not is_stagnant:
            return evolved_text, { "injected": False, "strategy": "none", "stagnation_count": current_count}
        injected_text = _inject_exploration(evolved_text)
        if injected_text == evolved_text:
            _log.warning(
                "[SelfCorrecting][%s] 停滞突破注入被幂等短路（探索标记已存在），"
                "文本未变: stagnation_count=%d",
                skill_name, current_count,
            )
            return evolved_text, {
                "injected": False,
                "strategy": "already_injected",
                "stagnation_count": current_count,
                "original_hash": current_hash,
            }
        self._bump_stagnation(_stagnation_key(skill_name, skill_dir), 0)
        _log.info(
            "[SelfCorrecting][%s] 停滞突破: "
            "strategy=exploration_injection, prev_count=%d",
            skill_name, prev_count,
        )
        return injected_text, {
            "injected": True,
            "strategy": "exploration_injection",
            "stagnation_count": prev_count,
            "original_hash": current_hash,
            "injected_hash": _content_hash(injected_text),
        }
    def derive_change_reason(self: Self, original_text: Any,
                             evolved_text: Any) -> str:
        if not isinstance(original_text, str):
            _log.warning(
                "[SelfCorrecting] derive_change_reason 收到非 str 进化前文本"
                "（归一为空串）: %s", type(original_text).__name__)
            original_text = ""
        if not isinstance(evolved_text, str):
            _log.warning(
                "[SelfCorrecting] derive_change_reason 收到非 str 进化后文本"
                "（归一为空串）: %s", type(evolved_text).__name__)
            evolved_text = ""
        if original_text == evolved_text:
            return "无变更"
        orig_lines = original_text.splitlines(keepends=True)
        evol_lines = evolved_text.splitlines(keepends=True)
        diff = list(unified_diff(orig_lines, evol_lines, n=1))
        additions, deletions, added_text, removed_text = _diff_line_stats(diff)
        reasons: list[str] = []
        if additions > 0:
            reasons.append(f"新增 {additions} 行")
        if deletions > 0:
            reasons.append(f"删除 {deletions} 行")
        reasons.extend(_feature_reasons(added_text, removed_text))
        reason_str = "；".join(reasons) if reasons else "内容微调"
        return f"自动推导: {reason_str}（+{additions}/-{deletions}）"
    def _record_score(self: Self, post_score: float) -> None:
        _append_capped(self._score_history, post_score, self._MAX_SCORE_HISTORY)
    def _rollback_response(
            self: Self, skill_name: str,
            restore_fn: Callable[[], None] | None, reason: str,
            pre_score: float | None, post_score: float | None,
            skill_dir: str | None = None,
    ) -> dict[str, Any]:
        try:
            rollback_info = self.auto_rollback(skill_name, skill_dir)
        except Exception as e:  # noqa: BLE001 — 回滚异常必须保持失败结果
            _log.error(
                "[SelfCorrecting][%s] 自动回滚异常: %s",
                skill_name, e, exc_info=True)
            rollback_info = self._rollback_payload(
                skill_name, reason="rollback_error")
            rollback_info["error"] = str(e)
        restore_error = _restore_quietly(restore_fn, skill_name)
        if restore_error is not None:
            rollback_info["snapshot_rolled_back"] = bool(
                rollback_info.get("rolled_back"))
            rollback_info["snapshot_reason"] = rollback_info.get("reason")
            rollback_info["rolled_back"] = False
            rollback_info["reason"] = "restore_fn_error"
            rollback_info["restore_error"] = restore_error
        elif restore_fn is not None and not rollback_info.get("rolled_back"):
            rollback_info["snapshot_rolled_back"] = False
            rollback_info["snapshot_reason"] = rollback_info.get("reason")
            rollback_info["rolled_back"] = True
            rollback_info["reason"] = "restore_fn_success"
        return _failure_result(
            reason, score_before=pre_score, score_after=post_score,
            rollback_info=rollback_info)
    def _check_laws_and_maybe_rollback(
            self: Self, state: _EvolutionState,
    ) -> dict[str, Any] | None:
        try:
            law_result = self.evolution_laws.check_evolution_safety(
                {"text": state.pre_content},
                {"text": state.evolved_content, "rollback_available": True},
            )
            for warning in law_result.warnings:
                _log.info("[EvolutionLaw] %s", warning)
            if not law_result.passed:
                for v in law_result.violations:
                    _log.warning("[EvolutionLaw] %s: %s", v.law_name, v.message)
                    self._append_correction_log({
                        "action": "evolution_law_violation",
                        "skill": state.skill_name,
                        "law": v.law_name,
                        "message": v.message,
                    })
        except Exception as e:  # noqa: BLE001 — 仅定律检查本身允许观测降级
            _log.warning("[EvolutionLaw] check failed: %s", e)
            return None
        if law_result.passed:
            return None
        return self._rollback_response(
            state.skill_name, state.restore_fn,
            "evolution_law_violation",
            state.pre_score, state.post_score, state.skill_dir)
    def evolve_with_rollback(
        self: Self,
        skill_name: str,
        skill_dir: str,
        evolve_fn: Callable[[str], str],
        score_fn: Callable[[str], float],
        restore_fn: Callable[[], None] | None = None,
        pre_content: str = "",
    ) -> dict[str, Any]:
        pre_content = _normalize_pre_content(pre_content, skill_name)
        rollback_skill_dir = (
            os.path.abspath(skill_dir)
            if isinstance(skill_dir, str) and skill_dir else skill_dir)
        rollback_md_path = (
            os.path.join(rollback_skill_dir, "SKILL.md")
            if isinstance(rollback_skill_dir, str) and rollback_skill_dir else "")
        rollback_content = pre_content
        if rollback_md_path and _safe_isfile(rollback_md_path):
            try:
                rollback_content = read_utf8_text(rollback_md_path)
            except (OSError, ValueError) as exc:
                _log.error(
                    "[SelfCorrecting][%s] 回滚原文读取失败，中止进化: %s",
                    skill_name, exc, exc_info=True)
                return _failure_result(f"rollback_snapshot_error: {exc}")
        pre_score, _score_err = _guarded_score_call(
            score_fn, pre_content, skill_name, "进化前评分")
        if _score_err is not None:
            return _failure_result(_score_err)
        self.capture_snapshot(
            skill_name=skill_name,
            skill_dir=skill_dir,
            content=rollback_content,
            score=pre_score,
            metadata={"step": "evolve_with_rollback", "md_path": rollback_md_path},
        )
        evolved_content, _err_resp = _run_evolve_fn(evolve_fn, pre_content, skill_name, pre_score)
        if _err_resp is not None:
            return self._rollback_response(
                skill_name, restore_fn, _err_resp["reason"],
                pre_score, None, rollback_skill_dir)
        post_score, _score_err = _guarded_score_call(score_fn, evolved_content, skill_name, "进化后评分")
        if _score_err is not None:
            return self._rollback_response(
                skill_name, restore_fn, _score_err,
                pre_score, None, rollback_skill_dir)
        _evaluation = self._evaluate_evolution(_EvolutionState(
            skill_name=skill_name, skill_dir=rollback_skill_dir, pre_content=pre_content,
            evolved_content=evolved_content, restore_fn=restore_fn,
            pre_score=pre_score, post_score=post_score))
        if _evaluation is not None:
            return _evaluation
        change_reason = self.derive_change_reason(pre_content, evolved_content)
        _log.info(
            "[SelfCorrecting][%s] 进化成功: %.3f → %.3f, reason=%s",
            skill_name, pre_score, post_score, change_reason,
        )
        return {
            "success": True,
            "reason": None,
            "evolved_content": evolved_content,
            "score_before": pre_score,
            "score_after": post_score,
            "change_reason": change_reason,
            "rolled_back": False,
        }
    def _evaluate_evolution(
            self, state: _EvolutionState,
    ) -> dict[str, Any] | None:
        self._record_score(state.post_score)
        _law_resp = self._check_laws_and_maybe_rollback(state)
        if _law_resp is not None:
            return _law_resp
        _check_convergence_warn(self.evolution_laws, self._score_history)
        if self.detect_regression(state.pre_score, state.post_score):
            _log.warning(
                "[SelfCorrecting][%s] 退化检测触发回滚: %.3f → %.3f",
                state.skill_name, state.pre_score, state.post_score,
            )
            return self._rollback_response(
                state.skill_name, state.restore_fn,
                f"score_regression: {state.pre_score:.3f} → {state.post_score:.3f}",
                state.pre_score, state.post_score, state.skill_dir)
        return None
    def get_correction_logs(self: Self) -> list[dict[str, Any]]:
        return list(self._correction_logs)
_evolver_instance: SelfCorrectingEvolver = SelfCorrectingEvolver()
def get_self_correcting_evolver() -> SelfCorrectingEvolver:
    return _evolver_instance
def _checked_regression_verdict(score_before: Any, score_after: Any) -> bool:
    before = _finite_float_or_none(score_before)
    after = _finite_float_or_none(score_after)
    if before is None or after is None:
        raise ValueError(
            "退化检测评分须为有限数值，实际 "
            f"before={type(score_before).__name__}, after={type(score_after).__name__}")
    detected = get_self_correcting_evolver().detect_regression(before, after)
    if not isinstance(detected, bool):
        raise TypeError(
            f"detect_regression 返回值须为 bool，实际 {type(detected).__name__}")
    return detected
_RESULT_VERIFICATION_DEFAULTS: dict[str, Any] = {
    "status": None,
    "diag_after": None,
    "score_delta": None,
    "evolution_guard": None,
}
def result_from_defaults(defaults: dict[str, Any], required: dict[str, Any],
                          overrides: dict[str, Any], label: str) -> dict[str, Any]:
    unknown = [key for key in (*required, *overrides) if key not in defaults]
    if unknown:
        raise ValueError(f"{label} 未知结果键: {unknown[0]}")
    result = dict(defaults)
    result.update(required)
    result.update(overrides)
    return result
def read_refactor_source(md_path: str) -> tuple[str | None, Exception | None]:
    md_path = normalize_path_arg(md_path)
    if not isinstance(md_path, str) or not md_path.strip():
        return None, TypeError(f"md_path 必须为非空字符串路径，实际 {type(md_path).__name__}")
    try:
        return read_utf8_text(md_path), None
    except (OSError, ValueError) as e:
        log_swallowed(__name__, e, context='read_refactor_source:OSError+')
        return None, e
def _skill_identity(md_path: str) -> tuple[str, str]:
    skill_dir = (resolve_skill_dir(md_path)
                 or os.path.dirname(os.path.abspath(md_path)))
    return (os.path.basename(skill_dir) or "unknown"), skill_dir
def _emit_snapshot(evolver: Any, md_path: str, content: str,
                   score: float, step: str) -> None:
    skill_name, skill_dir = _skill_identity(md_path)
    evolver.capture_snapshot(
        skill_name, skill_dir, content, score=score,
        metadata={"step": step, "md_path": md_path})
def _capture_evolution_snapshot(md_path: str, content: str,
                                score: float) -> None:
    try:
        _emit_snapshot(get_self_correcting_evolver(), md_path, content, score, "apply_refactor")
    except Exception as e:  # noqa: BLE001 — 快照为观测埋点，任一异常仅告警
        _log.warning("进化守卫快照失败（不影响执行）: %s", e)
def _diagnose_and_snapshot(doc_diagnoser: SkillDocDiagnoser, md_path: str,
                           original_content: str
                           ) -> tuple[Any, float | None, dict[str, Any] | None]:
    try:
        diag_before = doc_diagnoser.diag(md_path)
    except Exception as _e:  # noqa: BLE001 — 诊断失败结构化返回（未写盘）
        log_swallowed(__name__, _e, context='apply_refactored_doc:diag')
        return None, None, _apply_result("error", f"写回前诊断失败（未写盘）: {_e}")
    fatal_issue = _uv000_issue(diag_before)
    if fatal_issue is not None:
        return None, None, _apply_result(
            "error",
            f"写回前诊断失败（未写盘）: {fatal_issue.description}")
    score_before = _finite_float_or_none(getattr(diag_before, "overall_score", None))
    if score_before is None:
        _log.warning(
            "写回前诊断评分不可判定（%s），拒绝写回: %s",
            type(getattr(diag_before, "overall_score", None)).__name__,
            md_path)
        return None, None, _apply_result(
            "error", "写回前诊断评分不可判定（非有限数值），拒绝写回以免无法校验退化")
    _capture_evolution_snapshot(md_path, original_content, score_before)
    return diag_before, score_before, None
def _atomic_replace_via_tmp(md_path: str, stage: str,
                            write_payload: Callable[[str], None],
                            *, include_suffix: bool = True) -> None:
    _tmp_ext = os.path.splitext(md_path)[1] if include_suffix else ""
    tmp_path = (f"{md_path}.tmp_{stage}." f"{os.getpid()}.{threading.get_ident()}{_tmp_ext}")
    try:
        write_payload(tmp_path)
        os.replace(tmp_path, md_path)
    except Exception:
        _cleanup_tmp_quietly(tmp_path)
        raise
def _cleanup_tmp_quietly(tmp_path: str) -> None:
    try:
        cleaned = _discard_generated_path(tmp_path)
    except Exception as cleanup_exc:  # noqa: BLE001 — 清理失败不得掩盖原始异常
        _log.warning("临时文件清理异常（残留待后续回收）: %s: %s", tmp_path, cleanup_exc)
        return
    if not cleaned:
        _log.debug("临时文件清理失败（残留待后续回收）: %s", tmp_path)
def _atomic_write_lf_content(md_path: str, new_content: str) -> None:
    def _write_text(tmp_path: str) -> None:
        with guarded_open(tmp_path, "w", encoding="utf-8", newline="\n") as handle:
            handle.write(new_content)
    _atomic_replace_via_tmp(md_path, "apply", _write_text)
def _write_source_content(md_path: str, new_content: str, *,
                          backup_path: str | None = None,
                          score_before: float | None = None,
                          ) -> dict[str, Any] | None:
    try:
        _atomic_write_lf_content(md_path, new_content)
        return None
    except (OSError, ValueError, ContractViolationError) as e:
        log_swallowed(__name__, e, context='_write_source_content:OSError+')
        return _apply_result(
            "error", f"写盘失败（源文件未变动）: {e}",
            backup_path=backup_path, score_before=score_before)
def _guard_skeleton(score_before: float | None, score_after: float | None,
                    regressed: bool | None) -> dict[str, Any]:
    return {
        "change_reason": None,
        "score_before": _finite_float_or_none(score_before),
        "score_after": _finite_float_or_none(score_after),
        "regression_detected": regressed,
        "rolled_back": False,
        "rollback_failed": False,
    }
def _assess_evolution_guard(score_before: float, score_after: float,
                            original_content: str,
                            new_content: str) -> dict[str, Any]:
    evolution_guard = _guard_skeleton(score_before, score_after, None)
    evolver = get_self_correcting_evolver()
    try:
        evolution_guard["regression_detected"] = _checked_regression_verdict(
            score_before, score_after)
    except Exception as e:  # noqa: BLE001 — 写后验证必须失败关闭
        evolution_guard["verification_error"] = f"退化检测失败: {e}"
        _log.warning("进化守卫退化检测失败（验证不可判定）: %s", e)
    try:
        evolution_guard["change_reason"] = evolver.derive_change_reason(
            original_content, new_content)
    except Exception as e:  # noqa: BLE001 — 信息步骤软失败，只得 change_reason
        _log.warning("进化守卫变更理由推导失败（不影响结果）: %s", e)
    return evolution_guard
def _rollback_after_verification_failure(
        md_path: str, backup_path: str, score_before: float, err: Exception,
        *, score_after: float | None = None,
        evolution_guard: dict[str, Any] | None = None,
) -> dict[str, Any]:
    if evolution_guard is None:
        evolution_guard = _guard_skeleton(score_before, score_after, None)
    _log.warning("写后诊断或验证失败，自动撤回: %s", err)
    return rollback_after_regression(
        md_path, backup_path, score_before, score_after,
        evolution_guard=evolution_guard,
        reason_prefix="post_write_verification")
def _verify_after_apply(
        md_path: str, backup_path: str, score_before: float,
        original_content: str, new_content: str) -> dict[str, Any]:
    try:
        diag_after = get_doc_diagnoser().diag(md_path)
    except Exception as e:  # noqa: BLE001 - 刻意降级：写后诊断失败触发撤回
        log_swallowed(__name__, e, context='_verify_after_apply:diag')
        return _rollback_after_verification_failure(
            md_path, backup_path, score_before, e)
    fatal_issue = _uv000_issue(diag_after)
    if fatal_issue is not None:
        return _rollback_after_verification_failure(
            md_path, backup_path, score_before,
            ValueError(f"写后诊断失败: {fatal_issue.description}"))
    score_after = _finite_float_or_none(getattr(diag_after, "overall_score", None))
    if score_after is None:
        return _rollback_after_verification_failure(
            md_path, backup_path, score_before,
            ValueError("写后诊断评分不可判定（非有限数值）"))
    evolution_guard = _assess_evolution_guard(
        score_before, score_after, original_content, new_content)
    regressed = evolution_guard["regression_detected"]
    if regressed is True:
        return rollback_after_regression(
            md_path, backup_path, score_before, score_after,
            evolution_guard=evolution_guard)
    if regressed is not False:
        return _rollback_after_verification_failure(
            md_path, backup_path, score_before,
            ValueError("写后退化验证不可判定，禁止保留未验证写回"),
            score_after=score_after, evolution_guard=evolution_guard)
    try:
        diag_after_data = diag_after.to_dict()
        if not isinstance(diag_after_data, dict):
            raise TypeError(
                f"diag_after.to_dict 返回值须为 dict，实际 {type(diag_after_data).__name__}")
    except Exception as e:  # noqa: BLE001 — 写后结果形态违约必须撤回
        log_swallowed(__name__, e, context='_verify_after_apply:to_dict')
        return _rollback_after_verification_failure(
            md_path, backup_path, score_before, e,
            score_after=score_after, evolution_guard=evolution_guard)
    _log.info("[SkillDocApply] 审核执行完成: %s（%.1f→%.1f，备份: %s）",
              md_path, score_before, score_after, backup_path)
    return _apply_result(
        "ok", f"重构方案已写回源文件并通过评分验证: {md_path}",
        applied=True, backup_path=backup_path,
        score_before=score_before, score_after=score_after,
        score_delta=round(score_after - score_before, 1),
        diag_after=diag_after_data,
        evolution_guard=evolution_guard)
def _discard_degraded_proposal(out_path: str) -> tuple[bool, str]:
    try:
        if _discard_generated_path(out_path):
            return True, "score_regression_discard_proposal"
        _log.warning("退化方案清理未成功（discard_failed）: %s", out_path)
        return False, "discard_failed: 方案文件清理未成功"
    except Exception as e:  # noqa: BLE001 — 清理异常降级记录，不阻断重构主流程
        _log.warning("退化方案清理异常（discard_failed）: %s", out_path, exc_info=True)
        return False, f"discard_failed: {e}"
def _dispose_regressed_proposal(evolution_guard: dict[str, Any], out_path: str,
                                 output_path: str | None, score_before_val: float,
                                 actual_score_after: float) -> bool:
    if output_path is None:
        deleted, reason = _discard_degraded_proposal(out_path)
        evolution_guard["rollback_reason"] = reason
        evolution_guard["rolled_back"] = deleted
        evolution_guard["rollback_failed"] = not deleted
        if deleted:
            _log.warning(
                "[EvolutionGuard] 重构退化 %.3f→%.3f，退化方案已回收: %s",
                score_before_val, float(actual_score_after), out_path,
            )
            return False
        _log.error(
            "[EvolutionGuard] 重构退化 %.3f→%.3f，默认产物清理失败已保留: %s",
            score_before_val, float(actual_score_after), out_path)
        return True
    evolution_guard["rollback_reason"] = "explicit_output_path_kept_for_review"
    return True
def _detect_save_regression(score_before: float,
                           score_after: float | None) -> bool | None:
    if score_after is None:
        return None
    try:
        return _checked_regression_verdict(score_before, score_after)
    except Exception as e:  # noqa: BLE001 — 验证异常必须显式标记不可判定
        _log.warning("进化守卫退化检测失败，方案标记为未验证: %s", e)
        return None
def run_save_evolution_guard(actual_score_after: float | None,
                              score_before_val: float,
                              out_path: str,
                              output_path: str | None,
                              md_path: str,
                              new_content: str) -> tuple[dict[str, Any], bool]:
    regressed = _detect_save_regression(score_before_val, actual_score_after)
    evolution_guard = _guard_skeleton(
        score_before_val, actual_score_after, regressed)
    saved = True
    if regressed is True:
        saved = _dispose_regressed_proposal(
            evolution_guard, out_path, output_path,
            score_before_val, actual_score_after)
    _guard_info_chain(evolution_guard, md_path, score_before_val, new_content)
    return evolution_guard, saved
def _refresh_saved_verification(
        refactorer: SkillDocRefactorer,
        result: dict[str, Any],
        md_path: str,
        diag_before: DocQualityReport,
        new_content: str,
) -> None:
    try:
        _refresh_saved_verification_impl(
            refactorer, result, md_path, diag_before, new_content)
    except Exception as e:  # noqa: BLE001 — 装配失败必须结构化降级
        _log.warning("写后验证链异常，方案标记为未验证: %s", e, exc_info=True)
        evolution_guard = result.get("evolution_guard")
        if isinstance(evolution_guard, dict):
            evolution_guard["regression_detected"] = None
            evolution_guard["verification_error"] = f"写后验证链异常: {e}"
        result.update({
            "status": "unverified",
            "saved": True,
            "detail": f"写后验证链异常，禁止自动采纳: {e}",
        })
def _refresh_saved_verification_impl(
        refactorer: SkillDocRefactorer,
        result: dict[str, Any],
        md_path: str,
        diag_before: DocQualityReport,
        new_content: str,
) -> None:
    out_path = str(result.get("output_path") or "")
    (diag_after, actual_score_after, actual_grade_after,
     remaining_issues, score_delta) = refactorer._verify_saved_proposal(
        out_path, md_path, diag_before)
    score_before_val = _report_overall_score(diag_before)
    evolution_guard, saved = run_save_evolution_guard(
        actual_score_after, score_before_val, out_path,
        result.get("output_path_override"), md_path, new_content)
    diag_after_data = None
    serialization_error = None
    if diag_after is not None:
        try:
            diag_after_data = diag_after.to_dict()
            if not isinstance(diag_after_data, dict):
                raise TypeError(
                    "diag_after.to_dict 返回值须为 dict，实际 "
                    f"{type(diag_after_data).__name__}")
        except Exception as e:  # noqa: BLE001 — 结果形态违约必须禁止自动采纳
            serialization_error = e
            diag_after_data = None
            log_swallowed(
                __name__, e, context="_refresh_saved_verification:to_dict")
    regression_verdict = evolution_guard.get("regression_detected")
    if regression_verdict is True:
        status = "rejected"
        if not saved:
            detail = "方案评分退化，默认产物已回收，禁止自动采纳"
        elif result.get("output_path_override") is not None:
            detail = "方案评分退化，显式产物已保留供人工审核，禁止自动采纳"
        else:
            detail = "方案评分退化，默认产物清理失败并已保留，禁止自动采纳"
        if serialization_error is not None:
            evolution_guard["verification_error"] = (
                f"重构后诊断报告序列化失败: {serialization_error}")
    else:
        verification_error = None
        if serialization_error is not None:
            verification_error = (
                f"重构后诊断报告序列化失败，禁止自动采纳: {serialization_error}")
        elif (score_before_val is None or actual_score_after is None
              or regression_verdict is not False):
            verification_error = "重构前基线或最终方案评分不可判定，禁止自动采纳"
        if verification_error is not None:
            evolution_guard["regression_detected"] = None
            evolution_guard["verification_error"] = verification_error
            status = "unverified"
            detail = verification_error
        else:
            status = "ok"
            detail = f"重构方案已生成并通过评分验证: {out_path}"
    result.update({
        "status": status,
        "diag_after": diag_after_data,
        "actual_score": actual_score_after,
        "actual_grade": actual_grade_after,
        "score_delta": score_delta,
        "remaining_issues": remaining_issues,
        "evolution_guard": evolution_guard,
        "saved": saved,
        "detail": detail,
    })
def _guard_info_chain(evolution_guard: dict[str, Any], md_path: str,
                      score_before_val: float, new_content: str) -> None:
    try:
        evolver = get_self_correcting_evolver()
        original_content, _read_exc = read_refactor_source(md_path)
        if original_content is None:
            _log.warning("进化守卫源文件重读失败（跳过快照与理由推导）: %s",
                         _read_exc)
            return
        _emit_snapshot(evolver, md_path, original_content,
                       score_before_val, "refactor_and_save")
        evolution_guard["change_reason"] = evolver.derive_change_reason(
            original_content, new_content)
    except Exception as e:  # noqa: BLE001 — 信息链软失败，不影响退化决策
        _log.warning("进化守卫信息链执行失败（不影响重构结果）: %s", e)
def as_dict(value: Any) -> dict[str, Any]:
    return dict(value) if isinstance(value, dict) else {}
def _default_proposal_filename(md_path: str, skill_name: str) -> str:
    safe_name = sanitize_skill_name(skill_name) or "skill"
    return (f"{safe_name}-{_path_identity_digest(md_path)}"
            f"-{os.path.basename(md_path)}.refactored.md")
def resolve_proposal_path(output_path: str | None, md_path: str,
                          skill_name: str) -> tuple[str, str | None]:
    _raw_output_path = output_path
    output_path = normalize_out_path(output_path)
    md_path = normalize_path_arg(md_path)
    if _raw_output_path is not None and output_path is None:
        return "", ("输出路径无效（须为非空字符串）: "
                     f"{type(_raw_output_path).__name__}")
    if not isinstance(md_path, str) or not md_path.strip():
        return (output_path or "", f"源文档路径无效（方案写盘已阻断）: {type(md_path).__name__}")
    if output_path:
        try:
            same_target = (_path_identity_key(output_path)
                           == _path_identity_key(md_path))
        except (OSError, ValueError, TypeError) as _e:
            log_swallowed(__name__, _e, context='resolve_proposal_path:path_identity')
            return output_path, f"输出路径同一性校验失败（方案写盘已阻断）: {_e}"
        if same_target:
            return output_path, (f"输出路径不得与源文件相同" f"（方案写盘禁止覆盖源文件）: {output_path}")
        return output_path, None
    try:
        return os.path.join(
            get_workspace_output_dir(),
            _default_proposal_filename(md_path, skill_name)), None
    except (OSError, RuntimeError, ValueError) as _e:
        _log.error("resolve_proposal_path: 工作区输出目录解析失败: %s", _e, exc_info=True)
        return "", f"工作区输出目录解析失败（无可用工作空间或产物根被拒）: {_e}"
def write_proposal_text(out_path: str, new_content: str) -> str | None:
    out_type = type(out_path).__name__
    out_path = normalize_out_path(out_path)
    if not out_path:
        return f"输出路径无效（须为非空字符串）: {out_type}"
    try:
        with guarded_open(out_path, "w", encoding="utf-8", newline="\n") as f:
            f.write(new_content)
        return None
    except (OSError, ValueError, ContractViolationError) as _e:
        log_swallowed(__name__, _e, context='write_proposal_text:OSError+')
        return str(_e)
def capture_guard_snapshot(md_path: str, skill_name: str,
                            skill_dir: str, diag_before: Any,
                            new_content: str) -> dict[str, Any] | None:
    try:
        evolver = get_self_correcting_evolver()
        original_content = read_utf8_text(md_path)
        _score_before = _report_overall_score(diag_before)
        if _score_before is None:
            return None
        evolver.capture_snapshot(
            skill_name, skill_dir, original_content,
            score=_score_before,
            metadata={"step": "refactor_in_memory", "md_path": md_path},
        )
        evolution_guard = _guard_skeleton(_score_before, None, None)
        evolution_guard.update(
            change_reason=evolver.derive_change_reason(original_content, new_content),
            in_memory=True,
        )
        return evolution_guard
    except Exception as _e:  # noqa: BLE001
        _log.warning("进化守卫执行失败（不影响重构结果）: %s", _e)
        return None
def fill_evolution_guard(evolution_guard: dict[str, Any] | None,
                          apply_result: dict[str, Any],
                          diag_before: Any) -> None:
    if evolution_guard is None:
        return
    apply_result = as_dict(apply_result)
    _score_after = apply_result.get("score_after")
    if _score_after is not None:
        if not is_numeric_score(_score_after):
            _log.warning("退化检测回填跳过：score_after 非有限数值(不阻断): %s", type(_score_after).__name__)
        else:
            evolution_guard["score_after"] = float(_score_after)
            try:
                evolution_guard["regression_detected"] = _checked_regression_verdict(
                    diag_before.overall_score, _score_after)
            except Exception as _e:  # noqa: BLE001 — 回填是观测链，不得逃逸或伪造结论
                evolution_guard["regression_detected"] = None
                evolution_guard["verification_error"] = f"退化检测回填失败: {_e}"
                _log.warning("退化检测回填失败(不阻断): %s", _e)
    _apply_status = apply_result.get("status")
    if _apply_status in ("rolled_back", "rollback_failed"):
        is_regression = evolution_guard.get("regression_detected") is True
        reason_kind = "verify_regression" if is_regression else "verification_failure"
        if _apply_status == "rolled_back":
            evolution_guard["rolled_back"] = True
            evolution_guard.setdefault(
                "rollback_reason", f"apply_{reason_kind}_rolled_back")
        else:
            evolution_guard["rolled_back"] = False
            evolution_guard["rollback_failed"] = True
            evolution_guard.setdefault(
                "rollback_reason", f"apply_{reason_kind}_rollback_failed")
        if not is_regression:
            evolution_guard["regression_detected"] = None
def _locate_proposal(proposal_path: str | None,
                     proposal_content: str | None) -> tuple[str | None, dict[str, Any] | None]:
    if proposal_content is not None:
        if not isinstance(proposal_content, str):
            return None, _apply_result(
                "error", "proposal_content 须为字符串，"
                f"实际 {type(proposal_content).__name__}")
        if not proposal_content.strip():
            return None, _apply_result("error", "proposal_content 为空，拒绝采纳")
        return proposal_content, None
    if proposal_path is None:
        return None, _apply_result(
            "error", "须提供 proposal_path（方案文件）或 "
            "proposal_content（方案内容全文）")
    if not isinstance(proposal_path, str):
        return None, _apply_result(
            "error", "proposal_path 须为字符串路径，"
            f"实际 {type(proposal_path).__name__}")
    return _read_proposal_file(proposal_path)
def _read_proposal_file(proposal_path: str) -> tuple[str | None, dict[str, Any] | None]:
    if not _safe_isfile(proposal_path):
        return None, _apply_result("error", f"方案文件不存在: {proposal_path}")
    try:
        proposal_content = read_utf8_text(proposal_path)
    except (OSError, UnicodeDecodeError, ValueError) as _e:
        log_swallowed(__name__, _e, context='_locate_proposal:OSError')
        return None, _apply_result("error", f"方案文件读取失败: {_e}")
    if not proposal_content.strip():
        return None, _apply_result("error", "方案文件内容为空，拒绝采纳")
    return proposal_content, None
def _validate_apply_inputs(md_path: Any) -> dict[str, Any] | None:
    if not isinstance(md_path, str) or not md_path.strip():
        return _apply_result("error", "md_path 必须为非空字符串")
    if not _safe_isfile(md_path):
        return _apply_result("error", f"源 SKILL.md 不存在: {md_path}")
    return None
def _report_overall_score(report: Any) -> float | None:
    if _uv000_issue(report) is not None:
        return None
    return _finite_float_or_none(getattr(report, "overall_score", None))
@dataclass(frozen=True)
class _ApplyRequest:
    md_path: str
    proposal_path: str | None
    proposal_content: str
    original_content: str
def _document_body_text(content: str) -> str:
    normalized = _normalized_newlines(content)
    _name, _description, _keywords, body_start = extract_frontmatter_fields(
        normalized)
    if body_start is None:
        return normalized.strip()
    return normalized[body_start:].strip()
def _reject_body_loss(original_content: str, proposal_content: str) -> str | None:
    if not _document_body_text(original_content):
        return None
    if _document_body_text(proposal_content):
        return None
    return ("方案 frontmatter 之后没有任何正文，采纳会删除源文档全部章节，"
            "已拒绝写回（确需清空正文请先备份并显式编辑源文件）")
def _prepare_apply_request(
    md_path: Any, proposal_path: Any, proposal_content: str | None,
) -> tuple[_ApplyRequest | None, dict[str, Any] | None]:
    md_path = normalize_path_arg(md_path)
    proposal_path = normalize_path_arg(proposal_path)
    _input_err = _validate_apply_inputs(md_path)
    if _input_err is not None:
        return None, _input_err
    content, _loc_err = _locate_proposal(proposal_path, proposal_content)
    if _loc_err is not None:
        return None, _loc_err
    content = content.lstrip(_UTF8_BOM_TEXT)
    _reject_reason = validate_refactor_content(content)
    if _reject_reason is not None:
        return None, _apply_result("rejected", _reject_reason)
    original_content, _read_exc = read_refactor_source(md_path)
    if original_content is None:
        log_swallowed(__name__, _read_exc, context='_prepare_apply_request:read')
        return None, _apply_result("error", f"读取源文件失败: {_read_exc}")
    if (_normalized_newlines(content).rstrip()
            == _normalized_newlines(original_content).rstrip()):
        return None, _apply_result(
            "ok", "方案内容与源文件一致（幂等，无需写盘）")
    _body_loss = _reject_body_loss(original_content, content)
    if _body_loss is not None:
        _log.error("apply_refactored_doc: %s: %s", _body_loss, md_path)
        return None, _apply_result("rejected", _body_loss)
    return _ApplyRequest(md_path, proposal_path, content, original_content), None
def _apply_refactored_doc_impl(md_path: str,
                              proposal_path: str | None,
                              verify: bool,
                              proposal_content: str | None) -> dict[str, Any]:
    _req, _prep_result = _prepare_apply_request(
        md_path, proposal_path, proposal_content)
    if _prep_result is not None:
        return _prep_result
    _log.info("apply_refactored_doc: 采纳方案 %s → %s",
              _req.proposal_path or "<memory>", _req.md_path)
    ensure_entry_warmed(_skill_identity(_req.md_path)[1],
                        None, "文档采纳 apply_refactored_doc")
    if not verify:
        _backup_path, _backup_err = backup_source_for_apply(_req.md_path)
        if _backup_err is not None:
            return _backup_err
        _write_err = _write_source_content(
            _req.md_path, _req.proposal_content, backup_path=_backup_path)
        if _write_err is not None:
            return _write_err
        return _apply_result(
            "ok", "方案已采纳写盘（未启用写后验证）",
            applied=True, backup_path=_backup_path)
    _diag_before, score_before, _diag_err = _diagnose_and_snapshot(
        get_doc_diagnoser(), _req.md_path, _req.original_content)
    if _diag_err is not None:
        return _diag_err
    backup_path, _backup_err = _create_apply_backup(_req.md_path)
    if backup_path is None:
        return _apply_result(
            "error", f"写回前备份失败（阻断写入）: {_backup_err}",
            score_before=score_before)
    _write_err = _write_source_content(
        _req.md_path, _req.proposal_content,
        backup_path=backup_path, score_before=score_before)
    if _write_err is not None:
        return _write_err
    return _verify_after_apply(
        _req.md_path, backup_path, score_before,
        _req.original_content, _req.proposal_content)
def apply_refactored_doc(md_path: str,
                         proposal_path: str | None = None,
                         verify: bool = True,
                         proposal_content: str | None = None) -> dict[str, Any]:
    _t0 = time.monotonic()
    try:
        _result = _apply_refactored_doc_impl(md_path, proposal_path, verify, proposal_content)
    except Exception:
        write_module_run(
            "skill_doc_refactor_guard", "apply_refactored_doc",
            outcome="error",
            duration_ms=(time.monotonic() - _t0) * 1000.0,
            md_file=os.path.basename(str(md_path)),
            error="fail_fast_exception",
        )
        raise
    _status = _result.get("status")
    write_module_run(
        "skill_doc_refactor_guard", "apply_refactored_doc",
        outcome=_apply_outcome(_status),
        duration_ms=(time.monotonic() - _t0) * 1000.0,
        status=_status,
        applied=bool(_result.get("applied")),
        verify=bool(verify),
        md_file=os.path.basename(str(md_path)),
    )
    try:
        emit_step_html("doc_refactor_apply", _skill_identity(str(md_path))[1],
                        _result)
    except Exception as _html_err:  # noqa: BLE001 — 留痕失败不得篡改主结果
        _log.warning("apply_refactored_doc: HTML 留痕失败(不阻断): %s", _html_err)
    return _result
_REFACTOR_SAVE_RESULT_DEFAULTS: dict[str, Any] = {
    **_RESULT_VERIFICATION_DEFAULTS,
    "plan": None,
    "output_path": None,
    "output_path_override": None,
    "diag_before": None,
    "estimated_score": None,
    "actual_score": None,
    "actual_grade": None,
    "remaining_issues": None,
    "saved": False,
    "auto_apply": None,
    "proposal_in_memory": False,
    "proposal_consumed": False,
    "detail": None,
}
def _refactor_save_result(status: str, plan: Any, output_path: str | None,
                          diag_before: Any, **overrides: Any) -> dict[str, Any]:
    return result_from_defaults(
        _REFACTOR_SAVE_RESULT_DEFAULTS,
        {"status": status, "plan": plan,
         "output_path": output_path, "diag_before": diag_before},
        overrides, "_refactor_save_result")
@dataclass(frozen=True)
class _RefactorContext:
    md_path: str
    diag_report: DocQualityReport
    name: str
    description: str
    keywords: list[str]
    body_text: str
    skill_dir: str
def _as_str_list(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value] if value.strip() else []
    if isinstance(value, (list, tuple)):
        return [text for item in value
                if item is not None and (text := str(item).strip())]
    return []
@dataclass(frozen=True)
class _RefactorOptions:
    capabilities: list[str] = field(default_factory=list)
    file_extensions: list[str] = field(default_factory=list)
    exclusion_scopes: list[str] = field(default_factory=list)
    colloquial_examples: list[str] = field(default_factory=list)
    extra_frontmatter: dict[str, Any] = field(default_factory=dict)
    @classmethod
    def from_optional(cls, capabilities: list[str] | None = None,
                      file_extensions: list[str] | None = None,
                      exclusion_scopes: list[str] | None = None,
                      colloquial_examples: list[str] | None = None,
                      extra_frontmatter: dict[str, Any] | None = None,
                      ) -> _RefactorOptions:
        return cls(
            capabilities=_as_str_list(capabilities),
            file_extensions=_as_str_list(file_extensions),
            exclusion_scopes=_as_str_list(exclusion_scopes),
            colloquial_examples=_as_str_list(colloquial_examples),
            extra_frontmatter=as_dict(extra_frontmatter),
        )
def _dedupe_improvements(items: list[str]) -> list[str]:
    seen: set[str] = set()
    unique: list[str] = []
    for item in items:
        text = str(item)
        rule_key = (text.split("]", 1)[0] + "]" if text.startswith("[") and "]" in text else text)
        if rule_key in seen:
            continue
        seen.add(rule_key)
        unique.append(text)
    return unique
def _blank_proposal_reason(plan: Any, new_content: str) -> str | None:
    frontmatter = getattr(plan, "new_frontmatter", "")
    if not isinstance(frontmatter, str) or not frontmatter.strip():
        return "方案未生成 frontmatter"
    if not new_content.strip():
        return "refactor 未产出有效内容"
    if not _document_body_text(new_content):
        return "方案 frontmatter 之后没有任何正文（正文整体丢失）"
    return None
def _blank_proposal_tail(plan: Any) -> str:
    improvements = getattr(plan, "improvements", None)
    return "; ".join(improvements)[:200] if improvements else "未知原因"
def _reject_empty_proposal(plan: DocRefactorPlan, new_content: str,
                          diag_before: DocQualityReport,
                          out_path: str) -> dict[str, Any]:
    _reason = _blank_proposal_reason(plan, new_content) or "方案不可写"
    _detail_tail = _blank_proposal_tail(plan)
    _log.error("refactor_and_save: %s，拒绝写空白方案: %s",
               _reason, _detail_tail)
    return _refactor_save_result(
        "error", plan, out_path, diag_before.to_dict(),
        detail=f"{_reason}，拒绝写空白方案: {_detail_tail}")
def _assemble_refactor_plan(context: _RefactorContext, skill_name: str,
                            improved_desc: str, improvements: list[str],
                            options: _RefactorOptions) -> DocRefactorPlan:
    new_frontmatter, new_body_sections = build_refactor_content(
        skill_name, context.body_text, improved_desc,
        skill_dir=context.skill_dir,
        capabilities=options.capabilities,
        exclusion_scopes=options.exclusion_scopes,
        colloquial_examples=options.colloquial_examples,
        extra_frontmatter=options.extra_frontmatter)
    base_score = _report_overall_score(context.diag_report) or 0.0
    estimated_improvement = max(
        0.0, min(len(improvements) * 2.0, 95.0 - base_score))
    return DocRefactorPlan(
        skill_name=skill_name, original_path=context.md_path,
        issues=context.diag_report.issues, improvements=improvements,
        new_frontmatter=new_frontmatter,
        new_body_sections=new_body_sections,
        estimated_score_after=min(100.0, base_score + estimated_improvement))
class SkillDocRefactorer:
    def __init__(self: Self) -> None:
        self._doc_diagnoser = get_doc_diagnoser()
    def _prepare_refactor_context(
            self: Self, md_path: str,
            diag_report: DocQualityReport | None,
    ) -> tuple[_RefactorContext | None, DocRefactorPlan | None]:
        if diag_report is None:
            diag_report = self._doc_diagnoser.diag(md_path)
        original_content, _read_exc = read_refactor_source(md_path)
        if original_content is None:
            _log.debug("读取原始文件失败: %s", _read_exc)
            return None, DocRefactorPlan(
                skill_name=_skill_identity(md_path)[0],
                original_path=md_path,
                issues=[],
                improvements=[f"无法读取原始文件: {str(_read_exc)[:80]}"],
            )
        name, description, keywords, body_text, skill_dir = (
            self._doc_diagnoser.parse_document(original_content, md_path))
        return _RefactorContext(
            md_path=md_path, diag_report=diag_report, name=name,
            description=description, keywords=keywords,
            body_text=body_text, skill_dir=skill_dir), None
    def refactor(self: Self, md_path: str,
                 diag_report: DocQualityReport | None = None,
                 **optional: Any) -> DocRefactorPlan:
        raw_md_path = md_path
        try:
            options = _RefactorOptions.from_optional(**optional)
        except TypeError as _e:
            return DocRefactorPlan(
                original_path=str(raw_md_path),
                improvements=[f"未知重构选项: {_e}"],
            )
        md_path = normalize_path_arg(md_path)
        if not isinstance(md_path, str) or not md_path.strip():
            return DocRefactorPlan(
                original_path=str(raw_md_path),
                improvements=[("md_path 必须为非空字符串路径，" f"实际 {type(raw_md_path).__name__}")],
            )
        try:
            context, _err_plan = self._prepare_refactor_context(md_path, diag_report)
            if _err_plan is not None:
                return _err_plan
            skill_name = context.name or os.path.basename(context.skill_dir)
            improved_desc, improvements = self._build_improvement_plan(
                skill_name, context.description, context.keywords,
                context.diag_report, options)
            return _assemble_refactor_plan(
                context, skill_name, improved_desc, improvements, options)
        except Exception as _e:  # noqa: BLE001 — 公共方法用错误方案返回，不得抛穿
            _log.error("refactor: 方案生成失败: %s", _e, exc_info=True)
            return DocRefactorPlan(
                skill_name=_skill_identity(md_path)[0],
                original_path=md_path,
                improvements=[f"方案生成失败: {str(_e)[:120]}"],
            )
    def _description_improvement(self: Self, skill_name: str,
                                 description: str, keywords: list[str],
                                 diag_report: DocQualityReport,
                                 options: _RefactorOptions) -> tuple[str, list[str]]:
        desc_issues = [i for i in diag_report.issues if i.category == "matching"]
        if not desc_issues:
            return description, []
        desc_result = improve_description_from_issues(
            skill_name, description, keywords, desc_issues,
            capabilities=options.capabilities,
            file_extensions=options.file_extensions,
            exclusion_scopes=options.exclusion_scopes)
        return (desc_result["description"] or description,
                list(desc_result["improvements"]))
    def _upload_compliance_fix(self: Self, skill_name: str, description: str,
                               diag_report: DocQualityReport) -> tuple[str, list[str]]:
        upload_issues = [i for i in diag_report.issues if i.category == "upload"]
        if not upload_issues:
            return description, []
        upload_fixes = fix_upload_violation_descs(skill_name, description, upload_issues)
        return (upload_fixes["description"] or description, list(upload_fixes["improvements"]))
    def _build_improvement_plan(self: Self, skill_name: str,
                                description: str,
                                keywords: list[str],
                                diag_report: DocQualityReport,
                                options: _RefactorOptions) -> tuple[str, list[str]]:
        improved_desc, improvements = self._description_improvement(skill_name, description, keywords, diag_report, options)
        improved_desc, upload_improvements = self._upload_compliance_fix(skill_name, improved_desc, diag_report)
        improvements.extend(upload_improvements)
        improvements.extend(
            f"[{issue.rule_id}] {normalize_suggestion_text(issue, 120)}"
            for issue in diag_report.issues
            if issue.suggestion and issue.severity in ("critical", "high"))
        return improved_desc, _dedupe_improvements(improvements)
    def refactor_and_save(self: Self, md_path: str,
                          output_path: str | None = None,
                          **kwargs) -> dict[str, Any]:
        _raw_output_path = output_path
        output_path = normalize_out_path(output_path)
        if _raw_output_path is not None and output_path is None:
            return _refactor_save_result(
                "error", None, "", None,
                detail=("输出路径无效（须为非空字符串）: "
                        f"{type(_raw_output_path).__name__}"))
        raw_md_path = md_path
        md_path = normalize_path_arg(md_path)
        if not isinstance(md_path, str) or not md_path.strip():
            return _refactor_save_result(
                "error", None, output_path or "", None,
                detail=("md_path 必须为非空字符串路径，" f"实际 {type(raw_md_path).__name__}"))
        try:
            plan, new_content, diag_before, _err = self._compose_save_proposal(
                md_path, output_path, **kwargs)
            if _err is not None:
                return _err
            return self._persist_save_proposal(
                md_path, output_path, plan, new_content, diag_before)
        except Exception as _e:  # noqa: BLE001 — 公共方法用结构化错误返回
            _log.error("refactor_and_save: 方案链执行失败: %s", _e, exc_info=True)
            return _refactor_save_result(
                "error", None, output_path or "", None,
                detail=f"方案链执行失败（源 SKILL.md 未改动）: {_e}")
    def _compose_save_proposal(self: Self, md_path: str,
                               output_path: str | None,
                               **kwargs) -> tuple:
        try:
            diag_before = self._doc_diagnoser.diag(md_path)
        except Exception as _e:  # noqa: BLE001 — 诊断失败结构化返回（未产方案）
            _log.error("refactor_and_save: 重构前诊断失败: %s", _e, exc_info=True)
            return None, None, None, _refactor_save_result(
                "error", None, output_path or "", None,
                detail=f"重构前诊断失败（未产方案，源文件未改动）: {_e}")
        kwargs.pop('diag_report', None)
        plan = self.refactor(md_path, diag_report=diag_before, **kwargs)
        try:
            new_content = compose_refactor_document(plan)
        except ValueError:
            new_content = ""
        return plan, new_content, diag_before, None
    def _persist_save_proposal(self: Self, md_path: str,
                               output_path: str | None, plan: DocRefactorPlan,
                               new_content: str,
                               diag_before: DocQualityReport) -> dict[str, Any]:
        out_path, _loc_detail = resolve_proposal_path(output_path, md_path, plan.skill_name)
        if _loc_detail is not None:
            return _refactor_save_result(
                "error", plan, out_path, diag_before.to_dict(),
                estimated_score=plan.estimated_score_after,
                detail=_loc_detail)
        if _blank_proposal_reason(plan, new_content) is not None:
            return _reject_empty_proposal(
                plan, new_content, diag_before, out_path)
        _write_err = write_proposal_text(out_path, new_content)
        if _write_err is not None:
            _log.error("refactor_and_save: 方案写盘失败: %s", _write_err)
            return _refactor_save_result(
                "error", plan, out_path, diag_before.to_dict(),
                estimated_score=plan.estimated_score_after,
                detail=f"方案写盘失败: {_write_err}")
        result = _refactor_save_result(
            "unverified", plan, out_path, diag_before.to_dict(),
            estimated_score=plan.estimated_score_after,
            output_path_override=output_path)
        _refresh_saved_verification(
            self, result, md_path, diag_before, new_content)
        return result
    def _verify_saved_proposal(self: Self, out_path: str, md_path: str,
                               diag_before: DocQualityReport) -> tuple:
        try:
            diag_after = self._doc_diagnoser.diag(
                out_path,
                skill_dir=_skill_identity(md_path)[1],
            )
            fatal_issue = _uv000_issue(diag_after)
            if fatal_issue is not None:
                raise ValueError(f"重构后诊断失败: {fatal_issue.description}")
            score_after = _report_overall_score(diag_after)
            score_before = _report_overall_score(diag_before)
            score_delta = (
                round(score_after - score_before, 1)
                if score_after is not None and score_before is not None else None)
            return (diag_after, score_after, diag_after.overall_grade,
                    len(diag_after.issues), score_delta)
        except Exception as e:  # noqa: BLE001 - 刻意降级：记录日志不中断主流程
            _log.warning("重构后验证失败: %s", e)
            return None, None, None, None, None
_refactorer_instance = SkillDocRefactorer()
def get_refactorer() -> SkillDocRefactorer:
    return _refactorer_instance
_ATX_HEADING_START_RE = re.compile(r"^#{1,6}(?:[ \t]|$)")
def compose_refactor_document(plan: Any) -> str:
    frontmatter = getattr(plan, "new_frontmatter", "")
    if not isinstance(frontmatter, str) or not frontmatter.strip():
        raise ValueError("方案未生成 frontmatter")
    parts: list[str] = [frontmatter.strip()]
    for section in plan.new_body_sections:
        content = (section.content or "").strip()
        if not content:
            continue
        if section.title and not _ATX_HEADING_START_RE.match(content):
            content = f"## {section.title}\n{content}"
        parts.append(content)
    new_content = "\n\n".join(parts)
    _reject_reason = _blank_proposal_reason(plan, new_content)
    if _reject_reason is not None:
        raise ValueError(_reject_reason)
    return new_content
def _refactor_skill_doc_in_memory(md_path: str,
                                  enhance_six_dim: bool,
                                  **kwargs: Any) -> dict[str, Any]:
    _log.info("refactor_skill_doc: 内存直通链(auto_apply), path=%s", md_path)
    skill_name, skill_dir = _skill_identity(md_path)
    diag_before, plan, new_content, _err = _build_in_memory_plan(md_path, kwargs)
    if _err is not None:
        return _err
    new_content, six_dim = enhance_content_six_dim(
        new_content, skill_name, enhance_six_dim)
    chain = _InMemoryChain(
        plan=plan, diag_before=diag_before, content=new_content,
        six_dim=six_dim,
        evolution_guard=capture_guard_snapshot(md_path, skill_name, skill_dir, diag_before, new_content))
    return _assemble_in_memory_result(
        chain, _execute_in_memory_apply(md_path, new_content))
def _build_in_memory_plan(md_path: str, kwargs: dict[str, Any]) -> tuple:
    diag_before = get_doc_diagnoser().diag(md_path)
    plan = get_refactorer().refactor(md_path, diag_report=diag_before, **kwargs)
    try:
        new_content = compose_refactor_document(plan)
    except ValueError:
        new_content = ""
    _blank_reason = _blank_proposal_reason(plan, new_content)
    if _blank_reason is None:
        return diag_before, plan, new_content, None
    _detail_tail = _blank_proposal_tail(plan)
    _log.error("refactor_skill_doc: %s，拒绝内存直通采纳: %s",
               _blank_reason, _detail_tail)
    return diag_before, plan, "", _refactor_save_result(
        "error", plan, None, diag_before.to_dict(),
        estimated_score=plan.estimated_score_after,
        detail=f"{_blank_reason}，拒绝采纳: {_detail_tail}")
def _execute_in_memory_apply(md_path: str, new_content: str) -> dict[str, Any]:
    try:
        return apply_refactored_doc(md_path=md_path, proposal_content=new_content, verify=True)
    except Exception as _e:  # noqa: BLE001 — 采纳失败降级为 auto_apply 错误，主结果保持 ok
        _log.warning("refactor_skill_doc: 自动采纳失败(内存直通链): %s", _e)
        return _apply_result("error", f"自动采纳执行失败: {_e}")
@dataclass(frozen=True)
class _InMemoryChain:
    plan: Any
    diag_before: Any
    content: str
    six_dim: dict[str, Any]
    evolution_guard: dict[str, Any] | None
def _assemble_in_memory_result(chain: _InMemoryChain,
                               apply_result: dict[str, Any]) -> dict[str, Any]:
    fill_evolution_guard(
        chain.evolution_guard, apply_result, chain.diag_before)
    _score_after_val = _finite_float_or_none(apply_result.get("score_after"))
    _score_before_val = _report_overall_score(chain.diag_before)
    score_delta = (
        round(_score_after_val - _score_before_val, 1)
        if _score_after_val is not None and _score_before_val is not None
        else None
    )
    _diag_after = apply_result.get("diag_after")
    _diag_after_map = _diag_after if isinstance(_diag_after, dict) else None
    result = _refactor_save_result(
        "ok", chain.plan, None, chain.diag_before.to_dict(),
        diag_after=_diag_after_map,
        estimated_score=chain.plan.estimated_score_after,
        actual_score=_score_after_val,
        actual_grade=(_diag_after_map or {}).get("overall_grade"),
        score_delta=score_delta,
        remaining_issues=(
            len(_diag_after_map.get("issues") or [])
            if _diag_after_map is not None else None),
        evolution_guard=chain.evolution_guard,
        saved=apply_result.get("status") == "ok",
        detail=apply_result.get("detail"),
        auto_apply=apply_result,
        proposal_in_memory=True,
        proposal_consumed=apply_result.get("status") == "ok",
    )
    result.update(chain.six_dim)
    if apply_result.get("status") != "ok":
        apply_result["proposal_content"] = chain.content
    return result
def _auto_apply_proposal(result: dict[str, Any], md_path: str,
                          output_path: str | None) -> None:
    evolution_guard = result.get("evolution_guard")
    if (not isinstance(evolution_guard, dict)
            or evolution_guard.get("regression_detected") is not False):
        regressed = (
            isinstance(evolution_guard, dict)
            and evolution_guard.get("regression_detected") is True)
        result["auto_apply"] = {
            "status": "skipped_regression" if regressed else "skipped_unverified",
            "applied": False,
            "detail": ("方案已判定评分退化，保留供人工审核，跳过自动采纳"
                       if regressed else
                       "方案验证不可判定，保留供人工审核，跳过自动采纳"),
        }
        return
    _proposal = result.get("output_path") or output_path
    if not (_proposal and _safe_isfile(_proposal)):
        result["auto_apply"] = _apply_result(
            "error", f"方案文件不存在，跳过自动采纳: {_proposal}")
        return
    try:
        result["auto_apply"] = apply_refactored_doc(
            md_path=md_path, proposal_path=_proposal, verify=True)
        result["proposal_consumed"] = (
            result["auto_apply"].get("status") == "ok")
        _log.info(
            "refactor_skill_doc: 自动采纳完成, status=%s",
            result["auto_apply"].get("status"),
        )
    except Exception as _e:  # noqa: BLE001 — 采纳失败不得把主结果 error 化
        result["auto_apply"] = _apply_result(
            "error", f"自动采纳执行失败: {_e}")
        _log.warning("refactor_skill_doc: 自动采纳失败: %s", _e)
def _refactor_skill_doc_impl(md_path: str,
                            output_path: str | None,
                            enhance_six_dim: bool,
                            auto_apply: bool,
                            **kwargs) -> dict[str, Any]:
    md_path, output_path, _input_err = _prepare_refactor_target(
        md_path, output_path)
    if _input_err is not None:
        return _input_err
    kwargs.pop("diag_report", None)
    try:
        ensure_entry_warmed(_skill_identity(md_path)[1],
                            None, "文档重构 refactor_skill_doc")
        _log.info("refactor_skill_doc: 开始重构, path=%s, output=%s", md_path, output_path)
        if auto_apply and output_path is None:
            return _refactor_skill_doc_in_memory(md_path, enhance_six_dim=enhance_six_dim, **kwargs)
        return _run_refactor_pipeline(md_path, output_path, enhance_six_dim, auto_apply, kwargs)
    except Exception as _e:  # noqa: BLE001
        _log.error("refactor_skill_doc 异常: %s", _e, exc_info=True)
        return _refactor_save_result(
            "error", None, output_path or "", None,
            detail=f"refactor_skill_doc 异常: {_e}")
def _prepare_refactor_target(
    md_path: Any, output_path: Any,
) -> tuple[str, str | None, dict[str, Any] | None]:
    _raw_output_path = output_path
    md_path = normalize_path_arg(md_path)
    output_path = normalize_out_path(output_path)
    if _raw_output_path is not None and output_path is None:
        _log.warning("refactor_skill_doc: 输出路径类型无效, got=%r", _raw_output_path)
        return "", None, _refactor_save_result(
            "error", None, "", None,
            detail=("输出路径无效（须为非空字符串）: "
                    f"{type(_raw_output_path).__name__}"))
    if not isinstance(md_path, str) or not md_path.strip():
        _log.warning("refactor_skill_doc: md_path 为空或类型无效, got=%r", md_path)
        return "", None, _refactor_save_result(
            "error", None, output_path or "", None,
            detail="md_path 必须为非空字符串")
    if not _safe_isfile(md_path):
        _log.warning("refactor_skill_doc: 文件不存在, path=%s", md_path)
        return md_path, output_path, _refactor_save_result(
            "error", None, output_path or "", None,
            detail=f"SKILL.md 不存在: {md_path}")
    return md_path, output_path, None
def _revalidate_enhanced_proposal(
        result: dict[str, Any], md_path: str) -> None:
    try:
        refactorer = get_refactorer()
        diag_before = refactorer._doc_diagnoser.diag(md_path)
        new_content = read_utf8_text(str(result["output_path"]))
    except Exception as exc:  # noqa: BLE001 — 增强后无法验证时禁止自动采纳
        _log.warning("refactor_skill_doc: 六维增强后方案复检失败: %s", exc)
        result["status"] = "unverified"
        result["detail"] = f"六维增强后方案复检失败，禁止自动采纳: {exc}"
        evolution_guard = result.get("evolution_guard")
        if isinstance(evolution_guard, dict):
            evolution_guard["regression_detected"] = None
            evolution_guard["verification_error"] = result["detail"]
        return
    _refresh_saved_verification(
        refactorer, result, md_path, diag_before, new_content)
def _run_refactor_pipeline(md_path: str, output_path: str | None,
                           enhance_six_dim: bool, auto_apply: bool,
                           kwargs: dict[str, Any]) -> dict[str, Any]:
    result = get_refactorer().refactor_and_save(
        md_path=md_path, output_path=output_path, **kwargs)
    if result.get("status") != "ok":
        return result
    if enhance_six_dim:
        enhance_proposal_file_six_dim(result, md_path)
        if result.get("six_dim_enhanced"):
            _revalidate_enhanced_proposal(result, md_path)
    if result.get("status") != "ok":
        return result
    if auto_apply:
        _auto_apply_proposal(result, md_path, output_path)
    return result
def refactor_skill_doc(md_path: str,
                       output_path: str | None = None,
                       enhance_six_dim: bool = True,
                       auto_apply: bool = True,
                       **kwargs) -> dict[str, Any]:
    _t0 = time.monotonic()
    try:
        _result = _refactor_skill_doc_impl(md_path, output_path, enhance_six_dim, auto_apply, **kwargs)
    except Exception:
        write_module_run(
            "skill_doc_refactor_guard", "refactor_skill_doc",
            outcome="error",
            duration_ms=(time.monotonic() - _t0) * 1000.0,
            md_file=os.path.basename(str(md_path)),
            error="fail_fast_exception",
        )
        raise
    _apply_status = None
    if isinstance(_result.get("auto_apply"), dict):
        _apply_status = _result["auto_apply"].get("status")
    _status = _result.get("status")
    write_module_run(
        "skill_doc_refactor_guard", "refactor_skill_doc",
        outcome=_refactor_outcome(_status, _apply_status),
        duration_ms=(time.monotonic() - _t0) * 1000.0,
        status=_status,
        apply_status=_apply_status,
        md_file=os.path.basename(str(md_path)),
    )
    try:
        emit_step_html("doc_refactor_plan", _skill_identity(str(md_path))[1],
                        _result)
    except Exception as _html_err:  # noqa: BLE001 — 留痕失败不得篡改主结果
        _log.warning("refactor_skill_doc: HTML 留痕失败(不阻断): %s", _html_err)
    return _result

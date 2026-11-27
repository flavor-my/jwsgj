from __future__ import annotations

import glob
import hashlib
import json
import logging
import os
import re
import tempfile
import threading
import time
from collections import OrderedDict
from collections.abc import Callable
from itertools import count
from typing import Any, NamedTuple

from jwsgj.diag_types_vocab import (
    DIAG_REPORT_DIRNAME,
    MAX_SKILL_NAME_LENGTH,
    PROJECT_ROOT_MARKERS,
)
from jwsgj.log_config import locked_artifact, log_swallowed
from jwsgj.runtime_scope import (
    LEGACY_BACKUP_DIR_NAME,
    RUNTIME_DIR_NAME,
    STATE_DIR_NAME,
    canonical_path,
    expand_git_bash_path,
    is_real_skill_dir,
    is_runtime_temp_path,
    is_under_root,
    normalize_skill_dir,
    safe_ns,
)

try:
    import coverage as _cov_mod
except ImportError as _imp_err:
    logging.getLogger(__name__).debug("[runtime_paths] 导入失败，降级占位 None: %s", _imp_err)
    _cov_mod = None
_LOGGER = logging.getLogger(__name__)
def _text_path(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    try:
        return os.fsdecode(os.fspath(value))
    except (TypeError, ValueError) as _e:
        log_swallowed(__name__, _e, context="_text_path:TypeError,ValueError")
        return ""
def _basename_text(name: Any) -> str:
    basename = os.path.basename(_text_path(name))
    return "" if basename in {".", ".."} else basename
def optional_artifact_path(resolver, skill_dir: str, label: str) -> str:
    try:
        return resolver(skill_dir)
    except (RuntimeError, OSError, ValueError, TypeError) as exc:
        _LOGGER.warning("[CodeFeedback] %s 落点解析失败，降级为空路径: %s",
                       label, exc)
        return ""
def feedback_enhancement_log_context(skill_dir: str) -> tuple[str, str]:
    normalized = normalize_skill_dir(skill_dir)
    return normalized, normalized
__all__ = [
    "ARTIFACT_DEST_CONTRACT",
    "BACKUP_SUBDIR_NAME",
    "EVOLUTION_AUX_ARTIFACTS",
    "EVOLUTION_EVENTS_FILENAME",
    "EVOLUTION_EVENTS_KEEP_ROUNDS",
    "EVOLUTION_EVENTS_KEEP_UNSCOPED",
    "EVOLUTION_EVENTS_MAX_BYTES",
    "EVOLUTION_REPORT_FILENAME",
    "EVOLUTION_ROOT_ARTIFACTS",
    "EVOLUTION_SCRATCH_DIRNAME",
    "EVOLUTION_STATE_FILENAME",
    "EVOLUTION_STATE_SECTIONS",
    "EVOLUTION_STREAM_ARTIFACTS",
    "HTML_DIR_ENV_VAR",
    "HTML_REPORT_DIR_NAME",
    "JSON_ROOT_ENV_VAR",
    "PIPELINE_STATE_FILENAME",
    "SKILL_SEARCH_ENV_VAR",
    "SOURCE_LAYOUT_ROOT_NAMES",
    "STATE_ROOT_ENV_VAR",
    "TEMP_DIR_ENV_VAR",
    "TRIGGER_ENFORCEMENT_FILENAME",
    "WORKSPACE_CONTAINERS_ENV_VAR",
    "WORKSPACE_ENV_VAR",
    "ProjectPathError",
    "adjustment_plan_path",
    "ai_review_verdicts_path",
    "append_evolution_event",
    "append_evolution_events",
    "approved_adjustments_path",
    "artifact_lock_path",
    "baseline_data_dir",
    "baseline_session_id",
    "canonical_json_artifact_dir",
    "code_feedback_log_path",
    "consumption_state_path",
    "cv_conclusion_history_path",
    "cv_uncertain_path",
    "d4_registry_path",
    "describe_evolution_artifacts",
    "detect_package_root",
    "detect_workspace",
    "diag_intermediate_dir",
    "enhancement_log_path",
    "ensure_artifact_root_inside_workspace",
    "ensure_path_outside_skill_root",
    "epoch_anchor_dir",
    "evidence_weights_path",
    "evolution_artifact_path",
    "evolution_events_path",
    "evolution_events_stats",
    "evolution_report_path",
    "evolution_scratch_dir",
    "evolution_section_name",
    "evolution_section_of",
    "evolution_state_path",
    "feedback_enhancement_log_context",
    "feedback_history_path",
    "first_json_artifact",
    "fixer_experiences_path",
    "fp_rules_path",
    "fp_suppression_path",
    "fp_tracker_path",
    "fp_tracker_rules_path",
    "get_backup_base",
    "get_html_report_base",
    "get_jinhua_dir",
    "get_legacy_backup_roots",
    "get_skill_backup_roots",
    "get_temp_base",
    "get_temp_dir",
    "get_workspace_output_dir",
    "governance_acceptance_path",
    "governance_baseline_path",
    "governance_decisions_path",
    "hallucination_registry_path",
    "human_confirmations_path",
    "incremental_snapshot_dir",
    "infer_project_root",
    "is_artifact_destination_allowed",
    "is_dir_creation_allowed",
    "is_own_skill_root",
    "is_path_within_skill",
    "is_workspace_root_available",
    "iter_sibling_session_roots",
    "json_artifact_candidates",
    "json_artifact_dir",
    "json_artifact_glob",
    "json_artifact_path",
    "json_artifact_path_candidates",
    "json_root_dir",
    "legacy_artifact_root",
    "legacy_json_artifact_path",
    "legacy_report_dirs",
    "lifecycle_state_dir",
    "load_evolution_events",
    "make_temp_dir",
    "method_adjustments_path",
    "metrics_baseline_dir",
    "normalize_project_root",
    "normalize_skill_name",
    "optional_artifact_path",
    "own_skill_root",
    "path_scoped_namespace",
    "read_evolution_section",
    "read_evolution_state",
    "redirect_host_coverage_data",
    "report_artifact_dir",
    "resolve_direct_output_path",
    "resolve_html_report_path",
    "resolve_session_root_from_artifact_path",
    "resolve_skill_dir",
    "resolve_skill_reference",
    "resolve_workspace_root",
    "sanitize_skill_name",
    "skill_dir_or_fallback",
    "skill_search_roots",
    "solidify_ssot_path",
    "source_import_roots",
    "stage_json_artifact_path",
    "state_home_root",
    "subprocess_noartifact_env",
    "t5_baseline_path",
    "threshold_history_path",
    "trigger_keywords_path",
    "update_evolution_section",
    "version_history_path",
    "warning_history_path",
    "write_evolution_section",
    "zero_backlog_ledger_path",
]
EVOLUTION_STATE_FILENAME = "evolution_state.json"
EVOLUTION_EVENTS_FILENAME = "evolution_events.jsonl"
EVOLUTION_REPORT_FILENAME = "retrospective_report.json"
# 事件流是 append-only 审计流水：单条约 0.4KB，4MB 约容纳 9000 条
# （按实测 300KB/天约 13 天窗口）。唯一消费者 ``_round_receipts`` 只取当前
# 轮回执，保留窗口远大于其需求；设预算的目的是让全量读取的耗时与磁盘占用
# 都有上界，不在无界增长下退化。
EVOLUTION_EVENTS_MAX_BYTES = 4 * 1024 * 1024
# 双层保留契约：先按轮次保留最近 N 轮（消费者的匹配单位），灰数据（无轮次
# 回执）只留最近 M 条；两者都满足后若仍超 ``EVOLUTION_EVENTS_MAX_BYTES``，
# 再由 ``prune_jsonl_file`` 按字节兜底。轮次优先是因为消费者按轮次精确匹配，
# 单一字节判据会在单轮超大时把前几轮全裁掉（保留窗口剧烈抖动）。
EVOLUTION_EVENTS_KEEP_ROUNDS = 20
EVOLUTION_EVENTS_KEEP_UNSCOPED = 200
EVOLUTION_SCRATCH_DIRNAME = "jinhua_scratch"
EVOLUTION_STATE_SECTIONS: dict[str, str] = {
    "enhancement_log": "enhancement_log.json",
    "feedback_history": "feedback_history.json",
    "growth_history": "_growth_history.json",
    "finding_closure": "log_finding_closure.json",
    "enhancement_snapshots": "_enhancement_snapshots.json",
    "coordinator_state": "_coordinator_state.json",
    "method_adjustments": "method_adjustments.json",
    "approved_adjustments": "_ai_approved_adjustments.json",
    "threshold_history": "_threshold_adjustment_history.json",
    "template_meta": "_template_meta.json",
    "code_feedback_log": "code_feedback_log.json",
    "fn_probe_history": "_fn_probe_history.json",
    "probe_template_candidates": "_probe_template_candidates.json",
    "probe_templates": "_probe_templates.json",
}
EVOLUTION_AUX_ARTIFACTS: dict[str, str] = {
    "fp_rules": "fp_rules.json",
    "fp_suppression": "fp_suppression.json",
    "fp_tracker": "fp_tracker.json",
    "fp_tracker_rules": "fp_tracker_rules.json",
    "fixer_experiences": "_fixer_experiences.json",
    "evidence_weights": "evidence_weights.json",
    "threshold_history": "rule_threshold_history.json",
    "solidify_ssot": "_solidify_ssot.json",
    "hallucination_registry": "_hallucination_registry.json",
    "human_confirmations": "_human_confirmations.json",
    "consumption_state": "consumption_state.json",
    "warning_history": "warning_history.json",
    "version_history": "_version_history.json",
    "trigger_keywords": "trigger_keywords_custom.json",
    "zero_backlog_ledger": "zero_backlog_ledger.jsonl",
    "ai_review_verdicts": "ai_review_verdicts.jsonl",
    "cv_conclusion_history": "cv_conclusion_history.jsonl",
}
EVOLUTION_STREAM_ARTIFACTS: dict[str, str] = {
    key: EVOLUTION_AUX_ARTIFACTS[key]
    for key in ("zero_backlog_ledger", "ai_review_verdicts",
                "cv_conclusion_history")
}
EVOLUTION_ROOT_ARTIFACTS: frozenset[str] = frozenset({
    EVOLUTION_STATE_FILENAME,
    EVOLUTION_EVENTS_FILENAME,
    EVOLUTION_REPORT_FILENAME,
    *EVOLUTION_AUX_ARTIFACTS.values(),
    "lifecycle_state",
})
HTML_DIR_ENV_VAR = "JWSGJ_HTML_OUT"
HTML_REPORT_DIR_NAME = "htm"
BACKUP_SUBDIR_NAME = "_backups"
PIPELINE_STATE_FILENAME = "active-pipeline.json"
TRIGGER_ENFORCEMENT_FILENAME = "trigger_enforcement.json"
_TEMP_BASE_CACHE: OrderedDict = OrderedDict()
_JINHUA_DIR_CACHE: OrderedDict = OrderedDict()
_HTML_BASE_CACHE: OrderedDict = OrderedDict()
_JINHUA_DIRNAME = STATE_DIR_NAME
_JINHUA_UNROOTED_SUBDIR = "jinhua_unrooted"
_PROJECT_MARKERS = PROJECT_ROOT_MARKERS
_DEFAULT_ARTIFACT_CONTEXT = "运行时产物"
STATE_ROOT_ENV_VAR = "JWSGJ_STATE_ROOT"
TEMP_DIR_ENV_VAR = "JWSGJ_TEMP_ROOT"
JSON_ROOT_ENV_VAR = "JWSGJ_JSON_ROOT"
WORKSPACE_ENV_VAR = "WORKSPACE_DIR"
WORKSPACE_CONTAINERS_ENV_VAR = "JWSGJ_WORKSPACE_CONTAINERS"
_SKILL_ROOT = os.path.realpath(os.path.dirname(os.path.abspath(__file__)))
_SKILL_ROOT_IDENTITY = os.path.normcase(_SKILL_ROOT)
SKILL_SEARCH_ENV_VAR = "JWSGJ_SKILLS_ROOTS"
def own_skill_root() -> str:
    return _SKILL_ROOT
def is_own_skill_root(path: str | os.PathLike | None) -> bool:
    if not path:
        return False
    return _path_identity(path) == _SKILL_ROOT_IDENTITY
def _skill_search_root_candidates() -> list[str]:
    roots: list[str] = []
    env = os.environ.get(SKILL_SEARCH_ENV_VAR, "")
    if env:
        roots.extend(expand_git_bash_path(os.path.expanduser(p.strip()))
                     for p in env.split(os.pathsep) if p.strip())
    _parent = os.path.dirname(_SKILL_ROOT)
    _grand = os.path.dirname(_parent)
    roots.extend((
        _parent,
        os.path.join(_grand, "target_skills"),
        os.path.join(_parent, "skills"),
        os.path.join(_grand, "skills"),
    ))
    try:
        roots.append(os.getcwd())
    except OSError as exc:
        log_swallowed(__name__, exc, context="skill_search_roots:OSError")
    try:
        ws = resolve_workspace_root()
    except RuntimeError as exc:
        log_swallowed(__name__, exc, context="skill_search_roots:RuntimeError")
        ws = ""
    if ws:
        roots.append(ws)
    return roots
def _existing_search_root_identity(root: str) -> tuple[str, str] | None:
    try:
        absolute = os.path.abspath(root)
        real = canonical_path(absolute)
    except (OSError, TypeError, ValueError) as exc:
        log_swallowed(__name__, exc, context="skill_search_roots:OSError,TypeError,ValueError")
        return None
    return (real, absolute) if os.path.isdir(real) else None
def skill_search_roots() -> list[str]:
    seen: set[str] = set()
    ordered: list[str] = []
    for root in _skill_search_root_candidates():
        resolved = _existing_search_root_identity(root)
        if resolved is None:
            continue
        real, absolute = resolved
        if real in seen:
            continue
        seen.add(real)
        ordered.append(absolute)
    return ordered
def _artifact_host_roots() -> tuple[str, ...]:
    hosts: list[str] = []
    try:
        ws = resolve_workspace_root()
    except RuntimeError as _e:
        _LOGGER.debug("[artifacts] 工作空间不可用，仅按 Temp 段判定: %s", _e)
        ws = ""
    if ws:
        ws_root = os.path.abspath(ws)
        hosts.append(os.path.join(ws_root, RUNTIME_DIR_NAME))
        hosts.append(os.path.join(ws_root, HTML_REPORT_DIR_NAME))
    try:
        hosts.append(json_root_dir())
    except (RuntimeError, ValueError) as _e:
        _LOGGER.debug("[artifacts] 阶段快照根不可用（跳过）: %s", _e)
    return tuple(host for host in hosts if host)
def _is_intermediate_dir(root: str) -> bool:
    parts = [p.lower() for p in os.path.normpath(root).replace("\\", "/").split("/")]
    if not ("_intermediate" in parts or "htm" in parts
            or any(re.fullmatch(r"report_\d+", part) for part in parts)):
        return False
    if any(is_under_root(root, host) for host in _artifact_host_roots()):
        return True
    return is_runtime_temp_path(root)
def _is_bare_skill_name(ref: str) -> bool:
    leaf = ref.rstrip("/\\")
    if not leaf or leaf in (".", ".."):
        return False
    if os.path.isabs(leaf) or os.path.splitdrive(leaf)[0]:
        return False
    return not os.path.dirname(leaf)
def resolve_skill_reference(ref: str | os.PathLike | None) -> str | None:
    if ref is None:
        return None
    try:
        raw = os.fsdecode(os.fspath(ref)).strip()
    except (TypeError, ValueError) as exc:
        log_swallowed(__name__, exc, context="resolve_skill_reference:TypeError,ValueError")
        return None
    if not raw:
        return None
    raw = os.path.expanduser(raw)
    raw = expand_git_bash_path(raw)
    norm_raw = os.path.normpath(raw)
    candidates: list[str] = [os.path.abspath(raw)]
    if os.path.basename(norm_raw).lower() == "skill.md":
        candidates.append(os.path.dirname(os.path.abspath(norm_raw)))
    for cand in candidates:
        if os.path.isdir(cand) and is_real_skill_dir(cand):
            return cand
    if not _is_bare_skill_name(raw):
        return None
    leaf = os.path.basename(raw.rstrip("/\\"))
    query = normalize_skill_name(leaf)
    for root in skill_search_roots():
        hit = _match_skill_in_root(root, raw, leaf, query)
        if hit is not None:
            return hit
    return None
def _match_skill_in_root(root: str, raw: str, leaf: str, query: str) -> str | None:
    direct = os.path.join(root, raw)
    if os.path.isdir(direct) and is_real_skill_dir(direct):
        return os.path.abspath(direct)
    try:
        entries = os.listdir(root)
    except OSError as exc:
        log_swallowed(__name__, exc, context="resolve_skill_reference:OSError")
        return None
    matches: list[str] = []
    for entry in entries:
        if query:
            if normalize_skill_name(entry) != query:
                continue
        elif entry.casefold() != leaf.casefold():
            continue
        path = os.path.join(root, entry)
        if os.path.isdir(path) and is_real_skill_dir(path):
            matches.append(os.path.abspath(path))
    if len(matches) == 1:
        return matches[0]
    if matches:
        _LOGGER.warning(
            "[resolve_skill_reference] 技能名 %r 在搜索根 %s 命中多个目录，"
            "拒绝按枚举顺序选择；请改用精确技能路径: %s",
            raw, root, sorted(matches))
    return None
_PATH_CACHE_LOCK = threading.Lock()
_PATH_CACHE_MAX = 32
def _path_cache_key(skill_dir, extra_env_vars: tuple = ()) -> tuple:
    _cwd = _cwd_for_error()
    return (skill_dir,
            *(os.environ.get(_evar, "") for _evar in extra_env_vars),
            os.environ.get(TEMP_DIR_ENV_VAR, ""),
            os.environ.get(WORKSPACE_ENV_VAR, ""),
            os.environ.get(WORKSPACE_CONTAINERS_ENV_VAR, ""),
            _cwd)
def _path_cache_get(cache: OrderedDict, key: tuple):
    with _PATH_CACHE_LOCK:
        hit = cache.get(key)
        if hit is not None:
            cache.move_to_end(key)
        return hit
def _path_cache_put(cache: OrderedDict, key: tuple, value: str) -> None:
    with _PATH_CACHE_LOCK:
        cache[key] = value
        if len(cache) > _PATH_CACHE_MAX:
            cache.popitem(last=False)
def _cached_path(cache: OrderedDict, key: tuple,
                 resolve: Callable[[], tuple[str, bool]]) -> str:
    hit = _path_cache_get(cache, key)
    if hit is not None:
        return hit
    value, cacheable = resolve()
    if cacheable:
        _path_cache_put(cache, key, value)
    return value
def _cwd_for_error() -> str:
    try:
        return os.getcwd()
    except OSError as _e:
        _LOGGER.debug('静默降级[_cwd_for_error:OSError]: %s: %s', type(_e).__name__, _e)
        return "<cwd 不可用>"
def ensure_path_outside_skill_root(path: str, env_var: str,
                                    context: str = _DEFAULT_ARTIFACT_CONTEXT) -> None:
    text = _text_path(path)
    if not text.strip():
        raise RuntimeError(
            f"{env_var}={path!r} 为空或不可解码，{context}落点守卫拒绝；"
            "空路径会被 abspath('') 解成进程 cwd，不能作为有效落点。")
    if is_under_root(text, _SKILL_ROOT):
        raise RuntimeError(
            f"{env_var}={text!r} 指向技能根内部，"
            f"{context}禁止落入技能根（Temp 治理契约）；"
            "请将该变量指向会话工作空间或其他隔离目录。")
def ensure_artifact_root_inside_workspace(path: str, env_var: str,
                                           context: str = _DEFAULT_ARTIFACT_CONTEXT) -> None:
    text = _text_path(path)
    if not text.strip():
        raise RuntimeError(
            f"{env_var}={path!r} 为空或不可解码，{context}落点守卫拒绝"
            f"（Temp 治理契约，不设其他位置兜底）：空路径会被 abspath('') "
            f"解成进程 cwd（{_cwd_for_error()}），不属于任何会话工作空间。")
    try:
        _real = os.path.abspath(text)
    except (OSError, ValueError, TypeError) as e:
        raise RuntimeError(
            f"{env_var}={path!r} 路径归一失败，{context}落点守卫拒绝"
            f"（Temp 治理契约，不设其他位置兜底）: {e}") from e
    ws = resolve_workspace_root()
    if ws:
        if is_path_within_skill(_real, ws):
            return
        raise RuntimeError(
            f"{env_var}={path!r} 不在会话工作空间内（当前会话工作空间：{ws!r}），"
            f"{context}落点只能是当前会话工作空间（Temp 治理契约：不设其他"
            f"位置兜底，也不放行其他会话目录，防止过程产物污染其他文件夹）。"
            f"请将该变量指向会话工作空间之内（如 "
            f"<工作空间>/{RUNTIME_DIR_NAME} 之下），或设置 "
            f"{WORKSPACE_ENV_VAR} / 在会话工作空间目录下运行以建立"
            "工作空间上下文。")
    _path_ws = _detect_workspace_from_path(_real)
    if _path_ws:
        if is_path_within_skill(_real, _path_ws):
            _LOGGER.warning(
                "[dest_gate] %s 无显式会话上下文，按路径归属会话工作空间放行: "
                "%s（工作空间 %s）", context, _real, _path_ws)
            return
        raise RuntimeError(
            f"{env_var}={path!r} 不在会话工作空间内（按路径字面值归属于 "
            f"{_path_ws!r}，但规范路径为 {_path_identity(_real)!r}）。"
            f"{context}落点守卫拒绝符号链接或目录联接逃逸；请将实际目标"
            "置于该会话工作空间之内。")
    raise RuntimeError(
        f"{env_var}={path!r} 不在会话工作空间内（未设置 {WORKSPACE_ENV_VAR}"
        f"且 cwd 不在会话工作空间中，路径也不属于任何会话工作空间），"
        f"{context}落点只能是会话工作空间（Temp 治理契约：不设其他"
        f"位置兜底，也不放行其他会话目录，防止过程产物污染其他文件夹）。"
        f"请将该变量指向会话工作空间之内（如 "
        f"<工作空间>/{RUNTIME_DIR_NAME} 之下），或设置 "
        f"{WORKSPACE_ENV_VAR} / 在会话工作空间目录下运行以建立"
        "工作空间上下文。")
class _WorkspaceDirInvalid(RuntimeError):
    pass
def resolve_workspace_root() -> str:
    ws = os.environ.get(WORKSPACE_ENV_VAR, "").strip()
    if ws:
        resolved = expand_git_bash_path(ws)
        if not os.path.isabs(os.path.normpath(resolved)):
            raise _WorkspaceDirInvalid(
                f"{WORKSPACE_ENV_VAR}={ws!r} 必须是绝对路径，收到相对路径"
                f"（cwd={_cwd_for_error()}）。相对路径会随 cwd 漂移成另一个"
                f"落点（Temp 治理契约：产物落点只能是会话工作空间，不设"
                f"其他位置兜底）。")
        try:
            ensure_path_outside_skill_root(
                resolved, WORKSPACE_ENV_VAR, context="会话工作空间与运行时产物")
        except RuntimeError as _guard_exc:
            raise _WorkspaceDirInvalid(str(_guard_exc)) from _guard_exc
        if os.path.isdir(resolved):
            return os.path.normpath(resolved)
        raise _WorkspaceDirInvalid(
            f"{WORKSPACE_ENV_VAR}={ws!r} 不是已存在的目录，会话工作空间"
            f"不可用（Temp 治理契约：产物落点只能是会话工作空间，不设"
            f"其他位置兜底）。请将其指向本会话工作空间目录，或清除该"
            f"变量以改用 cwd 探测（cwd={_cwd_for_error()}）。")
    return _detect_workspace_from_cwd()
def is_workspace_root_available() -> bool:
    try:
        return bool(resolve_workspace_root())
    except _WorkspaceDirInvalid as _ws_unavailable:
        _LOGGER.debug("[workspace] 可用性查询：会话工作空间不可用: %s",
                      _ws_unavailable)
        return False
_SESSION_NAME_ANY = "any"
_SESSION_NAME_TIMESTAMP = "timestamp"
_DEFAULT_WORKSPACE_CONTAINERS: tuple[str, ...] = (
    "lingxi-claw", "灵犀工作空间")
_DEFAULT_WORKSPACE_SESSION_POLICIES = {"lingxi-claw": _SESSION_NAME_ANY}
_WS_SESSION_DIR_RE = re.compile(r"^\d{8}-\d{2}-\d{2}-\d{2}-\d{3}$")
_NON_SESSION_CONTAINER_ENTRIES = frozenset({".trash", "shared", "users", "temp"})
def _parse_workspace_container_rule(item: str) -> tuple[str, str | None] | None:
    name, separator, raw_policy = item.partition("=")
    name = name.strip()
    if not name:
        return None
    if not separator:
        return name, None
    policy = raw_policy.strip().lower()
    if policy == "*":
        policy = _SESSION_NAME_ANY
    if policy not in (_SESSION_NAME_ANY, _SESSION_NAME_TIMESTAMP):
        _LOGGER.warning(
            "[workspace] 忽略非法容器会话名策略 %r；支持的声明为 "
            "host=any 或 host=timestamp", item)
        return None
    return name, policy
def _workspace_container_rules() -> tuple[tuple[str, str], ...]:
    rules: OrderedDict[str, list[str]] = OrderedDict()
    for name in _DEFAULT_WORKSPACE_CONTAINERS:
        rules[name.casefold()] = [
            name, _DEFAULT_WORKSPACE_SESSION_POLICIES.get(
                name.casefold(), _SESSION_NAME_TIMESTAMP)]
    raw = os.environ.get(WORKSPACE_CONTAINERS_ENV_VAR, "")
    for item in re.split(r"[,;]", raw):
        if not item.strip():
            continue
        parsed = _parse_workspace_container_rule(item)
        if parsed is None:
            continue
        name, policy = parsed
        key = name.casefold()
        if key in rules and policy is None:
            continue
        rules[key] = [name, policy or _SESSION_NAME_TIMESTAMP]
    return tuple((name, policy) for name, policy in rules.values())
def _is_workspace_container(part: str) -> bool:
    low = part.casefold()
    return any(low == name.casefold()
               for name, _policy in _workspace_container_rules())
def _is_session_form_dir(cont_name: str, name: str) -> bool:
    if not name:
        return False
    leaf = name.casefold()
    if leaf.startswith(".") or leaf in _NON_SESSION_CONTAINER_ENTRIES:
        return False
    policy: str | None = None
    for container, declared_policy in _workspace_container_rules():
        if cont_name.casefold() == container.casefold():
            policy = declared_policy
            break
    if policy is None:
        return False
    if policy == _SESSION_NAME_ANY:
        return True
    return _WS_SESSION_DIR_RE.fullmatch(name) is not None
def _detect_workspace_from_path(path: str) -> str:
    try:
        cur = os.path.abspath(expand_git_bash_path(str(path)))
    except (OSError, ValueError, TypeError) as e:
        _LOGGER.debug("[workspace] 路径探测失败（按无工作空间处理）: %s: %s", path, e)
        return ""
    parts = cur.replace("\\", "/").split("/")
    for i, part in enumerate(parts):
        if not _is_workspace_container(part):
            continue
        ws = _workspace_root_at(parts, i)
        if ws:
            return ws
    return ""
def _workspace_root_at(parts: list[str], i: int) -> str | None:
    if i + 2 > len(parts):
        return None
    if not _is_session_form_dir(parts[i], parts[i + 1]):
        return None
    ws = os.path.abspath("/".join(parts[: i + 2]))
    return ws if os.path.isdir(ws) else None
def _detect_workspace_from_cwd() -> str:
    try:
        cwd = os.getcwd()
    except OSError as e:
        _LOGGER.debug("[workspace] cwd 探测失败（按无工作空间处理）: %s", e)
        return ""
    return _detect_workspace_from_path(cwd)
def resolve_session_root_from_artifact_path(path: str) -> str:
    text = _text_path(path)
    if not text:
        return ""
    try:
        cur = os.path.abspath(expand_git_bash_path(text))
    except (OSError, ValueError) as e:
        _LOGGER.debug("[workspace] 产物路径会话根解析失败（不回收）: %s: %s", path, e)
        return ""
    return _session_root_upward(cur)
def _session_root_upward(cur: str) -> str:
    while True:
        parent = os.path.dirname(cur)
        if parent == cur:
            return ""
        session = _session_root_if_temp(cur)
        if session:
            return session
        cur = parent
def _session_form_in_container(session: str) -> tuple[str, str] | None:
    container = os.path.dirname(session)
    cont_name = os.path.basename(container)
    if not _is_workspace_container(cont_name):
        return None
    if not _is_session_form_dir(cont_name, os.path.basename(session)):
        return None
    return container, cont_name
def _session_root_if_temp(cur: str) -> str | None:
    if os.path.basename(cur).lower() != RUNTIME_DIR_NAME.lower():
        return None
    parent = os.path.dirname(cur)
    if not os.path.isdir(parent):
        return None
    if _session_form_in_container(parent) is None:
        return None
    return parent
def iter_sibling_session_roots(current_ws_root: str) -> list:
    if not current_ws_root or not os.path.isdir(current_ws_root):
        return []
    session = os.path.abspath(current_ws_root)
    form = _session_form_in_container(session)
    if form is None:
        return []
    container = form[0]
    names = _list_container_entries(container)
    if names is None:
        return []
    return _sibling_candidates(container, names, session)
def _sibling_candidates(container: str, names: list[str], session: str) -> list:
    out = []
    for name in sorted(names):
        cand = os.path.join(container, name)
        if _is_sibling_candidate(cand, session):
            out.append(cand)
    return out
def _list_container_entries(container: str) -> list[str] | None:
    try:
        return os.listdir(container)
    except OSError as e:
        _LOGGER.debug("[workspace] 同容器会话枚举失败（跳过回收）: %s: %s",
                      container, e)
        return None
def _path_identity(path: str) -> str:
    try:
        return canonical_path(path)
    except (OSError, ValueError, TypeError) as _e:
        _LOGGER.debug('[path_identity] 归一失败（降级 abspath）: %s: %s',
                      type(_e).__name__, _e)
    try:
        return os.path.normcase(os.path.abspath(str(path)))
    except (OSError, ValueError, TypeError) as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_path_identity:OSError+')
        return str(path)
def _is_sibling_candidate(cand: str, session: str) -> bool:
    if _session_form_in_container(cand) is None:
        return False
    if not is_path_within_skill(cand, os.path.dirname(cand)):
        return False
    if not os.path.isdir(cand):
        return False
    return _path_identity(cand) != _path_identity(session)
def path_scoped_namespace(root: str) -> str:
    """目标作用域命名空间（报告目录与旧布局归属识别共用）。"""
    base = safe_ns(os.path.basename(os.path.normpath(root)))
    digest = hashlib.md5(
        _path_identity(root).encode("utf-8", "replace"),
        usedforsecurity=False).hexdigest()[:8]
    return f"{base}-{digest}"
def _absolute_override(value: str, env_var: str, stray: str) -> str:
    expanded = expand_git_bash_path(value)
    normalized = os.path.normpath(expanded)
    if os.path.isabs(normalized):
        return normalized
    raise ValueError(
        f"{env_var}={value!r} 必须是绝对路径，收到相对路径 "
        f"(cwd={_cwd_for_error()})；相对路径会被消费方拼接到当前目录，"
        f"可能在意外的位置创建游离{stray}目录")
def _ensure_override_in_workspace(value: str, env_var: str,
                                  context: str) -> None:
    ensure_path_outside_skill_root(value, env_var, context=context)
    ensure_artifact_root_inside_workspace(value, env_var, context=context)
def _resolve_temp_override(override: str) -> str:
    resolved = _absolute_override(override, TEMP_DIR_ENV_VAR, "产物")
    _ensure_override_in_workspace(resolved, TEMP_DIR_ENV_VAR, "运行时产物")
    return resolved
def _temp_root_of_workspace(ws: str) -> str:
    return os.path.join(os.path.abspath(ws), RUNTIME_DIR_NAME)
def _temp_root_under_workspace(base: str) -> str | None:
    ws = resolve_workspace_root()
    if not ws:
        return None
    ws_root = _temp_root_of_workspace(ws)
    if os.path.normcase(base) == os.path.normcase(_SKILL_ROOT):
        return ws_root
    if _path_identity(base) == _path_identity(ws):
        return ws_root
    if is_real_skill_dir(base):
        return os.path.join(ws_root, path_scoped_namespace(base))
    if is_under_root(base, ws):
        return os.path.join(ws_root, path_scoped_namespace(base))
    return None
def _get_temp_base_impl(skill_dir: str | None) -> str:
    base = _normalize_skill_base(skill_dir)
    override = os.environ.get(TEMP_DIR_ENV_VAR, "").strip()
    if override:
        return _resolve_temp_override(override)
    _hit = _temp_root_under_workspace(base)
    if _hit is not None:
        return _hit
    raise RuntimeError(
        f"运行时产物根解析失败：skill_dir={base!r} 无法解析产物落点。"
        f"产物落点只能是会话工作空间（Temp 治理契约，不设其他位置兜底）。"
        f"可能原因：① 目录非真实被审计根（无 SKILL.md/__init__.py 且"
        f"无任何 .py 文件，含目录不存在）；"
        f"② 无可用工作空间（{WORKSPACE_ENV_VAR} "
        f"未设置且 cwd 不在任何已登记的宿主容器目录下）。"
        f"请传入真实技能根目录、设置 {WORKSPACE_ENV_VAR}，"
        f"或测试场景经 {TEMP_DIR_ENV_VAR} 显式指定产物根。"
    )
def _normalize_skill_base(skill_dir: str | None) -> str:
    if skill_dir is not None and not isinstance(
            skill_dir, (str, bytes, os.PathLike)):
        raise TypeError(
            f"skill_dir 必须是 str / bytes / os.PathLike / None，收到 "
            f"{type(skill_dir).__name__}: {skill_dir!r}")
    if not skill_dir:
        return _SKILL_ROOT
    expanded = expand_git_bash_path(_text_path(skill_dir))
    if not os.path.isabs(os.path.normpath(expanded)):
        raise ValueError(
            f"skill_dir 必须是绝对路径，收到相对路径 {skill_dir!r} "
            f"(cwd={_cwd_for_error()})；相对路径会被拼接到当前目录，"
            "可能在意外的位置创建产物目录")
    return os.path.realpath(os.path.abspath(expanded))
def _cache_key_dir(skill_dir: Any) -> Any:
    text = _text_path(skill_dir)
    if text.strip():
        try:
            expanded = expand_git_bash_path(text)
            if not os.path.isabs(os.path.normpath(expanded)):
                return text
            # 与 _normalize_skill_base 保持同一口径（realpath）：target_skills
            # 这类目录常是指向 user_skills 的符号链接/junction，不解析链接会让
            # 缓存键与真实落点错位（同一目录多算一份，且归档/轮次切换时
            # 可能拿到不同缓存槽位）。
            return os.path.normcase(
                os.path.realpath(os.path.abspath(expanded)))
        except (OSError, ValueError) as _e:
            log_swallowed(__name__, _e, context="_cache_key_dir:abspath")
    return text if text else skill_dir
def get_temp_base(skill_dir: str | None = None) -> str:
    key_dir = _cache_key_dir(skill_dir)
    return _cached_path(_TEMP_BASE_CACHE, _path_cache_key(key_dir),
                        lambda: (_get_temp_base_impl(skill_dir), True))
def json_root_dir(skill_dir: str | None = None) -> str:
    env = os.environ.get(JSON_ROOT_ENV_VAR, "").strip()
    if env:
        resolved = _absolute_override(env, JSON_ROOT_ENV_VAR, "过程 JSON")
        _ensure_override_in_workspace(resolved, JSON_ROOT_ENV_VAR, "过程 JSON")
        return resolved
    ws = resolve_workspace_root()
    if not ws:
        raise RuntimeError(
            f"过程 JSON 落点解析失败：无可用工作空间（{WORKSPACE_ENV_VAR} "
            "未设置且 cwd 不在任何已登记的宿主容器目录下）。"
            f"请设置 {WORKSPACE_ENV_VAR}，或经 {JSON_ROOT_ENV_VAR} 显式"
            "指定中间态落点（须位于会话工作空间内）。")
    return os.path.join(os.path.abspath(ws), DIAG_REPORT_DIRNAME)
def diag_intermediate_dir(output_dir: str) -> str:
    text = _text_path(output_dir)
    return os.path.abspath(text) if text else ""
def _default_html_report_root() -> str:
    try:
        ws = resolve_workspace_root()
    except RuntimeError as _e:
        _LOGGER.debug("[json_paths] 交付目录判定跳过（工作空间不可用）: %s", _e)
        return ""
    return os.path.join(os.path.abspath(ws), HTML_REPORT_DIR_NAME) if ws else ""
def json_artifact_dir(skill_dir: str | None = None) -> str:
    return diag_intermediate_dir(get_temp_base(skill_dir))
def canonical_json_artifact_dir(skill_dir: str | None,
                                output_dir: str | None = None) -> str:
    text = _text_path(output_dir)
    if not text:
        return json_artifact_dir(skill_dir)
    candidate = os.path.abspath(text)
    try:
        stage_root = json_root_dir(skill_dir)
    except (RuntimeError, ValueError):
        stage_root = ""
    html_root = _default_html_report_root()
    if (legacy_artifact_root(candidate)
            or (stage_root and is_under_root(candidate, stage_root))
            or (html_root and is_under_root(candidate, html_root))):
        target = json_artifact_dir(skill_dir)
        _LOGGER.warning(
            "[json_paths] 非阶段 JSON 写入已归正 Temp（zhenduan/旧布局只读）: %s -> %s",
            candidate, target)
        return target
    _ensure_override_in_workspace(candidate, "output_dir", "过程 JSON")
    return diag_intermediate_dir(candidate)
def json_artifact_path(skill_dir: str | None, name: str) -> str:
    basename = _basename_text(name)
    if not basename:
        raise ValueError(f"内部过程 JSON 需要可用的文件名: {name!r}")
    return os.path.join(json_artifact_dir(skill_dir), basename)
def stage_json_artifact_path(html_path: str, skill_dir: str | None = None) -> str:
    text = _text_path(html_path)
    basename = os.path.basename(text)
    stem, extension = os.path.splitext(basename)
    if not text or not stem or extension.lower() not in {".html", ".htm"}:
        raise ValueError(f"阶段配套 JSON 需要 HTML 文件路径: {html_path!r}")
    return os.path.join(json_root_dir(skill_dir), stem + ".json")
def legacy_json_artifact_path(skill_dir: str | None, name: str) -> str:
    legacy = _legacy_temp_artifact_dir(skill_dir)
    basename = _basename_text(name)
    if not legacy or not basename:
        return ""
    return os.path.join(legacy, basename)
def _legacy_temp_artifact_dir(skill_dir: str | None) -> str:
    try:
        return get_temp_base(skill_dir)
    except (RuntimeError, ValueError, TypeError) as _e:
        _LOGGER.debug("[json_paths] 旧布局 Temp 根不可用（跳过只读兜底）: %s", _e)
        return ""
def _legacy_json_artifact_dirs(skill_dir: str | None) -> list[str]:
    dirs: list[str] = []
    try:
        stage_root = json_root_dir(skill_dir)
        base = _normalize_skill_base(skill_dir)
        if (base and os.path.normcase(base) != _SKILL_ROOT_IDENTITY
                and is_real_skill_dir(base)):
            dirs.append(os.path.join(stage_root, path_scoped_namespace(base)))
        dirs.append(stage_root)
    except (RuntimeError, OSError, ValueError, TypeError) as _e:
        _LOGGER.debug("[json_paths] 旧 zhenduan 不可用（跳过只读兜底）: %s", _e)
    legacy = _legacy_temp_artifact_dir(skill_dir)
    if legacy:
        dirs.append(legacy)
        dirs.extend(os.path.join(legacy, *sub)
                    for sub in _LEGACY_TEMP_SUBDIRS)
    try:
        ws = resolve_workspace_root()
    except (RuntimeError, OSError, ValueError) as _e:
        _LOGGER.debug("[json_paths] 工作空间不可用（跳过其他旧布局）: %s", _e)
        ws = ""
    if ws:
        ws_root = os.path.abspath(ws)
        temp_root = os.path.join(ws_root, RUNTIME_DIR_NAME)
        dirs.extend(os.path.join(temp_root, *sub)
                    for sub in _LEGACY_TEMP_SUBDIRS)
        dirs.append(temp_root)
        dirs.extend(os.path.join(ws_root, *sub)
                    for sub in _LEGACY_WS_READ_SUBDIRS)
    unique: list[str] = []
    seen: set[str] = set()
    for directory in dirs:
        key = canonical_path(directory)
        if key in seen:
            continue
        seen.add(key)
        unique.append(directory)
    return unique
def json_artifact_glob(skill_dir: str | None, pattern: str) -> list[str]:
    pattern_text = _text_path(pattern)
    if (not pattern_text.strip() or os.path.isabs(pattern_text)
            or os.path.splitdrive(pattern_text)[0]):
        return []
    dirs: list[str] = []
    try:
        dirs.append(json_artifact_dir(skill_dir))
    except (RuntimeError, ValueError, TypeError) as _e:
        _LOGGER.warning("[json_paths] 中间态落点解析失败（仅扫旧布局）: %s", _e)
    dirs.extend(_legacy_json_artifact_dirs(skill_dir))
    found: list[str] = []
    seen_dirs: set[str] = set()
    seen_files: set[str] = set()
    for directory in dirs:
        dir_key = canonical_path(directory)
        if dir_key in seen_dirs:
            continue
        seen_dirs.add(dir_key)
        glob_pattern = os.path.join(directory, pattern_text)
        if not is_under_root(glob_pattern, directory):
            continue
        for path in glob.glob(glob_pattern):
            if not is_under_root(path, directory):
                continue
            file_key = canonical_path(path)
            if file_key in seen_files:
                continue
            seen_files.add(file_key)
            found.append(path)
    return found
def json_artifact_path_candidates(path: str) -> list[str]:
    text = _text_path(path)
    if not text:
        return []
    original = os.path.abspath(text)
    ordered = [original]
    try:
        ws = resolve_workspace_root()
        stage_root = json_root_dir()
    except (RuntimeError, OSError, ValueError, TypeError):
        return ordered
    if not ws:
        return ordered
    temp_root = os.path.join(os.path.abspath(ws), RUNTIME_DIR_NAME)
    in_stage = is_under_root(original, stage_root)
    in_temp = is_under_root(original, temp_root)
    if not in_stage and not in_temp:
        return ordered
    source_root = stage_root if in_stage else temp_root
    rel = os.path.relpath(original, source_root)
    if rel == "." or rel.startswith(".." + os.sep):
        return ordered
    rel_dir = os.path.dirname(rel)
    basename = os.path.basename(rel)
    relative_options = [rel]
    if rel_dir:
        relative_options.append(basename)
    candidates: list[str] = []
    if in_temp:
        candidates.extend(os.path.join(stage_root, option)
                          for option in relative_options)
    ws_root = os.path.abspath(ws)
    legacy_roots = [
        temp_root,
        *(os.path.join(temp_root, *sub) for sub in _LEGACY_TEMP_SUBDIRS),
        *(os.path.join(ws_root, *sub) for sub in _LEGACY_WS_READ_SUBDIRS),
    ]
    if rel_dir:
        scoped = os.path.join(temp_root, rel_dir)
        for old_sub in _LEGACY_TEMP_SUBDIRS:
            candidates.append(os.path.join(scoped, *old_sub, basename))
    for legacy_root in legacy_roots:
        candidates.extend(os.path.join(legacy_root, option)
                          for option in relative_options)
    ordered.extend(candidates)
    unique: list[str] = []
    seen: set[str] = set()
    for candidate in ordered:
        key = canonical_path(candidate)
        if key in seen:
            continue
        seen.add(key)
        unique.append(candidate)
    return unique
def first_json_artifact(skill_dir: str | None, name: str) -> str:
    for cand in json_artifact_candidates(skill_dir, name):
        if os.path.isfile(cand):
            return cand
    return ""
def json_artifact_candidates(skill_dir: str | None, name: str) -> list[str]:
    basename = _basename_text(name)
    if not basename:
        return []
    ordered: list[str] = []
    try:
        ordered.append(json_artifact_path(skill_dir, basename))
    except (RuntimeError, ValueError, TypeError) as _e:
        _LOGGER.warning("[json_paths] 新落点解析失败（仅读旧布局）: %s", _e)
    ordered.extend(os.path.join(directory, basename)
                   for directory in _legacy_json_artifact_dirs(skill_dir))
    unique: list[str] = []
    seen: set[str] = set()
    for path in ordered:
        key = canonical_path(path)
        if key in seen:
            continue
        seen.add(key)
        unique.append(path)
    return unique
def legacy_report_dirs(skill_dir: str | None = None) -> list[str]:
    base = _normalize_skill_base(skill_dir)
    try:
        ws = resolve_workspace_root()
    except (RuntimeError, OSError, ValueError) as _ws_exc:
        _LOGGER.debug("[runtime_paths] 旧布局枚举跳过（工作空间不可用）: %s",
                      _ws_exc)
        ws = ""
    skill_subdirs: tuple[tuple[str, ...], ...] = (
        ("report_34",), ("report_34", "_intermediate"),
        ("_intermediate",), (HTML_REPORT_DIR_NAME,),
        *((RUNTIME_DIR_NAME, *sub) for sub in _LEGACY_TEMP_SUBDIRS),
        (RUNTIME_DIR_NAME, HTML_REPORT_DIR_NAME),
    )
    roots: list[tuple[str, tuple[tuple[str, ...], ...]]] = [(base, skill_subdirs)]
    if ws:
        ws_root = os.path.abspath(ws)
        roots.append((os.path.join(ws_root, RUNTIME_DIR_NAME),
                      _LEGACY_WS_READ_SUBDIRS))
    found: list[str] = []
    seen: set[str] = set()
    for root, subdirs in roots:
        for sub in subdirs:
            cand = os.path.join(root, *sub)
            key = canonical_path(cand)
            if key in seen or not os.path.isdir(cand):
                continue
            seen.add(key)
            found.append(cand)
    return found
def get_backup_base(skill_dir: str | None = None) -> str:
    base = get_temp_base(skill_dir)
    path = os.path.join(base, BACKUP_SUBDIR_NAME)
    ensure_path_outside_skill_root(path, "get_backup_base", context="备份文件")
    if not is_path_within_skill(path, base):
        raise RuntimeError(
            f"备份根 {path!r} 不在产物根 {base!r} 内，已拒绝写入"
            f"（产物治理契约：备份文件只能落会话工作空间 "
            f"<工作空间>/{RUNTIME_DIR_NAME}/{BACKUP_SUBDIR_NAME}）")
    return path
def _resolve_html_override(env: str) -> str:
    resolved = _absolute_override(env, HTML_DIR_ENV_VAR, "报告")
    _ensure_override_in_workspace(resolved, HTML_DIR_ENV_VAR, "HTML 可视化报告")
    _legacy = legacy_artifact_root(resolved)
    if _legacy:
        raise RuntimeError(
            f"{HTML_DIR_ENV_VAR}={env!r} 指向旧布局产物目录 {_legacy!r}，"
            f"HTML 报告落点只能是 <工作空间>/{HTML_REPORT_DIR_NAME} 或其他"
            "非旧布局目录（Temp/htm 等旧组合已停用，否则与写入守卫自相矛盾）")
    try:
        os.makedirs(resolved, exist_ok=True)
    except OSError as e:
        raise RuntimeError(
            f"{HTML_DIR_ENV_VAR}={env!r} 目录创建失败，HTML 报告落点"
            f"不可用（Temp 治理契约：不设兜底回退）: {e}") from e
    if not os.access(resolved, os.W_OK):
        raise RuntimeError(
            f"{HTML_DIR_ENV_VAR}={env!r} 不可写，HTML 报告落点"
            "不可用（Temp 治理契约：不设兜底回退）")
    return resolved
def _get_html_report_base_impl() -> str:
    env = os.environ.get(HTML_DIR_ENV_VAR, "").strip()
    if env:
        return _resolve_html_override(env)
    ws = resolve_workspace_root()
    if not ws:
        raise RuntimeError(
            f"HTML 报告落点解析失败：无可用工作空间（{WORKSPACE_ENV_VAR} "
            "未设置且 cwd 不在任何已登记的宿主容器目录下）。"
            f"请设置 {WORKSPACE_ENV_VAR}，或经 {HTML_DIR_ENV_VAR} 显式"
            "指定报告落点（须位于会话工作空间内）。")
    return os.path.join(os.path.abspath(ws), HTML_REPORT_DIR_NAME)
def get_html_report_base() -> str:
    return _cached_path(
        _HTML_BASE_CACHE,
        _path_cache_key(None, extra_env_vars=(HTML_DIR_ENV_VAR,)),
        lambda: (_get_html_report_base_impl(), True))
def _jinhua_unrooted_fallback(root: str) -> str:
    ws = resolve_workspace_root()
    if not ws:
        ws = _detect_workspace_from_path(root)
        if ws:
            _LOGGER.warning(
                "[jinhua_paths] 无显式会话上下文，按路径归属会话工作空间归口: "
                "skill_dir=%s 工作空间=%s", root, ws)
    if not ws:
        raise RuntimeError(
            f"jinhua 落点解析失败：skill_dir={root!r} 及其上级均无受支持项目标记，"
            f"且无可用会话工作空间（{WORKSPACE_ENV_VAR} 未设置、cwd 不在 "
            "任何已登记的宿主容器目录下，路径也不属于任何会话"
            "工作空间）。"
            "jinhua 与过程产物落点只能是会话工作空间（Temp 治理契约，"
            "不设其他位置兜底）；请传入真实技能根或设置 "
            f"{WORKSPACE_ENV_VAR}。")
    if is_under_root(root, ws):
        return ""
    return os.path.join(
        _temp_root_of_workspace(ws), _JINHUA_UNROOTED_SUBDIR,
        _unrooted_namespace(root))
def _unrooted_namespace(root: str) -> str:
    base = safe_ns(os.path.basename(os.path.normpath(root))) or "skill"
    digest = hashlib.sha1(
        os.path.normcase(os.path.abspath(root)).encode("utf-8"),
        usedforsecurity=False,
    ).hexdigest()[:8]
    return f"{base}-{digest}"
def _find_ancestor_marker_root(root: str, markers: tuple[str, ...]) -> str:
    _walker = root
    _temp_root = canonical_path(tempfile.gettempdir())
    while True:
        _walker = os.path.dirname(_walker)
        if _walker in (os.path.dirname(_walker), ""):
            return ""
        if canonical_path(_walker) == _temp_root:
            return ""
        if any(os.path.exists(os.path.join(_walker, marker))
               for marker in markers):
            return _walker
def _is_project_root(root: str) -> bool:
    return any(os.path.exists(os.path.join(root, marker))
               for marker in _PROJECT_MARKERS)
def _is_flat_artifact_scope(intermediate_dir: str) -> bool:
    if not intermediate_dir:
        return False
    roots: list[str] = []
    temp_root = _workspace_temp_root()
    if temp_root:
        roots.append(temp_root)
    try:
        roots.append(json_root_dir())
    except (RuntimeError, OSError, ValueError, TypeError) as _e:
        _LOGGER.debug("[runtime_paths] 扁平布局判定跳过 zhenduan: %s", _e)
    path_ws = _detect_workspace_from_path(intermediate_dir)
    if path_ws:
        roots.append(os.path.join(os.path.abspath(path_ws), RUNTIME_DIR_NAME))
        try:
            current_ws = resolve_workspace_root()
        except RuntimeError:
            current_ws = ""
        if not current_ws or _path_identity(path_ws) != _path_identity(current_ws):
            roots.append(os.path.join(os.path.abspath(path_ws), DIAG_REPORT_DIRNAME))
    return any(root and is_under_root(intermediate_dir, root)
               for root in roots)
def resolve_skill_dir(intermediate_dir: str) -> str:
    text = _text_path(intermediate_dir)
    if not text:
        return ""
    if _is_flat_artifact_scope(text):
        _LOGGER.warning(
            "[runtime_paths] 中间目录 %s 属于新扁平布局（不含技能根信息），"
            "不按目录层级反推 skill_dir（避免 jinhua/FP 规则库落点错位）",
            intermediate_dir)
        return ""
    skill_dir = text
    for _ in range(3):
        skill_dir = os.path.dirname(skill_dir)
    if _is_project_root(skill_dir):
        return skill_dir
    found = _find_ancestor_marker_root(text, _PROJECT_MARKERS)
    if found and found != skill_dir:
        _LOGGER.warning("[runtime_paths] skill_dir 推导错位: %s -> 修正为 %s",
                        skill_dir, found)
        return found
    _LOGGER.warning(
        "[runtime_paths] skill_dir 推导结果 %s 未找到受支持项目标记，"
        "FP 规则库可能加载错位", skill_dir)
    return skill_dir
def _jinhua_orphan_fallback(root: str) -> str | None:
    _fallback = _jinhua_unrooted_fallback(root)
    if _fallback:
        _LOGGER.warning(
            "[jinhua_paths] skill_dir %s 及其上级均无受支持项目标记"
            "（非真实项目根），jinhua 归口会话工作空间防外部污染: %s",
            root, _fallback)
        return _fallback
    _LOGGER.warning(
        "[jinhua_paths] skill_dir %s 及其上级均无受支持项目标记，"
        "但原路径已在会话工作空间内（受信区），jinhua 目录保持原路径",
        root)
    return None
def _resolve_jinhua_root(skill_dir: str) -> tuple[str, bool, str | None]:
    _root = os.path.realpath(os.path.abspath(skill_dir))
    if (_root == _SKILL_ROOT
            and os.environ.get(STATE_ROOT_ENV_VAR, "").strip()):
        return _root, True, _state_home_jinhua()
    if _is_project_root(_root):
        return _root, True, None
    _found = _find_ancestor_marker_root(_root, _PROJECT_MARKERS)
    if _found:
        _LOGGER.warning(
            "[jinhua_paths] skill_dir 缺少项目标记，jinhua 目录归正到项目根: "
            "%s -> %s", _root, _found)
        return _found, False, None
    _fallback = _jinhua_orphan_fallback(_root)
    return _root, False, (_fallback or None)
def state_home_root() -> str:
    env = os.environ.get(STATE_ROOT_ENV_VAR, "").strip()
    if not env:
        return _SKILL_ROOT
    return _absolute_override(env, STATE_ROOT_ENV_VAR, "状态")
def _state_home_jinhua() -> str:
    """反哺进化产物的唯一归口。

    反哺进化是跨目标通用的长期账本：被治理目标无论是本包自身、外部技能
    还是 python 项目，产物集固定且共用同一个 ``jinhua``（不设 per-target
    容器层，避免账本随治理目标数量无限膨胀）。
    """
    return os.path.join(state_home_root(), _JINHUA_DIRNAME)
def _is_workspace_scratch_root(root: str) -> bool:
    try:
        ws = resolve_workspace_root()
    except RuntimeError as _e:
        _LOGGER.debug("[jinhua_paths] 会话工作空间不可用，按路径归属判定: %s", _e)
        ws = ""
    if ws:
        return is_under_root(root, ws)
    _path_ws = _detect_workspace_from_path(root)
    return bool(_path_ws) and is_under_root(root, _path_ws)
def _is_workspace_temp_sandbox(root: str) -> bool:
    try:
        ws = resolve_workspace_root()
    except RuntimeError as exc:
        log_swallowed(__name__, exc, context="_is_workspace_temp_sandbox:RuntimeError")
        return False
    if not ws or not is_under_root(root, ws):
        return False
    try:
        rel = os.path.relpath(canonical_path(root), canonical_path(ws))
    except (OSError, ValueError, TypeError) as exc:
        log_swallowed(
            __name__, exc,
            context="_is_workspace_temp_sandbox:relpath")
        return False
    parts = [p for p in rel.split(os.sep) if p and p != "."]
    return len(parts) >= 2 and parts[0].lower() == RUNTIME_DIR_NAME.lower()
def _is_unscoped_system_temp_root(root: str) -> bool:
    if os.environ.get(STATE_ROOT_ENV_VAR, "").strip():
        return False
    if not is_under_root(root, tempfile.gettempdir()):
        return False
    return not _is_workspace_scratch_root(root)
def _shared_state_jinhua(root: str) -> str:
    """外部被治理目标的长期状态落点：本包自己的 jinhua。"""
    path = _state_home_jinhua()
    if is_under_root(path, root):
        raise RuntimeError(
            f"状态目录 {path!r} 落入被治理技能根 {root!r} 内部，已拒绝写入"
            f"（{STATE_ROOT_ENV_VAR} 不得指向被治理技能包；状态归口只能是"
            "本治理包自己的 jinhua）。")
    return path
def _is_artifact_root(root: str) -> bool:
    try:
        artifact = json_root_dir()
    except (RuntimeError, ValueError):
        return False
    return bool(artifact) and is_under_root(root, artifact)
def _validate_jinhua_root_allowed(root: str, local: str) -> None:
    if (_is_intermediate_dir(root) or _is_artifact_root(root)
            or (is_runtime_temp_path(local)
                and not _is_workspace_temp_sandbox(root))):
        raise RuntimeError(
            f"jinhua目录被错误放入Temp下。skill_dir可能传入了intermediate_dir。"
            f"当前路径: {local}"
        )
    if _is_unscoped_system_temp_root(root):
        raise RuntimeError(
            f"jinhua 落点拒绝：skill_dir={root!r} 位于系统临时区且不在会话"
            f"工作空间内（未设置 {STATE_ROOT_ENV_VAR} 隔离），长期状态不得写入"
            "本治理技能包的 jinhua；请设置 WORKSPACE_DIR 或 "
            f"{STATE_ROOT_ENV_VAR} 后重试。")
def _get_jinhua_dir_impl(skill_dir: str) -> tuple[str, bool]:
    _root, _cacheable, _direct = _resolve_jinhua_root(skill_dir)
    if _direct is not None:
        return _direct, False
    _local = os.path.join(_root, _JINHUA_DIRNAME)
    _validate_jinhua_root_allowed(_root, _local)
    if not is_under_root(_root, _SKILL_ROOT) and not _is_workspace_scratch_root(_root):
        return _shared_state_jinhua(_root), _cacheable
    return _local, _cacheable
def get_jinhua_dir(skill_dir: str) -> str:
    if not _text_path(skill_dir).strip():
        raise ValueError(
            "skill_dir 不能为空或不可解码；jinhua 长期状态不得按进程 cwd 推导")
    key_dir = _cache_key_dir(skill_dir)
    return _cached_path(
        _JINHUA_DIR_CACHE,
        _path_cache_key(
            key_dir,
            extra_env_vars=(STATE_ROOT_ENV_VAR, JSON_ROOT_ENV_VAR),
        ),
        lambda: _get_jinhua_dir_impl(skill_dir))
def _current_coverage_file(cur) -> str:
    value = getattr(getattr(cur, "_data", None), "_filename", "")
    return value if isinstance(value, str) else ""
def _resolve_landing_realpath(cur) -> str | None:
    _cur_file = _current_coverage_file(cur)
    if not _cur_file:
        return None
    try:
        return canonical_path(_cur_file)
    except (OSError, ValueError) as _e:
        _LOGGER.debug("[host_cov] 激活采集器落点归一失败（不重定向）: %s: %s",
                      _cur_file, _e)
        return None
def _landing_in_workspace(real: str) -> bool:
    try:
        _ws = resolve_workspace_root()
    except RuntimeError as _e:
        _LOGGER.debug('静默降级[redirect_host_coverage_data:RuntimeError]: %s: %s', type(_e).__name__, _e)
        return False
    if not _ws:
        return False
    return is_under_root(real, _ws)
def _has_explicit_absolute_target(cur) -> bool:
    _raw_file = getattr(getattr(cur, "config", None), "data_file", "")
    return (isinstance(_raw_file, str) and bool(_raw_file)
            and os.path.isabs(os.path.normpath(_raw_file)))
def redirect_host_coverage_data() -> bool:
    if _cov_mod is None:
        return False
    _cur = _cov_mod.Coverage.current()
    if not _cur:
        return False
    _real = _resolve_landing_realpath(_cur)
    if _real is None:
        return False
    if _landing_in_workspace(_real):
        return False
    if (not is_under_root(_real, _SKILL_ROOT)
            and _has_explicit_absolute_target(_cur)):
        return False
    _disable_coverage_auto_save(_cur)
    return True
def _disable_coverage_auto_save(cur) -> None:
    cur._auto_save = False
    _LOGGER.info(
        "[host_cov] 宿主采集器落点不可信（技能根内/相对路径解析到工作"
        "空间外，原落点: %s），退出自动落盘已关闭（零产出）",
        _current_coverage_file(cur))
def subprocess_noartifact_env() -> dict[str, str]:
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env.pop("COVERAGE_PROCESS_START", None)
    env.pop("COVERAGE_PROCESS_CONFIG", None)
    return env
SOURCE_LAYOUT_ROOT_NAMES: tuple[str, ...] = ("src", "lib")
def source_import_roots(project_root: str) -> list[str]:
    text = _text_path(project_root)
    if not text.strip():
        return []
    root = os.path.abspath(expand_git_bash_path(text))
    roots: list[str] = []
    for name in SOURCE_LAYOUT_ROOT_NAMES:
        candidate = os.path.join(root, name)
        if os.path.isdir(candidate):
            roots.append(candidate)
    return roots
_LEGACY_TEMP_SUBDIRS: tuple[tuple[str, ...], ...] = (
    ("report_34", "_intermediate"),
    ("report_34",),
    ("_intermediate",),
)
_LEGACY_WS_READ_SUBDIRS: tuple[tuple[str, ...], ...] = (
    *_LEGACY_TEMP_SUBDIRS,
    (HTML_REPORT_DIR_NAME,),
)
_LEGACY_ARTIFACT_SUBDIRS: tuple[tuple[str, ...], ...] = (
    ("report_34",),
    ("report_34", "_intermediate"),
    ("_intermediate",),
    (RUNTIME_DIR_NAME, HTML_REPORT_DIR_NAME),
    (RUNTIME_DIR_NAME, DIAG_REPORT_DIRNAME),
    *((RUNTIME_DIR_NAME, *sub) for sub in _LEGACY_TEMP_SUBDIRS),
)
_LEGACY_ARTIFACT_SUBDIRS_BY_DEPTH: tuple[tuple[str, ...], ...] = tuple(
    sorted(_LEGACY_ARTIFACT_SUBDIRS, key=len, reverse=True))
def legacy_artifact_root(path: str) -> str:
    text = _text_path(path)
    if not text:
        return ""
    try:
        ws = resolve_workspace_root()
    except (RuntimeError, OSError, ValueError) as _ws_exc:
        _LOGGER.debug("[dest_gate] 旧布局校验跳过（工作空间不可用）: %s", _ws_exc)
        return ""
    if not ws:
        return ""
    ws_abs = os.path.abspath(ws)
    target_abs = os.path.abspath(text)
    try:
        target_real = os.path.realpath(target_abs)
        ws_real = os.path.realpath(ws_abs)
        if not is_under_root(target_real, ws_real):
            return ""
        rel = os.path.relpath(target_real, ws_real).replace("\\", "/")
    except (OSError, ValueError, TypeError) as _pe:
        _LOGGER.debug("[dest_gate] 旧布局校验路径归一失败: %s: %s", text, _pe)
        return ""
    parts = tuple(part for part in rel.split("/") if part and part != ".")
    if not parts or ".." in parts:
        return ""
    folded = tuple(part.casefold() for part in parts)
    for legacy in _LEGACY_ARTIFACT_SUBDIRS_BY_DEPTH:
        if (len(folded) >= len(legacy)
                and folded[:len(legacy)] == tuple(
                    part.casefold() for part in legacy)):
            return os.path.join(ws_abs, *legacy)
    if parts and parts[0].casefold() == RUNTIME_DIR_NAME.casefold():
        for index, part in enumerate(parts[1:], start=1):
            if part.casefold() in {
                    "report_34", "_intermediate", HTML_REPORT_DIR_NAME,
                    DIAG_REPORT_DIRNAME}:
                return os.path.join(ws_abs, *parts[:index + 1])
    return ""
def is_artifact_destination_allowed(path: str) -> bool:
    text = _text_path(path)
    if not text.strip():
        return False
    try:
        target = os.path.abspath(text)
    except (OSError, ValueError) as e:
        _LOGGER.debug("[dest_gate] 路径归一失败（按非法落点拒绝）: %s: %s", text, e)
        return False
    _legacy = legacy_artifact_root(target)
    if _legacy:
        _LOGGER.error(
            "[dest_gate] 拒绝写入旧布局产物目录 %s（新布局：内部 JSON 落 Temp，"
            "阶段快照落 <工作空间>/%s，HTML 报告落 <工作空间>/%s）: %s",
            _legacy, DIAG_REPORT_DIRNAME, HTML_REPORT_DIR_NAME, target)
        return False
    bases: list[str] = []
    override = os.environ.get(TEMP_DIR_ENV_VAR, "").strip()
    if override:
        try:
            bases.append(get_temp_base())
        except (RuntimeError, ValueError, TypeError) as _ov_exc:
            _LOGGER.warning("[dest_gate] 显式产物根不可用（按非法落点拒绝）: %s",
                            _ov_exc)
            return False
    try:
        ws = resolve_workspace_root()
    except (RuntimeError, OSError, ValueError) as _ws_exc:
        _LOGGER.debug("[dest_gate] 工作空间不可用，仅按显式产物根校验: %s",
                      _ws_exc)
        ws = ""
    if ws:
        bases.append(ws)
    return any(is_path_within_skill(target, base) for base in bases)
def is_dir_creation_allowed(path: str) -> bool:
    text = _text_path(path)
    if not text.strip():
        return False
    try:
        cur = os.path.abspath(text)
        if os.path.isdir(cur):
            return True
        if os.path.exists(cur):
            return False
        ancestor = _nearest_existing_ancestor(cur)
        if ancestor is None:
            return False
        if not os.path.isdir(ancestor):
            return False
        return os.path.dirname(ancestor) != ancestor
    except (OSError, ValueError, TypeError) as _e:
        _LOGGER.debug('静默降级[is_dir_creation_allowed:OSError]: %s: %s', type(_e).__name__, _e)
        return False
def _nearest_existing_ancestor(path: str) -> str | None:
    cur = path
    while True:
        parent = os.path.dirname(cur)
        if parent == cur:
            return None
        cur = parent
        if os.path.exists(cur):
            return cur
def _evolution_io() -> tuple[Any, Any, Any]:
    # 硬环：diag_guard_io / diag_guard_state 反向依赖本模块的 Temp 落点解析。
    from jwsgj.diag_guard_io import write_text_atomic  # lazy-by-design — 硬环断路器
    from jwsgj.diag_guard_state import read_json_artifact  # lazy-by-design — 硬环断路器
    return write_text_atomic, read_json_artifact, locked_artifact
def _evolution_skill_dir(skill_dir: Any) -> str:
    text = _text_path(skill_dir)
    if not text.strip():
        raise ValueError(
            "skill_dir 不能为空或不可解码；反哺进化产物不得按进程 cwd 推导")
    return normalize_skill_dir(text)
def evolution_state_path(skill_dir: str) -> str:
    return os.path.join(
        get_jinhua_dir(_evolution_skill_dir(skill_dir)),
        EVOLUTION_STATE_FILENAME)
def evolution_events_path(skill_dir: str) -> str:
    return os.path.join(
        get_jinhua_dir(_evolution_skill_dir(skill_dir)),
        EVOLUTION_EVENTS_FILENAME)
def evolution_report_path(skill_dir: str) -> str:
    return os.path.join(
        get_jinhua_dir(_evolution_skill_dir(skill_dir)),
        EVOLUTION_REPORT_FILENAME)
def evolution_scratch_dir(skill_dir: str) -> str:
    base = get_temp_base(_evolution_skill_dir(skill_dir))
    return os.path.join(base, EVOLUTION_SCRATCH_DIRNAME)
def evolution_section_name(domain: str, legacy_name: str) -> str:
    for section, legacy in EVOLUTION_STATE_SECTIONS.items():
        if os.path.normcase(legacy) == os.path.normcase(legacy_name):
            return section
    raise ValueError(
        f"未登记的反哺进化 section {legacy_name!r}（域 {domain!r}）；"
        f"已登记: {sorted(EVOLUTION_STATE_SECTIONS)}")
def evolution_section_of(filename: str) -> str | None:
    name = _basename_text(filename)
    if not name:
        return None
    for section, legacy in EVOLUTION_STATE_SECTIONS.items():
        if os.path.normcase(legacy) == os.path.normcase(name):
            return section
    return None
def evolution_artifact_path(skill_dir: str, name: str) -> str:
    base = _basename_text(name)
    if not base:
        raise ValueError(f"产物名不可用: {name!r}")
    folded = os.path.normcase(base)
    if folded in {os.path.normcase(n) for n in EVOLUTION_ROOT_ARTIFACTS}:
        return os.path.join(
            get_jinhua_dir(_evolution_skill_dir(skill_dir)), base)
    if evolution_section_of(base) is None:
        raise ValueError(
            f"{base!r} 不是反哺进化产物；非反哺长期状态请用 "
            "evolution_domain_dir(skill_dir, domain)")
    return evolution_state_path(skill_dir)
def read_evolution_state(skill_dir: str, *,
                         for_update: bool = False) -> dict[str, Any]:
    path = evolution_state_path(skill_dir)
    _write, read_json_artifact, _lock = _evolution_io()
    data, status, error = read_json_artifact(path, propagate_io=for_update)
    if status == "missing":
        return {}
    if status != "ok" or not isinstance(data, dict):
        if for_update:
            raise ValueError(
                f"反哺进化状态容器不可用（{status}），拒绝按空状态覆盖: "
                f"{path}: {error}")
        _LOGGER.warning(
            "[evolution_state] 容器不可用(%s)，按空状态继续: %s: %s",
            status, path, error)
        return {}
    return data
def _legacy_section_payload(skill_dir: str, section: str, *,
                            for_update: bool = False) -> Any | None:
    legacy_name = EVOLUTION_STATE_SECTIONS.get(section)
    if not legacy_name:
        return None
    legacy_path = os.path.join(get_jinhua_dir(_evolution_skill_dir(skill_dir)),
                               legacy_name)
    if not os.path.isfile(legacy_path):
        return None
    _write, read_json_artifact, _lock = _evolution_io()
    data, status, error = read_json_artifact(
        legacy_path, propagate_io=for_update)
    if status != "ok":
        if for_update:
            raise ValueError(
                f"历史 section 不可用（{status}），拒绝按空值更新: "
                f"{legacy_path}: {error}")
        _LOGGER.warning(
            "[evolution_state] 历史 section 读取失败，按缺失处理: %s: %s",
            legacy_path, error or status)
        return None
    _LOGGER.info(
        "[evolution_state] section %s 从历史独立文件读出（待下次写盘收敛）: %s",
        section, legacy_path)
    return data
def read_evolution_section(skill_dir: str, section: str,
                           default: Any = None) -> Any:
    if section not in EVOLUTION_STATE_SECTIONS:
        raise ValueError(
            f"未登记的反哺进化 section {section!r}；"
            f"已登记: {sorted(EVOLUTION_STATE_SECTIONS)}")
    state = read_evolution_state(skill_dir)
    if section in state:
        return state[section]
    legacy = _legacy_section_payload(skill_dir, section)
    return default if legacy is None else legacy
def _dump_evolution_state(payload: dict[str, Any]) -> str:
    return json.dumps(payload, ensure_ascii=False, indent=2, default=str)
def write_evolution_section(skill_dir: str, section: str, payload: Any) -> bool:
    if section not in EVOLUTION_STATE_SECTIONS:
        raise ValueError(
            f"未登记的反哺进化 section {section!r}；"
            f"已登记: {sorted(EVOLUTION_STATE_SECTIONS)}")
    try:
        path = evolution_state_path(skill_dir)
        write_text_atomic, read_json_artifact, locked_artifact = _evolution_io()
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
        with locked_artifact(path) as locked:
            if not locked:
                _LOGGER.warning(
                    "[evolution_state] 跨进程锁不可用，拒绝无锁写盘: %s", path)
                return False
            state, status, error = read_json_artifact(
                path, propagate_io=True)
            if status not in ("ok", "missing"):
                _LOGGER.warning(
                    "[evolution_state] 容器不可解析，拒绝覆盖: %s: %s",
                    path, error or status)
                return False
            if status == "ok" and not isinstance(state, dict):
                _LOGGER.warning(
                    "[evolution_state] 容器顶层非对象(%s)，拒绝覆盖: %s",
                    type(state).__name__, path)
                return False
            merged = dict(state) if isinstance(state, dict) else {}
            merged[section] = payload
            write_text_atomic(path, _dump_evolution_state(merged),
                              newline="\n")
            return True
    except (OSError, RuntimeError, ValueError, TypeError) as exc:
        _LOGGER.warning(
            "[evolution_state] section %s 写盘失败: %s", section, exc)
        return False
def update_evolution_section(skill_dir: str, section: str,
                            mutator: Callable[[Any], Any], *,
                            default: Any = None) -> tuple[bool, Any]:
    if section not in EVOLUTION_STATE_SECTIONS:
        raise ValueError(
            f"未登记的反哺进化 section {section!r}；"
            f"已登记: {sorted(EVOLUTION_STATE_SECTIONS)}")
    path = evolution_state_path(skill_dir)
    _write, _read, locked_artifact = _evolution_io()
    with locked_artifact(path) as locked:
        state = read_evolution_state(skill_dir, for_update=True)
        if section in state:
            current = state[section]
        else:
            legacy = _legacy_section_payload(
                skill_dir, section, for_update=True)
            current = default if legacy is None else legacy
        updated = mutator(current)
        if not locked:
            _LOGGER.warning(
                "[evolution_state] 跨进程锁不可用，拒绝无锁更新: %s", path)
            return False, updated
        return write_evolution_section(skill_dir, section, updated), updated
def append_evolution_event(skill_dir: str, event: Any) -> bool:
    try:
        path = evolution_events_path(skill_dir)
        _write, _read, locked_artifact = _evolution_io()
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
        line = json.dumps(event, ensure_ascii=False, default=str)
        with locked_artifact(path) as locked:
            if not locked:
                _LOGGER.warning(
                    "[evolution_events] 跨进程锁不可用，拒绝无锁追加: %s", path)
                return False
            separator = ""
            try:
                with open(path, "rb") as existing:
                    existing.seek(0, os.SEEK_END)
                    if existing.tell() > 0:
                        existing.seek(-1, os.SEEK_END)
                        if existing.read(1) not in (b"\n", b"\r"):
                            separator = "\n"
            except FileNotFoundError:
                pass
            with open(path, "a", encoding="utf-8",
                      errors="backslashreplace", newline="") as handle:
                handle.write(separator + line + "\n")
                handle.flush()
                os.fsync(handle.fileno())
    except (OSError, RuntimeError, ValueError, TypeError) as exc:
        _LOGGER.warning("[evolution_events] 事件追加失败: %s", exc)
        return False
    _prune_evolution_events(path, skill_dir)
    return True
def append_evolution_events(skill_dir: str, events: list[Any], *,
                            dedup_fields: tuple[str, ...] = (),
                            ) -> tuple[int, int]:
    if not events:
        return 0, 0
    try:
        path = evolution_events_path(skill_dir)
        _write, _read, locked_artifact = _evolution_io()
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    except (OSError, RuntimeError, ValueError, TypeError) as exc:
        _LOGGER.warning("[evolution_events] 事件流落点不可用: %s", exc)
        return 0, 0
    appended = 0
    skipped = 0
    try:
        with locked_artifact(path) as locked:
            if not locked:
                _LOGGER.warning(
                    "[evolution_events] 跨进程锁不可用，拒绝无锁追加: %s", path)
                return 0, 0
            seen: set[tuple] = set()
            if dedup_fields:
                for existing in _read_evolution_event_lines(path):
                    key = _event_dedup_key(existing, dedup_fields)
                    if key is not None:
                        seen.add(key)
            lines: list[str] = []
            for event in events:
                key = _event_dedup_key(event, dedup_fields)
                if dedup_fields and key is not None and key in seen:
                    skipped += 1
                    continue
                if dedup_fields and key is not None:
                    seen.add(key)
                lines.append(json.dumps(event, ensure_ascii=False, default=str))
            if not lines:
                return 0, skipped
            separator = ""
            try:
                with open(path, "rb") as existing:
                    existing.seek(0, os.SEEK_END)
                    if existing.tell() > 0:
                        existing.seek(-1, os.SEEK_END)
                        if existing.read(1) not in (b"\n", b"\r"):
                            separator = "\n"
            except FileNotFoundError:
                pass
            with open(path, "a", encoding="utf-8",
                      errors="backslashreplace", newline="") as handle:
                handle.write(separator + "\n".join(lines) + "\n")
                handle.flush()
                os.fsync(handle.fileno())
            appended = len(lines)
    except (OSError, RuntimeError, ValueError, TypeError) as exc:
        _LOGGER.warning("[evolution_events] 批量追加失败: %s", exc)
        return 0, 0
    _prune_evolution_events(path, skill_dir)
    return appended, skipped
def _current_round_anchor(skill_dir: str) -> str:
    """当前轮次锚（管线状态优先；读取失败按缺失降级，不抛穿）。"""
    try:
        from jwsgj.xv_intermediate_store import peek_round_start_ts
        return _text_path(peek_round_start_ts(skill_dir)).strip()
    except Exception as exc:  # noqa: BLE001 — 读不到按缺失降级
        _LOGGER.debug(
            "[evolution_events] 当前轮次锚读取失败，按缺失降级: %s", exc)
        return ""
def _event_line_anchor(line: str) -> str:
    """单行事件的轮次锚；空行/非法行/非映射返回空串（按灰数据处理）。"""
    text = line.strip()
    if not text:
        return ""
    try:
        record = json.loads(text)
    except (ValueError, RecursionError):
        return ""
    if not isinstance(record, dict):
        return ""
    return _text_path(record.get("round_start_ts")).strip()
def _read_event_lines(path: str) -> list[str] | None:
    try:
        with open(path, encoding="utf-8-sig", errors="replace",
                  newline="") as handle:
            return handle.readlines()
    except OSError as exc:
        _LOGGER.debug(
            "[evolution_events] 事件流读取失败，跳过轮次裁剪: %s: %s",
            path, exc)
        return None
def _retain_recent_rounds(path: str, skill_dir: str) -> tuple[int, int]:
    """按轮次保留最近 N 轮、灰数据只留最近 M 条；返回 (原条数, 保留条数)。

    单轮超大时轮次保证让位字节兜底：本函数只做「按轮次收缩」，之后
    ``prune_jsonl_file`` 仍会把结果裁到 ``EVOLUTION_EVENTS_MAX_BYTES``。
    """
    with locked_artifact(path) as locked:
        if not locked:
            _LOGGER.warning(
                "[evolution_events] 轮次裁剪写锁不可用，跳过: %s", path)
            return 0, 0
        lines = _read_event_lines(path)
        if lines is None:
            return 0, 0
        anchors = [_event_line_anchor(line) for line in lines]
        order: list[str] = []
        for anchor in anchors:
            if anchor and anchor not in order:
                order.append(anchor)
        keep_rounds = set(order[-EVOLUTION_EVENTS_KEEP_ROUNDS:])
        current = _current_round_anchor(skill_dir)
        if current:
            keep_rounds.add(current)
        unscoped_indexes = [
            index for index, anchor in enumerate(anchors) if not anchor]
        keep_unscoped = set(
            unscoped_indexes[-EVOLUTION_EVENTS_KEEP_UNSCOPED:])
        kept = [
            line for index, (line, anchor) in enumerate(zip(lines, anchors))
            if (anchor in keep_rounds if anchor else index in keep_unscoped)]
        if len(kept) == len(lines):
            return len(lines), len(lines)
        try:
            # 硬环：diag_guard_io 反向依赖本模块的产物根解析。
            from jwsgj.diag_guard_io import (
                write_text_atomic,  # lazy-by-design — 硬环断路器
            )
            write_text_atomic(path, "".join(kept))
        except (OSError, ValueError, TypeError) as exc:
            _LOGGER.warning(
                "[evolution_events] 轮次裁剪落盘失败（保留原文件）: %s", exc)
            return len(lines), len(lines)
        return len(lines), len(kept)
def _prune_evolution_events(path: str, skill_dir: str) -> None:
    """事件流双层保留：轮次优先 + 字节兜底。

    必须在追加写锁之外调用：``prune_jsonl_file`` 自带跨进程锁，在写锁内
    调用会把两次加锁合并成一次长持锁，放大竞争。条目已落盘，裁剪失败只
    告警不阻断（下一条追加时会重试）。
    """
    try:
        from jwsgj.log_config import prune_jsonl_file
        if not os.path.isfile(path):
            return
        before_bytes = os.path.getsize(path)
        before_events, after_events = _retain_recent_rounds(path, skill_dir)
        prune_jsonl_file(path, EVOLUTION_EVENTS_MAX_BYTES)
        after_bytes = os.path.getsize(path)
        if before_bytes != after_bytes or before_events != after_events:
            _LOGGER.info(
                "[evolution_events] 保留契约裁剪: %d -> %d 字节，%d -> %d 条"
                "（保留最近 %d 轮 + 灰数据 %d 条）",
                before_bytes, after_bytes, before_events, after_events,
                EVOLUTION_EVENTS_KEEP_ROUNDS, EVOLUTION_EVENTS_KEEP_UNSCOPED)
    except Exception as exc:  # noqa: BLE001 — 裁剪失败不得影响已落盘条目
        _LOGGER.warning(
            "[evolution_events] 事件流裁剪失败（条目已落盘）: %s", exc)
def evolution_events_stats(skill_dir: str) -> dict[str, Any]:
    """事件流保留面统计（只读，供门禁/诊断查询保留窗口健康度）。"""
    stats: dict[str, Any] = {
        "path": "",
        "bytes": 0,
        "events": 0,
        "rounds": 0,
        "unscoped": 0,
        "oldest_round": "",
        "newest_round": "",
        "budget_bytes": EVOLUTION_EVENTS_MAX_BYTES,
        "keep_rounds": EVOLUTION_EVENTS_KEEP_ROUNDS,
        "keep_unscoped": EVOLUTION_EVENTS_KEEP_UNSCOPED,
    }
    try:
        path = evolution_events_path(skill_dir)
    except (OSError, RuntimeError, ValueError) as exc:
        _LOGGER.debug("[evolution_events] 统计路径解析失败: %s", exc)
        return stats
    stats["path"] = path
    if not os.path.isfile(path):
        return stats
    try:
        stats["bytes"] = os.path.getsize(path)
    except OSError:
        return stats
    lines = _read_event_lines(path)
    if lines is None:
        return stats
    stats["events"] = len(lines)
    order: list[str] = []
    unscoped = 0
    for line in lines:
        anchor = _event_line_anchor(line)
        if not anchor:
            unscoped += 1
            continue
        if anchor not in order:
            order.append(anchor)
    stats["rounds"] = len(order)
    stats["unscoped"] = unscoped
    if order:
        stats["oldest_round"] = order[0]
        stats["newest_round"] = order[-1]
    return stats
def _event_dedup_key(event: Any, fields: tuple[str, ...]) -> tuple | None:
    if not fields or not isinstance(event, dict):
        return None
    if any(field not in event for field in fields):
        return None
    return tuple(str(event[field]) for field in fields)
def _read_evolution_event_lines(path: str) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    try:
        with open(path, encoding="utf-8-sig", errors="replace") as handle:
            for line in handle:
                text = line.strip()
                if not text:
                    continue
                try:
                    record = json.loads(text)
                except (ValueError, RecursionError):
                    continue
                if isinstance(record, dict):
                    records.append(record)
    except FileNotFoundError:
        return []
    return records
def load_evolution_events(skill_dir: str, *,
                          limit: int | None = None) -> list[dict[str, Any]]:
    try:
        path = evolution_events_path(skill_dir)
    except (OSError, RuntimeError, ValueError):
        return []
    if not os.path.isfile(path):
        return []
    events: list[dict[str, Any]] = []
    try:
        with open(path, encoding="utf-8-sig") as handle:
            for line in handle:
                text = line.strip()
                if not text:
                    continue
                try:
                    record = json.loads(text)
                except (ValueError, RecursionError) as exc:
                    _LOGGER.debug(
                        "[evolution_events] 跳过损坏行: %s: %s", path, exc)
                    continue
                if isinstance(record, dict):
                    events.append(record)
    except (OSError, UnicodeError) as exc:
        _LOGGER.warning("[evolution_events] 读取失败: %s: %s", path, exc)
        return []
    if limit is not None and limit >= 0:
        return events[-limit:] if limit else []
    return events
def artifact_lock_path(target: str) -> str:
    text = _text_path(target)
    if not text.strip():
        raise ValueError(
            "锁目标不能为空或不可解码；锁文件不得按进程 cwd 推导")
    identity = canonical_path(text)
    digest = hashlib.sha1(
        identity.encode("utf-8", errors="replace"),
        usedforsecurity=False,
    ).hexdigest()
    return os.path.join(get_temp_base(), "_locks", f"{digest}.lock")
def describe_evolution_artifacts() -> dict[str, Any]:
    return {
        "root_artifacts": sorted(EVOLUTION_ROOT_ARTIFACTS),
        "state_filename": EVOLUTION_STATE_FILENAME,
        "events_filename": EVOLUTION_EVENTS_FILENAME,
        "report_filename": EVOLUTION_REPORT_FILENAME,
        "sections": dict(EVOLUTION_STATE_SECTIONS),
        "aux_artifacts": dict(EVOLUTION_AUX_ARTIFACTS),
        "scratch_dirname": EVOLUTION_SCRATCH_DIRNAME,
    }
def _aux_artifact_path(skill_dir: str, key: str) -> str:
    return os.path.join(
        get_jinhua_dir(_evolution_skill_dir(skill_dir)),
        EVOLUTION_AUX_ARTIFACTS[key])
def evidence_weights_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "evidence_weights")
def threshold_history_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "threshold_history")
def zero_backlog_ledger_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "zero_backlog_ledger")
def ai_review_verdicts_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "ai_review_verdicts")
def consumption_state_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "consumption_state")
def warning_history_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "warning_history")
def version_history_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "version_history")
def fixer_experiences_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "fixer_experiences")
def trigger_keywords_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "trigger_keywords")
def fp_rules_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "fp_rules")
def fp_tracker_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "fp_tracker")
def fp_tracker_rules_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "fp_tracker_rules")
def fp_suppression_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "fp_suppression")
def metrics_baseline_dir(skill_dir: str) -> str:
    return os.path.join(evolution_scratch_dir(skill_dir), "baseline")
def baseline_data_dir(skill_dir: str) -> str:
    return os.path.join(evolution_scratch_dir(skill_dir), "baseline")
def t5_baseline_path(skill_dir: str) -> str:
    return os.path.join(metrics_baseline_dir(skill_dir),
                        "t5_regression_metrics.json")
def incremental_snapshot_dir(skill_dir: str) -> str:
    return os.path.join(evolution_scratch_dir(skill_dir),
                        "incremental_snapshot")
def _governance_scratch_path(skill_dir: str, name: str) -> str:
    return os.path.join(evolution_scratch_dir(skill_dir), "governance", name)
def governance_baseline_path(skill_dir: str) -> str:
    return _governance_scratch_path(skill_dir, "governance_baseline.json")
def governance_decisions_path(skill_dir: str) -> str:
    return _governance_scratch_path(skill_dir, "governance_decisions.jsonl")
def governance_acceptance_path(skill_dir: str) -> str:
    return _governance_scratch_path(skill_dir, "governance_acceptance.jsonl")
def adjustment_plan_path(skill_dir: str) -> str:
    return json_artifact_path(skill_dir, "_ai_adjustment_plan.json")
def approved_adjustments_path(skill_dir: str) -> str:
    return evolution_state_path(skill_dir)
def enhancement_log_path(skill_dir: str) -> str:
    return evolution_state_path(skill_dir)
def code_feedback_log_path(skill_dir: str) -> str:
    return evolution_state_path(skill_dir)
def feedback_history_path(skill_dir: str) -> str:
    return evolution_state_path(skill_dir)
def method_adjustments_path(skill_dir: str) -> str:
    return evolution_state_path(skill_dir)
_BASELINE_SESSION_SEQ = count()
def baseline_session_id(skill_dir: str) -> str:
    seq = os.getpid() * 1_000_000 + next(_BASELINE_SESSION_SEQ)
    ts = f"{time.strftime('%Y%m%d-%H%M%S')}.{seq:010d}"
    return f"{os.path.basename(os.path.abspath(skill_dir))}_{ts}"
def hallucination_registry_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "hallucination_registry")
def solidify_ssot_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "solidify_ssot")
def lifecycle_state_dir(skill_dir: str) -> str:
    return os.path.join(
        get_jinhua_dir(_evolution_skill_dir(skill_dir)), "lifecycle_state")
def d4_registry_path(skill_dir: str) -> str:
    return os.path.join(lifecycle_state_dir(skill_dir), "d4_registry.yaml")
def epoch_anchor_dir(skill_dir: str) -> str:
    return os.path.join(lifecycle_state_dir(skill_dir), "epoch_anchor", "v0.0")
def human_confirmations_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "human_confirmations")
def cv_conclusion_history_path(skill_dir: str) -> str:
    return _aux_artifact_path(skill_dir, "cv_conclusion_history")
def cv_uncertain_path(skill_dir: str) -> str:
    return json_artifact_path(
        normalize_skill_dir(skill_dir) if skill_dir else None,
        "_cv_uncertain_review.json")
def _workspace_temp_root() -> str | None:
    try:
        ws = resolve_workspace_root()
    except _WorkspaceDirInvalid as _ws_unavailable:
        _LOGGER.debug("[workspace] 只读枚举：会话工作空间不可用: %s",
                      _ws_unavailable)
        return None
    if not ws:
        return None
    return os.path.join(os.path.abspath(ws), RUNTIME_DIR_NAME)
def get_legacy_backup_roots() -> list:
    temp_root = _workspace_temp_root()
    if temp_root is None:
        return []
    candidates = (
        temp_root,
        os.path.join(temp_root, os.path.basename(_SKILL_ROOT)),
    )
    roots = []
    seen = set()
    for parent in candidates:
        path = os.path.join(parent, LEGACY_BACKUP_DIR_NAME)
        key = canonical_path(path)
        if key not in seen:
            seen.add(key)
            roots.append(path)
    return roots
def get_skill_backup_roots() -> list:
    try:
        if os.environ.get(TEMP_DIR_ENV_VAR, "").strip():
            return []
        temp_root = _workspace_temp_root()
        if temp_root is None or not os.path.isdir(temp_root):
            return []
        return _namespaced_backup_roots(temp_root)
    except OSError:
        _LOGGER.warning(
            "[SkillBackupRoots] per-skill 备份根枚举失败（跳过该裁剪候选通道）",
            exc_info=True)
        return []
def _namespaced_backup_roots(temp_root: str) -> list:
    roots = []
    for name in sorted(os.listdir(temp_root)):
        cand = os.path.join(temp_root, name, BACKUP_SUBDIR_NAME)
        if is_path_within_skill(cand, temp_root) and os.path.isdir(cand):
            roots.append(cand)
    return roots
def detect_package_root(filepath: str) -> str:
    text = _text_path(filepath)
    if not text.strip():
        return ""
    current = os.path.dirname(os.path.abspath(expand_git_bash_path(text)))
    while current and os.path.isfile(os.path.join(current, '__init__.py')):
        parent = os.path.dirname(current)
        if parent == current:
            break
        current = parent
    return current
def normalize_skill_name(skill_name: str | None) -> str:
    if not skill_name:
        return ""
    normalized = skill_name.strip().lower()
    normalized = re.sub(r"[^a-z0-9]+", "-", normalized)
    normalized = normalized.strip("-")
    if len(normalized) > MAX_SKILL_NAME_LENGTH:
        normalized = normalized[:MAX_SKILL_NAME_LENGTH].strip("-")
    return normalized
class ProjectPathError(ValueError):
    pass
def normalize_project_root(project_root) -> str:
    if isinstance(project_root, os.PathLike):
        try:
            project_root = os.fspath(project_root)
        except (TypeError, ValueError) as exc:
            raise ProjectPathError(
                f"Invalid project_root: {project_root!r}") from exc
    if isinstance(project_root, bytes):
        project_root = _text_path(project_root)
    if not isinstance(project_root, str) or not project_root.strip():
        raise ProjectPathError(f"Invalid project_root: {project_root!r}")
    project_root = os.path.abspath(expand_git_bash_path(project_root))
    if not os.path.isdir(project_root):
        raise ProjectPathError(f"Not a directory: {project_root}")
    return project_root
def get_temp_dir(skill_dir: str | None = None) -> str:
    text = _text_path(skill_dir)
    if not text.strip():
        return get_temp_base(None)
    return get_temp_base(os.path.abspath(expand_git_bash_path(text)))
def _sanitize_temp_prefix(prefix: str) -> str:
    cleaned = re.sub(r"[\\/:*?\"<>|\x00-\x1f]", "_", _text_path(prefix))
    cleaned = cleaned.lstrip(".")
    return cleaned or "tmp"
def make_temp_dir(prefix: str, base: str | None = None) -> str:
    base_text = _text_path(base)
    root = (_absolute_override(base_text, "make_temp_dir.base", "临时")
            if base_text else get_temp_base(None))
    _ensure_override_in_workspace(root, "make_temp_dir.base", "临时目录")
    os.makedirs(root, exist_ok=True)
    return tempfile.mkdtemp(prefix=_sanitize_temp_prefix(prefix), dir=root)
def skill_dir_or_fallback(cv) -> str | None:
    skill_dir = getattr(cv, 'skill_dir', '') or ''
    if not skill_dir:
        intermediate_dir = getattr(cv, '_intermediate_dir', '') or ''
        skill_dir = resolve_skill_dir(intermediate_dir) if intermediate_dir else ''
    if not skill_dir:
        return None
    return normalize_skill_dir(skill_dir)
class _WorkspaceCache(NamedTuple):
    key: tuple[str, str, str, str]
    path: str
_workspace_cache: _WorkspaceCache | None = None
def detect_workspace() -> str:
    global _workspace_cache
    env_key = _workspace_cache_key()
    cache = _workspace_cache
    if cache is not None and cache.key == env_key:
        return cache.path
    _workspace_cache = _WorkspaceCache(key=env_key,
                                       path=_ensure_workspace_temp_dir())
    return _workspace_cache.path
def _workspace_cache_key() -> tuple[str, str, str, str]:
    try:
        cwd = os.getcwd()
    except OSError as _e:
        log_swallowed(__name__, _e, context='detect_workspace:OSError')
        cwd = "<deleted-cwd>"
    return (os.environ.get(TEMP_DIR_ENV_VAR, "").strip(),
            os.environ.get(WORKSPACE_ENV_VAR, "").strip(),
            os.environ.get(WORKSPACE_CONTAINERS_ENV_VAR, "").strip(), cwd)
def _ensure_workspace_temp_dir() -> str:
    temp_dir = get_temp_base(os.path.dirname(os.path.abspath(__file__)))
    os.makedirs(temp_dir, exist_ok=True)
    return temp_dir
def sanitize_skill_name(skill_name: str | None) -> str:
    if not skill_name:
        return ""
    return normalize_skill_name(skill_name) or safe_ns(skill_name)
def get_workspace_output_dir(skill_name: str | None = None) -> str:
    base = detect_workspace()
    if skill_name:
        return os.path.join(base, safe_ns(skill_name))
    return base
def infer_project_root(fp: str) -> str:
    text = _text_path(fp)
    if not text.strip():
        return ""
    directory = os.path.dirname(os.path.abspath(expand_git_bash_path(text)))
    if _is_project_root(directory):
        return directory
    marked_root = _find_ancestor_marker_root(directory, _PROJECT_MARKERS)
    if marked_root:
        return marked_root
    for _ in range(5):
        parent = os.path.dirname(directory)
        if parent == directory or _ascent_blocked(parent):
            break
        directory = parent
    return directory
def _has_py_nested(directory: str, max_depth: int = 1) -> bool:
    if not directory:
        return False
    directory = os.path.abspath(directory)
    base_depth = directory.rstrip(os.sep).count(os.sep)
    for dirpath, dirs, files in os.walk(directory):
        depth = dirpath.rstrip(os.sep).count(os.sep) - base_depth
        if depth > max_depth:
            dirs[:] = []
            continue
        if any(name.lower().endswith(".py") for name in files):
            return True
        if depth >= max_depth:
            dirs[:] = []
        else:
            dirs[:] = [name for name in dirs if name != "__pycache__"]
    return False
def _ascent_blocked(parent: str) -> bool:
    if os.path.realpath(parent) == os.path.realpath(tempfile.gettempdir()):
        return True
    try:
        if len(os.listdir(parent)) > 200:
            return True
    except OSError as exc:
        _LOGGER.debug("[GF-16] 项目根上溯提前终止（父目录不可枚举）: %s: %s",
                      parent, exc)
        return True
    return not _has_py_nested(parent)
def resolve_html_report_path(explicit: str | None, filename: str) -> str:
    text = _text_path(explicit)
    if text.strip():
        target = os.path.abspath(expand_git_bash_path(text))
        if not is_artifact_destination_allowed(target):
            raise RuntimeError(
                f"HTML 报告显式落点非法: {explicit!r}——过程产物落点"
                "只能是会话工作空间（Temp 治理契约，不设其他位置兜底）；"
                "请传入会话工作空间内的路径。")
        if os.path.isdir(target):
            raise RuntimeError(
                f"HTML 报告显式落点非法（目标是目录而非文件）: {target}")
        return target
    safe_name = _basename_text(filename)
    if not safe_name or safe_name in (".", ".."):
        raise RuntimeError(f"HTML 报告文件名非法: {filename!r}")
    return os.path.join(get_html_report_base(), safe_name)
ARTIFACT_DEST_CONTRACT = (
    "产物落点只能是会话工作空间，含经工作空间守卫的 JWSGJ_TEMP_ROOT 显式产物根")
def resolve_direct_output_path(output_path) -> str:
    if not output_path:
        return ""
    if not isinstance(output_path, (str, bytes, os.PathLike)):
        _LOGGER.warning(
            "[HTMLReport] 非法 output_path 类型 %s，已降级为页内返回（不落盘）",
            type(output_path).__name__)
        return ""
    target = os.path.abspath(expand_git_bash_path(_text_path(output_path)))
    if not is_artifact_destination_allowed(target):
        raise RuntimeError(
            f"非法产物落点（{ARTIFACT_DEST_CONTRACT}）: {target}")
    if os.path.isdir(target):
        raise RuntimeError(f"非法产物落点（目标是目录而非文件）: {target}")
    return target
_REPORT_ARTIFACT_DIR_NAME = "reports"
def report_artifact_dir(kind: str = "html") -> str:
    if kind == "html":
        return get_html_report_base()
    if kind == "report":
        return os.path.join(
            get_temp_base(os.path.dirname(os.path.abspath(__file__))),
            _REPORT_ARTIFACT_DIR_NAME)
    raise ValueError(f"未知的报告产物类型: {kind!r}（仅支持 html/report）")
def is_path_within_skill(path: str, skill_dir: str) -> bool:
    try:
        root_raw = _text_path(skill_dir)
        candidate_raw = _text_path(path)
        if not root_raw.strip() or not candidate_raw.strip():
            return False
        root = canonical_path(root_raw)
        candidate = canonical_path(candidate_raw)
        return os.path.commonpath((root, candidate)) == root
    except (OSError, ValueError, TypeError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc, context='is_path_within_skill:OSError')
        return False

from __future__ import annotations

import hashlib
import json
import logging
import os
import re
import tempfile
import time
import uuid
from collections.abc import Callable, Iterable
from dataclasses import dataclass, field
from datetime import date, datetime
from functools import wraps
from pathlib import Path
from typing import Any, ClassVar, Self

import yaml

try:
    import ctypes
    import ctypes.wintypes as _wt
except Exception as _imp_err:
    logging.getLogger(__name__).debug(
        "[build_skill_lifecycle] ctypes/wintypes 不可用，非 Windows 平台降级占位: %s", _imp_err)
    ctypes = None
    _wt = None
from jwsgj.build_contract import (
    ADAPT_CONTRACT,
    DIAG_CONTRACT,
    REGISTER_CONTRACT,
    requires_contract,
)
from jwsgj.build_text_document import (
    count_words_cn_aware,
    iter_fence_lines,
    normalize_text,
    read_skill_text,
)
from jwsgj.build_text_frontmatter import (
    extract_description,
    parse_skill_md_text,
    split_frontmatter,
)
from jwsgj.build_text_scoring import (
    DESC_MAX_LENGTH,
)
from jwsgj.diag_guard_io import (
    JSON_READ_DEGRADE_EXC,
)
from jwsgj.diag_guard_state import (
    write_json_artifact,
)
from jwsgj.diag_shared_ast_views import register_cache_release
from jwsgj.diag_shared_source_core import (
    count_lines,
)
from jwsgj.diag_types_defs import ContractViolationError
from jwsgj.diag_types_normalize import (
    as_number,
    dict_or_empty,
    int_metric,
    signal_bool,
    yaml_safe_quote,
)
from jwsgj.diag_types_vocab import SKILL_MD_LINE_LIMIT
from jwsgj.log_config import locked_artifact, log_swallowed, timed_log
from jwsgj.runtime_paths import (
    d4_registry_path,
    lifecycle_state_dir,
    resolve_skill_reference,
    skill_search_roots,
)
from jwsgj.runtime_scope import (
    PACKAGE_NAME,
    is_pruned_dirname,
    is_pruned_scan_dir,
    is_scan_py_name,
)

logger = logging.getLogger(__name__)
ZOMBIE_THRESHOLDS = {
    "dormant_days": 90,
    "zombie_days": 180,
    "sunset_days": 365,
}
_VERY_RECENT_DAYS = 7
_RECENT_DAYS = 30
_STALE_DAYS = ZOMBIE_THRESHOLDS["dormant_days"]
_DEFAULT_DAYS_SINCE_UPDATE = _STALE_DAYS
_FALLBACK_INACTIVE_DAYS = ZOMBIE_THRESHOLDS["sunset_days"]
_TOKEN_SAVED_PER_USE = 5000
_NEUTRAL_SCORE = 50
_LIFECYCLE_FILE_SUFFIX = "_lifecycle.json"
_PURGE_MIN_SCORE = 20.0
_DEFAULT_USAGE_SUCCESS = True
_DEFAULT_TOKENS_SAVED = 0
def _parse_day(date_str: object) -> datetime | None:
    if not isinstance(date_str, str) or len(date_str) < 10:
        return None
    try:
        return datetime.strptime(date_str[:10], '%Y-%m-%d')
    except ValueError as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc, context='_parse_day:ValueError')
        return None
def _days_between(moment: datetime, now: datetime) -> int:
    comparable_now = (_to_naive_local(now)
                      if now.tzinfo is not None else now)
    if comparable_now is None:
        comparable_now = now.replace(tzinfo=None)
    return (comparable_now - moment).days
def _days_since(date_str: str | None, now: datetime) -> int:
    dt = _parse_day(date_str)
    if dt is None:
        if date_str:
            logger.warning('date parse failed: %r', str(date_str)[:32])
        return _DEFAULT_DAYS_SINCE_UPDATE
    return max(0, _days_between(dt, now))
def _calc_usage_frequency(usage_count: int, last_used_str: str | None,
                           now: datetime | None = None) -> tuple[float, int]:
    if now is None:
        now = datetime.now()
    days_since_use = _days_since(last_used_str, now)
    if days_since_use <= _VERY_RECENT_DAYS:
        score = min(100, usage_count * 10 + 60)
    elif days_since_use <= _RECENT_DAYS:
        score = min(100, usage_count * 5 + 30)
    elif days_since_use <= _STALE_DAYS:
        score = max(10, 30 - (days_since_use - _RECENT_DAYS) / 3.0)
    else:
        score = max(0, 10 - (days_since_use - _STALE_DAYS) * 0.1)
    return (round(float(score), 1), days_since_use)
_TOKEN_EFFICIENCY_BANDS = ((1000000, 100), (500000, 80),
                           (100000, 60), (10000, 40))
_TOKEN_EFFICIENCY_BASE = 20
def _calc_token_efficiency(
        usage_count: int, total_tokens_saved: object = None) -> tuple[int, int]:
    estimated_save = (usage_count * _TOKEN_SAVED_PER_USE
                      if total_tokens_saved is None
                      else int_metric(total_tokens_saved))
    for threshold, score in _TOKEN_EFFICIENCY_BANDS:
        if estimated_save >= threshold:
            return (score, estimated_save)
    return (_TOKEN_EFFICIENCY_BASE, estimated_save)
_ACTIVITY_BANDS: tuple[tuple[int, int], ...] = (
    (_VERY_RECENT_DAYS, 100), (_RECENT_DAYS, 80),
    (_STALE_DAYS, 50), (ZOMBIE_THRESHOLDS["zombie_days"], 20),
)
_FRESHNESS_FLOOR = 10
_MAINTENANCE_FLOOR = 0
def _calc_freshness(updated_at_str: str | None,
                    now: datetime | None = None) -> tuple[int, int]:
    if now is None:
        now = datetime.now()
    days_since_update = _days_since(updated_at_str, now)
    for limit, score in _ACTIVITY_BANDS:
        if days_since_update <= limit:
            return (score, days_since_update)
    return (_FRESHNESS_FLOOR, days_since_update)
_GRADE_BANDS = (
    (80, 'A', '技能健康，保持当前维护频率'),
    (60, 'B', '技能良好，建议增加使用或更新文档'),
    (40, 'C', '技能需关注，考虑更新或合并'),
    (20, 'D', '技能不健康，建议审查是否淘汰'),
)
_GRADE_FAIL = ('F', '技能应淘汰，长期未使用且成功率低')
def _calc_grade(composite: float) -> tuple[str, str]:
    for threshold, grade, rec in _GRADE_BANDS:
        if composite >= threshold:
            return (grade, rec)
    return _GRADE_FAIL
def calc_health(skill: dict[str, Any], now: datetime | None = None) -> dict[str, Any]:
    if now is None:
        now = datetime.now()
    if not isinstance(skill, dict):
        logger.warning("[SkillMgmt] calc_health 参数 skill 类型非法 %r，"
                       "已按空条目评分", skill)
        skill = {}
    usage_count = int_metric(skill.get('usage_count'))
    last_used = skill.get('last_used') or skill.get('created_at')
    freq_score, days_since_use = _calc_usage_frequency(
        usage_count, last_used, now)
    error_count = int_metric(skill.get('error_count'))
    success_rate = (round(max(0.0, (usage_count - error_count)
                             / usage_count * 100), 1)
                    if usage_count > 0 else float(_NEUTRAL_SCORE))
    efficiency_score, estimated_save = _calc_token_efficiency(
        usage_count, skill.get("total_tokens_saved"))
    freshness_score, days_since_update = _calc_freshness(
        skill.get('updated_at') or skill.get('created_at'), now)
    composite = (
        freq_score * WEIGHTS["call_frequency"]
        + success_rate * WEIGHTS["success_rate"]
        + efficiency_score * WEIGHTS["token_efficiency"]
        + freshness_score * WEIGHTS["maintenance_activity"]
    )
    grade, rec = _calc_grade(composite)
    return {
        'score': round(composite, 1),
        'grade': grade,
        'dimensions': {
            'usage_frequency': freq_score,
            'success_rate': success_rate,
            'token_efficiency': efficiency_score,
            'freshness': freshness_score,
        },
        'recommendation': rec,
        'days_since_use': days_since_use,
        'days_since_update': days_since_update,
        'zombie_status': _zombie_status_from_days(days_since_use),
        'estimated_save': estimated_save,
    }
def _lifecycle_finding(row: dict[str, Any], skill_dir: object) -> dict[str, Any]:
    return {
        "rule_id": "LIFECYCLE-STATE",
        "severity": "P2",
        "file": str(skill_dir), "line": 0,
        "message": (
            f"技能 '{row['name']}' 运营健康不佳: score={row.get('score', 0):.1f}, grade={row['grade']}"
            f"（状态={row.get('state', 'unknown')}，建议: {row.get('recommendation', '')}）"
        ),
        "source": "A2",
    }
_HEALTHY_GRADES = frozenset(("A", "B"))
_WARNING_GRADES = frozenset(("C", "D", "F"))
_UNSCORED_GRADE = "unknown"
_UNSCORED_SCORE = -1.0
def _grade_count(results: list[dict[str, Any]], grades: frozenset[str]) -> int:
    return sum(1 for result in results if result.get("grade") in grades)
def quick_health_check(skill_dir: str,
                       now: datetime | None = None) -> dict:
    sl = SkillLifecycle(skill_dir)
    state = sl.load_state()
    skills = dict_or_empty(state.get("skills"))
    results = []
    for name, info in skills.items():
        row = info if isinstance(info, dict) else {}
        health = calc_health(info, now)
        results.append({
            "name": name,
            "grade": health["grade"],
            "state": row.get("state", "unknown"),
            "score": health["score"],
            "recommendation": health["recommendation"],
        })
    if not results:
        results.append({
            "name": _skill_name_from_dir(skill_dir),
            "grade": _UNSCORED_GRADE, "state": "unknown",
            "score": _UNSCORED_SCORE, "no_data": True,
            "recommendation": ("无历史数据，未评定：先经 set_skill_state/"
                               "record_skill_usage 建立状态后再评"),
        })
    findings = [
        _lifecycle_finding(r, skill_dir) for r in results
        if r.get("grade") in _WARNING_GRADES]
    return {
        "total_skills": len(skills),
        "results": results,
        "findings": findings,
        "healthy_count": _grade_count(results, _HEALTHY_GRADES),
        "warning_count": _grade_count(results, _WARNING_GRADES),
    }
def diag_all_skills(manager: SkillLifecycle,
                    now: datetime | None = None) -> list[dict[str, Any]]:
    state = manager.load_state()
    results: list[dict[str, Any]] = []
    for name, skill in dict_or_empty(state.get("skills")).items():
        health = calc_health(skill, now)
        health['skill_name'] = name
        results.append(health)
    results.sort(key=lambda x: x['score'])
    return results
def auto_purge_candidates(
        manager: SkillLifecycle, min_score: float = _PURGE_MIN_SCORE,
        min_days_unused: int = ZOMBIE_THRESHOLDS["zombie_days"],
        now: datetime | None = None) -> list[str]:
    min_score = as_number(min_score, _PURGE_MIN_SCORE)
    min_days_unused = int_metric(
        min_days_unused, ZOMBIE_THRESHOLDS["zombie_days"])
    candidates: list[str] = []
    for result in diag_all_skills(manager, now):
        if (result.get('score', 100) < min_score
                and result.get('days_since_use', 0) >= min_days_unused):
            name = result.get('skill_name', '')
            if name:
                candidates.append(name)
    return candidates
WEIGHTS = {
    "call_frequency": 0.3,
    "success_rate": 0.25,
    "token_efficiency": 0.25,
    "maintenance_activity": 0.2,
}
_NO_REVIEW_WEIGHT_KEYS = ("call_frequency", "token_efficiency",
                          "maintenance_activity")
_WEIGHTS_WITHOUT_REVIEW = {
    key: WEIGHTS[key] / sum(WEIGHTS[name] for name in _NO_REVIEW_WEIGHT_KEYS)
    for key in _NO_REVIEW_WEIGHT_KEYS
}
_CALL_FREQUENCY_BANDS: tuple[tuple[float, int], ...] = (
    (50, 100), (20, 85), (5, 70), (1, _NEUTRAL_SCORE),
)
_SCORE_CALL_ACTIVE = 20
_SCORE_DESC_IDEAL_MIN = 15
_SCORE_DESC_IDEAL_MAX = 50
_SCORE_DESC_TOLERANT_MIN = 8
_SCORE_DESC_TOLERANT_MAX = 80
_LINE_COUNT_BANDS: tuple[tuple[int, int], ...] = (
    (300, 100), (600, 80), (1000, 60),
)
_LINE_COUNT_FLOOR = 30
_SCORE_GRADE_BANDS: tuple[tuple[int, str], ...] = (
    (90, "A"), (80, "B"), (70, "C"), (60, "D"),
)
def _band_score(value: float, bands: tuple) -> int | None:
    for limit, score in bands:
        if value <= limit:
            return score
    return None
def _floor_band(value: float, bands: tuple):
    for floor, result in bands:
        if value >= floor:
            return result
    return None
_SKILL_SEARCH_ROOTS: tuple[Path, ...] | None = None
def _normalize_skill_dir_name(name: str) -> str:
    return name.strip().lower().replace("_", "-").replace(" ", "-")
def _root_key(root: Path) -> str:
    try:
        resolved = str(root.resolve())
    except OSError as exc:
        log_swallowed(__name__, exc, context="_root_key:OSError")
        resolved = str(root)
    return os.path.normcase(resolved)
def _dedupe_roots(roots: list[Path]) -> list[Path]:
    deduped: list[Path] = []
    seen: set[str] = set()
    for root in roots:
        key = _root_key(root)
        if key in seen or not root.is_dir():
            continue
        seen.add(key)
        deduped.append(root)
    return deduped
def _search_roots() -> list[Path]:
    if _SKILL_SEARCH_ROOTS is not None:
        return _dedupe_roots(list(_SKILL_SEARCH_ROOTS))
    roots: list[Path] = []
    try:
        roots.extend(Path(p) for p in skill_search_roots())
    except Exception as _sre:
        logger.warning("[Quality] 动态技能搜索根解析失败，降级为静态根: %s", _sre)
    return _dedupe_roots(roots)
def find_skill_md(skill_name: str) -> Path | None:
    if not isinstance(skill_name, str) or not skill_name:
        return None
    resolved = resolve_skill_reference(skill_name)
    if resolved:
        skill_md = Path(resolved) / "SKILL.md"
        if skill_md.is_file():
            return skill_md
    query = _normalize_skill_dir_name(skill_name)
    for root in _search_roots():
        skill_md = _match_skill_md_in_root(root, query)
        if skill_md is not None:
            return skill_md
    return None
def _match_skill_md_in_root(root: Path, query: str) -> Path | None:
    if not root.is_dir():
        return None
    try:
        entries = sorted(root.iterdir())
    except OSError as e:
        logger.warning("[Quality] 技能根目录列举失败 %s: %s", root, e)
        return None
    for entry in entries:
        skill_md = _skill_md_in_dir(entry, query)
        if skill_md is not None:
            return skill_md
    return None
def _skill_md_in_dir(entry: Path, query: str) -> Path | None:
    if not entry.is_dir():
        return None
    skill_md = entry / "SKILL.md"
    if skill_md.is_file() and _normalize_skill_dir_name(entry.name) == query:
        return skill_md
    return None
def load_skill_reputation(skills_root: str | None = None) -> dict[str, Any]:
    if skills_root:
        root = _path_text(skills_root)
        if not isinstance(root, str):
            logger.warning("[Quality] 声誉扫描根类型非法 %r，按空结果返回",
                           type(skills_root).__name__)
            return {}
        scan_root = Path(root)
        if (scan_root / "SKILL.md").is_file():
            item = _reputation_entry(scan_root)
            return {scan_root.name: item} if item is not None else {}
        scan_roots = [scan_root]
    else:
        scan_roots = _search_roots()
    reputation: dict[str, Any] = {}
    for skills_dir in scan_roots:
        _scan_reputation_root(skills_dir, reputation)
    return reputation
def _scan_reputation_root(skills_dir: Path, reputation: dict[str, Any]) -> None:
    try:
        entries = sorted(skills_dir.iterdir())
    except OSError as e:
        logger.warning("[Quality] 声誉扫描根目录列举失败 %s: %s", skills_dir, e)
        return
    for entry in entries:
        if _skip_reputation_entry(entry, reputation):
            continue
        item = _reputation_entry(entry)
        if item is not None:
            reputation[entry.name] = item
def _skip_reputation_entry(entry: Path, reputation: dict[str, Any]) -> bool:
    if entry.name in reputation:
        return True
    if is_pruned_scan_dir(entry.name, frozenset()):
        return True
    if not entry.is_dir():
        return True
    return not (entry / "SKILL.md").is_file()
def _reputation_activity_mtime(entry: Path, fallback: float) -> float:
    latest: float | None = None
    def _on_walk_error(exc: OSError) -> None:
        logger.warning("[Quality] 声誉活动扫描跳过 %s: %s", entry, exc)
    for root, dirs, files in os.walk(entry, onerror=_on_walk_error):
        dirs[:] = [name for name in dirs if not is_pruned_dirname(name)]
        for name in files:
            if name != "SKILL.md" and not is_scan_py_name(name):
                continue
            path = Path(root) / name
            try:
                file_mtime = path.stat().st_mtime
            except OSError as exc:
                logger.warning("[Quality] 声誉活动文件 stat 失败 %s: %s",
                               path, exc)
                continue
            latest = (file_mtime if latest is None
                      else max(latest, file_mtime))
    return fallback if latest is None else latest
def _reputation_entry(entry: Path) -> dict[str, Any] | None:
    try:
        py_files = sum(1 for f in entry.iterdir()
                       if f.is_file() and is_scan_py_name(f.name))
        last_modified = _reputation_activity_mtime(
            entry, entry.stat().st_mtime)
        return {
            "name": entry.name,
            "file_count": py_files,
            "last_modified": last_modified,
            "trust_score": min(100, py_files * 5),
        }
    except OSError as e:
        logger.warning("[Quality] 声誉扫描跳过 %s: %s", entry, e)
        return None
def _skill_entry_key(skills: Any, skill_name: str | None,
                     skill_dir: str) -> str | None:
    if not isinstance(skills, dict) or not skills:
        return None
    key = (skill_name if isinstance(skill_name, str) and skill_name
           else _skill_name_from_dir(skill_dir))
    if isinstance(skills.get(key), dict):
        return key
    normalized = _normalize_skill_dir_name(key)
    for name, candidate in skills.items():
        if (isinstance(candidate, dict)
                and _normalize_skill_dir_name(str(name)) == normalized):
            return name
    return None
def _skill_entry_of(skills: Any, skill_name: str | None,
                    skill_dir: str) -> dict[str, Any]:
    key = _skill_entry_key(skills, skill_name, skill_dir)
    return skills[key] if key is not None else {}
def _to_naive_local(dt: datetime) -> datetime | None:
    if dt.tzinfo is None:
        return dt
    try:
        return dt.astimezone().replace(tzinfo=None)
    except (OSError, OverflowError) as exc:
        logger.debug("时间戳时区归一越界（按无时间记录处理）: %s", exc)
        return None
def _parse_timestamp(value: object) -> datetime | None:
    if not isinstance(value, str) or not value:
        return None
    try:
        parsed = datetime.fromisoformat(value)
    except (TypeError, ValueError) as exc:
        logger.debug("时间戳格式解析失败（按无时间记录处理）: %s", exc)
        return None
    return _to_naive_local(parsed)
def _count_in_window(ages: list[float], days: int) -> int:
    return sum(1 for age in ages if 0 <= age < days)
def _usage_timestamps(entry: dict[str, Any]) -> list[datetime]:
    raw_history = entry.get("usage_history")
    history = raw_history if isinstance(raw_history, list) else []
    parsed = [stamp for stamp in map(_parse_timestamp, history)
              if stamp is not None]
    last_used = _parse_timestamp(entry.get("last_used"))
    if last_used is not None and (not parsed or last_used > max(parsed)):
        parsed.append(last_used)
    return parsed
def _usage_events_in_window(entry: dict[str, Any], days: int,
                            now: datetime) -> int:
    local_now = _to_naive_local(now)
    if local_now is None:
        return 0
    ages = [(local_now - stamp).total_seconds() / 86400
            for stamp in _usage_timestamps(entry)]
    return _count_in_window(ages, days)
def load_telemetry_stats(skill_dir: str, skill_name: str | None = None,
                         days: int = _RECENT_DAYS) -> dict[str, Any]:
    window = (days if isinstance(days, int) and not isinstance(days, bool)
              and days > 0 else _RECENT_DAYS)
    stats: dict[str, Any] = {"usage_events": 0, "error_events": 0,
                             "window_days": window}
    target = (os.fspath(skill_dir) if isinstance(skill_dir, os.PathLike)
              else (skill_dir if isinstance(skill_dir, str) else ""))
    if not target:
        logger.debug("[SkillMgmt] 遥测统计缺少技能目录，按零事件返回")
        return stats
    skills_map = dict_or_empty(
        SkillLifecycle(target).load_state().get("skills"))
    entry = _skill_entry_of(skills_map, skill_name, target)
    if not entry and len(skills_map) == 1:
        sole = next(iter(skills_map.values()))
        entry = sole if isinstance(sole, dict) else {}
    if not entry:
        return stats
    stats["usage_events"] = _usage_events_in_window(entry, window,
                                                   datetime.now())
    stats["error_events"] = int_metric(entry.get("error_count"))
    return stats
def skill_md_path(skill_dir: Any) -> Path:
    return Path(skill_dir) / "SKILL.md"
def _as_skill_md_path(skill_md: Any) -> Path | None:
    if skill_md is None:
        return None
    if isinstance(skill_md, (str, os.PathLike)):
        return Path(skill_md)
    logger.warning("[Quality] skill_md 参数类型非法 %r，已按无文件处理",
                 skill_md)
    return None
def score_call_frequency(rep: dict[str, Any], telemetry: dict[str, Any]) -> int:
    rep = dict_or_empty(rep)
    telemetry = dict_or_empty(telemetry)
    total_reviews = as_number(rep.get("total_reviews", 0), 0)
    recent_events = as_number(telemetry.get("usage_events", 0), 0)
    for threshold, score in _CALL_FREQUENCY_BANDS:
        if recent_events >= threshold:
            return score
    if total_reviews > _SCORE_CALL_ACTIVE:
        return 30
    if total_reviews > 0:
        return 15
    return 0
def score_success_rate(rep: dict[str, Any]) -> int:
    rep = dict_or_empty(rep)
    violations = max(0.0, as_number(rep.get("violation_count", 0), 0))
    total_reviews = max(0.0, as_number(rep.get("total_reviews", 0), 0))
    status = normalize_text(rep.get("status", "active")).strip().lower()
    if status == "banned":
        return 0
    if total_reviews == 0:
        return _NEUTRAL_SCORE
    violation_rate = violations / max(total_reviews, 1)
    if violation_rate == 0:
        return 100
    if violation_rate < 0.05:
        return 80
    if violation_rate < 0.10:
        return 60
    if violation_rate < 0.20:
        return 40
    return 20
def _read_skill_md_text(skill_md: Any) -> str | None:
    path = _as_skill_md_path(skill_md)
    if path is None or not path.exists():
        return None
    try:
        return read_skill_text(path)
    except (OSError, UnicodeDecodeError) as e:
        logger.warning("[Quality] SKILL.md 读取失败 %s: %s", path, e)
        return None
_DESC_KEY_LINE_RE = re.compile(r'^description\s*:\s*(.*)$')
def _description_text(content: str) -> str:
    description = extract_description(content)
    if description:
        return description
    lines = content.split("\n")
    for line, in_fence in iter_fence_lines(lines):
        if in_fence:
            continue
        stripped = line.strip()
        if stripped.startswith("#"):
            continue
        matched = _DESC_KEY_LINE_RE.match(stripped)
        if matched:
            return matched.group(1).strip().strip('"').strip("'")
    return ""
def _token_efficiency_from_profile(
        content: str | None, profile: tuple[int, int]) -> int:
    if content is None:
        return _NEUTRAL_SCORE
    desc_words, total_lines = profile
    desc_score = _desc_word_score(desc_words)
    line_score = _line_count_score(total_lines)
    return int(desc_score * 0.5 + line_score * 0.5)
def score_token_efficiency(skill_md: Path | None) -> int:
    content = _read_skill_md_text(skill_md)
    return _token_efficiency_from_profile(content, _skill_profile(content))
def _desc_word_score(desc_words: float) -> int:
    if _SCORE_DESC_IDEAL_MIN <= desc_words <= _SCORE_DESC_IDEAL_MAX:
        return 100
    if _SCORE_DESC_TOLERANT_MIN <= desc_words <= _SCORE_DESC_TOLERANT_MAX:
        return 80
    return _NEUTRAL_SCORE
def _line_count_score(total_lines: int) -> int:
    if total_lines <= 0:
        return _LINE_COUNT_FLOOR
    score = _band_score(total_lines, _LINE_COUNT_BANDS)
    return _LINE_COUNT_FLOOR if score is None else score
def _last_activity_timestamp(rep: dict[str, Any]) -> float:
    data = dict_or_empty(rep)
    timestamps = (
        as_number(data.get(key, 0), 0)
        for key in ("last_active", "last_modified")
    )
    return max((timestamp for timestamp in timestamps if timestamp > 0),
               default=0)
def _days_since_last_activity(rep: dict[str, Any], skill_md: Path | None) -> float:
    now = time.time()
    last_active = _last_activity_timestamp(rep)
    days_since_active = ((now - last_active) / 86400) if last_active else float(
        _FALLBACK_INACTIVE_DAYS)
    file_mtime_days: float = float(_FALLBACK_INACTIVE_DAYS)
    skill_md = _as_skill_md_path(skill_md)
    if skill_md and skill_md.exists():
        try:
            file_mtime_days = (now - Path(skill_md).stat().st_mtime) / 86400
        except OSError as e:
            logger.warning("[Quality] SKILL.md stat 失败（时效计算退化为回退天数）%s: %s", skill_md, e)
    return max(0.0, min(days_since_active, file_mtime_days))
def _maintenance_score_from_days(days: float) -> int:
    score = _band_score(days, _ACTIVITY_BANDS)
    return _MAINTENANCE_FLOOR if score is None else score
def score_maintenance_activity(rep: dict[str, Any], skill_md: Path | None) -> int:
    return _maintenance_score_from_days(_days_since_last_activity(rep, skill_md))
def _zombie_status_from_days(days: float) -> str:
    for status, key in (("sunset", "sunset_days"),
                        ("zombie", "zombie_days"),
                        ("dormant", "dormant_days")):
        if days >= ZOMBIE_THRESHOLDS[key]:
            return status
    return "active"
def detect_zombie_status(rep: dict[str, Any], skill_md: Path | None) -> str:
    return _zombie_status_from_days(_days_since_last_activity(rep, skill_md))
def detect_duplicate_names(all_skills: list[str]) -> list[tuple[str, str]]:
    if isinstance(all_skills, (str, bytes)) or not isinstance(all_skills, Iterable):
        logger.warning("[SkillMgmt] detect_duplicate_names 入参非序列 %r，按空结果返回",
                       type(all_skills).__name__)
        return []
    normalized: dict[str, str] = {}
    duplicates: list[tuple[str, str]] = []
    for name in all_skills:
        if not isinstance(name, str):
            continue
        key = _normalize_skill_dir_name(name)
        if key in normalized:
            duplicates.append((normalized[key], name))
        else:
            normalized[key] = name
    return duplicates
def _get_grade(score: float) -> str:
    grade = _floor_band(score, _SCORE_GRADE_BANDS)
    return "F" if grade is None else grade
def reputation_key(reputation: dict[str, Any],
                    skill_name: object) -> str | None:
    if not isinstance(reputation, dict):
        logger.warning("[Quality] reputation_key 台账类型非法 %r，按未命中返回",
                       type(reputation).__name__)
        return None
    if not isinstance(skill_name, str) or not skill_name:
        return None
    if skill_name in reputation:
        return skill_name
    query = _normalize_skill_dir_name(skill_name)
    for name in sorted(k for k in reputation if isinstance(k, str)):
        if _normalize_skill_dir_name(name) == query:
            return name
    return None
def _load_reputation(skill_name: str) -> dict[str, Any]:
    reputation = load_skill_reputation()
    if isinstance(reputation, dict):
        key = reputation_key(reputation, skill_name)
        if key is None:
            return {}
        entry = reputation[key]
        return entry if isinstance(entry, dict) else {}
    return {}
def _score_dimensions(rep: dict[str, Any], telemetry: dict[str, Any],
                      token_efficiency: int, days_since_active: float
                      ) -> dict[str, float]:
    return {
        "call_frequency": score_call_frequency(rep, telemetry),
        "success_rate": score_success_rate(rep),
        "token_efficiency": token_efficiency,
        "maintenance_activity": _maintenance_score_from_days(days_since_active),
    }
def _review_evidence_available(rep: dict[str, Any]) -> bool:
    return as_number(dict_or_empty(rep).get("total_reviews", 0), 0) > 0
def _weighted_overall(scores: dict[str, float],
                      weights: dict[str, float]) -> float:
    return sum(scores[key] * weight for key, weight in weights.items())
def _usage_evidence_available(rep: dict[str, Any],
                              telemetry: dict[str, Any]) -> bool:
    rep = dict_or_empty(rep)
    telemetry = dict_or_empty(telemetry)
    return bool(
        as_number(rep.get("total_reviews", 0), 0)
        or as_number(telemetry.get("usage_events", 0), 0)
        or as_number(telemetry.get("error_events", 0), 0)
    )
def _structural_overall(scores: dict[str, float]) -> float:
    weights = {"token_efficiency": 0.55, "maintenance_activity": 0.45}
    total = sum(weights.values())
    return sum(scores[key] * weight for key, weight in weights.items()) / total
def _skill_profile(content: str | None) -> tuple[int, int]:
    if content is None:
        return 0, 0
    return (count_words_cn_aware(_description_text(content)),
            count_lines(content))
def score_skill_health(skill_name: str, rep: dict[str, Any] | None = None) -> tuple[dict[str, Any], Path | None]:
    resolved_root = resolve_skill_reference(skill_name)
    if resolved_root:
        skill_name = Path(resolved_root).name
    if not isinstance(skill_name, str):
        skill_name = _normalize_skill_name(skill_name, "")
    if rep is None:
        rep = _load_reputation(skill_name)
    skill_md = find_skill_md(resolved_root) if resolved_root else None
    if skill_md is None:
        skill_md = find_skill_md(skill_name)
    telemetry = load_telemetry_stats(
        str(skill_md.parent) if skill_md is not None else "", skill_name)
    content = _read_skill_md_text(skill_md)
    days_since_active = _days_since_last_activity(rep, skill_md)
    profile = _skill_profile(content)
    token_efficiency = _token_efficiency_from_profile(content, profile)
    scores = _score_dimensions(
        rep, telemetry, token_efficiency, days_since_active)
    telemetry_available = _usage_evidence_available(rep, telemetry)
    review_available = _review_evidence_available(rep)
    if telemetry_available:
        weights = WEIGHTS if review_available else _WEIGHTS_WITHOUT_REVIEW
        overall = _weighted_overall(scores, weights)
        score_basis = "usage+structure"
    else:
        overall = _structural_overall(scores)
        score_basis = "structure_only"
    grade = _get_grade(overall)
    zombie = _zombie_status_from_days(days_since_active)
    desc_words, file_lines = profile
    _result = {
        "skill_name": skill_name,
        "call_frequency": scores["call_frequency"],
        "success_rate": scores["success_rate"],
        "token_efficiency": scores["token_efficiency"],
        "maintenance_activity": scores["maintenance_activity"],
        "overall_score": round(overall, 1),
        "grade": grade,
        "zombie": zombie,
        "zombie_status": zombie,
        "days_since_active": round(days_since_active, 1),
        "desc_words": desc_words,
        "file_lines": file_lines,
        "telemetry_available": telemetry_available,
        "review_available": review_available,
        "score_basis": score_basis,
    }
    return _result, skill_md
__all__ = [
    'WEIGHTS',
    'ZOMBIE_THRESHOLDS',
    "AdaptationPlan",
    "AdaptationResult",
    "DiagnoseReport",
    "ExperienceAtom",
    "ExperienceCrystallizer",
    "SkillAdapter",
    "SkillDiagnoser",
    "SkillHealth",
    "SkillLifecycle",
    "SkillState",
    "adapt_skill",
    "auto_crystallize",
    'auto_purge_candidates',
    'calc_health',
    'detect_duplicate_names',
    'detect_zombie_status',
    'diag_all_skills',
    "diag_skills_directory",
    'find_skill_md',
    "get_lifecycle",
    "is_d4_registered",
    'load_skill_reputation',
    'load_telemetry_stats',
    "query_d4_registry",
    'quick_health_check',
    "record_skill_usage",
    "register_to_d4",
    'reputation_key',
    "run_registration",
    'score_call_frequency',
    'score_maintenance_activity',
    'score_skill_health',
    'score_success_rate',
    'score_token_efficiency',
    "set_skill_state",
    'skill_md_path',
    "update_lifecycle",
    "write_diag_report_json",
]
logger.info("build_skill_lifecycle 已加载: %d 项导出", len(__all__))
@dataclass
class ExperienceAtom:
    atom_id: str = field(default_factory=lambda: str(uuid.uuid4())[:8])
    timestamp: float = field(default_factory=time.time)
    operation: str = ""
    action: str = ""
    module: str = ""
    skill_name: str = ""
    inputs_hash: str = ""
    outcome: str = "success"
    duration_ms: float = 0.0
    constraints_passed: list[str] = field(default_factory=list)
    invariants_held: list[str] = field(default_factory=list)
    health_snapshot: dict[str, Any] = field(default_factory=dict)
    raw_error: str | None = None
    context: dict[str, Any] = field(default_factory=dict)
    def __post_init__(self: Self) -> None:
        if self.action and not self.operation:
            self.operation = self.action
class ExperienceCrystallizer:
    _MAX_ATOMS: ClassVar[int] = 500
    _atoms: ClassVar[list[ExperienceAtom]] = []
    @classmethod
    def crystallize(cls: type[Self], **kwargs: Any) -> ExperienceAtom:
        atom = ExperienceAtom(**kwargs)
        cls._atoms.append(atom)
        if len(cls._atoms) > cls._MAX_ATOMS:
            del cls._atoms[:len(cls._atoms) - cls._MAX_ATOMS]
        logger.debug("经验结晶: op=%s, module=%s, outcome=%s",
                     atom.operation, atom.module, atom.outcome)
        return atom
    @classmethod
    def clear(cls: type[Self]) -> int:
        count = len(cls._atoms)
        cls._atoms.clear()
        return count
def _wrap_with_crystallize(func: Callable, mod: str, op: str) -> Callable:
    @wraps(func)
    def wrapper(*args: Any, **kwargs: Any) -> Any:
        start = time.monotonic()
        outcome = "failure"
        raw_error: str | None = None
        try:
            result = func(*args, **kwargs)
            outcome = "success"
            return result
        except Exception as exc:
            raw_error = str(exc)
            raise
        finally:
            duration = (time.monotonic() - start) * 1000
            try:
                ExperienceCrystallizer.crystallize(
                    operation=op,
                    module=mod,
                    duration_ms=duration,
                    outcome=outcome,
                    raw_error=raw_error,
                )
            except Exception as exc:
                logger.warning(
                    "经验结晶记录失败(不劫持主流程, op=%s): %s", op, exc)
    return wrapper
def auto_crystallize(operation_name: str = "", module_name: str = "") -> Any:
    if callable(operation_name):
        func = operation_name
        mod = func.__module__.split(".")[-1]
        return _wrap_with_crystallize(func, mod, func.__name__)
    def decorator(func: Callable) -> Callable:
        mod = module_name or func.__module__.split(".")[-1]
        op = operation_name or func.__name__
        return _wrap_with_crystallize(func, mod, op)
    return decorator
register_cache_release(
    "experience_atoms", ExperienceCrystallizer.clear, "经验结晶器", order=60)
_PACKAGE_DIR = Path(__file__).resolve().parent
def _epoch_state_dir(skill_dir: object = None) -> Path:
    target = (_coerce_skill_dir(skill_dir) if skill_dir is not None
              else str(_PACKAGE_DIR))
    return Path(lifecycle_state_dir(target or str(_PACKAGE_DIR)))
def _path_text(value: object) -> object:
    return os.fspath(value) if isinstance(value, os.PathLike) else value
def _skill_name_from_dir(skill_dir: object) -> str:
    skill_dir = _path_text(skill_dir)
    if not isinstance(skill_dir, str) or not skill_dir:
        return "default"
    name = os.path.basename(os.path.normpath(skill_dir))
    if name in ("", ".", ".."):
        name = os.path.basename(os.path.abspath(skill_dir))
    return name or "default"
def _coerce_skill_dir(skill_dir: object) -> str:
    skill_dir = _path_text(skill_dir)
    if skill_dir is not None and not isinstance(skill_dir, str):
        logger.warning(
            "[SkillMgmt] skill_dir 类型非法 %r，已归一空串（状态键落 default）",
            skill_dir)
    return skill_dir if isinstance(skill_dir, str) else ""
def _fallback_state_dir(skill_dir: object) -> str:
    identity = os.path.normcase(
        os.path.abspath(str(skill_dir or _PACKAGE_DIR)))
    digest = hashlib.sha1(identity.encode("utf-8", "replace")).hexdigest()[:12]
    return os.path.join(tempfile.gettempdir(), "jwsgj_lifecycle_state", digest)
def _state_file_with_dir(path: str, skill_dir: object = None) -> str:
    name = path or f"{_skill_name_from_dir(skill_dir)}{_LIFECYCLE_FILE_SUFFIX}"
    if os.path.isabs(name):
        return os.path.normpath(name)
    try:
        base = str(_epoch_state_dir(skill_dir))
    except RuntimeError as exc:
        logger.warning(
            "[SkillMgmt] 状态目录不可用，回退系统临时隔离目录: %s", exc)
        base = _fallback_state_dir(skill_dir)
    return os.path.normpath(os.path.join(base, name))
def _coerce_state_file(state_file: object) -> str | None:
    state_file = _path_text(state_file)
    if state_file is not None and not isinstance(state_file, str):
        logger.warning(
            "[SkillMgmt] state_file 类型非法 %r，已回退默认状态文件",
            state_file)
        return None
    if not isinstance(state_file, str):
        return None
    cleaned = state_file.strip()
    if not cleaned or cleaned == "None":
        return None
    return cleaned
def _normalize_skill_name(skill_name: object, skill_dir: str = "") -> str:
    if isinstance(skill_name, str) and skill_name.strip():
        return skill_name.strip()
    fallback = _skill_name_from_dir(skill_dir)
    if not isinstance(skill_name, str) and skill_name not in (None, ""):
        logger.warning("[SkillMgmt] skill_name 类型非法 %r，已归一 %s",
                       skill_name, fallback)
    return fallback
class SkillState:
    DRAFT = "draft"
    TESTING = "testing"
    REGISTERED = "registered"
    ACTIVE = "active"
    DEPRECATED = "deprecated"
    RETIRED = "retired"
    TRANSITIONS: ClassVar[dict[str, frozenset[str]]] = {
        DRAFT: frozenset({TESTING}),
        TESTING: frozenset({REGISTERED, DRAFT}),
        REGISTERED: frozenset({ACTIVE, DEPRECATED}),
        ACTIVE: frozenset({DEPRECATED}),
        DEPRECATED: frozenset({RETIRED, ACTIVE}),
        RETIRED: frozenset(),
    }
    @classmethod
    def can_transition(cls, current: str, target: str) -> bool:
        if not isinstance(current, str) or not isinstance(target, str):
            return False
        return target in cls.TRANSITIONS.get(current, frozenset())
_VALID_STATES = frozenset(SkillState.TRANSITIONS)
_USAGE_HISTORY_LIMIT = 200
_STATE_HISTORY_LIMIT = _USAGE_HISTORY_LIMIT
def _default_skill_entry(skill_name: str, now: str) -> dict[str, Any]:
    return {
        "name": skill_name, "created_at": now, "state": SkillState.DRAFT,
        "state_history": [], "test_results": [], "usage_count": 0,
        "last_used": None, "error_count": 0, "total_tokens_saved": 0,
    }
_RESERVED_METADATA_KEYS = frozenset({
    *_default_skill_entry("", "").keys(), "usage_history", "updated_at",
})
def _heal_skill_entries(state: dict[str, Any], state_file: str) -> dict[str, Any]:
    now = datetime.now().isoformat(timespec="seconds")
    for name, entry in list(state["skills"].items()):
        if not isinstance(entry, dict):
            logger.warning(
                "[SkillMgmt] 技能条目非对象，归一为默认态: %s[%s] "
                "(type=%s)",
                state_file, name, type(entry).__name__)
            state["skills"][name] = _default_skill_entry(str(name), now)
            continue
        if entry.get("state") not in _VALID_STATES:
            current = entry.get("state")
            if current in (None, ""):
                logger.debug(
                    "[SkillMgmt] 技能条目缺少 state，归 DRAFT: %s[%s]",
                    state_file, name)
            else:
                logger.warning(
                    "[SkillMgmt] 技能条目 state 非法值，归 DRAFT: "
                    "%s[%s] (state=%r)",
                    state_file, name, current)
            entry["state"] = SkillState.DRAFT
    return state
class SkillLifecycle:
    def __init__(self: Self, skill_dir: str, state_file: str | None = None) -> None:
        self.skill_dir = _coerce_skill_dir(skill_dir)
        self.state_file = _state_file_with_dir(
            _coerce_state_file(state_file) or "", self.skill_dir)
        self._state_cache: dict[str, Any] | None = None
    def _default_state(self: Self) -> dict[str, Any]:
        return {
            "initialized": True,
            "version": "1.0.0",
            "timestamp": time.time(),
            "stages": [],
            "skills": {},
            "stats": {"total": 0, "active": 0, "deprecated": 0, "retired": 0},
        }
    def _read_state_file(self: Self) -> dict[str, Any] | None:
        try:
            with open(self.state_file, encoding="utf-8-sig") as f:
                state = json.load(f)
        except FileNotFoundError:
            logger.debug("[SkillMgmt] 状态文件不存在，按默认态启动: %s",
                         self.state_file)
            return None
        except JSON_READ_DEGRADE_EXC as e:
            logger.warning("[SkillMgmt] 生命周期状态加载失败，降级默认态: %s (%s)", self.state_file, e)
            return None
        if not isinstance(state, dict):
            logger.warning(
                "[SkillMgmt] 状态顶层非对象，降级默认态: %s (%s)",
                self.state_file, type(state).__name__)
            return None
        if "skills" not in state:
            logger.debug(
                "[SkillMgmt] 旧版状态缺少 skills，兼容为空表: %s",
                self.state_file)
            state["skills"] = {}
        elif not isinstance(state["skills"], dict):
            logger.warning(
                "[SkillMgmt] 状态文件 skills 非对象，状态不可用: %s (%s)",
                self.state_file, type(state["skills"]).__name__)
            return None
        else:
            _heal_skill_entries(state, self.state_file)
        self._recalc_stats(state)
        return state
    def load_state(self: Self) -> dict[str, Any]:
        if self._state_cache is not None:
            return self._state_cache
        state_path = str(self.state_file or "").strip()
        if state_path in ("", "None"):
            return self._default_state()
        state = self._read_state_file()
        if state is None:
            return self._default_state()
        self._state_cache = state
        return state
    def _save_state(self, state: dict) -> bool:
        try:
            self.state_file = _state_file_with_dir(
                str(self.state_file), self.skill_dir)
            write_json_artifact(str(self.state_file), state, indent=2)
            self._state_cache = state
            return True
        except (OSError, ValueError, TypeError, RuntimeError, MemoryError,
                ContractViolationError) as exc:
            logger.warning("[SkillMgmt] 保存生命周期状态失败: %s", exc)
            self._state_cache = None
            return False
    def _run_mutation_locked(self, operation: Callable[[], bool]) -> bool:
        state_path = str(self.state_file)
        try:
            lock_dir = os.path.dirname(state_path)
            if lock_dir:
                os.makedirs(lock_dir, exist_ok=True)
        except (OSError, ValueError) as exc:
            logger.warning("[SkillMgmt] 生命周期状态目录创建失败: %s", exc)
            return False
        with locked_artifact(state_path) as locked:
            if not locked:
                logger.warning("[SkillMgmt] 生命周期写锁不可用，拒绝解锁写入")
                return False
            latest = (self._read_state_file()
                      if os.path.exists(state_path) else self._default_state())
            if latest is None:
                self._state_cache = None
                logger.warning(
                    "[SkillMgmt] 状态文件存在但不可用，拒绝覆盖: %s",
                    state_path)
                return False
            cached = self._state_cache
            if cached is None:
                self._state_cache = latest
            else:
                cached.clear()
                cached.update(latest)
                self._state_cache = cached
            return operation()
    def initialize(self) -> dict:
        def _create_if_missing() -> bool:
            if not os.path.exists(self.state_file):
                return self._save_state(self._default_state())
            if self._read_state_file() is None:
                logger.warning(
                    "[SkillMgmt] 状态文件存在但不可用，拒绝用默认态覆盖: %s",
                    self.state_file)
                return False
            return True
        initialized = self._run_mutation_locked(_create_if_missing)
        state = dict(self.load_state())
        state["initialized"] = initialized
        return state
    def _recalc_stats(self, state: dict) -> None:
        skills = state.get("skills", {})
        stats = {"total": len(skills), "active": 0,
                 "deprecated": 0, "retired": 0}
        for entry in skills.values():
            current = entry.get("state") if isinstance(entry, dict) else None
            if current == SkillState.ACTIVE:
                stats["active"] += 1
            elif current == SkillState.DEPRECATED:
                stats["deprecated"] += 1
            elif current == SkillState.RETIRED:
                stats["retired"] += 1
        state["stats"] = stats
    def _open_entry(self: Self, skill_name: str) -> tuple[str, dict, dict, str]:
        skill_name = _normalize_skill_name(skill_name, self.skill_dir)
        state = self.load_state()
        now = datetime.now().isoformat(timespec="seconds")
        existing = _skill_entry_key(
            state["skills"], skill_name, self.skill_dir)
        key = existing if existing is not None else skill_name
        entry = state["skills"].get(
            key, _default_skill_entry(key, now))
        return key, state, entry, now
    def _commit_entry(self: Self, state: dict, skill_name: str,
                      entry: dict) -> bool:
        state["skills"][skill_name] = entry
        self._recalc_stats(state)
        return self._save_state(state)
    def set_skill_state(self, skill_name: str, new_state: str,
                         metadata: dict | None = None) -> bool:
        return self._run_mutation_locked(
            lambda: self._set_skill_state_locked(
                skill_name, new_state, metadata))
    def _set_skill_state_locked(self, skill_name: str, new_state: str,
                                metadata: dict | None) -> bool:
        skill_name, state, entry, now = self._open_entry(skill_name)
        current = entry.get("state", SkillState.DRAFT)
        if current != new_state:
            if not SkillState.can_transition(current, new_state):
                logger.warning("技能[%s]状态转换被拒绝: %s -> %s",
                             skill_name, current, new_state)
                return False
            entry["state"] = new_state
            raw_state_history = entry.get("state_history")
            state_history = (list(raw_state_history)
                             if isinstance(raw_state_history, list) else [])
            state_history.append({"from": current, "to": new_state, "at": now})
            entry["state_history"] = state_history[-_STATE_HISTORY_LIMIT:]
        entry["updated_at"] = now
        if metadata is not None and not isinstance(metadata, dict):
            logger.warning("[SkillMgmt] set_skill_state 参数 metadata 类型"
                           "非法 %r，已跳过元数据合并", metadata)
        elif metadata:
            reserved = sorted(_RESERVED_METADATA_KEYS.intersection(metadata))
            if reserved:
                logger.warning(
                    "[SkillMgmt] set_skill_state metadata 含受管字段 %s，已跳过",
                    reserved)
            entry.update({key: value for key, value in metadata.items()
                          if key not in _RESERVED_METADATA_KEYS})
        return self._commit_entry(state, skill_name, entry)
    def record_skill_usage(self, skill_name: str,
                            success: bool = _DEFAULT_USAGE_SUCCESS,
                            tokens_saved: int = _DEFAULT_TOKENS_SAVED) -> bool:
        return self._run_mutation_locked(
            lambda: self._record_skill_usage_locked(
                skill_name, success, tokens_saved))
    def _record_skill_usage_locked(self, skill_name: str, success: bool,
                                   tokens_saved: int) -> bool:
        skill_name, state, entry, now = self._open_entry(skill_name)
        entry["usage_count"] = int_metric(entry.get("usage_count")) + 1
        entry["last_used"] = now
        entry["updated_at"] = now
        raw_history = entry.get("usage_history")
        history = list(raw_history) if isinstance(raw_history, list) else []
        history.append(now)
        entry["usage_history"] = history[-_USAGE_HISTORY_LIMIT:]
        entry["total_tokens_saved"] = (
            int_metric(entry.get("total_tokens_saved")) + int_metric(tokens_saved))
        if not signal_bool(success):
            entry["error_count"] = int_metric(entry.get("error_count")) + 1
        return self._commit_entry(state, skill_name, entry)
def set_skill_state(skill_dir: str, skill_name: str, new_state: str,
                     reason: str = "") -> bool:
    return SkillLifecycle(skill_dir).set_skill_state(
        skill_name, new_state, metadata={"reason": reason} if reason else None)
def _lifecycle_snapshot(manager: SkillLifecycle,
                        skill_name: str | None) -> dict:
    state = manager.load_state()
    skills = dict_or_empty(state.get("skills"))
    key = _normalize_skill_name(skill_name, manager.skill_dir)
    resolved = _skill_entry_key(skills, key, manager.skill_dir)
    if resolved is not None:
        key = resolved
    candidate = skills.get(key)
    entry = candidate if isinstance(candidate, dict) else {}
    stats = state.get("stats")
    return {"skill": key,
            "state": entry.get("state") or SkillState.DRAFT,
            "stats": dict(stats) if isinstance(stats, dict) else {},
            "info": dict(entry)}
def get_lifecycle(skill_dir: str, skill_name: str | None = None) -> dict:
    return _lifecycle_snapshot(SkillLifecycle(skill_dir), skill_name)
def update_lifecycle(skill_dir: str, skill_name: str, state: str,
                      reason: str = "") -> dict:
    manager = SkillLifecycle(skill_dir)
    updated = manager.set_skill_state(
        skill_name, state, metadata={"reason": reason} if reason else None)
    result = _lifecycle_snapshot(manager, skill_name)
    result["updated"] = updated
    return result
def record_skill_usage(skill_dir: str, skill_name: str,
                        success: bool = _DEFAULT_USAGE_SUCCESS,
                        tokens_saved: int = _DEFAULT_TOKENS_SAVED) -> bool:
    return SkillLifecycle(skill_dir).record_skill_usage(
        skill_name, success=success, tokens_saved=tokens_saved)
def _d4_registry_path() -> str:
    return d4_registry_path(os.path.dirname(os.path.abspath(__file__)))
def _d4_scalar_text(value: object) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (date, datetime)):
        return value.isoformat()
    if isinstance(value, (int, float)):
        return str(value)
    raise ValueError(f"D4 registry 字段值非标量: {type(value).__name__}")
def _parse_d4_entries(content: str) -> list[dict[str, str]] | None:
    try:
        raw_entries = yaml.safe_load(content)
        if raw_entries is None:
            return []
        if not isinstance(raw_entries, list):
            raise ValueError("D4 registry 顶层必须是列表")
        entries: list[dict[str, str]] = []
        for raw_entry in raw_entries:
            if not isinstance(raw_entry, dict):
                raise ValueError("D4 registry 条目必须是对象")
            entry: dict[str, str] = {}
            for key, value in raw_entry.items():
                if not isinstance(key, str):
                    raise ValueError("D4 registry 字段名必须是字符串")
                entry[key] = _d4_scalar_text(value)
            entries.append(entry)
        return entries
    except (yaml.YAMLError, ValueError) as exc:
        logger.warning("D4 registry 内容或结构非法: %s", exc)
        return None
def _d4_entry_exists(d4_path: str, skill_name: str) -> bool | None:
    content = _load_d4_registry_content(d4_path)
    if content is None:
        return None
    entries = _parse_d4_entries(content)
    if entries is None:
        return None
    return _find_d4_entry(entries, skill_name.strip()) is not None
def _normalize_d4_field(raw: str, field: str) -> str:
    if not isinstance(raw, str):
        raise TypeError(
            f"D4 registry {field} 入参非 str（{type(raw).__name__}），拒绝注册")
    value = raw.strip()
    if not value:
        raise ValueError(f"D4 registry {field} 归一后为空，拒绝注册")
    if "\r" in value or "\n" in value:
        raise ValueError(f"D4 registry {field} 含行分隔符，拒绝注册: {value!r}")
    if "#" in value:
        raise ValueError(f"D4 registry {field} 含 YAML 行内注释符 '#'，拒绝注册: {value!r}")
    return value
_FILE_APPEND_DATA = 0x0004
_SHARE_READ_WRITE = 0x00000003
_OPEN_ALWAYS = 4
_FILE_ATTRIBUTE_NORMAL = 0x00000080
def _append_windows(path: str, data: str) -> None:
    if ctypes is None or _wt is None:
        raise OSError("ctypes.wintypes 不可用：无法执行内核级原子追加")
    k32 = ctypes.WinDLL("kernel32", use_last_error=True)
    k32.CreateFileW.restype = _wt.HANDLE
    k32.CreateFileW.argtypes = [_wt.LPCWSTR, _wt.DWORD, _wt.DWORD,
                                _wt.LPVOID, _wt.DWORD, _wt.DWORD, _wt.HANDLE]
    k32.WriteFile.restype = _wt.BOOL
    k32.WriteFile.argtypes = [_wt.HANDLE, _wt.LPCVOID, _wt.DWORD,
                              _wt.LPVOID, _wt.LPVOID]
    k32.CloseHandle.restype = _wt.BOOL
    k32.CloseHandle.argtypes = [_wt.HANDLE]
    handle = k32.CreateFileW(path, _FILE_APPEND_DATA, _SHARE_READ_WRITE, None,
                             _OPEN_ALWAYS, _FILE_ATTRIBUTE_NORMAL, None)
    if handle is None or handle == _wt.HANDLE(-1).value:
        raise OSError(ctypes.get_last_error(), f"追加打开失败: {path}")
    try:
        payload = data.encode("utf-8")
        written = _wt.DWORD(0)
        ok = k32.WriteFile(handle, payload, len(payload),
                           ctypes.byref(written), None)
        if not ok or written.value != len(payload):
            raise OSError(ctypes.get_last_error(), f"追加写入失败: {path}")
    finally:
        k32.CloseHandle(handle)
def _append_posix(path: str, data: str) -> None:
    with open(path, "a", encoding="utf-8") as f:
        f.write(data)
def _atomic_append(path: str, data: str) -> None:
    if os.name == "nt":
        _append_windows(path, data)
    else:
        _append_posix(path, data)
def _register_to_d4_locked(skill_name: str, skill_type: str,
                           d4_path: str) -> bool:
    _registered = _d4_entry_exists(d4_path, skill_name)
    if _registered is None and os.path.exists(d4_path):
        raise OSError(
            f"D4 registry 存在但不可读，拒绝在未知内容上追加改写: {d4_path}")
    if _registered:
        logger.info("[OK] D4 registry 已存在 %s，跳过重复注册", skill_name)
        return True
    if not os.path.exists(d4_path):
        _atomic_append(d4_path, "# D4 Registry\n")
    created_date = datetime.now().date().isoformat()
    entry = f"""
- name: {yaml_safe_quote(skill_name)}
  type: {yaml_safe_quote(skill_type)}
  source: {yaml_safe_quote(PACKAGE_NAME)}
  created: {created_date}
  status: active
"""
    _atomic_append(d4_path, entry)
    logger.info("[OK] D4 registry 已更新: %s", d4_path)
    return True
def register_to_d4(skill_name: str, skill_type: str) -> bool:
    try:
        skill_name = _normalize_d4_field(skill_name, "skill_name")
        skill_type = _normalize_d4_field(skill_type, "skill_type")
    except (TypeError, ValueError) as exc:
        logger.warning("[WARN] D4 注册字段非法，拒绝注册: %s", exc)
        return False
    try:
        d4_path = _d4_registry_path()
    except RuntimeError as exc:
        logger.warning("[WARN] D4 registry 路径不可用，拒绝注册: %s", exc)
        return False
    try:
        os.makedirs(os.path.dirname(d4_path), exist_ok=True)
    except OSError as exc:
        logger.warning("[WARN] D4 registry 目录创建失败，拒绝注册: %s", exc)
        return False
    try:
        with locked_artifact(d4_path) as locked:
            if not locked:
                logger.warning("[WARN] D4 registry 写锁不可用，拒绝解锁写入")
                return False
            return _register_to_d4_locked(skill_name, skill_type, d4_path)
    except OSError as exc:
        logger.warning("[WARN] D4 registry 更新失败: %s", exc)
        return False
def _find_d4_entry(entries: list[dict], name: str) -> dict | None:
    for entry in entries:
        if entry.get("name") == name:
            return entry
    return None
def query_d4_registry(skill_name: str | None = None) -> list[dict] | dict | None:
    try:
        d4_path = _d4_registry_path()
    except RuntimeError as exc:
        logger.warning("[WARN] D4 registry 路径不可用，按未注册处理: %s", exc)
        return [] if skill_name is None else None
    if skill_name is not None:
        if not isinstance(skill_name, str):
            return None
        skill_name = skill_name.strip()
    content = _load_d4_registry_content(d4_path)
    if content is None:
        return [] if skill_name is None else None
    entries = _parse_d4_entries(content)
    if entries is None:
        logger.warning("[WARN] D4 registry 查询失败，按未注册处理: %s", d4_path)
        return [] if skill_name is None else None
    if skill_name is None:
        return entries
    return _find_d4_entry(entries, skill_name)
def _load_d4_registry_content(d4_path: str) -> str | None:
    if not os.path.exists(d4_path):
        return None
    try:
        with open(d4_path, encoding="utf-8-sig") as f:
            return f.read()
    except (OSError, UnicodeDecodeError) as e:
        logger.warning("D4 registry 读取失败: %s", e)
        return None
def is_d4_registered(skill_name: str) -> bool:
    if not isinstance(skill_name, str) or not skill_name.strip():
        return False
    return query_d4_registry(skill_name) is not None
def _advance_registered_state(lifecycle: SkillLifecycle, skill_name: str,
                              current: str) -> bool:
    if current != SkillState.TESTING and not lifecycle.set_skill_state(
            skill_name, SkillState.TESTING):
        logger.warning(
            "run_registration: %s 无法进入 testing，停止注册状态推进", skill_name)
        return False
    if lifecycle.set_skill_state(skill_name, SkillState.REGISTERED):
        return True
    logger.warning(
        "run_registration: %s 无法进入 registered，生命周期注册未完成", skill_name)
    return False
def _current_lifecycle_state(lifecycle: SkillLifecycle,
                             skill_name: str) -> Any:
    state = lifecycle.load_state()
    skills_map = state.get("skills") if isinstance(state, dict) else None
    entry = _skill_entry_of(skills_map, skill_name, "")
    if not entry:
        return SkillState.DRAFT
    current = entry.get("state")
    if not isinstance(current, str) or current not in SkillState.TRANSITIONS:
        if current not in (None, ""):
            logger.warning(
                "run_registration: %s 生命周期状态非法 %r，按 draft 继续",
                skill_name, current)
        return SkillState.DRAFT
    return current
def _registration_metadata(registration_ok: bool) -> dict[str, Any]:
    return {
        "last_registration_at": datetime.now().isoformat(timespec="seconds"),
        "last_registration_ok": registration_ok,
    }
def _advance_lifecycle(skill_dir: str, skill_name: str,
                       registration_ok: bool) -> bool:
    try:
        lifecycle = SkillLifecycle(skill_dir)
        state_ok = False
        if registration_ok:
            current = _current_lifecycle_state(lifecycle, skill_name)
            if current in (SkillState.REGISTERED, SkillState.ACTIVE,
                           SkillState.DEPRECATED, SkillState.RETIRED):
                logger.info(
                    "run_registration: %s 已处于 %s，跳过状态推进（幂等重注册）",
                    skill_name, current)
                state_ok = True
            else:
                state_ok = _advance_registered_state(
                    lifecycle, skill_name, current)
        recorded = lifecycle.set_skill_state(
            skill_name, _current_lifecycle_state(lifecycle, skill_name),
            metadata=_registration_metadata(registration_ok))
        if not recorded:
            logger.warning(
                "run_registration: %s 注册记录写入失败，生命周期结果不完整",
                skill_name)
        return state_ok and recorded
    except (OSError, ValueError, TypeError, RuntimeError) as exc:
        logger.warning("run_registration: 生命周期状态写入失败(不阻断): %s", exc)
        return False
@requires_contract(REGISTER_CONTRACT)
@auto_crystallize(operation_name="pipeline.run_registration", module_name="pipeline")
def run_registration(
    skill_name: str,
    skill_type: str,
    skill_dir: str,
) -> dict:
    skill_name = _normalize_d4_field(skill_name, "skill_name")
    skill_type = _normalize_d4_field(skill_type, "skill_type")
    results = {
        "skill_name": skill_name,
        "skill_type": skill_type,
        "d4": False,
    }
    logger.info("\n=== 注册技能: %s (%s) ===\n", skill_name, skill_type)
    try:
        results["d4"] = register_to_d4(skill_name, skill_type)
    except OSError as exc:
        logger.warning("run_registration: D4 注册失败(降级继续): %s", exc)
        results["d4"] = False
    registration_ok = bool(results["d4"])
    results["lifecycle"] = _advance_lifecycle(
        skill_dir, skill_name, registration_ok)
    all_ok = registration_ok and results["lifecycle"]
    logger.info("\n=== 注册%s ===", "成功" if all_ok else "部分完成")
    for k, v in results.items():
        if isinstance(v, bool):
            logger.info("  %s: %s", k, "OK" if v else "FAIL")
    return results
_DESC_OPTIMAL_MAX_LENGTH = 200
_DESC_ISSUE_MAX_LENGTH = DESC_MAX_LENGTH
_DESC_MIN_LENGTH = 50
_DESC_SCORE_MIN_LENGTH = 30
_DESC_SCORE_GOOD = 20
_DESC_SCORE_OK = 10
_DESC_SCORE_PENALTY = 10
_DESC_ERROR_THRESHOLD = 500
_KEYWORD_HIT_BONUS = 3
_KEYWORD_BONUS_CAP = 20
_SCENARIO_SIGNAL_BONUS = 5
_QUALITY_BASE_SCORE = 50
_QUALITY_SCORE_MIN = 0
_QUALITY_SCORE_MAX = 100
_LOW_QUALITY_ADVICE_SCORE = 50
_DUPLICATE_SIMILARITY_THRESHOLD = 0.8
_DIR_SIZE_WARN_BYTES = 1024 * 1024
_INACTIVITY_MESSAGES = (
    (f"休眠技能: {_RECENT_DAYS}天内无调用", "检查是否仍需要此技能"),
    (f"僵尸技能: {ZOMBIE_THRESHOLDS['zombie_days']}天内无调用记录",
     "考虑标记为 deprecated 或清理"),
)
_SKILL_MD_MAX_LINES = SKILL_MD_LINE_LIMIT
_TRIGGER_KEYWORDS = ("使用", "触发", "MUST", "when", "创建", "编辑", "处理",
                     "生成", "导出", "分析", "读取", "转换")
_SCENARIO_SIGNAL_GROUPS = (
    ("must",),
    ("触发", "when"),
    ("禁止", "严禁"),
)
def _keyword_coverage_bonus(description: str) -> int:
    lowered = description.lower()
    hit_count = sum(1 for keyword in _TRIGGER_KEYWORDS
                    if keyword.lower() in lowered)
    return min(hit_count * _KEYWORD_HIT_BONUS, _KEYWORD_BONUS_CAP)
def _scenario_signal_bonus(description: str) -> int:
    lowered = description.lower()
    return sum(
        _SCENARIO_SIGNAL_BONUS
        for signals in _SCENARIO_SIGNAL_GROUPS
        if any(signal in lowered for signal in signals)
    )
def _description_length_score(length: int) -> int:
    if length <= 0:
        return -_DESC_SCORE_PENALTY
    if _DESC_MIN_LENGTH <= length <= _DESC_OPTIMAL_MAX_LENGTH:
        return _DESC_SCORE_GOOD
    if _DESC_SCORE_MIN_LENGTH <= length <= _DESC_ERROR_THRESHOLD:
        return _DESC_SCORE_OK
    if length > _DESC_ERROR_THRESHOLD:
        return -_DESC_SCORE_PENALTY
    return 0
@dataclass
class SkillHealth:
    name: str
    path: str
    description: str = ""
    description_length: int = 0
    skill_md_lines: int = 0
    skill_md_chars: int = 0
    total_file_size: int = 0
    last_called: str | None = None
    call_count_30d: int = 0
    call_count_90d: int = 0
    is_zombie: bool = False
    is_duplicate: bool = False
    duplicate_of: str = ""
    quality_score: int = 0
    issues: list[str] = field(default_factory=list)
    suggestions: list[str] = field(default_factory=list)
@dataclass
class DiagnoseReport:
    skills: list[SkillHealth] = field(default_factory=list)
    total_skills: int = 0
    zombie_count: int = 0
    duplicate_pairs: list[tuple[str, str]] = field(default_factory=list)
    total_token_usage: int = 0
    avg_quality_score: float = 0.0
    generated_at: str = ""
def _description_tokens(text: str) -> set[str]:
    tokens: set[str] = set()
    for m in re.finditer(r"[a-zA-Z0-9]+|([\u4e00-\u9fff]+)", text.lower()):
        seg = m.group(0)
        if m.group(1):
            if len(seg) == 1:
                tokens.add(seg)
            else:
                tokens.update(seg[i:i + 2] for i in range(len(seg) - 1))
        else:
            tokens.add(seg)
    return tokens
def _read_lifecycle_entries(state_dir: str, fname: str) -> dict[str, dict]:
    skill_name = fname[: -len(_LIFECYCLE_FILE_SUFFIX)]
    fpath = os.path.join(state_dir, fname)
    try:
        with open(fpath, encoding="utf-8-sig") as f:
            state = json.load(f)
    except JSON_READ_DEGRADE_EXC as exc:
        logger.debug("usage state unreadable: %s (%s)", fpath, exc)
        return {}
    if not isinstance(state, dict):
        return {}
    skills_map = state.get("skills")
    if not isinstance(skills_map, dict) or not skills_map:
        return {}
    entries: dict[str, dict] = {}
    for key, entry in skills_map.items():
        if not isinstance(entry, dict) or not entry:
            continue
        key_text = str(key).strip()
        if key_text:
            entries.setdefault(key_text, entry)
        recorded = entry.get("name")
        if isinstance(recorded, str) and recorded.strip():
            entries.setdefault(recorded.strip(), entry)
    if not entries:
        return {}
    matched = _skill_entry_of(entries, skill_name, "")
    if not matched and len(skills_map) == 1:
        matched = next(iter(entries.values()))
    if matched:
        entries.setdefault(skill_name, matched)
    return entries
class SkillDiagnoser:
    def __init__(self: Self, skills_dir: str, state_dir: str | None = None) -> None:
        self.skills_dir = _coerce_skill_dir(skills_dir)
        self.state_dir = state_dir
    def _child_skill_dirs(self: Self) -> list[str]:
        try:
            entries = sorted(os.listdir(self.skills_dir))
        except OSError as exc:
            logger.warning(
                "_child_skill_dirs: 列举目录失败，跳过子目录扫描: %s (%s)",
                self.skills_dir,
                exc,
            )
            return []
        children: list[str] = []
        for item in entries:
            if is_pruned_scan_dir(item, frozenset()):
                continue
            item_path = os.path.join(self.skills_dir, item)
            if not os.path.isdir(item_path):
                continue
            if not os.path.isfile(os.path.join(item_path, "SKILL.md")):
                continue
            children.append(item_path)
        return children
    def _collect_skills(self: Self) -> list[SkillHealth]:
        skills = []
        if not os.path.isdir(self.skills_dir):
            return skills
        own_md = os.path.join(self.skills_dir, "SKILL.md")
        if os.path.isfile(own_md):
            skills.append(self._health_of(
                os.path.basename(os.path.normpath(self.skills_dir)),
                self.skills_dir, own_md))
        for item_path in self._child_skill_dirs():
            skills.append(self._health_of(
                os.path.basename(item_path), item_path,
                os.path.join(item_path, "SKILL.md")))
        return skills
    def _health_of(self, name: str, path: str, skill_md: str) -> SkillHealth:
        health = SkillHealth(name=name, path=path)
        self._parse_skill_md(health, skill_md)
        health.total_file_size = self._compute_dir_size(path)
        return health
    def _parse_skill_md(self: Self, health: SkillHealth, skill_md_path: str) -> None:
        try:
            content = _read_skill_md_text(skill_md_path)
            if content is None:
                return
            health.skill_md_lines = count_lines(content)
            health.skill_md_chars = len(content)
            meta = parse_skill_md_text(content)
            description = meta.get("description")
            health.description = description if isinstance(description, str) else ""
            health.description_length = len(health.description)
        except (RuntimeError, ValueError, TypeError, OSError) as exc:
            logger.warning("SKILL.md 解析失败: %s (%s)", skill_md_path, exc)
    @staticmethod
    def _compute_dir_size(dir_path: str) -> int:
        total = 0
        def _on_walk_error(exc: OSError) -> None:
            logger.warning(
                "_compute_dir_size: 目录遍历失败，按已收集部分统计: %s", exc)
        for root, dirs, files in os.walk(dir_path, onerror=_on_walk_error):
            dirs[:] = [d for d in dirs if not is_pruned_dirname(d)]
            for f in files:
                fp = os.path.join(root, f)
                try:
                    total += os.path.getsize(fp)
                except OSError:
                    logger.warning("File size read failed: %s", fp)
        return total
    def _diag_token_usage(self: Self, skills: list[SkillHealth]) -> None:
        for s in skills:
            if s.description_length > _DESC_ISSUE_MAX_LENGTH:
                s.issues.append(f"description 过长 ({s.description_length} 字符)")
                s.suggestions.append(
                    f"精简 description 到 {_DESC_ISSUE_MAX_LENGTH} 字符以内")
            if s.skill_md_lines > _SKILL_MD_MAX_LINES:
                s.issues.append(
                    f"SKILL.md 行数超标 ({s.skill_md_lines} > {_SKILL_MD_MAX_LINES})")
                s.suggestions.append("将细节内容拆分到 references/ 子文件")
            if s.total_file_size > _DIR_SIZE_WARN_BYTES:
                s.issues.append(f"技能目录过大 ({s.total_file_size / 1024:.0f} KB)")
                s.suggestions.append("检查是否有冗余文件或大文件可移除")
    @staticmethod
    def _add_state_dir(dirs: list[str], seen: set[str], path: str) -> None:
        try:
            key = os.path.normcase(os.path.abspath(path))
        except (OSError, ValueError, TypeError) as exc:
            logger.debug("_add_state_dir: 状态目录归一失败，跳过 %s (%s)",
                         path, exc)
            return
        if key in seen or not os.path.isdir(path):
            return
        seen.add(key)
        dirs.append(path)
    def _state_dirs(self: Self) -> list[str]:
        dirs: list[str] = []
        seen: set[str] = set()
        if self.state_dir:
            self._add_state_dir(dirs, seen, self.state_dir)
            return dirs
        try:
            primary = lifecycle_state_dir(self.skills_dir)
        except (RuntimeError, ValueError) as exc:
            primary = _fallback_state_dir(self.skills_dir)
            logger.warning(
                "_state_dirs: 根状态目录不可用，改读写入侧隔离回退目录: %s (%s)",
                primary, exc)
        if primary:
            self._add_state_dir(dirs, seen, primary)
        for child in self._child_skill_dirs():
            try:
                child_dir = lifecycle_state_dir(child)
            except (RuntimeError, ValueError) as exc:
                child_dir = _fallback_state_dir(child)
                logger.debug(
                    "_state_dirs: 子技能状态目录不可用，改读写入侧隔离回退目录: %s (%s)",
                    child_dir, exc)
            self._add_state_dir(dirs, seen, child_dir)
        return dirs
    def _load_usage_records(self) -> dict[str, dict]:
        records: dict[str, dict] = {}
        for state_dir in self._state_dirs():
            try:
                entries = sorted(os.listdir(state_dir))
            except OSError as exc:
                logger.warning(
                    "_load_usage_records: 列举状态目录失败: %s (%s)",
                    state_dir, exc)
                continue
            for fname in entries:
                if not fname.endswith(_LIFECYCLE_FILE_SUFFIX):
                    continue
                file_records = _read_lifecycle_entries(state_dir, fname)
                for name, entry in file_records.items():
                    records.setdefault(name, entry)
        return records
    @staticmethod
    def _has_time_evidence(entry: dict, now: datetime) -> bool:
        return any(stamp <= now for stamp in _usage_timestamps(entry))
    def _detect_zombies(self: Self, skills: list[SkillHealth]) -> None:
        records = self._load_usage_records()
        now = datetime.now()
        for s in skills:
            entry = _skill_entry_of(records, s.name, s.path)
            if not isinstance(entry, dict) or int_metric(
                    entry.get("usage_count")) <= 0:
                continue
            last_used = entry.get("last_used")
            s.last_called = (
                last_used if isinstance(last_used, str) and last_used else None
            )
            s.call_count_30d = _usage_events_in_window(
                entry, _RECENT_DAYS, now)
            s.call_count_90d = _usage_events_in_window(
                entry, _STALE_DAYS, now)
            if s.call_count_30d > 0:
                continue
            if not self._has_time_evidence(entry, now):
                logger.debug("[SkillDiagnoser] %s 无时间证据，跳过僵尸判定", s.name)
                continue
            s.is_zombie = _usage_events_in_window(
                entry, ZOMBIE_THRESHOLDS["zombie_days"], now) == 0
            issue, suggestion = _INACTIVITY_MESSAGES[s.is_zombie]
            s.issues.append(issue)
            s.suggestions.append(suggestion)
    def _detect_duplicates(self: Self, skills: list[SkillHealth]) -> list[tuple[str, str]]:
        duplicates = []
        for i in range(len(skills)):
            for j in range(i + 1, len(skills)):
                sim = self._description_similarity(skills[i].description, skills[j].description)
                if sim > _DUPLICATE_SIMILARITY_THRESHOLD:
                    duplicates.append((skills[i].name, skills[j].name))
                    skills[i].is_duplicate = True
                    skills[j].is_duplicate = True
                    if not skills[j].duplicate_of:
                        skills[j].duplicate_of = (
                            skills[i].duplicate_of or skills[i].name)
        return duplicates
    @staticmethod
    def _description_similarity(desc1: str, desc2: str) -> float:
        if not desc1 or not desc2:
            return 0.0
        set1 = _description_tokens(desc1)
        set2 = _description_tokens(desc2)
        if not set1 or not set2:
            return 0.0
        intersection = len(set1 & set2)
        union = len(set1 | set2)
        return intersection / union if union > 0 else 0.0
    @staticmethod
    def _score_one_skill(s: SkillHealth) -> int:
        score = (_QUALITY_BASE_SCORE
                 + _keyword_coverage_bonus(s.description)
                 + _scenario_signal_bonus(s.description)
                 + _description_length_score(s.description_length))
        return max(_QUALITY_SCORE_MIN, min(_QUALITY_SCORE_MAX, score))
    def _score_quality(self: Self, skills: list[SkillHealth]) -> None:
        for s in skills:
            s.quality_score = self._score_one_skill(s)
            if s.quality_score < _LOW_QUALITY_ADVICE_SCORE:
                s.issues.append(f"描述质量偏低 ({s.quality_score}/100)")
                s.suggestions.append("增加触发关键词,明确触发场景和禁止场景")
    @timed_log()
    def run_full_diag(self: Self) -> DiagnoseReport:
        skills = self._collect_skills()
        self._diag_token_usage(skills)
        self._detect_zombies(skills)
        detected_pairs = self._detect_duplicates(skills)
        self._score_quality(skills)
        zombie_count = sum(1 for s in skills if s.is_zombie)
        duplicate_pairs = [tuple(sorted(pair)) for pair in detected_pairs]
        total_token_usage = sum(
            max(1, s.skill_md_chars // 4) if s.skill_md_chars else 0
            for s in skills
        )
        avg_quality = sum(s.quality_score for s in skills) / max(len(skills), 1)
        return DiagnoseReport(
            generated_at=datetime.now().isoformat(),
            total_skills=len(skills),
            zombie_count=zombie_count,
            duplicate_pairs=duplicate_pairs,
            total_token_usage=total_token_usage,
            avg_quality_score=round(avg_quality, 1),
            skills=skills,
        )
@requires_contract(DIAG_CONTRACT)
@auto_crystallize(operation_name="pipeline.diag_skills_directory", module_name="pipeline")
def diag_skills_directory(
    skills_dir: str,
    output_json: str | None = None,
) -> DiagnoseReport:
    diagnoser = SkillDiagnoser(skills_dir)
    report = diagnoser.run_full_diag()
    if output_json:
        try:
            write_diag_report_json(report, output_json)
        except (OSError, ValueError, TypeError, ContractViolationError) as exc:
            logger.warning("[SkillDiagnoser] 诊断报告落盘失败(不阻断): %s (%s)",
                           output_json, exc)
    return report
def write_diag_report_json(report: DiagnoseReport, output_json: str) -> None:
    report_data = {
        "generated_at": report.generated_at,
        "total_skills": report.total_skills,
        "zombie_count": report.zombie_count,
        "duplicate_pairs": report.duplicate_pairs,
        "total_token_usage": report.total_token_usage,
        "avg_quality_score": report.avg_quality_score,
        "skills": [
            {
                "name": s.name,
                "path": s.path,
                "description_length": s.description_length,
                "skill_md_lines": s.skill_md_lines,
                "skill_md_chars": s.skill_md_chars,
                "total_file_size": s.total_file_size,
                "last_called": s.last_called,
                "call_count_30d": s.call_count_30d,
                "call_count_90d": s.call_count_90d,
                "is_zombie": s.is_zombie,
                "is_duplicate": s.is_duplicate,
                "duplicate_of": s.duplicate_of,
                "quality_score": s.quality_score,
                "issues": s.issues,
                "suggestions": s.suggestions,
            }
            for s in report.skills
        ],
    }
    write_json_artifact(output_json, report_data, indent=2)
def _is_crlf_only(text: str) -> bool:
    return "\r\n" in text and "\n" not in text.replace("\r\n", "")
def _detect_line_ending(text: str) -> str:
    if _is_crlf_only(text):
        return "\r\n"
    if "\r" in text and "\n" not in text:
        return "\r"
    return ""
def _normalize_newlines(text: str, eol: str) -> str:
    if eol == "\r\n":
        return text.replace("\r\n", "\n")
    if eol == "\r":
        return text.replace("\r", "\n")
    return text
def _split_doc_form(doc: str) -> tuple[str, str, str]:
    bom = "\ufeff" if doc.startswith("\ufeff") else ""
    body = doc[len(bom):]
    eol = _detect_line_ending(body)
    return bom, _normalize_newlines(body, eol), eol
def _join_doc_form(bom: str, text: str, eol: str) -> str:
    return bom + (text.replace("\n", eol) if eol else text)
@dataclass(frozen=True)
class _SectionSpec:
    label: str
    markers: tuple[str, ...]
    inserted_title: str
    prefixed_title: str
_INPUT_SECTION = _SectionSpec(
    "Inputs",
    ("## Input", "## Inputs", "## 输入", "## 输入参数", "## 参数"),
    "Adaptation Note", "Input Adaptation Note")
_WORKFLOW_SECTION = _SectionSpec(
    "Workflow",
    ("## Workflow", "## Quick Start", "## Usage", "## 工作流",
     "## 快速开始", "## 快速上手", "## 使用说明", "## 使用方法"),
    "Workflow Adaptation Note", "Workflow Adaptation Note")
_STOP_SECTION = _SectionSpec(
    "Stop conditions",
    ("## Stop", "## Completion", "## Output", "## Limitations",
     "## 停止条件", "## 完成条件", "## 输出", "## 限制", "## 能力边界"),
    "Stop Condition Adaptation Note", "Stop Condition Note")
def _marker_line_pattern(marker: str) -> re.Pattern[str]:
    return re.compile(
        r"(?m)^(" + re.escape(marker) + r"(?:[ \t]+[^\n]*)?)$")
@dataclass
class AdaptationPlan:
    source_skill: str = ""
    target_name: str = ""
    differences: list = field(default_factory=list)
    description_changes: dict = field(default_factory=dict)
    input_changes: dict = field(default_factory=dict)
    workflow_changes: dict = field(default_factory=dict)
    stop_condition_changes: dict = field(default_factory=dict)
@dataclass
class AdaptationResult:
    plan: AdaptationPlan | None = None
    adapted_skill_md: str = ""
    warnings: list = field(default_factory=list)
    errors: list = field(default_factory=list)
class SkillAdapter:
    def __init__(self, skills_dir: str | None = None) -> None:
        self.skills_dir = normalize_text(skills_dir) or os.getcwd()
    def _locate_source_skill_md(self, source_skill: str) -> str:
        source_skill = normalize_text(source_skill).strip()
        if os.path.basename(os.path.normpath(source_skill)).lower() == "skill.md":
            return os.path.join(self.skills_dir, source_skill)
        primary = os.path.join(self.skills_dir, source_skill, "SKILL.md")
        if os.path.exists(primary):
            return primary
        root_name = os.path.basename(os.path.normpath(self.skills_dir))
        if source_skill == root_name:
            return os.path.join(self.skills_dir, "SKILL.md")
        return primary
    def analyze_differences(self, source_skill: str, user_requirements: str = "",
                            source_md: str | None = None) -> AdaptationPlan:
        source_skill = normalize_text(source_skill)
        user_requirements = normalize_text(user_requirements)
        plan = AdaptationPlan(source_skill=source_skill)
        differences = []
        source_desc = ""
        if source_md is not None:
            source_desc = extract_description(source_md)
        else:
            skill_md_path = self._locate_source_skill_md(source_skill)
            if os.path.exists(skill_md_path):
                source_desc = _read_source_description(skill_md_path)
        if user_requirements:
            differences.append("User requires: " + user_requirements)
            _plan_requirement_review(plan, user_requirements, source_desc)
        plan.differences = differences
        logger.info("[SkillAdapter] Analyzed %d differences for %s", len(differences), source_skill)
        return plan
    def adapt_description(self, md: str, description_changes: dict) -> str:
        if not description_changes or not isinstance(description_changes, dict):
            return md
        action = description_changes.get("action", "")
        if action == "update":
            target_req = normalize_text(
                description_changes.get("target_requirements", ""))
            if target_req:
                requirement_lines = target_req.replace(
                    "\r\n", "\n").replace("\r", "\n").split("\n")
                note = f"> Adapted for: {requirement_lines[0]}" + "".join(
                    f"\n> {line}" for line in requirement_lines[1:])
                normalized_md = md.replace("\r\n", "\n").replace("\r", "\n")
                if note not in normalized_md:
                    md = self._insert_after_frontmatter(md, note)
        logger.info("[SkillAdapter] Description adapted (action=%s)", action)
        return md
    @staticmethod
    def _insert_after_frontmatter(md: str, note_line: str) -> str:
        bom, text, crlf = _split_doc_form(md)
        parts = split_frontmatter(text)
        if len(parts) >= 3 and not parts[0].strip():
            lf_text = text.replace("\r\n", "\n").replace("\r", "\n")
            close_end_lf = len(lf_text) - len(parts[2])
            close_end = close_end_lf
            if lf_text != text:
                raw_pos = 0
                lf_pos = 0
                while raw_pos < len(text) and lf_pos < close_end_lf:
                    raw_pos += 2 if text.startswith("\r\n", raw_pos) else 1
                    lf_pos += 1
                close_end = raw_pos
            head = text[:close_end]
            body = text[close_end:].lstrip("\r\n")
        else:
            head = ""
            body = text.lstrip("\r\n")
        block = f"{head}\n\n{note_line}" if head else note_line
        result = f"{block}\n\n{body}" if body else f"{block}\n"
        return _join_doc_form(bom, result, crlf)
    def _adapt_review_section(self, md: str, changes: dict,
                             spec: _SectionSpec) -> str:
        if not changes or not isinstance(changes, dict):
            return md
        action = changes.get("action", "")
        note = changes.get("note", "")
        if action == "review" and note:
            md = self._insert_marker_note(
                md, list(spec.markers), spec.inserted_title,
                spec.prefixed_title, note)
        logger.info("[SkillAdapter] %s adapted (action=%s)", spec.label, action)
        return md
    @staticmethod
    def _insert_marker_note(md: str, markers: list[str],
                            inserted_title: str, prefixed_title: str,
                            note: str) -> str:
        bom, text, crlf = _split_doc_form(md)
        note_blocks = (
            f"> **{inserted_title}**: {note}",
            f"> **{prefixed_title}**: {note}",
        )
        if any(note_block in text for note_block in note_blocks):
            return md
        suffix = f"\n\n{note_blocks[0]}"
        lines = text.splitlines(keepends=True)
        content_lines = [line.rstrip("\r\n") for line in lines]
        fenced = [in_fence for _line, in_fence in iter_fence_lines(content_lines)]
        for marker in markers:
            marker_pat = _marker_line_pattern(marker)
            for idx, line in enumerate(lines):
                candidate = content_lines[idx]
                if fenced[idx] or not marker_pat.match(candidate):
                    continue
                lines[idx] = candidate + suffix + line[len(candidate):]
                return _join_doc_form(bom, "".join(lines), crlf)
        fallback = SkillAdapter._insert_after_frontmatter(
            text, f"> **{prefixed_title}**: {note}")
        if fallback == text:
            return md
        return _join_doc_form(bom, fallback, crlf)
def _read_source_description(skill_md_path: str) -> str:
    content = _read_skill_md_text(skill_md_path)
    return extract_description(content) if content is not None else ""
def _plan_requirement_review(plan: AdaptationPlan, user_requirements: str,
                             source_desc: str) -> None:
    plan.description_changes = {
        "action": "update",
        "source_description": source_desc[:200],
        "target_requirements": user_requirements,
    }
    plan.input_changes = {"action": "review",
                          "note": "Inputs may need adjustment based on new requirements"}
    plan.workflow_changes = {"action": "review",
                             "note": "Workflow steps may need adjustment for target skill"}
    plan.stop_condition_changes = {"action": "review",
                                   "note": "Stop conditions should align with target skill scope"}
def _load_source_md(candidate: str) -> tuple[str, str | None]:
    if not os.path.exists(candidate):
        return "", f"源 SKILL.md 不存在，仅返回改造计划: {candidate}"
    content = _read_skill_md_text(candidate)
    if content is None:
        return "", f"读取源 SKILL.md 失败，仅返回改造计划: {candidate}"
    return content, None
def _apply_adaptation_plan(adapter: SkillAdapter, plan: AdaptationPlan,
                           md: str) -> str:
    md = adapter.adapt_description(md, plan.description_changes)
    md = adapter._adapt_review_section(md, plan.input_changes, _INPUT_SECTION)
    md = adapter._adapt_review_section(
        md, plan.workflow_changes, _WORKFLOW_SECTION)
    return adapter._adapt_review_section(
        md, plan.stop_condition_changes, _STOP_SECTION)
def _derive_target_name(source_skill: str) -> str:
    text = normalize_text(source_skill).strip().rstrip("/\\")
    if not text:
        return ""
    leaf = os.path.basename(text)
    if leaf.lower() == "skill.md":
        leaf = os.path.basename(os.path.dirname(text))
    return leaf or text
@requires_contract(ADAPT_CONTRACT)
def adapt_skill(source_skill: str, target_name: str | None = None,
                user_requirements: str = "", skills_dir: str | None = None,
                source_md: str | None = None) -> AdaptationResult:
    target_name = normalize_text(target_name)
    user_requirements = normalize_text(user_requirements)
    source_md = normalize_text(source_md)
    adapter = SkillAdapter(skills_dir)
    plan = adapter.analyze_differences(
        source_skill, user_requirements, source_md=source_md or None)
    plan.target_name = target_name or _derive_target_name(source_skill)
    result = AdaptationResult(plan=plan)
    md = source_md
    if not md:
        candidate = adapter._locate_source_skill_md(source_skill)
        md, _load_warning = _load_source_md(candidate)
        if _load_warning:
            logger.warning("[SkillAdapter] %s", _load_warning)
            result.warnings.append(_load_warning)
    if md:
        result.adapted_skill_md = _apply_adaptation_plan(adapter, plan, md)
    return result

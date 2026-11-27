from __future__ import annotations

import itertools
import json
import logging
import os
import threading
import time
from dataclasses import (
    MISSING,
    asdict,
    dataclass,
    field,
)
from typing import (
    Any,
)

from jwsgj.diag_guard_io import (
    guarded_open,
    path_identity,
    safe_delete,
)
from jwsgj.diag_guard_state import (
    read_json_artifact,
    write_json_artifact,
)
from jwsgj.diag_types_normalize import (
    as_number,
    canonical_rule_key,
    dict_or_empty,
    make_locator_fast,
    parse_locator_file,
    safe_finding_line,
    safe_float,
    severity_penalty_weight,
    signal_bool,
)
from jwsgj.diag_types_vocab import (
    CONF_BOOST_SMALL,
    CONF_FLOOR,
    CONF_VERY_HIGH,
    HIGH_SEVERITY_PROTECTED,
    MESSAGE_TRUNCATE_LEN,
    SIGNAL_BASELINE_HIT_COUNT,
    SIGNAL_BASELINE_PERSISTENT_NOISE,
)
from jwsgj.log_config import (
    locked_artifact,
    log_swallowed,
)
from jwsgj.runtime_paths import (
    baseline_session_id,
    cv_conclusion_history_path,
    metrics_baseline_dir,
    path_scoped_namespace,
)
from jwsgj.runtime_scope import (
    is_diagnosis_out_of_scope,
    normalize_skill_dir,
    prune_walk_dirs,
)
from jwsgj.shared_cache_store import (
    T5_BASELINE_FILENAME,
)
from jwsgj.treatment_state import (
    apply_human_confirmation,
    canonical_locator_key,
)
from jwsgj.xv_context_derivation import (
    _is_dead_code_finding,
    _resolve_round_skill_dir,
    _skill_root_arg,
    generate_missing_placeholders,
)
from jwsgj.xv_intermediate_store import (
    compute_code_hash,
    get_round_start_ts,
    load_all_intermediates,
    peek_round_start_ts,
)

logger = logging.getLogger(__name__)
__all__ = [
    'COEXISTING_BASELINE_DATA_FILES',
    'COLD_START_EXEMPT_FAMILIES',
    'CONFIDENCE_DECAY_PER_OCCURRENCE',
    'MAX_BASELINE_SESSIONS',
    'OSCILLATION_FLIP_PAIRS',
    'OSCILLATION_HISTORY_KEEP',
    'PERSISTENT_NOISE_THRESHOLD',
    'BaselineDiffResult',
    'BaselineEntry',
    'BaselineSession',
    'BaselineStore',
    'MetricsBaselineStore',
    'OscillationDetector',
    'annotate_findings',
    'apply_round_human_decisions',
    'build_oscillation_degraded_report',
    'build_oscillation_report_for_cv',
    'create_baseline_store',
    'diff_findings_with_baseline',
    'load_stage2b_baseline',
    'open_round_inputs',
    'persist_stage2b_baseline',
]
OSCILLATION_FLIP_PAIRS = frozenset({
    frozenset(("confirmed", "suppressed")),
    frozenset(("confirmed", "uncertain")),
    frozenset(("likely", "suppressed")),
    frozenset(("confirmed", "contradictory")),
})
OSCILLATION_HISTORY_KEEP = 20
_OSCILLATION_LOOKBACK_ROUNDS = 3
_OSCILLATION_HISTORY_LOCK = threading.RLock()
def _oscillation_report(enabled: bool) -> dict:
    return {"enabled": enabled, "history_rounds": 0,
            "oscillating_count": 0, "demoted_count": 0, "locators": []}
_CONCLUSIONS = ("confirmed", "likely", "uncertain", "suppressed",
                "investigated", "contradictory", "review", "reviewed")
def _history_round(raw_line: str) -> dict | None:
    line = raw_line.strip()
    if not line:
        return None
    try:
        obj = json.loads(line)
    except (json.JSONDecodeError, RecursionError) as e:
        logger.debug("JSON 解析失败（跳过）: %s", e)
        return None
    return obj if isinstance(obj, dict) else None
def _is_flipped(a: str, b: str) -> bool:
    if not a or not b or a == b:
        return False
    if a not in _CONCLUSIONS or b not in _CONCLUSIONS:
        return False
    return frozenset((a, b)) in OSCILLATION_FLIP_PAIRS
def _conclusions_map(history_entry) -> dict:
    if not isinstance(history_entry, dict):
        return {}
    conclusions = history_entry.get("conclusions", {})
    if not isinstance(conclusions, dict):
        return {}
    return {canonical_locator_key(locator): conclusion
            for locator, conclusion in conclusions.items()}
def _prev_round_maps(history: list) -> tuple:
    prev = _conclusions_map(history[-1]) if history else {}
    prev2 = _conclusions_map(history[-2]) if len(history) >= 2 else {}
    return prev, prev2
def _locator_conclusion(xvr: dict) -> tuple:
    loc = str(xvr.get("locator") or "")
    concl = str(xvr.get("conclusion") or "")
    if not loc or loc.startswith(("__statistical__", "CONTRADICTION:")):
        return "", ""
    if concl not in _CONCLUSIONS:
        return "", ""
    return loc, concl
class OscillationDetector:
    """跨轮振荡检测器。

    ``cv_conclusion_history.jsonl`` 是反哺进化的共享账本，而 locator 是项目
    内相对定位。若跨项目比较，B 项目会因 A 项目同名相对路径的结论翻转被误降
    级为 ``uncertain``，故按项目作用域只回看本项目轮次。
    """
    def __init__(self, skill_dir: str):
        try:
            self.skill_dir = normalize_skill_dir(_skill_root_arg(skill_dir))
            self._history_path = cv_conclusion_history_path(self.skill_dir)
            self._project = path_scoped_namespace(self.skill_dir)
        except Exception as e:  # noqa: BLE001
            self.skill_dir = ""
            self._history_path = ""
            self._project = ""
            logger.warning("[Oscillation] 历史路径初始化失败，振荡检测按无历史处理: %s", e)
    def _annotate_oscillations(self, xv_findings, prev: dict, prev2: dict,
                               report: dict) -> dict:
        current_map: dict = {}
        for xvr in xv_findings or []:
            if not isinstance(xvr, dict):
                continue
            loc, concl = _locator_conclusion(xvr)
            if not loc:
                continue
            self._annotate_flip_if_oscillating(
                xvr, loc, concl, prev, prev2, report)
            current_map[canonical_locator_key(loc)] = str(
                xvr.get("conclusion") or concl)
        return current_map
    def _annotate_flip_if_oscillating(
        self, xvr: dict, loc: str, concl: str, prev: dict, prev2: dict,
        report: dict,
    ) -> None:
        prev_conclusion = str(prev.get(canonical_locator_key(loc), "") or "")
        if prev_conclusion and _is_flipped(prev_conclusion, concl):
            self._annotate_flip(xvr, loc, prev_conclusion, prev2, report)
    def _annotate_flip(self, xvr: dict, loc: str,
                       prev_c: str, prev2: dict, report: dict) -> None:
        concl = str(xvr.get("conclusion", ""))
        xvr["_oscillating"] = True
        path2 = [str(prev2.get(canonical_locator_key(loc), "?")),
                 prev_c, concl]
        xvr["_oscillation_path"] = "→".join(path2)
        prev2_conclusion = str(
            prev2.get(canonical_locator_key(loc), "") or "")
        if (prev2 and _is_flipped(prev2_conclusion, prev_c)
                and xvr.get("conclusion") in ("confirmed", "suppressed", "contradictory")):
            xvr["_oscillation_demoted"] = True
            xvr["conclusion"] = "uncertain"
            xvr["conclusion_v2"] = "uncertain"
            report["demoted_count"] += 1
        report["locators"].append({
            "locator": loc,
            "path": xvr["_oscillation_path"],
            "demoted": bool(xvr.get("_oscillation_demoted")),
        })
    def _read_history_lines(self, *, propagate_io: bool = False) -> list[str]:
        if not self._history_path or not os.path.isfile(self._history_path):
            return []
        try:
            with open(self._history_path, encoding="utf-8") as f:
                return [ln for ln in f.read().splitlines() if ln.strip()]
        except (OSError, ValueError) as e:
            if propagate_io:
                raise
            logger.warning("[Oscillation] 历史读取失败，按无历史处理: %s", e)
            return []
    def _load_history(
            self, max_rounds: int = _OSCILLATION_LOOKBACK_ROUNDS) -> list[dict]:
        rounds = [obj for obj in map(_history_round, self._read_history_lines())
                  if obj is not None
                  and obj.get("project") == self._project]
        return rounds[-max_rounds:]
    def _ensure_history_dir(self) -> bool:
        try:
            os.makedirs(os.path.dirname(self._history_path), exist_ok=True)
            return True
        except (OSError, ValueError) as e:
            logger.warning("[Oscillation] 历史目录创建失败（不阻断 CV）: %s", e)
            return False
    def _append_and_trim(self, record: dict) -> None:
        if not self._history_path:
            return
        if not self._ensure_history_dir():
            return
        with _OSCILLATION_HISTORY_LOCK:
            self._append_and_trim_locked(record)
    def _append_and_trim_locked(self, record: dict) -> None:
        """锁内读-改-写：共享账本后多治理会话可同时追加。

        ``_OSCILLATION_HISTORY_LOCK`` 只是进程内线程锁；跨进程要靠
        ``locked_artifact`` 串行化，否则后写者会用旧快照覆盖前者新落的轮次。
        """
        try:
            with locked_artifact(self._history_path) as locked:
                if not locked:
                    logger.warning(
                        "[Oscillation] 历史写锁不可用，跳过追加保留原历史: %s",
                        self._history_path)
                    return
                lines = self._read_history_lines(propagate_io=True)
                lines.append(json.dumps(record, ensure_ascii=False))
                if len(lines) > OSCILLATION_HISTORY_KEEP:
                    lines = lines[-OSCILLATION_HISTORY_KEEP:]
                self._atomic_replace_history(lines)
        except (OSError, ValueError) as e:
            logger.warning(
                "[Oscillation] 历史读取失败，跳过追加保留原历史: %s", e)
    def _atomic_replace_history(self, lines: list[str]) -> None:
        tmp = (f"{self._history_path}.{os.getpid()}"
               f".{threading.get_ident()}.tmp")
        try:
            with open(tmp, "w", encoding="utf-8") as f:
                f.write("\n".join(lines) + "\n")
            os.replace(tmp, self._history_path)
        except (OSError, ValueError) as e:
            if os.path.isfile(tmp) and not safe_delete(tmp):
                logger.warning("[Oscillation] 半写 tmp 回收失败（残留待清）: %s", tmp)
            logger.warning("[Oscillation] 历史写入失败（不阻断 CV）: %s", e)
    def detect_and_annotate(self, xv_findings: list) -> dict:
        report = _oscillation_report(bool(self._history_path))
        history = self._load_history()
        report["history_rounds"] = len(history)
        prev, prev2 = _prev_round_maps(history)
        current_map = self._annotate_oscillations(xv_findings, prev, prev2, report)
        report["oscillating_count"] = len(report["locators"])
        _now_iso = time.strftime("%Y-%m-%dT%H:%M:%S")
        if current_map:
            self._append_and_trim({
                "ts": _now_iso,
                "timestamp": _now_iso,
                "project": self._project,
                "round_start_ts": peek_round_start_ts(self.skill_dir),
                "conclusions": current_map,
            })
        if report["oscillating_count"]:
            logger.info("[Oscillation] 检测到 %d 个跨轮振荡 locator（降级 %d 个）",
                        report["oscillating_count"], report["demoted_count"])
        return report
def build_oscillation_degraded_report(error: object) -> dict:
    report = _oscillation_report(False)
    report["error"] = str(error)
    return report
def build_oscillation_report_for_cv(skill_dir: str, xv_findings: list) -> dict:
    try:
        detector = OscillationDetector(skill_dir)
        return detector.detect_and_annotate(xv_findings)
    except Exception as e:
        logger.warning("[Oscillation] 振荡检测失败（不阻断 CV）: %s", e, exc_info=True)
        return build_oscillation_degraded_report(e)
def open_round_inputs(cv, intermediate_dir: str,
                      skill_dir: str | None = None) -> str:
    cv._intermediate_dir = intermediate_dir
    resolved = _resolve_round_skill_dir(skill_dir, intermediate_dir)
    cv.skill_dir = normalize_skill_dir(resolved) if resolved else ""
    cutoff = get_round_start_ts(cv.skill_dir) if cv.skill_dir else ""
    cv.independent_results = load_all_intermediates(
        intermediate_dir, freshness_cutoff=cutoff)
    generate_missing_placeholders(cv)
    return cv.skill_dir
def apply_round_human_decisions(validator, xv_findings) -> tuple[Any, int, int]:
    store, confirmed, suppressed = apply_human_confirmation(validator, xv_findings)
    if confirmed or suppressed:
        logger.info("[CV] 人工确认应用: %d 确认 / %d 抑制", confirmed, suppressed)
    return store, confirmed, suppressed
def _baseline_store_dir(skill_dir: str) -> str:
    return metrics_baseline_dir(_skill_root_arg(skill_dir))
MAX_BASELINE_SESSIONS = 30
_NO_GLOBAL_BASELINE_DIR = ""
_DEFAULT_BASELINE_SEVERITY = "P3"
METRICS_BASELINE_FILENAME = "metrics_baseline.json"
COEXISTING_BASELINE_DATA_FILES: frozenset[str] = frozenset({
    METRICS_BASELINE_FILENAME,
    T5_BASELINE_FILENAME,
})
@dataclass
class BaselineEntry:
    rule_id: str
    file: str
    line: int
    message: str = ""
    severity: str = _DEFAULT_BASELINE_SEVERITY
    session_id: str = ""
    code_hash: str = ""
    rule_family: str = ""
    def to_dict(self, compact: bool = False) -> dict:
        try:
            d = asdict(self)
            if compact:
                d.pop("message", None)
            return d
        except Exception as e:  # noqa: BLE001
            logger.warning("[XV] to_dict异常降级: %s", e)
            return {"_error": True, "_partial": True}
    @classmethod
    def from_dict(cls, d: dict) -> BaselineEntry:
        kwargs = _entry_kwargs(cls, d if isinstance(d, dict) else {})
        return cls(**_normalize_entry_kwargs(kwargs))
_STR_FIELD_DEFAULTS: dict[str, str] = {
    "rule_id": "", "file": "", "message": "",
    "severity": _DEFAULT_BASELINE_SEVERITY, "rule_family": "",
    "session_id": "", "code_hash": "",
}
_REQUIRED_FIELD_FALLBACKS: dict[str, object] = {"line": 0}
def _entry_kwargs(cls: type, data: dict) -> dict:
    kwargs = {}
    for name, f in cls.__dataclass_fields__.items():
        if name in data:
            kwargs[name] = data[name]
        elif f.default is not MISSING:
            kwargs[name] = f.default
        elif f.default_factory is not MISSING:
            kwargs[name] = f.default_factory()
        else:
            kwargs[name] = _REQUIRED_FIELD_FALLBACKS.get(
                name, _STR_FIELD_DEFAULTS.get(name, ""))
    return kwargs
def _normalize_entry_kwargs(kwargs: dict) -> dict:
    kwargs["line"] = safe_finding_line({"line": kwargs.get("line")})
    for key, default in _STR_FIELD_DEFAULTS.items():
        value = kwargs.get(key, default)
        kwargs[key] = value if isinstance(value, str) else default
    return kwargs
@dataclass
class BaselineSession:
    session_id: str
    timestamp: float
    skill_dir: str
    entries: list[BaselineEntry] = field(default_factory=list)
    is_seed: bool = False
    def to_dict(self, compact: bool = True) -> dict:
        try:
            return {
                "session_id": self.session_id,
                "timestamp": self.timestamp,
                "skill_dir": self.skill_dir,
                "entries": [e.to_dict(compact=compact) for e in self.entries],
                "is_seed": self.is_seed,
            }
        except Exception as e:  # noqa: BLE001
            logger.warning("[XV] to_dict异常降级: %s", e)
            return {"_error": True, "_partial": True}
    @classmethod
    def from_dict(cls, d: dict) -> BaselineSession:
        data = d if isinstance(d, dict) else {}
        sid = data.get("session_id", "")
        sid = sid if isinstance(sid, str) else ""
        skill_dir = data.get("skill_dir", "")
        return cls(
            session_id=sid,
            timestamp=safe_float(data.get("timestamp"), 0.0),
            skill_dir=skill_dir if isinstance(skill_dir, str) else "",
            entries=_session_entries(data.get("entries", []), sid),
            is_seed=signal_bool(data.get("is_seed", False)),
        )
def _session_entries(raw_entries: Any, session_id: str) -> list[BaselineEntry]:
    entries = (raw_entries if isinstance(raw_entries, list) else [])
    parsed = [BaselineEntry.from_dict(e) for e in entries if isinstance(e, dict)]
    dropped = len(entries) - len(parsed)
    if dropped:
        logger.warning("[Baseline] 会话条目含 %d 个非 dict 脏元素，已剔除",
                       dropped)
    if session_id:
        for entry in parsed:
            if not entry.session_id:
                entry.session_id = session_id
    return parsed
@dataclass
class BaselineDiffResult:
    locator: str
    is_new: bool
    hit_count: int
    code_unchanged_since: bool
    is_persistent_noise: bool
    confidence_multiplier: float
    first_seen_at: str = ""
    last_seen_at: str = ""
    def to_dict(self) -> dict:
        try:
            return {
                "locator": self.locator,
                "is_new": self.is_new,
                "hit_count": self.hit_count,
                "code_unchanged_since": self.code_unchanged_since,
                "is_persistent_noise": self.is_persistent_noise,
                "confidence_multiplier": self.confidence_multiplier,
                "first_seen_at": self.first_seen_at,
                "last_seen_at": self.last_seen_at,
            }
        except Exception as e:  # noqa: BLE001
            logger.warning("[to_dict] 异常降级: %s", e)
            return {"_error": True, "_partial": True}
def _locator_key(entry: BaselineEntry) -> str:
    return make_locator_fast({
        "file": entry.file,
        "line": entry.line,
        "rule_family": entry.rule_family,
        "rule_id": entry.rule_id,
    })
def _baseline_finding_rule_family(f: dict) -> str:
    rf = f.get("rule_family") or f.get("rule_id") or "diag_general"
    return rf if isinstance(rf, str) else str(rf)
def _session_skill_key(fname: str) -> str:
    stem = fname[:-len(".json")]
    return stem.rsplit("_", 1)[0] if "_" in stem else stem
def _global_session_group_key(directory: str, fname: str) -> tuple[str, str]:
    session = _load_session_file(os.path.join(directory, fname))
    if session is not None and session.skill_dir:
        return "skill", path_identity(session.skill_dir)
    return "legacy", _session_skill_key(fname)
def _session_order_key(directory: str, fname: str) -> tuple[float, str]:
    path = os.path.join(directory, fname)
    session = _load_session_file(path)
    if session is not None:
        return session.timestamp, fname
    try:
        return os.path.getmtime(path), fname
    except OSError:
        return 0.0, fname
def _roll_session_filenames(fnames: list[str], source: str,
                            directory: str) -> list[str]:
    if len(fnames) <= MAX_BASELINE_SESSIONS:
        return fnames
    if source == "global":
        groups: dict[tuple[str, str], list[str]] = {}
        for fname in fnames:
            groups.setdefault(
                _global_session_group_key(directory, fname), []).append(fname)
        return sorted(
            _f
            for _members in groups.values()
            for _f in sorted(
                _members,
                key=lambda name: _session_order_key(directory, name),
            )[-MAX_BASELINE_SESSIONS:])
    ordered = sorted(
        fnames, key=lambda name: _session_order_key(directory, name))
    return ordered[-MAX_BASELINE_SESSIONS:]
COLD_START_EXEMPT_FAMILIES: set[str] = {
    'security', 'sql_injection', 'path_traversal', 'command_injection',
    'hardcoded_credential', 'hardcoded_secret', 'insecure_random', 'insecure_config',
    'xxe', 'ssrf', 'csrf', 'weak_crypto', 'danger_pattern', 'unsafe_eval',
}
PERSISTENT_NOISE_THRESHOLD: int = 5
CONFIDENCE_DECAY_PER_OCCURRENCE: float = 0.10
_MAX_CONFIDENCE_DECAY: float = 1.0 - CONF_FLOOR
def _session_applies_to_skill(session: BaselineSession,
                              self_skill_key: str) -> bool:
    if not session.skill_dir:
        logger.debug("[Baseline] 全局会话缺 skill_dir，无法归因已排除"
                     "（会话无归因键，隐去会话标识）")
        return False
    return path_identity(session.skill_dir) == self_skill_key
def _global_sessions_for_skill(
        sessions: list[BaselineSession], skill_dir: str,
) -> list[BaselineSession]:
    self_skill_key = path_identity(skill_dir)
    return [session for session in sessions
            if _session_applies_to_skill(session, self_skill_key)]
def _ordered_history_sessions(sessions: list[BaselineSession],
                              global_sessions: list[BaselineSession],
                              skill_dir: str) -> list[BaselineSession]:
    ordered: dict[str, BaselineSession] = {}
    for session in [*sessions,
                    *_global_sessions_for_skill(global_sessions, skill_dir)]:
        ordered.setdefault(session.session_id, session)
    return sorted(ordered.values(), key=lambda s: (s.timestamp, s.session_id))
def _build_full_history_index(sessions: list[BaselineSession],
                              global_sessions: list[BaselineSession],
                              skill_dir: str) -> dict[str, list]:
    history_index: dict[str, list[BaselineEntry]] = {}
    for session in _ordered_history_sessions(
            sessions, global_sessions, skill_dir):
        for entry in session.entries:
            _append_history_entry(history_index, entry)
    return history_index
def _append_history_entry(history_index: dict, entry: BaselineEntry) -> None:
    bucket = history_index.setdefault(_locator_key(entry), [])
    key = (entry.session_id, entry.code_hash)
    if any((e.session_id, e.code_hash) == key for e in bucket):
        return
    bucket.append(entry)
def _seed_session_ids(sessions: list[BaselineSession],
                      global_sessions: list[BaselineSession],
                      skill_dir: str) -> set:
    seed_ids = {s.session_id for s in sessions if s.is_seed}
    seed_ids.update(
        s.session_id
        for s in _global_sessions_for_skill(global_sessions, skill_dir)
        if s.is_seed)
    return seed_ids
_UNKNOWN_CODE_HASHES: frozenset[str] = frozenset({"", "err_hash"})
def _hash_unchanged(skill_dir: str, f: dict, history: list) -> bool:
    if not history:
        return False
    current_hash = compute_code_hash(
        os.path.join(skill_dir, parse_locator_file(make_locator_fast(f))),
        safe_finding_line(f),
    )
    latest_hash = history[-1].code_hash
    if not isinstance(latest_hash, str) or latest_hash in _UNKNOWN_CODE_HASHES:
        return False
    return (current_hash not in _UNKNOWN_CODE_HASHES
            and current_hash == latest_hash)
def _noise_decay(f: dict, history: list, seed_session_ids: set,
                 code_unchanged: bool) -> tuple[bool, float]:
    is_new = not history
    hit_count = len(history) + 1
    non_seed_history_count = sum(
        1 for e in history if e.session_id not in seed_session_ids
    )
    if _is_decay_exempt(f, is_new, code_unchanged, bool(seed_session_ids),
                       non_seed_history_count):
        return False, 1.0
    if hit_count >= PERSISTENT_NOISE_THRESHOLD:
        decay = min(
            (hit_count - PERSISTENT_NOISE_THRESHOLD + 1) * CONFIDENCE_DECAY_PER_OCCURRENCE,
            _MAX_CONFIDENCE_DECAY,
        )
        return True, max(1.0 - decay, CONF_FLOOR)
    if hit_count >= 3:
        decay = (hit_count - 2) * CONF_BOOST_SMALL
        return False, max(1.0 - decay, CONF_VERY_HIGH)
    return False, 1.0
def _is_decay_exempt(f: dict, is_new: bool, code_unchanged: bool,
                     has_seed: bool, non_seed_history_count: int) -> bool:
    if is_new or not code_unchanged:
        return True
    severity = f.get("severity")
    if (isinstance(severity, str)
            and severity.strip().upper() in HIGH_SEVERITY_PROTECTED):
        return True
    family = (canonical_rule_key(f.get("rule_id")),
              canonical_rule_key(f.get("rule_family")))
    if any(name in COLD_START_EXEMPT_FAMILIES for name in family if name):
        return True
    return has_seed and non_seed_history_count == 0
def _diff_one_finding(f: dict, history_index: dict, seed_session_ids: set,
                      skill_dir: str,
                      session_id: str) -> BaselineDiffResult | None:
    if not isinstance(f, dict):
        return None
    locator = make_locator_fast(f)
    history = history_index.get(locator, [])
    is_new = not history
    hit_count = len(history) + 1
    code_unchanged = _hash_unchanged(skill_dir, f, history)
    is_persistent_noise, confidence_multiplier = _noise_decay(
        f, history, seed_session_ids, code_unchanged)
    return BaselineDiffResult(
        locator=locator,
        is_new=is_new,
        hit_count=hit_count,
        code_unchanged_since=code_unchanged,
        is_persistent_noise=is_persistent_noise,
        confidence_multiplier=confidence_multiplier,
        first_seen_at=(history[0].session_id if history else session_id),
        last_seen_at=session_id,
    )
def _write_session_json(
        path: str, session: BaselineSession) -> OSError | ValueError | None:
    try:
        parent = os.path.dirname(path)
        if parent:
            os.makedirs(parent, exist_ok=True)
        with guarded_open(path, "w", encoding="utf-8") as f:
            json.dump(session.to_dict(), f, ensure_ascii=False,
                      separators=(",", ":"), default=str)
    except (OSError, ValueError) as e:
        log_swallowed(
            __name__, e,
            context=f'_write_session_json:{type(e).__name__}')
        return e
    return None
class BaselineStore:
    def __init__(self, skill_dir: str,
                 global_baseline_dir: str = _NO_GLOBAL_BASELINE_DIR):
        root = _skill_root_arg(skill_dir)
        if not root:
            raise ValueError("BaselineStore: skill_dir 不能为空")
        self.skill_dir = os.path.abspath(root)
        self._baseline_dir = _baseline_store_dir(self.skill_dir)
        self._global_baseline_dir = os.path.abspath(global_baseline_dir) if global_baseline_dir else ""
        self._session_id = baseline_session_id(self.skill_dir)
        self._sessions: list[BaselineSession] = []
        self._global_sessions: list[BaselineSession] = []
        self._load()
    def _entry_of_finding(self, f: dict) -> BaselineEntry:
        _ln = safe_finding_line(f)
        _fp = parse_locator_file(make_locator_fast(f))
        _msg = f.get("message", "")
        _sev = f.get("severity", _DEFAULT_BASELINE_SEVERITY)
        _rid = f.get("rule_id")
        return BaselineEntry(
            rule_id=_rid if isinstance(_rid, str) else "",
            file=_fp,
            line=_ln,
            message=(_msg if isinstance(_msg, str) else "")[:MESSAGE_TRUNCATE_LEN],
            severity=(_sev if isinstance(_sev, str)
                      else _DEFAULT_BASELINE_SEVERITY),
            session_id=self._session_id,
            code_hash=compute_code_hash(os.path.join(self.skill_dir, _fp), _ln),
            rule_family=_baseline_finding_rule_family(f),
        )
    def save_snapshot(self, findings: list[dict], is_seed: bool = False) -> str:
        entries = [self._entry_of_finding(f) for f in findings
                   if isinstance(f, dict)]
        dedup_entries = _dedup_entries_by_locator(entries)
        session = BaselineSession(
            session_id=self._session_id,
            timestamp=time.time(),
            skill_dir=self.skill_dir,
            entries=dedup_entries,
            is_seed=is_seed,
        )
        previous_sessions = list(self._sessions)
        self._sessions = [s for s in self._sessions
                          if s.session_id != session.session_id]
        self._sessions.append(session)
        if len(self._sessions) > MAX_BASELINE_SESSIONS:
            self._sessions.sort(key=lambda s: (s.timestamp, s.session_id))
            self._sessions = self._sessions[-MAX_BASELINE_SESSIONS:]
        if not self._persist(session):
            self._sessions = previous_sessions
            return ""
        if self._global_baseline_dir:
            _sync_global_snapshot(self._global_baseline_dir, session)
        return self._session_id
    def save_seed_snapshot(self, findings: list[dict]) -> str:
        try:
            global_sessions = _global_sessions_for_skill(
                self._global_sessions, self.skill_dir)
            for session in itertools.chain(self._sessions, global_sessions):
                if session.is_seed:
                    logger.info("[Baseline] 种子基线已存在: %s", session.session_id)  # jwsgj:suppress SE-36 — session_id 为本地基线快照标识，非凭据
                    return session.session_id
            session_id = self.save_snapshot(findings, is_seed=True)
            if not session_id:
                logger.warning("[save_seed_snapshot] 种子基线写盘失败，未落盘")
                return ""
            entry_count = next(
                (len(s.entries) for s in self._sessions
                 if s.session_id == session_id), 0)
            logger.info("[Baseline] 种子基线已创建: %s (%d entries)",  # jwsgj:suppress SE-36 — session_id 为本地基线快照标识，非凭据
                        session_id, entry_count)
            return session_id
        except Exception as e:  # noqa: BLE001
            logger.warning("[save_seed_snapshot] 异常降级: %s", e)
            return ""
    def is_cold_start(self) -> bool:
        try:
            global_sessions = _global_sessions_for_skill(
                self._global_sessions, self.skill_dir)
            non_seed_count = sum(
                1 for s in itertools.chain(self._sessions, global_sessions)
                if not s.is_seed)
            return non_seed_count == 0
        except Exception as e:  # noqa: BLE001
            logger.warning("[is_cold_start] 异常降级: %s", e)
            return False
    def diff_against_baseline(self, findings: list[dict]) -> dict[str, BaselineDiffResult]:
        results: dict[str, BaselineDiffResult] = {}
        try:
            history_index = _build_full_history_index(
                self._sessions, self._global_sessions, self.skill_dir)
            seed_session_ids = _seed_session_ids(
                self._sessions, self._global_sessions, self.skill_dir)
            for f in findings:
                diff = _diff_one_finding(
                    f, history_index, seed_session_ids,
                    self.skill_dir, self._session_id)
                if diff is not None:
                    results[diff.locator] = diff
            return results
        except Exception as e:  # noqa: BLE001
            logger.warning("[diff_against_baseline] 异常降级: %s", e)
            return results
    def get_session_count(self) -> int:
        try:
            return len(self._sessions)
        except Exception as e:  # noqa: BLE001
            logger.warning("[get_session_count] 异常降级: %s", e)
            return 0
    def clear(self) -> None:
        self._sessions.clear()
        _clear_session_files(self._baseline_dir, None)
        if self._global_baseline_dir:
            _clear_session_files(self._global_baseline_dir, self.skill_dir)
            self_skill_key = path_identity(self.skill_dir)
            self._global_sessions = [
                s for s in self._global_sessions
                if not _session_applies_to_skill(s, self_skill_key)
            ]
        logger.info("[Baseline] 已清空所有历史基线")
    def _load_global_sessions(self) -> None:
        self._global_sessions = []
        if self._global_baseline_dir and os.path.isdir(self._global_baseline_dir):
            self._global_sessions = _load_sessions_from_dir(
                self._global_baseline_dir, source="global")
            logger.info("[Baseline] 加载 %d 个全局基线会话 (%d entries)",
                        len(self._global_sessions),
                        sum(len(s.entries) for s in self._global_sessions))
            _prune_sessions_in_dir(self._global_baseline_dir, "global")
    def _load(self) -> None:
        _local_dir_ready = True
        try:
            if not os.path.isdir(self._baseline_dir):
                os.makedirs(self._baseline_dir, exist_ok=True)
        except OSError as e:
            logger.warning("[Baseline] 基线目录创建失败，本地历史按空处理: %s", e)
            _local_dir_ready = False
        self._load_global_sessions()
        if not _local_dir_ready:
            self._sessions = []
            return
        _prune_sessions_in_dir(self._baseline_dir, "local")
        self._sessions = _load_sessions_from_dir(self._baseline_dir)
        if self._sessions:
            logger.info("[Baseline] 加载 %d 个历史基线会话 (%d 条 entries)",
                        len(self._sessions),
                        sum(len(s.entries) for s in self._sessions))
    def _persist(self, session: BaselineSession) -> bool:
        fpath = os.path.join(self._baseline_dir, f"{session.session_id}.json")
        error = _write_session_json(fpath, session)
        if error is not None:
            logger.error("[Baseline] 持久化失败 %s: %s", fpath, error)
            return False
        logger.info("[Baseline] 已保存会话 %s (%d entries, compact)",  # jwsgj:suppress SE-36 — session_id 为本地基线快照标识，非凭据
                    session.session_id, len(session.entries))
        return True
def _dedup_entries_by_locator(entries: list[BaselineEntry]) -> list[BaselineEntry]:
    seen_locators = set()
    dedup_entries = []
    for e in reversed(entries):
        key = _locator_key(e)
        if key not in seen_locators:
            seen_locators.add(key)
            dedup_entries.append(e)
    dedup_entries.reverse()
    return dedup_entries
def _sync_global_snapshot(global_dir: str, session: BaselineSession) -> None:
    gpath = os.path.join(global_dir, f"{session.session_id}.json")
    error = _write_session_json(gpath, session)
    if error is not None:
        logger.warning("[Baseline] 全局基线同步失败: %s", error)
        return
    logger.info("[Baseline] 已同步到全局基线 %s (%d entries)",
                global_dir, len(session.entries))
def _should_clear_session_file(fname: str) -> bool:
    return (fname.endswith(".json")
            and fname not in COEXISTING_BASELINE_DATA_FILES)
def _session_filenames(baseline_dir: str) -> list[str]:
    return sorted(
        fname for fname in os.listdir(baseline_dir)
        if _should_clear_session_file(fname)
        and os.path.isfile(os.path.join(baseline_dir, fname))
    )
def _load_sessions_from_dir(baseline_dir: str, source: str = "local") -> list[BaselineSession]:
    sessions = []
    if not os.path.isdir(baseline_dir):
        return sessions
    try:
        fnames = _session_filenames(baseline_dir)
    except OSError as e:
        logger.warning("[Baseline] %s 基线目录列举失败 %s: %s",
                       source, baseline_dir, e)
        return sessions
    fnames = _roll_session_filenames(fnames, source, baseline_dir)
    for fname in fnames:
        session = _load_session_file(os.path.join(baseline_dir, fname))
        if session is None:
            logger.warning("[Baseline] %s 加载失败或非会话快照 %s", source, fname)
            continue
        sessions.append(session)
    return sessions
def _load_session_file(path: str) -> BaselineSession | None:
    try:
        with open(path, encoding="utf-8-sig") as handle:
            data = json.load(handle)
        session = BaselineSession.from_dict(data)
    except (json.JSONDecodeError, UnicodeDecodeError, OSError, RecursionError) as _swallow_e:
        log_swallowed(__name__, _swallow_e,
                      context=f'_load_session_file:{type(_swallow_e).__name__}')
        return None
    if session is None or not session.session_id:
        return None
    if session.timestamp <= 0:
        try:
            session.timestamp = os.path.getmtime(path)
        except OSError as exc:
            logger.warning("[Baseline] 会话时间戳缺失且文件时间读取失败 %s: %s",
                           path, exc)
    return session
def _prune_sessions_in_dir(directory: str, source: str) -> None:
    try:
        fnames = _session_filenames(directory)
    except OSError as e:
        logger.warning("[Baseline] %s 基线目录列举失败（跳过滚动清理）: %s",
                       source, e)
        return
    keep = set(_roll_session_filenames(fnames, source, directory))
    for old in fnames:
        if old in keep:
            continue
        path = os.path.join(directory, old)
        if not safe_delete(path):
            logger.warning("[Baseline] %s 旧基线清理失败: %s", source, old)
def _clear_session_files(baseline_dir: str, skill_dir: str | None) -> None:
    if not os.path.isdir(baseline_dir):
        return
    try:
        fnames = _session_filenames(baseline_dir)
    except OSError:
        logger.warning("clear: 基线目录列举失败 %s", baseline_dir, exc_info=True)
        return
    self_skill_key = path_identity(skill_dir) if skill_dir is not None else ""
    for fname in fnames:
        path = os.path.join(baseline_dir, fname)
        if skill_dir is not None:
            session = _load_session_file(path)
            if (session is None
                    or not _session_applies_to_skill(session, self_skill_key)):
                continue
        if not safe_delete(path):
            logger.warning("clear: 基线文件删除失败: %s", fname)
def create_baseline_store(
    skill_dir: str,
    global_baseline_dir: str = _NO_GLOBAL_BASELINE_DIR,
) -> BaselineStore | None:
    try:
        return BaselineStore(skill_dir, global_baseline_dir=global_baseline_dir)
    except Exception as e:  # noqa: BLE001
        logger.warning("[create_baseline_store] 异常降级: %s", e)
        return None
def diff_findings_with_baseline(
    skill_dir: str,
    findings: list[dict],
    auto_save: bool = True,
    global_baseline_dir: str = _NO_GLOBAL_BASELINE_DIR,
) -> tuple[dict[str, BaselineDiffResult], str | None]:
    try:
        store = create_baseline_store(_skill_root_arg(skill_dir),
                                      global_baseline_dir=global_baseline_dir)
        if store is None:
            return {}, None
        results = store.diff_against_baseline(findings)
        session_id = None
        if auto_save:
            try:
                session_id = store.save_snapshot(findings)
            except Exception as save_e:
                logger.warning(
                    "[diff_findings_with_baseline] 快照保存失败（保留本轮 diff 结果）: %s",
                    save_e, exc_info=True)
                session_id = None
        return results, session_id
    except Exception as e:  # noqa: BLE001
        logger.warning("[diff_findings_with_baseline] 异常降级: %s", e)
        return {}, None
_BASELINE_ANNOTATION_FIELDS: tuple[str, ...] = (
    "_baseline_is_new",
    SIGNAL_BASELINE_PERSISTENT_NOISE,
    SIGNAL_BASELINE_HIT_COUNT,
    "_baseline_confidence_multiplier",
    "_baseline_first_seen_at",
)
def annotate_findings(
    findings: list[dict],
    diff_results: dict[str, BaselineDiffResult],
) -> list[dict]:
    try:
        annotated = []
        for f in findings:
            if not isinstance(f, dict):
                annotated.append(f)
                continue
            locator = make_locator_fast(f)
            diff = diff_results.get(locator)
            if diff:
                f["_baseline_is_new"] = diff.is_new
                f[SIGNAL_BASELINE_PERSISTENT_NOISE] = diff.is_persistent_noise
                f[SIGNAL_BASELINE_HIT_COUNT] = diff.hit_count
                f["_baseline_confidence_multiplier"] = diff.confidence_multiplier
                f["_baseline_first_seen_at"] = diff.first_seen_at
            else:
                for key in _BASELINE_ANNOTATION_FIELDS:
                    f.pop(key, None)
            annotated.append(f)
        return annotated
    except Exception as e:  # noqa: BLE001
        logger.warning("[annotate_findings] 异常降级: %s", e)
        return findings
def _normalized_snapshots(data, source: str) -> list[dict]:
    if not isinstance(data, dict):
        return []
    snaps = data.get("snapshots", [])
    if not isinstance(snaps, list):
        return []
    kept = [s for s in snaps if isinstance(s, dict)]
    if len(kept) != len(snaps):
        logger.warning(
            "[MetricsBaselineStore] 快照列表含 %d 个非 dict 病态元素，已剔除: %s",
            len(snaps) - len(kept), source)
    return kept
def _metrics_baseline_file(skill_dir: str) -> str:
    return os.path.join(_baseline_store_dir(skill_dir),
                        METRICS_BASELINE_FILENAME)
class MetricsBaselineStore:
    MAX_SNAPSHOTS = 10
    def __init__(self, skill_dir: str):
        root = _skill_root_arg(skill_dir)
        if not root:
            raise ValueError("MetricsBaselineStore: skill_dir 不能为空")
        self.skill_dir = os.path.abspath(root)
        self._metrics_file = _metrics_baseline_file(self.skill_dir)
        self._snapshots: list[dict] = []
        self._corrupt_source = ""
        self._read_failed = False
        self._load()
    def _load(self):
        self._snapshots = []
        self._corrupt_source = ""
        self._read_failed = False
        data = None
        if os.path.isfile(self._metrics_file):
            try:
                data, status, error = read_json_artifact(
                    self._metrics_file, propagate_io=True)
            except OSError as error:
                self._read_failed = True
                logger.warning(
                    "[MetricsBaselineStore] 读取 I/O 失败，保留原文件并禁止本次写回: %s",
                    error)
                return
            if status != "ok":
                logger.warning(
                    "[MetricsBaselineStore] 读取失败（%s），按默认值降级: %s",
                    error, self._metrics_file)
                if status == "parse_error":
                    self._corrupt_source = self._metrics_file
                data = None
        if data is None:
            return
        if (not isinstance(data, dict)
                or not isinstance(data.get("snapshots", []), list)):
            logger.warning(
                "[MetricsBaselineStore] 基线结构非法，写前隔离原文件: %s",
                self._metrics_file)
            self._corrupt_source = self._metrics_file
            return
        self._snapshots = _normalized_snapshots(data, self._metrics_file)
    def _quarantine_corrupt(self) -> bool:
        source = self._corrupt_source
        if not source:
            return True
        target = (f"{source}.corrupt-{time.strftime('%Y%m%d%H%M%S')}"
                  f"-{os.getpid()}-{time.time_ns()}")
        try:
            os.replace(source, target)
        except (OSError, ValueError) as exc:
            logger.warning(
                "[MetricsBaselineStore] 损坏基线隔离失败，放弃本次写盘保留原文件: %s",
                exc)
            return False
        logger.warning(
            "[MetricsBaselineStore] 损坏基线已隔离（保留原文件）: %s", target)
        self._corrupt_source = ""
        return True
    def _persist(self) -> bool:
        if self._read_failed:
            logger.warning(
                "[MetricsBaselineStore] 历史读取未完成，拒绝按空基线覆盖: %s",
                self._metrics_file)
            return False
        if not self._quarantine_corrupt():
            return False
        try:
            parent = os.path.dirname(self._metrics_file)
            if parent:
                os.makedirs(parent, exist_ok=True)
            write_json_artifact(
                self._metrics_file, {"snapshots": self._snapshots}, indent=2)
        except (OSError, TypeError, ValueError) as exc:
            log_swallowed(
                __name__, exc,
                context=f"MetricsBaselineStore._persist:{type(exc).__name__}")
            logger.warning("_persist: 基线指标持久化失败(不影响审计流程): %s", exc)
            return False
        return True
    @property
    def snapshot_count(self) -> int:
        return len(self._snapshots)
    def get_previous(self) -> dict | None:
        if not self._snapshots:
            return None
        return self._snapshots[-1]
    def save_current(self, metrics: dict) -> bool:
        if not isinstance(metrics, dict):
            logger.warning("[MetricsBaselineStore] metrics 非 dict（%s），跳过本次指标快照保存",
                           type(metrics).__name__)
            return False
        try:
            with locked_artifact(self._metrics_file) as locked:
                if not locked:
                    logger.warning(
                        "[MetricsBaselineStore] 基线写锁不可用，保留原文件: %s",
                        self._metrics_file)
                    return False
                self._load()
                previous_snapshots = list(self._snapshots)
                snapshot = {
                    **metrics,
                    "timestamp": time.time(),
                    "session_id": baseline_session_id(self.skill_dir),
                }
                self._snapshots.append(snapshot)
                if len(self._snapshots) > self.MAX_SNAPSHOTS:
                    self._snapshots[:] = self._snapshots[-self.MAX_SNAPSHOTS:]
                if self._persist():
                    return True
                self._snapshots[:] = previous_snapshots
                return False
        except (OSError, RuntimeError, TypeError, ValueError) as exc:
            logger.warning(
                "[MetricsBaselineStore] 基线事务写入失败，保留原文件: %s", exc)
            return False
def load_stage2b_baseline(skill_dir: str, result: dict) -> dict:
    _baseline_info = _load_metrics_baseline(skill_dir)
    result["baseline"] = _baseline_info
    return _baseline_info
def persist_stage2b_baseline(skill_dir: str, cv_report: dict, result: dict,
                             baseline_info: dict | None,
                             progress: dict) -> None:
    try:
        _baseline_saved = _persist_baseline_metrics(
            skill_dir, cv_report, baseline_info, progress)
        if _baseline_saved:
            _baseline = result.get("baseline")
            if not isinstance(_baseline, dict):
                _baseline = {}
                result["baseline"] = _baseline
            _baseline.update(_baseline_saved)
    except Exception as _pb_err:  # noqa: BLE001
        logger.warning("[Stage2b] 指标基线持久化跳过: %s", _pb_err)
def _open_baseline_store(skill_dir: str,
                         failure_label: str) -> MetricsBaselineStore | None:
    try:
        return MetricsBaselineStore(skill_dir)
    except (OSError, ValueError, RuntimeError, TypeError) as e:
        logger.warning("[Stage2b] %s: %s", failure_label, e)
        return None
def _load_metrics_baseline(skill_dir: str) -> dict:
    store = _open_baseline_store(skill_dir, "指标基线存储初始化失败")
    if store is None:
        return {"has_previous": False, "snapshot_count": 0}
    prev = None
    try:
        prev = store.get_previous()
    except (OSError, KeyError, TypeError) as e:
        logger.warning("[Stage2b] 指标基线加载失败: %s", e)
    _snap_count = _read_snapshot_count(store)
    info = {
        "has_previous": prev is not None,
        "snapshot_count": _snap_count,
    }
    if isinstance(prev, dict):
        info["previous"] = {
            k: prev.get(k) for k in
            ("timestamp", "health", "health_score", "file_count",
             "total_findings", "confirmed_findings")
        }
        logger.info("[Stage2b] 指标基线: 已有 %d 次历史快照, 上次 health=%s score=%s findings=%s",
                    _snap_count, prev.get("health"),
                    prev.get("health_score"), prev.get("total_findings"))
    return info
def _read_snapshot_count(store) -> int:
    try:
        return store.snapshot_count
    except Exception as _sc_err:  # noqa: BLE001
        logger.warning("[Stage2b] 指标基线快照计数读取失败（降级为 0）: %s", _sc_err)
        return 0
def _compute_health_penalty(cv_report: dict) -> int:
    penalty = 0
    for f in (dict_or_empty(cv_report).get("confirmed_findings", []) or []):
        if isinstance(f, dict):
            penalty += severity_penalty_weight(f.get("severity"))
    return penalty
def _count_skill_py_files(skill_dir: str) -> int:
    file_count = 0
    skill_dir = _skill_root_arg(skill_dir)
    walk_errors: list[OSError] = []
    try:
        for root, dirs, files in os.walk(skill_dir, onerror=walk_errors.append):
            prune_walk_dirs(dirs, root_dir=skill_dir)
            for fn in files:
                if not fn.lower().endswith(".py"):
                    continue
                if is_diagnosis_out_of_scope(os.path.join(root, fn),
                                              root_dir=skill_dir):
                    continue
                file_count += 1
    except (OSError, ValueError) as _fc_err:
        logger.warning("[Stage2b] py 文件计数失败(file_count=0 继续): %s", _fc_err)
    if walk_errors:
        logger.warning("[Stage2b] py 文件计数不完整（%d 个目录不可读）: %s",
                       len(walk_errors), walk_errors[0])
    return file_count
def _resolve_delta_baseline(store: MetricsBaselineStore,
                            baseline_info: dict | None) -> dict | None:
    prev = None
    if isinstance(baseline_info, dict):
        _bp = baseline_info.get("previous")
        if isinstance(_bp, dict):
            prev = _bp
    if prev is None:
        try:
            prev = store.get_previous()
        except (OSError, KeyError, TypeError) as _prev_err:
            logger.warning("[Stage2b] delta 基准回退现读失败（按首次审计处理）: %s",
                           _prev_err)
            prev = None
    return prev
def _persist_baseline_metrics(skill_dir: str, cv_report: dict,
                              baseline_info: dict | None = None,
                              progress: dict | None = None) -> dict:
    store = _open_baseline_store(skill_dir, "指标基线持久化跳过")
    if store is None:
        return {}
    metrics = _build_baseline_metrics(
        cv_report, progress or {}, _count_skill_py_files(skill_dir))
    prev = _resolve_delta_baseline(store, baseline_info)
    saved = store.save_current(metrics)
    out = {"saved": saved is not False, "metrics": metrics}
    if saved is False:
        logger.warning("[Stage2b] 指标基线写盘失败，本轮快照未落盘")
    delta = _delta_against_previous(metrics, prev)
    if delta is not None:
        out["delta_vs_previous"] = delta
    if saved is not False:
        _log_baseline_persisted(metrics, delta)
    return out
def _build_baseline_metrics(cv_report: dict, progress: dict,
                            file_count: int) -> dict:
    _report = dict_or_empty(cv_report)
    es = _report.get("executive_summary") or {}
    if not isinstance(es, dict):
        es = {}
    return {
        "health": es.get("health", "unknown"),
        "health_score": max(0, 100 - _compute_health_penalty(cv_report)),
        "file_count": file_count,
        "total_findings": as_number(es.get("total_findings", 0)),
        "confirmed_findings": as_number(es.get("confirmed", 0)),
        "dead_code_count": _count_dead_code_findings(
            _report.get("confirmed_findings", []) or []),
        "methods_total": as_number(progress.get("total", 0)),
        "methods_completed": as_number(progress.get("completed", 0)),
    }
def _delta_against_previous(metrics: dict, prev) -> dict | None:
    if not isinstance(prev, dict):
        return None
    delta_keys = ("health_score", "total_findings",
                  "confirmed_findings", "file_count")
    delta: dict[str, float] = {}
    for key in delta_keys:
        prev_value = safe_float(prev.get(key), None)
        if prev_value is None:
            continue
        delta[key] = metrics[key] - prev_value
    return delta or None
def _log_baseline_persisted(metrics: dict, delta: dict | None) -> None:
    if delta is None:
        logger.info("[Stage2b] 指标基线已持久化(首次): health=%s score=%s files=%s findings=%s",
                    metrics["health"], metrics["health_score"], metrics["file_count"],
                    metrics["total_findings"])
        return
    delta_text = ", ".join(
        f"Δ{key}={value:+g}" for key, value in delta.items())
    logger.info("[Stage2b] 指标基线已持久化: health=%s score=%s files=%s findings=%s (%s)",
                metrics["health"], metrics["health_score"], metrics["file_count"],
                metrics["total_findings"], delta_text)
def _count_dead_code_findings(findings: list) -> int:
    return sum(1 for f in findings
               if isinstance(f, dict) and _is_dead_code_finding(f))
logger.info("xv_context_history 已加载: %d 项导出", len(__all__))

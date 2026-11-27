from __future__ import annotations

import hashlib
import http.client
import json
import logging
import math
import os
import re
import time
import urllib.request
from collections.abc import Iterable
from copy import deepcopy
from dataclasses import MISSING, asdict, dataclass, field, replace
from datetime import date
from threading import RLock
from typing import Any, Self

from jwsgj.diag_guard_io import two_level_unlink
from jwsgj.diag_types_normalize import (
    as_pure_count,
    clean_source_ids,
    is_finite_num,
    severity_key,
    signal_bool,
    str_or_empty,
    strict_iterable_list,
    strip_bom,
)
from jwsgj.runtime_paths import (
    get_temp_base,
)

_log = logging.getLogger(__name__)
try:
    import yaml
except ImportError as _imp_err:
    _log.debug(
        "[diag_se_knowledge] PyYAML 缺失，情报同步降级 partial: %s", _imp_err)
    yaml = None
__all__ = [
    "BUILTIN_CWE_KNOWLEDGE",
    "BUILTIN_FRAMEWORK_PROFILES",
    "BUILTIN_ORM_GUIDES",
    "BUILTIN_VULN_PATTERNS",
    "CWE_CATEGORY_MAP",
    "OWASP_TOP_10_2021",
    "PYPA_API_TREE",
    "PYPA_RAW_BASE",
    "PYTHON_CPE_KEYWORDS",
    "AdvisoryEntry",
    "InternetKnowledgeBase",
    "KnowledgeEntry",
    "PyPAAdvisorySync",
    "SecurityKnowledgeLearner",
    "SyncResult",
    "VulnerabilityCache",
    "VulnerabilityEntry",
    "cwe_to_category",
    "discover_project_packages",
    "get_security_knowledge",
    "search_vuln_patterns",
    "sync_pypa_advisories",
]
_log.info("diag_se_knowledge 安全情报与知识域已加载: %d 项导出",
          len(__all__))
_DEFAULT_QUERY_LIMIT = 100
_DEFAULT_TTL_SECONDS = 7 * 24 * 3600
_DEFAULT_CATEGORY = "general"
_DEFAULT_VULNERABILITY_SEVERITY = "medium"
_DEFAULT_KNOWLEDGE_CONFIDENCE = 1.0
_DEFAULT_LEARNED_CONFIDENCE = 0.5
_DEFAULT_RULE_SEVERITY = "P2"
_PYPA_PATTERN_QUERY_LIMIT = 200
_PYPA_PATTERN_SINK_LIMIT = 6
_CACHE_DB_FILENAME = "vulnerabilities.json"
_PYPA_SOURCE = "pypa"
_DEFAULT_FETCH_TIMEOUT = 30
def _finite_float_or_default(value: Any, default: float = 0.0) -> float:
    if not is_finite_num(value):
        return default
    try:
        return float(value)
    except OverflowError:
        return default
def _normalize_list_field(value: Any) -> list[str]:
    if not isinstance(value, (list, tuple)):
        return []
    return [item for item in value if isinstance(item, str) and item]
def _normalize_optional_number(value: Any) -> float | int | None:
    if value is None or not is_finite_num(value):
        return None
    return value
def _normalize_entry_field(fdef: Any, value: Any) -> Any:
    if fdef.default_factory is not MISSING:
        if fdef.default_factory is list:
            return _normalize_list_field(value)
        return fdef.default_factory() if value is None else value
    if fdef.default is None:
        return _normalize_optional_number(value)
    if not isinstance(value, str):
        return fdef.default
    return value
def _normalized_dataclass_fields(cls: type, data: dict[str, Any], *,
                                 excluded: tuple[str, ...] = ()) -> dict[str, Any]:
    excluded_names = frozenset(excluded)
    definitions = cls.__dataclass_fields__
    fields = {key: value for key, value in data.items()
              if key in definitions and key not in excluded_names}
    for fname, fdef in definitions.items():
        if fname not in excluded_names:
            fields[fname] = _normalize_entry_field(fdef, fields.get(fname))
    return fields
@dataclass
class VulnerabilityEntry:
    entry_id: str = ""
    source: str = ""
    aliases: list[str] = field(default_factory=list)
    name: str = ""
    description: str = ""
    severity: str = _DEFAULT_VULNERABILITY_SEVERITY
    cvss_score: float | None = None
    cwe_ids: list[str] = field(default_factory=list)
    category: str = _DEFAULT_CATEGORY
    affected_packages: list[str] = field(default_factory=list)
    fixed_versions: list[str] = field(default_factory=list)
    sinks: list[str] = field(default_factory=list)
    sanitizers: list[str] = field(default_factory=list)
    fix_guidance: str = ""
    references: list[str] = field(default_factory=list)
    source_url: str = ""
    published_date: str = ""
    modified_date: str = ""
    created_at: float = field(default_factory=time.time)
    def to_dict(self) -> dict[str, Any]:
        d = asdict(self)
        d.pop("created_at", None)
        return d
    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> VulnerabilityEntry:
        if not isinstance(data, dict):
            return cls()
        return cls(**_normalized_dataclass_fields(
            cls, data, excluded=("created_at",)))
@dataclass
class AdvisoryEntry:
    advisory_id: str = ""
    source: str = ""
    title: str = ""
    description: str = ""
    severity: str = _DEFAULT_VULNERABILITY_SEVERITY
    package_name: str = ""
    affected_versions: list[str] = field(default_factory=list)
    patched_versions: list[str] = field(default_factory=list)
    published_date: str = ""
    url: str = ""
    def to_dict(self) -> dict[str, Any]:
        return asdict(self)
    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> AdvisoryEntry:
        if not isinstance(data, dict):
            return cls()
        return cls(**_normalized_dataclass_fields(cls, data))
def _default_cache_dir() -> str:
    _skill_root = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(get_temp_base(_skill_root), "vuln_cache")
def _cache_db_path(cache_dir: str) -> str:
    return os.path.join(cache_dir, _CACHE_DB_FILENAME)
def _coerce_cache_dir(value: Any) -> str | None:
    if isinstance(value, os.PathLike):
        try:
            value = os.fspath(value)
        except TypeError as _e:
            _log.debug("VulnerabilityCache: 缓存目录 PathLike 解析失败，回落默认目录: %s", _e)
            return None
    if isinstance(value, str) and value:
        return value
    return None
def _normalize_cache_entry(data: Any) -> dict[str, Any] | None:
    if not isinstance(data, dict):
        return None
    data["cached_at"] = _finite_float_or_default(data.get("cached_at"))
    for fname, fdef in VulnerabilityEntry.__dataclass_fields__.items():
        if fname == "created_at":
            continue
        if fname in data:
            data[fname] = _normalize_entry_field(fdef, data[fname])
        elif fdef.default_factory is list:
            data[fname] = []
    data["severity"] = _canonical_severity(data.get("severity"))
    data["category"] = _lookup_key(data.get("category")) or _DEFAULT_CATEGORY
    data["source"] = _lookup_key(data.get("source"))
    return data
def _is_live(data: dict[str, Any], cutoff: float) -> bool:
    return _finite_float_or_default(data.get("cached_at")) > cutoff
def _lookup_key(value: Any) -> str:
    return value.strip().lower() if isinstance(value, str) else ""
def _entry_identity_keys(data: dict[str, Any]) -> set[str]:
    values = [data.get("entry_id")]
    aliases = data.get("aliases")
    if isinstance(aliases, list):
        values.extend(aliases)
    keys: set[str] = set()
    for value in values:
        key = _lookup_key(value)
        if key:
            keys.add(key)
    return keys
def _merge_replaced_identity(data: dict[str, Any], previous_id: Any,
                             previous: dict[str, Any]) -> None:
    aliases = _normalize_list_field(data.get("aliases"))
    known = {_lookup_key(value)
             for value in (data.get("entry_id"), *aliases)}
    for value in (previous_id, *_normalize_list_field(previous.get("aliases"))):
        key = _lookup_key(value)
        if key and key not in known:
            aliases.append(value)
            known.add(key)
    data["aliases"] = aliases
def _category_filter(value: Any) -> str | None:
    if value is None:
        return ""
    if not isinstance(value, str):
        return None
    return _lookup_key(value)
def _normalize_package_name(value: Any) -> str:
    if not isinstance(value, str):
        return ""
    return re.sub(r"[-_.]+", "-", value.strip().lower())
class VulnerabilityCache:
    _instance: VulnerabilityCache | None = None
    _lock: RLock = RLock()
    def __new__(cls, cache_dir: str | os.PathLike[str] | None = None) -> Self:
        if cls._instance is None:
            with cls._lock:
                if cls._instance is None:
                    cls._instance = super().__new__(cls)
                    cls._instance._initialized = False
        return cls._instance
    def __init__(self, cache_dir: str | os.PathLike[str] | None = None) -> None:
        resolved_dir = _coerce_cache_dir(cache_dir)
        with VulnerabilityCache._lock:
            if self._initialized:
                new_dir = os.path.realpath(resolved_dir) if resolved_dir else None
                if new_dir and new_dir != os.path.realpath(self.cache_dir):
                    self._switch_cache_dir(new_dir)
                return
            self.cache_dir = (os.path.realpath(resolved_dir)
                              if resolved_dir else _default_cache_dir())
            self.db_path = _cache_db_path(self.cache_dir)
            self.ttl = _DEFAULT_TTL_SECONDS
            self._db_lock = RLock()
            self._entries: dict[str, dict[str, Any]] = {}
            self._sync_state: dict[str, dict[str, Any]] = {}
            self._load()
            self._initialized = True
    @property
    def ttl(self) -> float:
        return self._ttl
    @ttl.setter
    def ttl(self, value: Any) -> None:
        normalized = _finite_float_or_default(value, _DEFAULT_TTL_SECONDS)
        self._ttl = max(0.0, normalized)
    def _switch_cache_dir(self, new_dir: str) -> None:
        with self._db_lock:
            self.cache_dir = new_dir
            self.db_path = _cache_db_path(new_dir)
            self._entries = {}
            self._sync_state = {}
            self._load()
    @staticmethod
    def _normalize_loaded_entries(raw: Any) -> dict[str, dict[str, Any]]:
        if not isinstance(raw, dict):
            return {}
        normalized: dict[str, dict[str, Any]] = {}
        identity_keys: dict[str, str] = {}
        for eid, value in raw.items():
            normed = _normalize_cache_entry(value)
            if normed is None:
                continue
            normed["entry_id"] = eid
            current_keys = _entry_identity_keys(normed)
            previous_ids = {
                previous_id for key in current_keys
                if (previous_id := identity_keys.get(key)) is not None
            }
            for previous_id in previous_ids:
                previous = normalized.pop(previous_id, None)
                if previous is None:
                    continue
                for previous_key in _entry_identity_keys(previous):
                    if identity_keys.get(previous_key) == previous_id:
                        identity_keys.pop(previous_key, None)
                _merge_replaced_identity(normed, previous_id, previous)
            current_keys = _entry_identity_keys(normed)
            normalized[eid] = normed
            for identity_key in current_keys:
                identity_keys[identity_key] = eid
        return normalized
    @staticmethod
    def _normalize_loaded_sync_state(raw: Any) -> dict[str, dict[str, Any]]:
        if not isinstance(raw, dict):
            return {}
        normalized: dict[str, dict[str, Any]] = {}
        for source, state in raw.items():
            source_key = _lookup_key(source)
            if source_key and isinstance(state, dict):
                normalized[source_key] = state
        return normalized
    def _load(self) -> None:
        with self._db_lock:
            if not os.path.exists(self.db_path):
                return
            try:
                with open(self.db_path, encoding="utf-8") as f:  # jwsgj:suppress TAINT — 审计认可：db_path 为内部缓存目录 vulnerabilities.json，属性根污染近似导致误判
                    data = json.loads(strip_bom(f.read()))
            except (json.JSONDecodeError, UnicodeDecodeError, OSError,
                    RecursionError) as _e:
                _log.debug("VulnerabilityCache._load: 缓存文件损坏或不可读，降级为空缓存: %s", _e)
                self._entries = {}
                self._sync_state = {}
                return
            if not isinstance(data, dict):
                _log.debug("VulnerabilityCache._load: 缓存顶层结构非法，降级为空缓存")
                self._entries = {}
                self._sync_state = {}
                return
            self._entries = self._normalize_loaded_entries(data.get("entries"))
            self._sync_state = self._normalize_loaded_sync_state(
                data.get("sync_state"))
    def _purge_expired_locked(self) -> int:
        cutoff = time.time() - self.ttl
        expired = [
            eid for eid, data in self._entries.items()
            if not _is_live(data, cutoff)
        ]
        for eid in expired:
            self._entries.pop(eid, None)
        return len(expired)
    def _save(self) -> None:
        with self._db_lock:
            self._purge_expired_locked()
            _tmp_path = f"{self.db_path}.{os.getpid()}.{time.time_ns()}.tmp"
            try:
                os.makedirs(self.cache_dir, exist_ok=True)
                with open(_tmp_path, "w", encoding="utf-8") as f:
                    json.dump(
                        {"entries": self._entries, "sync_state": self._sync_state},
                        f, ensure_ascii=False, default=str,
                    )
                os.replace(_tmp_path, self.db_path)
            except OSError as _e:
                two_level_unlink(_tmp_path)
                _log.warning("VulnerabilityCache._save: 缓存写入失败（下次将重建缓存）: %s", _e)
    def insert_batch(self, entries: list[VulnerabilityEntry]) -> int:
        if not isinstance(entries, (list, tuple)):
            _log.warning(
                "VulnerabilityCache.insert_batch: 非序列入参已跳过: %r",
                type(entries).__name__)
            return 0
        count = 0
        with self._db_lock:
            for entry in entries:
                if not isinstance(entry, VulnerabilityEntry):
                    _log.warning(
                        "VulnerabilityCache.insert_batch: 非 VulnerabilityEntry "
                        "元素已跳过: %r", type(entry).__name__)
                    continue
                entry_id = entry.entry_id
                if not isinstance(entry_id, str) or not entry_id:
                    _log.warning(
                        "VulnerabilityCache.insert_batch: 空/非 str entry_id 条目已跳过: %r",
                        type(entry_id).__name__)
                    continue
                data = _normalize_cache_entry({
                    **entry.to_dict(),
                    "cached_at": time.time(),
                }) or {}
                current_keys = _entry_identity_keys(data)
                for existing_id, existing in tuple(self._entries.items()):
                    if (existing_id != entry_id
                            and current_keys.intersection(
                                _entry_identity_keys(existing))):
                        self._entries.pop(existing_id, None)
                        _merge_replaced_identity(data, existing_id, existing)
                        current_keys = _entry_identity_keys(data)
                self._entries[entry_id] = data
                count += 1
            if count:
                self._save()
        return count
    @staticmethod
    def _entry_matches_identity(data: dict[str, Any], identity_key: str) -> bool:
        if _lookup_key(data.get("entry_id")) == identity_key:
            return True
        if not identity_key:
            return False
        aliases = data.get("aliases")
        return isinstance(aliases, list) and any(
            _lookup_key(alias) == identity_key for alias in aliases)
    def _find_live_entry_locked(self, entry_id: str) -> dict[str, Any] | None:
        if not isinstance(entry_id, str) or not entry_id:
            return None
        identity_key = _lookup_key(entry_id)
        cutoff = time.time() - self.ttl
        entry = self._entries.get(entry_id)
        if entry is not None and _is_live(entry, cutoff):
            return entry
        if not identity_key:
            return None
        for data in self._entries.values():
            if not _is_live(data, cutoff):
                continue
            if self._entry_matches_identity(data, identity_key):
                return data
        return None
    def contains(self, entry_id: str) -> bool:
        with self._db_lock:
            return self._find_live_entry_locked(entry_id) is not None
    def get(self, entry_id: str) -> VulnerabilityEntry | None:
        with self._db_lock:
            data = self._find_live_entry_locked(entry_id)
            return VulnerabilityEntry.from_dict(data) if data is not None else None
    @staticmethod
    def _scalar_matches(actual: Any, expected: str | None) -> bool:
        if expected is None:
            return True
        if not isinstance(expected, str):
            return False
        expected_key = _lookup_key(expected)
        if not expected_key:
            return True
        return _lookup_key(actual) == expected_key
    @staticmethod
    def _severity_matches(actual: Any, expected: Any) -> bool:
        if expected is None:
            return True
        if not isinstance(expected, str):
            return False
        expected_key = _severity_match_key(expected)
        if not expected_key:
            return True
        return _severity_match_key(actual) == expected_key
    @classmethod
    def _entry_matches_scalar_filters(cls, data: dict[str, Any],
                                      source: str | None,
                                      severity: str | None,
                                      category: str | None) -> bool:
        if not cls._severity_matches(data.get("severity"), severity):
            return False
        for key, expected in (("source", source), ("category", category)):
            if not cls._scalar_matches(data.get(key), expected):
                return False
        return True
    @classmethod
    def _entry_matches_query_filters(cls, data: dict[str, Any], cutoff: float,
                                     source: str | None,
                                     severity: str | None,
                                     category: str | None,
                                     package: str | None) -> bool:
        if not _is_live(data, cutoff):
            return False
        if not cls._entry_matches_scalar_filters(
                data, source, severity, category):
            return False
        if package is not None:
            if not isinstance(package, str):
                return False
            package_key = _normalize_package_name(package)
            if not package_key:
                return True
            affected = data.get("affected_packages")
            if not isinstance(affected, list):
                return False
            if not any(_normalize_package_name(item) == package_key
                       for item in affected):
                return False
        return True
    def query(
        self,
        source: str | None = None,
        severity: str | None = None,
        category: str | None = None,
        package: str | None = None,
        limit: int = _DEFAULT_QUERY_LIMIT,
    ) -> list[VulnerabilityEntry]:
        if (not isinstance(limit, int) or isinstance(limit, bool)
                or limit < 0):
            limit = _DEFAULT_QUERY_LIMIT
        with self._db_lock:
            cutoff = time.time() - self.ttl
            matched: list[tuple[float, dict[str, Any]]] = []
            for data in self._entries.values():
                if not self._entry_matches_query_filters(
                        data, cutoff, source, severity, category, package):
                    continue
                matched.append((_finite_float_or_default(data.get("cached_at")), data))
            matched.sort(key=lambda t: (-t[0], str(t[1].get("entry_id", ""))))
            return [VulnerabilityEntry.from_dict(d) for _, d in matched[:limit]]
    def count(self, source: str | None = None) -> int:
        with self._db_lock:
            cutoff = time.time() - self.ttl
            return sum(
                1 for data in self._entries.values()
                if _is_live(data, cutoff)
                and self._scalar_matches(data.get("source"), source)
            )
    def cleanup(self) -> int:
        with self._db_lock:
            expired_n = self._purge_expired_locked()
            if expired_n:
                self._save()
            return expired_n
    def clear(self) -> None:
        with self._db_lock:
            self._entries.clear()
            self._sync_state.clear()
            self._save()
    def remove(self, entry_id: str) -> bool:
        if not isinstance(entry_id, str) or not entry_id:
            return False
        identity_key = _lookup_key(entry_id)
        with self._db_lock:
            existing_id = next(
                (eid for eid, data in self._entries.items()
                 if self._entry_matches_identity(data, identity_key)),
                None,
            )
            if existing_id is None:
                return False
            self._entries.pop(existing_id, None)
            self._save()
            return True
    def get_sync_state(self, source: str) -> dict[str, Any] | None:
        source_key = _lookup_key(source)
        if not source_key:
            return None
        with self._db_lock:
            state = self._sync_state.get(source_key)
            return deepcopy(state) if state is not None else None
    def set_sync_state(self, source: str, state: dict[str, Any]) -> None:
        source_key = _lookup_key(source)
        if not source_key:
            _log.warning(
                "VulnerabilityCache.set_sync_state: 非 str/空 source 已跳过: %r",
                source)
            return
        with self._db_lock:
            self._sync_state[source_key] = {
                **deepcopy(state if isinstance(state, dict) else {}),
                "last_synced": time.time(),
            }
            self._save()
BUILTIN_VULN_PATTERNS: list = [
    {"rule_id": "SE-08", "category": "command_injection",
     "pattern": r"subprocess\.(?:Popen|call|run|check_output|check_call)\s*\(",
     "sinks": ["subprocess.Popen", "subprocess.call", "subprocess.run",
               "subprocess.check_output", "subprocess.check_call"],
     "sanitizers": ["shlex.quote", "shlex.join"],
     "severity": "high",
     "description": "subprocess call without shell=False or input sanitization"},
    {"rule_id": "SE-02", "category": "command_injection",
     "pattern": r"os\.system\s*\(",
     "sinks": ["os.system"],
     "sanitizers": ["shlex.quote"],
     "severity": "high",
     "description": "os.system() is vulnerable to command injection"},
    {"rule_id": "SE-30b", "category": "command_injection",
     "pattern": r"os\.popen\s*\(",
     "sinks": ["os.popen"],
     "sanitizers": ["shlex.quote"],
     "severity": "high",
     "description": "os.popen() is vulnerable to command injection"},
    {"rule_id": "SE-04", "category": "deserialization",
     "pattern": r"pickle\.loads?\s*\(",
     "sinks": ["pickle.load", "pickle.loads", "cPickle.load", "cPickle.loads"],
     "sanitizers": ["json.loads", "yaml.safe_load"],
     "severity": "high",
     "description": "pickle deserialization is unsafe for untrusted data"},
    {"rule_id": "CV-01b", "category": "deserialization",
     "pattern": r"marshal\.loads?\s*\(",
     "sinks": ["marshal.load", "marshal.loads"],
     "sanitizers": ["json.loads"],
     "severity": "high",
     "description": "marshal deserialization is unsafe for untrusted data"},
    {"rule_id": "SE-07", "category": "deserialization",
     "pattern": r"yaml\.load\s*\(",
     "sinks": ["yaml.load"],
     "sanitizers": ["yaml.safe_load"],
     "severity": "high",
     "description": "yaml.load() without Loader=safe_load is unsafe"},
    {"rule_id": "NW-01", "category": "network_security",
     "pattern": (r"(?:requests\.(?:get|post|put|delete|patch|head)|"
                 r"httpx\.(?:get|post|put|delete|patch)|aiohttp\.ClientSession)"
                 r"[^\n]*verify\s*=\s*False"),
     "sinks": ["requests.get", "requests.post", "requests.put",
               "requests.delete", "requests.patch", "requests.head"],
     "sanitizers": ["verify=True"],
     "severity": "medium",
     "description": "HTTP client explicitly disables SSL verification"},
    {"rule_id": "NW-02", "category": "network_security",
     "pattern": r"urllib\.request\.urlopen\s*\(",
     "sinks": ["urllib.request.urlopen"],
     "sanitizers": [],
     "severity": "medium",
     "description": "urllib.request.urlopen without timeout"},
    {"rule_id": "NW-03", "category": "network_security",
     "pattern": r"httpx\.(?:get|post|put|delete|patch|stream)\s*\(",
     "sinks": ["httpx.get", "httpx.post", "httpx.put",
               "httpx.delete", "httpx.patch"],
     "sanitizers": [],
     "severity": "medium",
     "description": "httpx request without timeout"},
    {"rule_id": "NW-04", "category": "network_security",
     "pattern": r"aiohttp\.ClientSession",
     "sinks": ["aiohttp.ClientSession"],
     "sanitizers": [],
     "severity": "low",
     "description": "aiohttp ClientSession without timeout"},
]
CWE_CATEGORY_MAP: dict = {
    "CWE-89": "sql_injection",
    "CWE-78": "command_injection",
    "CWE-94": "code_injection",
    "CWE-502": "deserialization",
    "CWE-22": "path_traversal",
    "CWE-79": "xss",
    "CWE-918": "ssrf",
    "CWE-287": "auth_bypass",
    "CWE-798": "secret",
    "CWE-20": "input_validation",
    "CWE-200": "info_leak",
    "CWE-352": "csrf",
    "CWE-434": "unrestricted_upload",
    "CWE-611": "xxe",
    "CWE-77": "command_injection",
    "CWE-601": "open_redirect",
    "CWE-732": "incorrect_permission",
    "CWE-295": "insecure_config",
    "CWE-330": "weak_crypto",
    "CWE-862": "missing_authorization",
    "CWE-863": "incorrect_authorization",
}
_CWE_ID_RE = re.compile(r"^CWE-(\d+)$")
def _cwe_number(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value > 0 else None
    if not isinstance(value, str):
        return None
    text = value.strip().upper()
    match = _CWE_ID_RE.match(text)
    if match:
        return int(match.group(1))
    return int(text) if text.isdigit() and int(text) > 0 else None
def cwe_to_category(cwe_id: str) -> str:
    number = _cwe_number(cwe_id)
    if number is not None:
        info = BUILTIN_CWE_KNOWLEDGE.get(number)
        if info is not None:
            return (str_or_empty(info.get("category"))
                    or _DEFAULT_CATEGORY)
        return CWE_CATEGORY_MAP.get(f"CWE-{number}", _DEFAULT_CATEGORY)
    normalized = str_or_empty(cwe_id).strip().upper()
    return CWE_CATEGORY_MAP.get(normalized, _DEFAULT_CATEGORY)
def _filter_builtin_patterns(category: str, severity: str) -> list:
    results = []
    for p in BUILTIN_VULN_PATTERNS:
        if category and _lookup_key(p.get("category")) != category:
            continue
        if severity and _severity_match_key(p.get("severity")) != severity:
            continue
        results.append({**p,
                        "sinks": list(p.get("sinks", [])),
                        "sanitizers": list(p.get("sanitizers", []))})
    return results
def _pattern_from_entry(entry: VulnerabilityEntry) -> dict | None:
    sinks = list(dict.fromkeys(s for s in entry.sinks if s))
    if not sinks:
        return None
    return {
        "rule_id": entry.entry_id,
        "category": entry.category,
        "pattern": "|".join(
            re.escape(s) for s in sinks[:_PYPA_PATTERN_SINK_LIMIT]),
        "sinks": sinks,
        "sanitizers": list(entry.sanitizers),
        "severity": entry.severity,
        "description": entry.description or entry.name,
    }
def _pypa_synced_patterns(cache: VulnerabilityCache, category: str,
                          severity: str) -> list:
    patterns = []
    for entry in cache.query(
        source=_PYPA_SOURCE,
        severity=severity or None,
        category=category or None,
        limit=_PYPA_PATTERN_QUERY_LIMIT,
    ):
        pattern = _pattern_from_entry(entry)
        if pattern is not None:
            patterns.append(pattern)
    return patterns
def search_vuln_patterns(category: str = "", severity: str = "",
                         include_synced: bool = True) -> list:
    category_key = _category_filter(category)
    if category_key is None:
        return []
    severity_text = severity.strip() if isinstance(severity, str) else severity
    severity_norm = _severity_match_key(severity_text) if severity_text else ""
    if severity_text and not severity_norm:
        return []
    results = _filter_builtin_patterns(category_key, severity_norm)
    if not signal_bool(include_synced):
        return results
    try:
        cache = VulnerabilityCache()
        results.extend(_pypa_synced_patterns(cache, category_key, severity_norm))
    except (RuntimeError, OSError, TypeError, AttributeError,
            ValueError) as _e:  # jwsgj:silent-ok 缓存通道不可用时回退内置模式
        _log.debug("漏洞缓存检索不可用，回退内置模式: %s", _e)
    return results
def _pattern_matches(pattern: dict, query_lower: str) -> bool:
    return (query_lower in _lookup_key(pattern.get("name"))
            or query_lower in _lookup_key(pattern.get("description")))
_DEFAULT_TOP_K = 5
_DEFAULT_MAX_ENTRIES = 1000
@dataclass
class KnowledgeEntry:
    key: str = ""
    content: str = ""
    source: str = ""
    category: str = _DEFAULT_CATEGORY
    confidence: float = _DEFAULT_KNOWLEDGE_CONFIDENCE
    tags: list[str] = field(default_factory=list)
    created_at: float = 0.0
@dataclass(frozen=True)
class _KnowledgeDraft:
    content: str
    source: str
    category: str
    tags: list[str]
    confidence: float
def _coerce_confidence(value: Any) -> float:
    if isinstance(value, bool):
        return _DEFAULT_KNOWLEDGE_CONFIDENCE
    if isinstance(value, str):
        try:
            value = float(value.strip())
        except ValueError:
            return _DEFAULT_KNOWLEDGE_CONFIDENCE
    if not isinstance(value, (int, float)):
        return _DEFAULT_KNOWLEDGE_CONFIDENCE
    if isinstance(value, float) and not math.isfinite(value):
        return _DEFAULT_KNOWLEDGE_CONFIDENCE
    return min(1.0, max(0.0, float(value)))
def _entry_rank_key(entry: KnowledgeEntry) -> tuple:
    return (-entry.confidence, entry.key)
class InternetKnowledgeBase:
    def __init__(self) -> None:
        self._entries: dict[str, KnowledgeEntry] = {}
        self._index: dict[str, set[str]] = {}
        self._max_entries = _DEFAULT_MAX_ENTRIES
        self._lock = RLock()
    def _make_key(self, content: str) -> str:
        return hashlib.sha256(
            content.encode("utf-8", "surrogatepass")).hexdigest()[:16]
    @staticmethod
    def _normalize_store_args(content: Any, source: Any, category: Any,
                              tags: Any, confidence: Any) -> _KnowledgeDraft:
        if not isinstance(content, str):
            content = "" if content is None else str(content)
        return _KnowledgeDraft(
            content=content,
            source=source if isinstance(source, str) else "",
            category=_lookup_key(category) or _DEFAULT_CATEGORY,
            tags=_normalize_list_field(tags),
            confidence=_coerce_confidence(confidence),
        )
    def store(self, content: str, source: str = "",
              category: str = _DEFAULT_CATEGORY, tags: list[str] | None = None,
              confidence: float = _DEFAULT_KNOWLEDGE_CONFIDENCE) -> str:
        draft = self._normalize_store_args(
            content, source, category, tags, confidence)
        key = self._make_key(draft.content)
        with self._lock:
            existing = self._entries.get(key)
            if existing is not None:
                self._merge_duplicate(existing, draft)
                return key
            entry = KnowledgeEntry(
                key=key, content=draft.content, source=draft.source,
                category=draft.category, confidence=draft.confidence,
                tags=draft.tags, created_at=time.time(),
            )
            self._entries[key] = entry
            self._index.setdefault("cat:" + draft.category, set()).add(key)
            for tag in draft.tags:
                tag_key = _lookup_key(tag)
                if tag_key:
                    self._index.setdefault("tag:" + tag_key, set()).add(key)
            if len(self._entries) > self._max_entries:
                self._evict_oldest()
            return key
    def _merge_duplicate(self, entry: KnowledgeEntry,
                        draft: _KnowledgeDraft) -> None:
        known_tags = {_lookup_key(tag) for tag in entry.tags}
        for tag in draft.tags:
            tag_key = _lookup_key(tag)
            if not tag_key or tag_key in known_tags:
                continue
            known_tags.add(tag_key)
            entry.tags.append(tag)
            self._index.setdefault("tag:" + tag_key, set()).add(entry.key)
        if (entry.category == _DEFAULT_CATEGORY
                and draft.category != _DEFAULT_CATEGORY):
            self._reindex_category(entry, draft.category)
        if not entry.source and draft.source:
            entry.source = draft.source
        entry.confidence = max(entry.confidence, draft.confidence)
    def _reindex_category(self, entry: KnowledgeEntry,
                          new_category: str) -> None:
        old_key = "cat:" + entry.category
        self._index.setdefault(old_key, set()).discard(entry.key)
        if not self._index[old_key]:
            del self._index[old_key]
        entry.category = new_category
        self._index.setdefault("cat:" + new_category, set()).add(entry.key)
    @classmethod
    def _detached_ranked(cls, entries: Iterable[KnowledgeEntry],
                         top_k: int | None = None) -> list[KnowledgeEntry]:
        ranked = sorted(entries, key=_entry_rank_key)
        if top_k is not None:
            ranked = ranked[:top_k]
        return [replace(entry, tags=list(entry.tags)) for entry in ranked]
    @staticmethod
    def _normalize_search_args(query: str, category: Any,
                               top_k: int) -> tuple[str, str | None, int]:
        if not isinstance(query, str):
            query = ""
        query = query.strip()
        if (not isinstance(top_k, int) or isinstance(top_k, bool)
                or top_k < 0):
            top_k = _DEFAULT_TOP_K
        return query, _category_filter(category), top_k
    @staticmethod
    def _entry_matches(entry: KnowledgeEntry,
                       query_lower: str) -> bool:
        content = entry.content if isinstance(entry.content, str) else str(entry.content)
        if query_lower in content.lower():
            return True
        return any(
            query_lower in tag.lower()
            for tag in entry.tags if isinstance(tag, str)
        )
    def search(self, query: str, category: str = "",
               top_k: int = _DEFAULT_TOP_K) -> list[KnowledgeEntry]:
        query, category_key, top_k = self._normalize_search_args(
            query, category, top_k)
        if not query or category_key is None:
            return []
        results = []
        query_lower = query.lower()
        with self._lock:
            pool = self._entries.values()
            if category_key:
                keys = self._index.get("cat:" + category_key, set())
                pool = [self._entries[k] for k in keys if k in self._entries]
            for entry in pool:
                if self._entry_matches(entry, query_lower):
                    results.append(entry)
            return self._detached_ranked(results, top_k)
    def get_by_index(self, namespace: str,
                     value: str) -> list[KnowledgeEntry]:
        namespace_key = _lookup_key(namespace)
        value_key = _lookup_key(value)
        if namespace_key not in {"cat", "tag"} or not value_key:
            return []
        with self._lock:
            keys = self._index.get(f"{namespace_key}:{value_key}", set())
            entries = [self._entries[k] for k in keys if k in self._entries]
            return self._detached_ranked(entries)
    def list_categories(self) -> list[str]:
        with self._lock:
            return sorted({e.category for e in self._entries.values()})
    def stats(self) -> dict[str, Any]:
        with self._lock:
            return {
                "total_entries": len(self._entries),
                "categories": len({e.category for e in self._entries.values()}),
            }
    def _evict_oldest(self) -> None:
        with self._lock:
            if not self._entries:
                return
            oldest_key = min(
                self._entries,
                key=lambda k: self._entries[k].created_at)
            self._entries.pop(oldest_key)
            for cat in list(self._index.keys()):
                self._index[cat].discard(oldest_key)
                if not self._index[cat]:
                    del self._index[cat]
    def clear(self) -> None:
        with self._lock:
            self._entries.clear()
            self._index.clear()
    def export_patterns(self, category: str = "") -> list[dict[str, Any]]:
        target = _category_filter(category)
        if target is None:
            return []
        with self._lock:
            if target:
                entries = self.get_by_index("cat", target)
            else:
                entries = self._detached_ranked(self._entries.values())
        return [
            {"pattern": e.content,
             "source": e.source if isinstance(e.source, str) else "",
             "confidence": e.confidence,
             "tags": _normalize_list_field(e.tags)}
            for e in entries
        ]
OWASP_TOP_10_2021: list[dict[str, Any]] = [
    {"rank": 1, "id": "A01:2021", "name": "Broken Access Control"},
    {"rank": 2, "id": "A02:2021", "name": "Cryptographic Failures"},
    {"rank": 3, "id": "A03:2021", "name": "Injection"},
    {"rank": 4, "id": "A04:2021", "name": "Insecure Design"},
    {"rank": 5, "id": "A05:2021", "name": "Security Misconfiguration"},
    {"rank": 6, "id": "A06:2021", "name": "Vulnerable and Outdated Components"},
    {"rank": 7, "id": "A07:2021", "name": "Identification and Authentication Failures"},
    {"rank": 8, "id": "A08:2021", "name": "Software and Data Integrity Failures"},
    {"rank": 9, "id": "A09:2021", "name": "Security Logging and Monitoring Failures"},
    {"rank": 10, "id": "A10:2021", "name": "Server-Side Request Forgery (SSRF)"},
]
BUILTIN_CWE_KNOWLEDGE: dict[int, dict] = {
    22: {"name": "路径遍历", "severity": "P1", "category": "path_traversal",
         "description": "外部输入拼入文件路径可穿越目录边界，用 realpath 规范化并验证根目录"},
    78: {"name": "OS 命令注入", "severity": "P0", "category": "command_injection",
         "description": "外部输入拼入 shell 命令导致任意命令执行，用参数列表 + shell=False 或 shlex.quote"},
    79: {"name": "跨站脚本 XSS", "severity": "P1", "category": "xss",
         "description": "外部输入未转义输出到 HTML，用模板自动转义或 html.escape"},
    89: {"name": "SQL 注入", "severity": "P0", "category": "sql_injection",
         "description": "外部输入拼接 SQL 语句，改用参数化查询/预编译语句"},
    94: {"name": "代码注入", "severity": "P0", "category": "code_injection",
         "description": "外部输入进入 eval/exec/模板渲染导致任意代码执行"},
    330: {"name": "弱随机数", "severity": "P2", "category": "weak_crypto",
           "description": "安全场景使用 random 模块可预测，改用 secrets/os.urandom"},
    295: {"name": "证书校验缺失", "severity": "P1", "category": "insecure_config",
           "description": "verify=False/禁用证书校验导致中间人攻击"},
    601: {"name": "开放重定向", "severity": "P2", "category": "open_redirect",
           "description": "外部输入直接作为重定向目标，用白名单校验目标 URL"},
    611: {"name": "XXE 外部实体注入", "severity": "P1", "category": "xxe",
           "description": "XML 解析器默认解析外部实体，禁用 resolve_entities/no_network"},
    798: {"name": "硬编码凭据", "severity": "P1", "category": "secret",
           "description": "密钥/密码硬编码在源码中，改从环境变量或密钥管理服务获取"},
    918: {"name": "SSRF 服务端请求伪造", "severity": "P2", "category": "ssrf",
           "description": "外部输入控制请求 URL 可探测内网，用目标白名单/scheme 校验"},
    502: {"name": "不安全反序列化", "severity": "P0", "category": "deserialization",
           "description": "反序列化不可信数据可导致代码执行，用 JSON 等安全格式或校验器"},
}
BUILTIN_FRAMEWORK_PROFILES: dict[str, dict] = {
    "django": {
        "builtin_protections": ["模板自动转义(auto-escape)", "ORM 默认参数化查询", "CSRF 中间件"],
        "dangerous_patterns": ["mark_safe", "Manager.raw", "extra(select=...)", "format_html 拼接"],
        "safe_alternatives": ["模板上下文变量传递", "QuerySet.filter/参数化", "escape()"],
    },
    "flask": {
        "builtin_protections": ["Jinja2 自动转义(.html 模板)"],
        "dangerous_patterns": ["render_template_string", "Markup", "make_response 拼接 HTML"],
        "safe_alternatives": ["render_template + 上下文", "markupsafe.escape"],
    },
    "fastapi": {
        "builtin_protections": ["Pydantic 请求模型验证", "响应序列化"],
        "dangerous_patterns": ["HTMLResponse 拼接", "Jinja2Templates.from_string"],
        "safe_alternatives": ["Pydantic 模型 + 模板上下文"],
    },
}
BUILTIN_ORM_GUIDES: dict[str, dict[str, list[str]]] = {
    "django_orm": {
        "safe_methods": ["QuerySet.filter", "QuerySet.get", "QuerySet.exclude", "参数化 raw(sql, params)"],
        "dangerous_methods": ["Manager.raw(拼接 SQL)", "extra(select=拼接)", "cursor.execute(拼接)"],
    },
    "sqlalchemy": {
        "safe_methods": ["session.execute(text(sql), params)", "Query.filter(参数绑定)"],
        "dangerous_methods": ["session.execute(f-string SQL)", "engine.execute(拼接)"],
    },
    "peewee": {
        "safe_methods": ["Model.select().where(参数绑定)"],
        "dangerous_methods": ["Database.execute_sql(f-string SQL)"],
    },
}
def _internet_pattern_rows(entries: list[KnowledgeEntry],
                           seen_names: set[str]) -> list[dict]:
    rows: list[dict] = []
    for entry in entries:
        tags = getattr(entry, "tags", None)
        if not isinstance(tags, (list, tuple)):
            continue
        content = getattr(entry, "content", "")
        source = getattr(entry, "source", "")
        category = getattr(entry, "category", "")
        for tag in tags:
            tag_norm = _lookup_key(tag)
            if not tag_norm or tag_norm in seen_names:
                continue
            seen_names.add(tag_norm)
            rows.append({
                "name": tag,
                "description": content if isinstance(content, str) else "",
                "source": source if isinstance(source, str) else "",
                "category": _lookup_key(category) or _DEFAULT_CATEGORY,
                "confidence": getattr(
                    entry, "confidence", _DEFAULT_KNOWLEDGE_CONFIDENCE),
            })
    return rows
def _normalize_pattern_record(pattern: dict) -> dict:
    record = deepcopy(pattern)
    name = record.get("name")
    record["name"] = name.strip() if isinstance(name, str) else ""
    if "description" in record and not isinstance(record["description"], str):
        record["description"] = ""
    if "category" in record:
        record["category"] = _lookup_key(
            record["category"]) or _DEFAULT_CATEGORY
    if "severity" in record:
        severity = record["severity"]
        record["severity"] = (severity.strip()
                              if isinstance(severity, str) and severity.strip()
                              else _DEFAULT_RULE_SEVERITY)
    if "confidence" in record:
        record["confidence"] = _coerce_confidence(record["confidence"])
    if "source" in record:
        source = record["source"]
        if not (isinstance(source, str) and source.strip()):
            record.pop("source")
    return record
def _detection_rule_of(pattern: dict) -> dict:
    record = _normalize_pattern_record(pattern)
    name = record["name"]
    return {
        "rule_id": f"KL_{name}",
        "name": name,
        "severity": record.get("severity") or _DEFAULT_RULE_SEVERITY,
        "category": record.get("category") or _DEFAULT_CATEGORY,
        "dimension": "security",
        "description": record.get("description") or "",
        "confidence": record.get("confidence", _DEFAULT_LEARNED_CONFIDENCE),
        "source": record.get("source") or "knowledge",
    }
class SecurityKnowledgeLearner:
    def __init__(self) -> None:
        self.patterns: list[dict] = []
        self.cwe_database: dict[int, dict] = {
            k: dict(v) for k, v in BUILTIN_CWE_KNOWLEDGE.items()}
        self.framework_profiles: dict[str, dict] = {
            k: {ik: list(iv) for ik, iv in v.items()}
            for k, v in BUILTIN_FRAMEWORK_PROFILES.items()}
        self.orm_guides: dict[str, dict[str, list[str]]] = {
            k: {ik: list(iv) for ik, iv in v.items()}
            for k, v in BUILTIN_ORM_GUIDES.items()}
        self.owasp_top_10: list[dict[str, Any]] = [
            dict(item) for item in OWASP_TOP_10_2021]
        self.internet_kb = InternetKnowledgeBase()
        self._session_seq = 0
    def _pattern_dicts(self) -> list[dict]:
        return [p for p in self.patterns if isinstance(p, dict)]
    def add_pattern(self, pattern: dict) -> bool:
        if not isinstance(pattern, dict):
            return False
        record = _normalize_pattern_record(pattern)
        name = record["name"]
        if not name:
            _log.warning("[Security] add_pattern 跳过无效 name 的模式: %r",
                         pattern.get("name"))
            return False
        is_new = True
        effective_record = record
        name_key = _lookup_key(name)
        for existing in self._pattern_dicts():
            existing_name = existing.get("name", "")
            if _lookup_key(existing_name) == name_key:
                record["name"] = existing_name
                existing.update(record)
                effective_record = existing
                is_new = False
                break
        if is_new:
            self.patterns.append(record)
        self.internet_kb.store(
            content=effective_record.get("description") or name,
            source=effective_record.get("source", "learner"),
            category=effective_record.get("category", _DEFAULT_CATEGORY),
            tags=[name],
            confidence=effective_record.get(
                "confidence", _DEFAULT_LEARNED_CONFIDENCE),
        )
        return is_new
    def search_patterns(self, query: str) -> list[dict]:
        if not isinstance(query, str):
            query = ""
        if not query.strip():
            return []
        query_lower = query.strip().lower()
        patterns = self._pattern_dicts()
        results = [deepcopy(p) for p in patterns
                   if _pattern_matches(p, query_lower)]
        seen_names = {_lookup_key(p.get("name")) for p in patterns}
        entries = self.internet_kb.search(query, top_k=_DEFAULT_TOP_K)
        results.extend(_internet_pattern_rows(entries, seen_names))
        return results
    def export_as_detection_rules(self, category: str = "") -> list[dict]:
        target = _category_filter(category)
        if target is None:
            return []
        rules = []
        for pattern in self._pattern_dicts():
            rule = _detection_rule_of(pattern)
            if not rule["name"]:
                continue
            if target and _lookup_key(rule["category"]) != target:
                continue
            rules.append(rule)
        return rules
    def generate_knowledge_summary(self) -> dict[str, Any]:
        patterns = self._pattern_dicts()
        categories: dict[str, int] = {}
        for p in patterns:
            cat = _lookup_key(p.get("category")) or _DEFAULT_CATEGORY
            categories[cat] = categories.get(cat, 0) + 1
        cwe_severity: dict[str, int] = {}
        for info in self.cwe_database.values():
            sev = severity_key(info.get("severity"), _DEFAULT_RULE_SEVERITY)
            cwe_severity[sev] = cwe_severity.get(sev, 0) + 1
        return {
            "total_patterns": len(patterns),
            "categories": categories,
            "cwe_severity": cwe_severity,
            "total_cwes": len(self.cwe_database),
            "owasp_top_10_count": len(self.owasp_top_10),
        }
    def get_framework_profile_list(self, framework: str,
                                   field_name: str) -> list[str]:
        profile = self.framework_profiles.get(_lookup_key(framework))
        if not isinstance(profile, dict):
            return []
        return _normalize_list_field(profile.get(field_name))
    def get_orm_safe_methods(self, orm_name: str) -> dict[str, list[str]]:
        guide = self.orm_guides.get(_lookup_key(orm_name))
        if not isinstance(guide, dict):
            return {}
        return {key: _normalize_list_field(value)
                for key, value in guide.items()
                if isinstance(key, str) and key}
    def get_cwe_info(self, cwe_id: int | str) -> dict[str, Any] | None:
        number = _cwe_number(cwe_id)
        if number is None:
            return None
        info = self.cwe_database.get(number)
        return dict(info) if info is not None else None
    def get_cwe_by_severity(self, severity: str) -> list[dict[str, Any]]:
        target = severity_key(_severity_word(severity) or severity)
        if not target:
            return []
        return [
            {**info, "id": cid}
            for cid, info in self.cwe_database.items()
            if severity_key(info.get("severity")) == target
        ]
    def start_learning_session(self, sources: list[str] | None = None) -> dict:
        normalized_sources = clean_source_ids(
            [sources] if isinstance(sources, str) else sources)
        self._session_seq += 1
        return {
            "session_id": f"session_{int(time.time())}_{self._session_seq}",
            "sources": normalized_sources,
            "started": True,
            "completed": False,
            "patterns_count": len(self._pattern_dicts()),
        }
    def complete_session(self, session: dict, new_count: int,
                         update_count: int) -> dict:
        if not isinstance(session, dict):
            session = {}
        session["completed"] = True
        session["new_patterns"] = as_pure_count(new_count)
        session["updated_patterns"] = as_pure_count(update_count)
        return session
    def register_external_rules(self, rules: list[dict]) -> int:
        if not isinstance(rules, (list, tuple)):
            _log.warning(
                "[Security] register_external_rules 非序列入参已跳过: %r",
                type(rules).__name__)
            return 0
        count = 0
        for rule in rules:
            if self.add_pattern(rule):
                count += 1
        return count
    def get_owasp_top_10(self) -> list[dict[str, Any]]:
        return [dict(item) for item in self.owasp_top_10]
    def get_owasp_by_id(self, owasp_id: str) -> dict[str, Any] | None:
        target = _lookup_key(owasp_id)
        if not target:
            return None
        for item in self.owasp_top_10:
            if _lookup_key(item.get("id")) == target:
                return dict(item)
        return None
_learner_instance: SecurityKnowledgeLearner | None = None
_learner_instance_lock = RLock()
def get_security_knowledge() -> SecurityKnowledgeLearner:
    global _learner_instance
    if _learner_instance is None:
        with _learner_instance_lock:
            if _learner_instance is None:
                _learner_instance = SecurityKnowledgeLearner()
    return _learner_instance
_DEFAULT_RATE_LIMIT_SEC = 1.0
PYTHON_CPE_KEYWORDS: list[str] = [
    "python", "django", "flask", "fastapi", "tornado", "bottle",
    "pyramid", "celery", "sqlalchemy", "requests", "urllib3",
    "jinja2", "mako", "pillow", "numpy", "pandas", "cryptography",
    "aiohttp", "starlette", "pydantic", "sqlmodel",
    "httpx", "websockets", "asyncpg", "aiomysql",
]
_DEFAULT_RELEVANT_PACKAGES: frozenset[str] = frozenset(
    _normalize_package_name(pkg) for pkg in PYTHON_CPE_KEYWORDS)
PYPA_RAW_BASE = "https://raw.githubusercontent.com/pypa/advisory-database/main"
PYPA_API_TREE = "https://api.github.com/repos/pypa/advisory-database/git/trees/main?recursive=1"
_SYNC_SEVERITY_WORDS = frozenset({"critical", "high", "medium", "low", "unknown"})
_BATCH_FLUSH_SIZE = 20
_MAX_PROCESSED_STATE = 20000
_MAX_FUTURE_SKEW_SECONDS = 300.0
_DEFAULT_MAX_FILES = 100
_CVSS3_AV = {"N": 0.85, "A": 0.62, "L": 0.55, "P": 0.2}
_CVSS3_AC = {"L": 0.77, "H": 0.44}
_CVSS3_PR = {"N": 0.85, "L": 0.62, "H": 0.27}
_CVSS3_PR_CHANGED = {"N": 0.85, "L": 0.68, "H": 0.5}
_CVSS3_UI = {"N": 0.85, "R": 0.62}
_CVSS3_CIA = {"H": 0.56, "L": 0.22, "N": 0.0}
_PACKAGE_SINK_HINTS: tuple[tuple[tuple[str, ...], tuple[str, ...]], ...] = (
    (("django",), ("django.db.connection.execute", "mark_safe")),
    (("flask",), ("render_template_string", "flask.send_file")),
    (("requests",), ("requests.get", "requests.post", "requests.request")),
    (("urllib", "urllib3"), ("urllib.request.urlopen",)),
    (("jinja", "jinja2"), ("jinja2.Template", "from_string")),
    (("mako",), ("mako.template.Template",)),
    (("yaml", "pyyaml"), ("yaml.load", "yaml.unsafe_load")),
    (("pickle", "pickle5"), ("pickle.loads", "pickle.load")),
)
@dataclass
class SyncResult:
    source: str = ""
    status: str = "pending"
    new_entries: int = 0
    updated_entries: int = 0
    skipped_entries: int = 0
    errors: list[str] = field(default_factory=list)
    duration_ms: float = 0.0
    last_synced: str = ""
    def to_dict(self) -> dict[str, Any]:
        return asdict(self)
def _parse_cvss3_metrics(vector: str) -> tuple[dict[str, str], str, bool]:
    metrics: dict[str, str] = {}
    prefix, separator, body = vector.partition("/")
    version = prefix.removeprefix("CVSS:")
    if not separator or version not in {"3.0", "3.1"}:
        return metrics, "", False
    for seg in body.split("/"):
        if ":" in seg:
            k, v = seg.split(":", 1)
            metrics[k] = v
    if metrics.get("S") not in {"U", "C"}:
        return {}, "", False
    return metrics, version, metrics.get("S") == "C"
def _cvss3_severity_band(base: float) -> str:
    if base >= 9.0:
        return "critical"
    if base >= 7.0:
        return "high"
    if base >= 4.0:
        return "medium"
    return "low"
def _cvss3_base_severity(vector: str) -> str:
    metrics, version, scope_changed = _parse_cvss3_metrics(vector)
    if not version:
        return ""
    try:
        av = _CVSS3_AV[metrics["AV"]]
        ac = _CVSS3_AC[metrics["AC"]]
        pr = (_CVSS3_PR_CHANGED if scope_changed else _CVSS3_PR)[metrics["PR"]]
        ui = _CVSS3_UI[metrics["UI"]]
        c = _CVSS3_CIA[metrics["C"]]
        i = _CVSS3_CIA[metrics["I"]]
        a = _CVSS3_CIA[metrics["A"]]
    except KeyError:  # jwsgj:silent-ok 非法或缺项 CVSS 向量按未知严重度降级
        return ""
    iss = 1 - (1 - c) * (1 - i) * (1 - a)
    if scope_changed:
        if version == "3.0":
            impact = (7.52 * (iss - 0.029)
                      - 3.25 * (iss * 0.9731 - 0.02) ** 13)
        else:
            impact = 7.52 * (iss - 0.029) - 3.25 * (iss - 0.02) ** 15
    else:
        impact = 6.42 * iss
    if impact <= 0:
        return "low"
    base = min((1.08 if scope_changed else 1.0)
               * (impact + 8.22 * av * ac * pr * ui), 10)
    base = math.ceil(base * 10 - 1e-9) / 10
    return _cvss3_severity_band(base)
def _cvss_vector_severity(sev_entries: list) -> str:
    if not isinstance(sev_entries, list):
        return ""
    candidates: list[str] = []
    for entry in sev_entries:
        if isinstance(entry, dict) and str(entry.get("score") or "").startswith("CVSS:3."):
            severity = _cvss3_base_severity(str(entry["score"]))
            if severity:
                candidates.append(severity)
    if not candidates:
        return ""
    return min(candidates, key=severity_key)
def _normalize_cwe_ids(data: dict[str, Any],
                      db_specific: dict) -> list[str]:
    primary = _normalize_list_field(data.get("cwe_ids"))
    return primary or _normalize_list_field(db_specific.get("cwe_ids"))
def _collect_affected_info(
        data: dict[str, Any]) -> tuple[list[str], list[str]] | None:
    _affected = data.get("affected")
    if _affected is None:
        _affected = []
    elif not isinstance(_affected, list):
        return None
    packages: list[str] = []
    fixed_versions: list[str] = []
    for aff in _affected:
        if not isinstance(aff, dict):
            continue
        _pkg_node = aff.get("package")
        pkg = (str_or_empty(_pkg_node.get("name", ""))
               if isinstance(_pkg_node, dict) else "")
        if pkg and pkg not in packages:
            packages.append(pkg)
        _collect_fixed_versions(aff, fixed_versions)
    return packages, fixed_versions
def _collect_fixed_versions(aff: dict[str, Any],
                            fixed_versions: list[str]) -> None:
    ranges = aff.get("ranges")
    if not isinstance(ranges, list):
        return
    for rng in ranges:
        if not isinstance(rng, dict):
            continue
        events = rng.get("events")
        if not isinstance(events, list):
            continue
        for ev in events:
            if not isinstance(ev, dict):
                continue
            fixed = str_or_empty(ev.get("fixed"))
            if fixed and fixed not in fixed_versions:
                fixed_versions.append(fixed)
_SEVERITY_WORD_BY_LEVEL: dict[str, str] = {
    "P0": "critical", "P1": "high", "P2": "medium", "P3": "low",
}
def _severity_word(value: Any) -> str:
    word = str(value or "").strip().lower()
    if word == "moderate":
        word = "medium"
    return word if word in _SYNC_SEVERITY_WORDS else ""
def _severity_match_key(value: Any) -> str:
    word = _severity_word(value)
    if word:
        return word
    return _SEVERITY_WORD_BY_LEVEL.get(severity_key(value), "") or _lookup_key(value)
def _canonical_severity(value: Any) -> str:
    if not isinstance(value, str):
        return _DEFAULT_VULNERABILITY_SEVERITY
    text = value.strip()
    if not text:
        return _DEFAULT_VULNERABILITY_SEVERITY
    return _severity_match_key(text) or text
def _resolve_severity(data: dict[str, Any],
                      db_specific: dict) -> str:
    word = _severity_word(db_specific.get("severity"))
    if word and word != "unknown":
        return word
    return (_cvss_vector_severity(data.get("severity") or [])
            or word or _DEFAULT_VULNERABILITY_SEVERITY)
def _normalize_db_specific(data: dict[str, Any]) -> dict[str, Any]:
    raw = data.get("database_specific")
    return raw if isinstance(raw, dict) else {}
def _collect_references(data: dict[str, Any]) -> list[str]:
    _refs_raw = data.get("references") or []
    if not isinstance(_refs_raw, list):
        _refs_raw = []
    return [url for r in _refs_raw
            if isinstance(r, dict)
            for url in [r.get("url")]
            if isinstance(url, str) and url]
def _fix_guidance(fixed_versions: list[str]) -> str:
    if not fixed_versions:
        return ""
    return f"升级受影响包至修复版本: {', '.join(fixed_versions)}"
def _is_withdrawn_advisory(data: Any) -> bool:
    if not isinstance(data, dict):
        return False
    withdrawn = data.get("withdrawn")
    return (isinstance(withdrawn, (str, date))
            and bool(str(withdrawn).strip()))
def _advisory_to_entry(data: dict[str, Any],
                       file_path: str) -> VulnerabilityEntry | None:
    if not isinstance(data, dict) or _is_withdrawn_advisory(data):
        return None
    adv_id = str_or_empty(data.get("id"))
    if not adv_id:
        return None
    summary = str_or_empty(data.get("summary"))
    details = str_or_empty(data.get("details"))
    aliases = _normalize_list_field(data.get("aliases"))
    db_specific = _normalize_db_specific(data)
    cwe_ids = _normalize_cwe_ids(data, db_specific)
    affected = _collect_affected_info(data)
    if affected is None:
        return None
    packages, fixed_versions = affected
    severity = _resolve_severity(data, db_specific)
    category = _first_cwe_category(cwe_ids)
    sinks = _infer_sinks_for_package(packages)
    references = _collect_references(data)
    return VulnerabilityEntry(
        entry_id=adv_id,
        source=_PYPA_SOURCE,
        aliases=aliases,
        name=(summary or adv_id)[:120],
        description=(summary or details)[:500],
        severity=severity,
        cwe_ids=cwe_ids,
        category=category,
        affected_packages=packages,
        fixed_versions=fixed_versions,
        sinks=sinks,
        references=references,
        source_url=f"https://github.com/pypa/advisory-database/blob/main/{file_path}",
        published_date=str_or_empty(data.get("published")),
        modified_date=str_or_empty(data.get("modified")),
        fix_guidance=_fix_guidance(fixed_versions),
    )
def _first_cwe_category(cwe_ids: list[str]) -> str:
    for cwe_id in cwe_ids:
        category = cwe_to_category(cwe_id)
        if category != _DEFAULT_CATEGORY:
            return category
    return _DEFAULT_CATEGORY
def _infer_sinks_for_package(packages: list[str]) -> list[str]:
    package_names = {
        _normalize_package_name(package) for package in packages
    } - {""}
    sinks: list[str] = []
    for aliases, hints in _PACKAGE_SINK_HINTS:
        if package_names.intersection(aliases):
            sinks.extend(hints)
    return sinks
def _valid_state_timestamp(value: Any, cutoff: float) -> bool:
    timestamp = _finite_float_or_default(value)
    return cutoff < timestamp <= time.time() + _MAX_FUTURE_SKEW_SECONDS
def _normalize_rate_limit(value: Any) -> float:
    normalized = _finite_float_or_default(value, _DEFAULT_RATE_LIMIT_SEC)
    return normalized if normalized >= 0 else _DEFAULT_RATE_LIMIT_SEC
def _normalize_relevant_packages(value: Any) -> set[str]:
    if value is None:
        return set(_DEFAULT_RELEVANT_PACKAGES)
    source: Iterable[Any] = (value,) if isinstance(value, str) else (
        strict_iterable_list(value))
    packages = {_normalize_package_name(pkg) for pkg in source
                if isinstance(pkg, str) and pkg.strip()} - {""}
    if packages:
        return packages
    _log.warning(
        "PyPA 相关包作用域为空（入参类型 %s），回落默认包清单 %d 项",
        type(value).__name__, len(_DEFAULT_RELEVANT_PACKAGES))
    return set(_DEFAULT_RELEVANT_PACKAGES)
_REQUIREMENT_NAME_RE = re.compile(r"^([A-Za-z0-9][A-Za-z0-9._-]*)")
_REQUIREMENT_SKIP_PREFIXES: tuple[str, ...] = (
    "-", "#", "http://", "https://", "git+", "svn+", "hg+", "file:",
    "./", "../", "/", "~/",
)
def _load_toml_document(path: str) -> dict:
    try:
        import tomllib  # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
    except ImportError as _imp_err:
        _log.debug("[deps] tomllib 不可用，跳过 TOML 依赖发现: %s", _imp_err)
        return {}
    try:
        with open(path, "rb") as handle:
            data = tomllib.loads(strip_bom(handle.read().decode("utf-8")))
    except (OSError, ValueError, TypeError) as _toml_err:
        _log.debug("[deps] TOML 读取失败（跳过）: %s: %s", path, _toml_err)
        return {}
    return data if isinstance(data, dict) else {}
def _requirement_names(specs: Any) -> set[str]:
    names: set[str] = set()
    for spec in specs if isinstance(specs, (list, tuple)) else ():
        if not isinstance(spec, str):
            continue
        text = spec.strip()
        if not text or text.startswith(_REQUIREMENT_SKIP_PREFIXES):
            continue
        match = _REQUIREMENT_NAME_RE.match(text)
        if match is None:
            continue
        name = _normalize_package_name(match.group(1))
        if name:
            names.add(name)
    return names
def _poetry_dependency_names(dependencies: Any) -> set[str]:
    if not isinstance(dependencies, dict):
        return set()
    return {
        _normalize_package_name(name) for name in dependencies
        if isinstance(name, str) and name.strip().lower() != "python"
    } - {""}
def _names_from_pyproject(path: str) -> set[str]:
    data = _load_toml_document(path)
    if not data:
        return set()
    names: set[str] = set()
    project = data.get("project")
    if isinstance(project, dict):
        names |= _requirement_names(project.get("dependencies"))
        optional = project.get("optional-dependencies")
        if isinstance(optional, dict):
            for specs in optional.values():
                names |= _requirement_names(specs)
    dependency_groups = data.get("dependency-groups")
    if isinstance(dependency_groups, dict):
        for specs in dependency_groups.values():
            names |= _requirement_names(specs)
    tool = data.get("tool")
    poetry = tool.get("poetry") if isinstance(tool, dict) else None
    if isinstance(poetry, dict):
        names |= _poetry_dependency_names(poetry.get("dependencies"))
        names |= _poetry_dependency_names(poetry.get("dev-dependencies"))
        groups = poetry.get("group")
        if isinstance(groups, dict):
            for group in groups.values():
                if isinstance(group, dict):
                    names |= _poetry_dependency_names(
                        group.get("dependencies"))
    return names
def _read_config_parser(path: str) -> Any:
    import configparser  # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
    parser = configparser.ConfigParser(interpolation=None)
    try:
        with open(path, encoding="utf-8") as handle:
            parser.read_string(strip_bom(handle.read()), source=path)
    except (configparser.Error, OSError, UnicodeDecodeError) as _cfg_err:
        _log.debug("[deps] 配置读取失败（跳过）: %s: %s", path, _cfg_err)
        return None
    return parser
def _names_from_setup_cfg(path: str) -> set[str]:
    parser = _read_config_parser(path)
    if parser is None:
        return set()
    specs: list[str] = []
    defaults = parser.defaults()
    if (parser.has_section("options")
            and "install_requires" in parser.options("options")
            and "install_requires" not in defaults):
        specs.extend(parser.get("options", "install_requires").splitlines())
    if parser.has_section("options.extras_require"):
        for extra in parser.options("options.extras_require"):
            if extra in defaults:
                continue
            specs.extend(str(
                parser.get("options.extras_require", extra)).splitlines())
    return _requirement_names(specs)
def _names_from_pipfile(path: str) -> set[str]:
    data = _load_toml_document(path)
    names: set[str] = set()
    for section in ("packages", "dev-packages"):
        deps = data.get(section)
        if isinstance(deps, dict):
            names |= {
                _normalize_package_name(name) for name in deps
                if isinstance(name, str) and name.strip()
            }
    return names - {""}
def _names_from_requirements(path: str) -> set[str]:
    try:
        with open(path, encoding="utf-8", errors="replace") as handle:
            text = strip_bom(handle.read())
    except OSError as _req_err:
        _log.debug("[deps] 需求文件读取失败（跳过）: %s: %s", path, _req_err)
        return set()
    return _requirement_names(
        [raw.split("#", 1)[0] for raw in text.splitlines()])
def _iter_requirement_files(root: str):
    import glob  # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
    escaped_root = glob.escape(root)
    for pattern in ("requirements*.txt", os.path.join("requirements", "*.txt")):
        yield from sorted(glob.glob(os.path.join(escaped_root, pattern)))
def discover_project_packages(project_root: Any) -> set[str]:
    if not isinstance(project_root, (str, bytes, os.PathLike)):
        return set()
    root = os.path.abspath(os.fsdecode(os.fspath(project_root)))
    if not os.path.isdir(root):
        return set()
    names: set[str] = set()
    for filename, loader in (
            ("pyproject.toml", _names_from_pyproject),
            ("setup.cfg", _names_from_setup_cfg),
            ("Pipfile", _names_from_pipfile)):
        path = os.path.join(root, filename)
        if os.path.isfile(path):
            names |= loader(path)
    for path in _iter_requirement_files(root):
        names |= _names_from_requirements(path)
    return {name for name in names if name}
def _normalize_max_files(max_files: int | None) -> int | None:
    if (max_files is not None
            and (not isinstance(max_files, int)
                 or isinstance(max_files, bool) or max_files < 0)):
        return _DEFAULT_MAX_FILES
    return max_files
class PyPAAdvisorySync:
    def __init__(self, cache: VulnerabilityCache | None = None,
                 rate_limit_sec: float = _DEFAULT_RATE_LIMIT_SEC,
                 relevant_packages: list[str] | None = None) -> None:
        self.cache = cache if cache is not None else VulnerabilityCache()
        self.rate_limit_sec = _normalize_rate_limit(rate_limit_sec)
        self._relevant = _normalize_relevant_packages(relevant_packages)
        self._last_request_time = 0.0
    def _rate_limit(self) -> None:
        elapsed = time.time() - self._last_request_time
        if elapsed < self.rate_limit_sec:
            time.sleep(self.rate_limit_sec - elapsed)
        self._last_request_time = time.time()
    def _fetch(self, url: str, timeout: int = _DEFAULT_FETCH_TIMEOUT,
               as_json: bool = False) -> Any:
        self._rate_limit()
        req = urllib.request.Request(
            url, headers={"User-Agent": "pypa-advisory-sync/1.0",
                          "Accept": "application/vnd.github+json"})
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:  # nosec B310
                if resp.status != 200:
                    return None
                body = resp.read()
        except (OSError, http.client.HTTPException):
            _log.warning("PyPA 网络拉取失败（URL: %s）", url)
            return None
        try:
            text = body.decode("utf-8")
        except UnicodeDecodeError as e:
            _log.warning("PyPA 拉取响应非 UTF-8 文本（URL: %s）: %s", url, e)
            return None
        if as_json:
            try:
                return json.loads(text)
            except (json.JSONDecodeError, RecursionError) as e:
                _log.warning("PyPA 拉取响应非合法 JSON（URL: %s）: %s", url, e)
                return None
        return text
    def _is_relevant_advisory_path(self, path: Any) -> bool:
        if not isinstance(path, str):
            return False
        parts = path.split("/")
        return (len(parts) == 3 and parts[0] == "vulns"
                and path.endswith(".yaml")
                and _normalize_package_name(parts[1]) in self._relevant)
    def _collect_candidates(self, tree_data: dict) -> list[tuple[str, str]]:
        tree_items = tree_data.get("tree")
        if not isinstance(tree_items, list):
            tree_items = []
        candidates: list[tuple[str, str]] = []
        for item in tree_items:
            if not isinstance(item, dict):
                continue
            path = item.get("path", "")
            if self._is_relevant_advisory_path(path):
                fingerprint = item.get("sha")
                candidates.append((
                    path, fingerprint if isinstance(fingerprint, str) else ""))
        return candidates
    def _load_candidate_entry(
            self, yaml_path: str,
            result: SyncResult) -> tuple[VulnerabilityEntry | None, bool]:
        text = self._fetch(f"{PYPA_RAW_BASE}/{yaml_path}")
        if not text:
            result.errors.append(f"Failed to fetch {yaml_path}")
            result.status = "partial"
            return None, False
        return self._parse_candidate(text, yaml_path, result)
    def _parse_candidate(self, text: str, yaml_path: str,
                         result: SyncResult) -> tuple[VulnerabilityEntry | None, bool]:
        try:
            data = yaml.safe_load(text)  # jwsgj:suppress D52 — PyYAML 缺失时 _fetch_candidates 已清空候选并整体降级 partial，本方法不可达
        except (yaml.YAMLError, RecursionError, ValueError) as e:  # jwsgj:silent-ok 解析错误已写入同步结果
            result.errors.append(f"YAML parse error in {yaml_path}: {e}")
            result.status = "partial"
            return None, False
        if _is_withdrawn_advisory(data):
            adv_id = str_or_empty(data.get("id"))
            if adv_id:
                aliases = _normalize_list_field(data.get("aliases"))
                for identity in (adv_id, *aliases):
                    self.cache.remove(identity)
                return None, True
        try:
            entry = _advisory_to_entry(data, yaml_path)
        except (AttributeError, TypeError, ValueError) as e:
            _log.debug("PyPA 条目解析异常（结构非法）: %s: %s", yaml_path, e)
            entry = None
        if entry is None:
            result.errors.append(f"Invalid advisory structure: {yaml_path}")
            result.status = "partial"
        return entry, entry is not None
    def sync_incremental(
            self, max_files: int | None = _DEFAULT_MAX_FILES) -> SyncResult:
        max_files = _normalize_max_files(max_files)
        start = time.time()
        result = SyncResult(source=_PYPA_SOURCE, status="running")
        candidates = self._fetch_candidates(result)
        if result.status == "failed":
            result.duration_ms = (time.time() - start) * 1000
            return result
        state = self.cache.get_sync_state(_PYPA_SOURCE)
        if not isinstance(state, dict):
            state = {}
        processed = self._load_processed_state(state)
        self._sync_candidates(candidates, processed, result, max_files)
        self._save_state(processed)
        if result.status == "running":
            result.status = "success"
        result.duration_ms = (time.time() - start) * 1000
        result.last_synced = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        return result
    def _fetch_candidates(self, result: SyncResult) -> list[tuple[str, str]]:
        tree_data = self._fetch(PYPA_API_TREE, as_json=True)
        if not isinstance(tree_data, dict):
            result.status = "failed"
            result.errors.append("Failed to fetch advisory-database tree")
            return []
        if tree_data.get("truncated"):
            result.status = "failed"
            result.errors.append("Advisory-database tree is truncated")
            return []
        if not isinstance(tree_data.get("tree"), list):
            result.status = "failed"
            result.errors.append("Advisory-database tree is malformed: expected a list")
            return []
        candidates = self._collect_candidates(tree_data)
        if yaml is None and candidates:
            result.errors.append("PyYAML not installed: advisory parse skipped (install: pip install pyyaml)")
            result.status = "partial"
            return []
        return candidates
    def _sync_candidates(
            self, candidates: list[tuple[str, str]],
            processed: dict[str, dict[str, Any]], result: SyncResult,
            max_files: int | None) -> None:
        batch: list[VulnerabilityEntry] = []
        batched_ids: set[str] = set()
        attempted = 0
        for yaml_path, fingerprint in candidates:
            if max_files is not None and attempted >= max_files:
                break
            previous = processed.get(yaml_path)
            if (fingerprint and previous is not None
                    and previous["fingerprint"] == fingerprint):
                result.skipped_entries += 1
                continue
            attempted += 1
            entry, ingested = self._load_candidate_entry(yaml_path, result)
            if not ingested:
                continue
            processed[yaml_path] = {
                "processed_at": time.time(),
                "fingerprint": fingerprint,
            }
            if entry is None:
                continue
            batch.append(entry)
            entry_identities = _entry_identity_keys({
                "entry_id": entry.entry_id,
                "aliases": entry.aliases,
            })
            if (entry_identities.intersection(batched_ids)
                    or any(self.cache.contains(identity)
                           for identity in entry_identities)):
                result.updated_entries += 1
            else:
                result.new_entries += 1
            batched_ids.update(entry_identities)
            if len(batch) >= _BATCH_FLUSH_SIZE:
                self.cache.insert_batch(batch)
                self._save_state(processed)
                batch = []
        if batch:
            self.cache.insert_batch(batch)
    def _load_processed_state(
            self, state: dict[str, Any]) -> dict[str, dict[str, Any]]:
        if not isinstance(state, dict):
            return {}
        raw = state.get("processed_files")
        cutoff = time.time() - self.cache.ttl
        if isinstance(raw, dict):
            processed: dict[str, dict[str, Any]] = {}
            for path, value in raw.items():
                timestamp = value.get("processed_at") if isinstance(value, dict) else value
                if not _valid_state_timestamp(timestamp, cutoff):
                    continue
                fingerprint = value.get("fingerprint") if isinstance(value, dict) else ""
                processed[str(path)] = {
                    "processed_at": _finite_float_or_default(timestamp),
                    "fingerprint": (fingerprint if isinstance(fingerprint, str) else ""),
                }
            return processed
        if isinstance(raw, list):
            base_ts = _finite_float_or_default(state.get("last_synced"))
            if not _valid_state_timestamp(base_ts, cutoff):
                return {}
            return {str(path): {"processed_at": base_ts, "fingerprint": ""}
                    for path in raw}
        return {}
    def _save_state(self, processed: dict[str, dict[str, Any]]) -> None:
        files = dict(
            sorted(processed.items(),
                   key=lambda kv: kv[1]["processed_at"], reverse=True)
            [:_MAX_PROCESSED_STATE]
        )
        self.cache.set_sync_state(_PYPA_SOURCE, {"processed_files": files})
def sync_pypa_advisories(max_files: int | None = _DEFAULT_MAX_FILES,
                         cache: VulnerabilityCache | None = None,
                         relevant_packages: Any = None,
                         project_root: Any = "") -> SyncResult:
    if relevant_packages is None and project_root:
        relevant_packages = sorted(discover_project_packages(project_root))
    syncer = PyPAAdvisorySync(cache=cache, relevant_packages=relevant_packages)
    return syncer.sync_incremental(max_files=max_files)

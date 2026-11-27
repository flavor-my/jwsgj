from __future__ import annotations

import hashlib
import json
import os
import time
from collections.abc import Iterable, Iterator, Sequence
from dataclasses import asdict, dataclass, field
from typing import Any

from jwsgj.diag_dependency_analyzer import module_name_of, package_name_of
from jwsgj.diag_guard_io import guarded_open, safe_delete
from jwsgj.diag_types_normalize import (
    as_list,
    dict_or_empty,
    finding_file_key,
    int_or,
    is_high_severity,
    normalize_severity_rank,
    path_key,
    round_anchor_matches,
    same_file,
    signal_bool,
    str_or,
    timestamp_ms,
)
from jwsgj.diag_types_vocab import (
    FANOUT_DEPENDENCY_THRESHOLD,
    FANOUT_EXCLUDED_FILE_NAMES,
    FANOUT_FORBIDDEN_ACTIONS,
    FANOUT_GOVERNANCE_RULE,
    FANOUT_LEVEL_EXCLUDED,
    FANOUT_LEVEL_LABELS,
    FANOUT_LEVEL_THRESHOLDS,
    FANOUT_LEVEL_UNKNOWN,
    FANOUT_LEVELS,
    FANOUT_ORCHESTRATOR_DEPENDENCY_THRESHOLD,
    FANOUT_ROLE_EXCLUDED,
    FANOUT_ROLE_LABELS,
    FANOUT_ROLE_MODULE,
    FANOUT_ROLE_ORCHESTRATOR,
    FANOUT_ROLE_UNMAPPED,
    FANOUT_STRATEGIES,
    FANOUT_STRATEGY_GOVERNANCE,
    FANOUT_STRATEGY_LABELS,
    FANOUT_THRESHOLD_PROFILE,
    FANOUT_TIER_ADVISORY,
    FANOUT_TIER_EXCLUDED,
    FANOUT_TIER_MANDATORY,
    FANOUT_TIER_UNKNOWN,
    SEVERITY_RANK,
    FanoutGovernance,
    classify_fanout_level,
    classify_fanout_role,
    coerce_fanout_level,
    coerce_fanout_role,
    fanout_degree_of,
    fanout_level_is_mandatory,
    fanout_level_label,
    fanout_threshold_of,
    finalize_fanout_module_governance,
    is_fanout_excluded_file,
    resolve_fanout_degree,
    resolve_fanout_governance_level,
)
from jwsgj.fix_guide_rule_identity import (
    MATCH_LEVELS,
    FanoutOccurrence,
    FanoutScanResult,
    FanoutSignature,
    MatchResult,
    NodeContext,
    build_signatures,
    describe_signature,
    match_level_rank,
    match_occurrence,
    read_file_contexts,
)
from jwsgj.log_config import get_module_logger, log_swallowed
from jwsgj.runtime_paths import (
    json_artifact_dir,
    json_artifact_path,
    legacy_report_dirs,
)
from jwsgj.runtime_scope import collect_python_files, normalize_skill_dir
from jwsgj.skill_profile import SkillProfileError, resolve_skill_profile

logger = get_module_logger(__name__)
__all__ = [
    'FANOUT_EXCLUDED_FILE_NAMES',
    'FANOUT_FORBIDDEN_ACTIONS',
    'FANOUT_GOVERNANCE_RULE',
    'FANOUT_LEVELS',
    'FANOUT_LEVEL_EXCLUDED',
    'FANOUT_LEVEL_LABELS',
    'FANOUT_LEVEL_THRESHOLDS',
    'FANOUT_ORCHESTRATOR_DEPENDENCY_THRESHOLD',
    'FANOUT_REPORT_KEEP',
    'FANOUT_REPORT_SCHEMA',
    'FANOUT_ROLE_EXCLUDED',
    'FANOUT_ROLE_LABELS',
    'FANOUT_ROLE_MODULE',
    'FANOUT_ROLE_ORCHESTRATOR',
    'FANOUT_ROLE_UNMAPPED',
    'FANOUT_SOURCE_ID',
    'FANOUT_STAGE_ID',
    'FANOUT_STAGE_LABEL',
    'FANOUT_STRATEGIES',
    'FANOUT_STRATEGY_GOVERNANCE',
    'FANOUT_STRATEGY_LABELS',
    'FANOUT_THRESHOLD_PROFILE',
    'FANOUT_TIER_EXCLUDED',
    'FanoutConfig',
    'FanoutGovernance',
    'FanoutReport',
    'build_fanout_findings',
    'build_fanout_report',
    'classify_fanout_level',
    'classify_fanout_role',
    'fanout_level_is_mandatory',
    'fanout_level_label',
    'fanout_module_counts',
    'fanout_plan_summary',
    'fanout_report_path',
    'fanout_threshold_of',
    'fanout_treatment_handoff',
    'is_fanout_excluded_file',
    'load_fanout_findings',
    'load_fanout_report',
    'save_fanout_report',
    'scan_signatures',
    'select_fanout_strategy',
    'select_seed_findings',
    'summarize_fanout_report',
    'summarize_fanout_strategies',
]
_TREATABLE_LEVELS = frozenset({'exact', 'variant'})
_OCCURRENCE_LEVELS: tuple[str, ...] = tuple(
    level for level in MATCH_LEVELS if level != 'none')
_FANOUT_LEVELS = frozenset(_OCCURRENCE_LEVELS)
_ROSTER_UNSET: Any = object()
_SEED_LEVEL = 'seed'
_DEFAULT_MIN_SEVERITY = 'P2'
_DEFAULT_OCCURRENCE_SEVERITY = 'P3'
_DEFAULT_SEED_LIMIT = 20
_DEFAULT_MAX_OCCURRENCES_PER_SIGNATURE = 200
_DEFAULT_MIN_LEVEL = 'weak'
_DEFAULT_SNIPPET_CONTEXT_LINES = 1
_TIER_VALUES = frozenset({
    FANOUT_TIER_MANDATORY, FANOUT_TIER_ADVISORY,
    FANOUT_TIER_UNKNOWN, FANOUT_TIER_EXCLUDED,
})
def _normalized_tier(value: Any) -> str:
    text = str_or(value).strip().lower()
    return text if text in _TIER_VALUES else ''
def _normalized_severity(value: Any,
                        default: str = _DEFAULT_OCCURRENCE_SEVERITY) -> str:
    text = str_or(value).strip().upper()
    return text if text in SEVERITY_RANK else default
def _require_severity(value: Any, field_name: str) -> None:
    if not isinstance(value, str) or value.strip().upper() not in SEVERITY_RANK:
        raise ValueError(
            f'FanoutConfig.{field_name} 非法严重度: {value!r}'
            '（可选 P0-P4 或等价别名）')
def _require_match_level(value: Any, field_name: str) -> None:
    if not isinstance(value, str) or value.strip().lower() not in MATCH_LEVELS:
        raise ValueError(
            f'FanoutConfig.{field_name} 非法匹配级别: {value!r}'
            f"（可选 {'/'.join(MATCH_LEVELS)}）")
def _require_count(value: Any, field_name: str, *,
                   minimum: int = 0) -> None:
    if (isinstance(value, bool) or not isinstance(value, int)
            or value < minimum):
        raise ValueError(
            f'FanoutConfig.{field_name} 必须是 >= {minimum} 的整数，'
            f'实为 {value!r}')
def _config_text(raw: dict, field_name: str, default: str) -> Any:
    value = raw.get(field_name)
    if value is None or (isinstance(value, str) and not value.strip()):
        return default
    return value
def _config_count(raw: dict, field_name: str, default: int) -> Any:
    value = raw.get(field_name)
    if value is None or (isinstance(value, str) and not value.strip()):
        return default
    if not isinstance(value, str):
        return value
    try:
        return int(value.strip())
    except ValueError as exc:
        raise ValueError(
            f'FanoutConfig.{field_name} 必须是整数，实为 {value!r}') from exc
def _config_bool(raw: dict, field_name: str, default: bool) -> bool:
    value = raw.get(field_name)
    if value is None:
        return default
    if isinstance(value, bool):
        return value
    if isinstance(value, int) and value in (0, 1):
        return bool(value)
    if isinstance(value, str):
        text = value.strip().lower()
        if text in {'1', 'true', 'yes', 'on'}:
            return True
        if text in {'', '0', 'false', 'no', 'off', 'none', 'null'}:
            return False
    raise ValueError(
        f'FanoutConfig.{field_name} 必须是布尔值，实为 {value!r}')
@dataclass(frozen=True)
class FanoutConfig:
    min_severity: str = _DEFAULT_MIN_SEVERITY
    seed_limit: int = _DEFAULT_SEED_LIMIT
    include_tests: bool = True
    max_files: int = 0
    max_occurrences_per_signature: int = _DEFAULT_MAX_OCCURRENCES_PER_SIGNATURE
    min_level: str = _DEFAULT_MIN_LEVEL
    snippet_context_lines: int = _DEFAULT_SNIPPET_CONTEXT_LINES
    def __post_init__(self) -> None:
        _require_severity(self.min_severity, 'min_severity')
        _require_match_level(self.min_level, 'min_level')
        if not isinstance(self.include_tests, bool):
            raise TypeError(
                'FanoutConfig.include_tests 必须是布尔值，实为 '
                f'{type(self.include_tests).__name__}')
        _require_count(self.seed_limit, 'seed_limit')
        _require_count(self.max_files, 'max_files')
        _require_count(self.max_occurrences_per_signature,
                       'max_occurrences_per_signature', minimum=1)
        _require_count(self.snippet_context_lines, 'snippet_context_lines')
    def normalized_min_level(self) -> str:
        level = str_or(self.min_level).strip().lower() or _DEFAULT_MIN_LEVEL
        return level if level in MATCH_LEVELS else _DEFAULT_MIN_LEVEL
    @classmethod
    def from_report(cls, report: dict,
                    config: FanoutConfig | None = None) -> FanoutConfig:
        if config is not None:
            if isinstance(config, cls):
                return config
            raise TypeError(
                f'config 必须是 FanoutConfig，实为 {type(config).__name__}')
        raw_value = dict_or_empty(report).get('config')
        if raw_value is None:
            return cls()
        if not isinstance(raw_value, dict):
            raise TypeError(
                'FanoutConfig 配置段必须是 dict，实为 '
                f'{type(raw_value).__name__}')
        if not raw_value:
            return cls()
        defaults = cls()
        return cls(
            min_severity=_config_text(
                raw_value, 'min_severity', defaults.min_severity),
            seed_limit=_config_count(
                raw_value, 'seed_limit', defaults.seed_limit),
            include_tests=_config_bool(
                raw_value, 'include_tests', defaults.include_tests),
            max_files=_config_count(
                raw_value, 'max_files', defaults.max_files),
            max_occurrences_per_signature=_config_count(
                raw_value, 'max_occurrences_per_signature',
                defaults.max_occurrences_per_signature),
            min_level=_config_text(
                raw_value, 'min_level', defaults.min_level),
            snippet_context_lines=_config_count(
                raw_value, 'snippet_context_lines',
                defaults.snippet_context_lines),
        )
def _strategy_priority(strategy: str) -> int:
    try:
        return FANOUT_STRATEGIES.index(strategy)
    except ValueError:  # jwsgj:silent-ok
        return len(FANOUT_STRATEGIES)
def _is_guarded(item: dict) -> bool:
    return signal_bool(dict_or_empty(item).get('guarded'))
def _is_treatable_occurrence(item: dict) -> bool:
    data = dict_or_empty(item)
    return (bool(data)
            and _fanout_level(data.get('level')) in _TREATABLE_LEVELS
            and not _is_guarded(data))
def _is_excluded_occurrence(item: dict) -> bool:
    data = dict_or_empty(item)
    source = data
    seed_file = str_or(data.get('seed_file'))
    if not str_or(data.get('file')) and seed_file:
        source = {**data, 'file': seed_file}
    return resolve_fanout_governance_level(source) == FANOUT_LEVEL_EXCLUDED
def _treatable_occurrences(family: dict) -> list[dict]:
    return [occurrence for occurrence in (
        dict_or_empty(raw)
        for raw in as_list(dict_or_empty(family).get('occurrences'))) if occurrence
        and _is_treatable_occurrence(occurrence)
        and not _is_excluded_occurrence(occurrence)]
def select_fanout_strategy(
        family: dict, *, skill_dir: str = '') -> FanoutGovernance:
    data = dict_or_empty(family)
    occurrences = _treatable_occurrences(data)
    seed_sites = []
    for seed in _family_signature_payloads(data):
        seed_file = str_or(seed.get('seed_file'))
        if not seed_file or _is_excluded_occurrence(seed):
            continue
        seed_sites.append(seed)
    raw_files = [str_or(item.get('file')) for item in occurrences]
    raw_files.extend(str_or(item.get('seed_file')) for item in seed_sites)
    files_by_key: dict[str, str] = {}
    for raw_path in raw_files:
        if not raw_path:
            continue
        display = raw_path.replace('\\', '/')
        key = path_key(raw_path, skill_dir) or display
        files_by_key.setdefault(key, display)
    files = tuple(sorted(files_by_key.values()))
    levels = {_fanout_level(item.get('level')) for item in occurrences}
    shape_matched = any(
        'shape_exact' in as_list(item.get('reasons'))
        for item in occurrences)
    scopes = {
        str_or(item.get('scope_kind')) or 'module' for item in occurrences
    } | {
        str_or(item.get('scope_kind')) or 'module' for item in seed_sites
    }
    guarded_sites = sum(
        1 for raw in as_list(data.get('occurrences'))
        if _is_guarded(raw) and not _is_excluded_occurrence(raw))
    rationale: list[str] = []
    if len(files) >= 2 and (shape_matched or 'exact' in levels):
        strategy = 'code_migration'
        rationale.append(f'同形位点跨 {len(files)} 个文件重复，迁移到既有宿主')
    elif len(files) >= 2:
        strategy = 'unified_entry'
        rationale.append(f'同语义位点跨 {len(files)} 个文件，收敛到统一入口')
    elif len(scopes) >= 2 or guarded_sites:
        strategy = 'layer_boundary'
        rationale.append('位点跨作用域或存在局部守卫分裂，按分层边界调整')
    else:
        strategy = 'unified_entry'
        if occurrences:
            rationale.append(
                f'同文件 {len(occurrences) + len(seed_sites)} 处同族位点，'
                '收敛到统一入口')
        elif len(seed_sites) > 1:
            rationale.append(
                f'同文件 {len(seed_sites)} 个同族种子位点，收敛到统一入口')
        else:
            rationale.append('单一种子位点，按统一入口最小干预')
    return FanoutGovernance(
        strategy=strategy,
        priority=_strategy_priority(strategy),
        label=FANOUT_STRATEGY_LABELS[strategy],
        governance_method=FANOUT_STRATEGY_GOVERNANCE[strategy],
        rationale=tuple(rationale),
        files=files,
    )
def _orchestrator_roster(skill_dir: str = '') -> dict[str, str] | None:
    try:
        roster = dict(resolve_skill_profile(skill_dir).orchestrator_modules)
    except (SkillProfileError, OSError, ValueError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc, context='_orchestrator_roster:profile')
        return None
    return roster or None
def _module_role(module_name: str, rel: str = '',
                 orchestrator_modules: dict[str, str] | None = None) -> str:
    if is_fanout_excluded_file(rel):
        return FANOUT_ROLE_EXCLUDED
    if not module_name:
        return FANOUT_ROLE_UNMAPPED
    if classify_fanout_role(
            module_name,
            orchestrator_modules=orchestrator_modules) == (
                FANOUT_ROLE_ORCHESTRATOR):
        return FANOUT_ROLE_ORCHESTRATOR
    return FANOUT_ROLE_MODULE
def _governance_tier_of(level: str) -> str:
    normalized = coerce_fanout_level(level)
    if normalized == FANOUT_LEVEL_UNKNOWN:
        return FANOUT_TIER_UNKNOWN
    if normalized == FANOUT_LEVEL_EXCLUDED:
        return FANOUT_TIER_EXCLUDED
    return (FANOUT_TIER_MANDATORY
            if fanout_level_is_mandatory(normalized)
            else FANOUT_TIER_ADVISORY)
def _excluded_occurrence_governance() -> dict:
    return {
        'module_dependency_fanout': None,
        'module_governance_tier': FANOUT_TIER_EXCLUDED,
        'module_governance_level': FANOUT_LEVEL_EXCLUDED,
        'module_governance_label': fanout_level_label(FANOUT_LEVEL_EXCLUDED),
        'module_role': FANOUT_ROLE_EXCLUDED,
        'module_role_label': _role_label(FANOUT_ROLE_EXCLUDED),
    }
def _excluded_module_names(degrees: dict, with_sites: Iterable[str],
                           file_universe: Iterable[str],
                           skill_dir: str) -> set[str]:
    names = {str(name) for name in with_sites if name}
    for rel in file_universe:
        if is_fanout_excluded_file(str_or(rel)):
            name = module_name_of(rel, skill_dir)
            if name:
                names.add(name)
    names.add('__main__')
    root_name = package_name_of(skill_dir)
    if root_name:
        names.add(root_name)
        names.add(f'{root_name}.__main__')
    return {name for name in names if name in degrees}
def _module_degrees(skill_dir: str) -> dict[str, int]:
    from jwsgj.diag_dependency_analyzer import (
        scan_module_fanout,  # lazy-by-design
    )
    return scan_module_fanout(skill_dir)
def _attach_module_governance(occurrences: Sequence[FanoutOccurrence],
                              skill_dir: str, *,
                              file_universe: Sequence[str] = (),
                              degrees: dict | None = None,
                              orchestrator_roster: Any = _ROSTER_UNSET,
                              ) -> dict:
    degrees = _module_degrees(skill_dir) if degrees is None else degrees
    roster = (_orchestrator_roster(skill_dir)
              if orchestrator_roster is _ROSTER_UNSET
              else orchestrator_roster)
    rows: dict[str, dict] = {}
    excluded_modules: set[str] = set()
    excluded_sites = 0
    excluded_treatable_sites = 0
    for occurrence in occurrences:
        rel = path_key(occurrence.file, skill_dir)
        if is_fanout_excluded_file(rel):
            for field_name, value in _excluded_occurrence_governance().items():
                setattr(occurrence, field_name, value)
            excluded_name = module_name_of(occurrence.file, skill_dir)
            if excluded_name:
                excluded_modules.add(excluded_name)
            excluded_sites += 1
            if (_fanout_level(occurrence.level) in _TREATABLE_LEVELS
                    and not occurrence.guarded):
                excluded_treatable_sites += 1
            continue
        module_name = module_name_of(occurrence.file, skill_dir)
        degree = degrees.get(module_name) if module_name else None
        role = _module_role(module_name, rel, roster)
        level = classify_fanout_level(degree, role)
        tier = _governance_tier_of(level)
        occurrence.module_dependency_fanout = degree
        occurrence.module_governance_tier = tier
        occurrence.module_governance_level = level
        occurrence.module_governance_label = fanout_level_label(level)
        occurrence.module_role = role
        occurrence.module_role_label = _role_label(role)
        key = finding_file_key(rel) or rel
        if not key:
            continue
        row = rows.setdefault(key, {
            'module': rel,
            'module_key': key,
            'module_name': module_name,
            'module_role': role,
            'module_role_label': _role_label(role),
            'dependency_fanout': degree,
            'governance_level': level,
            'governance_label': fanout_level_label(level),
            'governance_tier': tier,
            'governance_threshold': fanout_threshold_of(role),
            'sites': 0,
            'treatable': 0,
        })
        row['sites'] += 1
        if (_fanout_level(occurrence.level) in _TREATABLE_LEVELS
                and not occurrence.guarded):
            row['treatable'] += 1
    modules = sorted(rows.values(),
                     key=lambda item: (-int_or(item.get('sites')),
                                       str_or(item.get('module'))))
    governed_excluded = _excluded_module_names(
        degrees, excluded_modules, file_universe, skill_dir)
    tiers = _tier_summary(modules)
    tiers['levels'][FANOUT_LEVEL_EXCLUDED] = {
        'modules': len(governed_excluded),
        'sites': excluded_treatable_sites,
    }
    tiers['excluded_modules'] = len(governed_excluded)
    tiers['excluded_sites'] = excluded_sites
    counts = {
        key: tiers[key]
        for key in (
            'mandatory_modules', 'advisory_modules', 'unknown_modules',
            'mandatory_sites', 'advisory_sites', 'unknown_sites',
        )
    }
    counts['excluded_modules'] = len(governed_excluded)
    counts['excluded_sites'] = excluded_sites
    level_modules = tiers['level_modules']
    level_sites = tiers['level_sites']
    return {
        'threshold': FANOUT_DEPENDENCY_THRESHOLD,
        'thresholds': dict(FANOUT_THRESHOLD_PROFILE),
        'levels': dict(tiers['levels']),
        'level_modules': level_modules,
        'level_sites': level_sites,
        'source': 'diag_dependency_analyzer.scan_graph',
        'basis': 'module_import_fanout',
        'rule': FANOUT_GOVERNANCE_RULE,
        'module_total': max(len(degrees) - len(governed_excluded), 0),
        'excluded': {
            'modules': sorted(governed_excluded),
            'module_count': len(governed_excluded),
            'site_count': excluded_sites,
            'file_names': sorted(FANOUT_EXCLUDED_FILE_NAMES),
            'reason': '包根/入口模块不参与模块级内部扇出治理',
        },
        'counts': counts,
        'modules': modules,
        'by_key': {row['module_key']: row for row in modules},
    }
FANOUT_REPORT_SCHEMA = 'fanout_report/1.1'
FANOUT_STAGE_ID = 'G'
FANOUT_STAGE_LABEL = '阶段G: 扇出诊断与治疗'
FANOUT_REPORT_KEEP = 3
_LATEST_NAME = 'fanout_report_latest.json'
_REPORT_PREFIX = 'fanout_report_'
_REPORT_SUFFIX = '.json'
_KNOWN_LINE_TOLERANCE = 3
_CONCLUSION_SEEDABLE = frozenset({'confirmed', 'likely', 'investigated'})
@dataclass
class FanoutReport:
    round_start_ts: str = ''
    skill_dir: str = ''
    generated_at: str = ''
    stage_id: str = FANOUT_STAGE_ID
    stage_label: str = FANOUT_STAGE_LABEL
    source_report_path: str = ''
    config: dict = field(default_factory=dict)
    summary: dict = field(default_factory=dict)
    gate: dict = field(default_factory=dict)
    families: list[dict] = field(default_factory=list)
    occurrences: list[dict] = field(default_factory=list)
    degraded_seeds: list[dict] = field(default_factory=list)
    errors: list[dict] = field(default_factory=list)
    file_universe: list[str] = field(default_factory=list)
    module_fanout: dict = field(default_factory=dict)
    evolution: dict = field(default_factory=dict)
    def to_dict(self) -> dict:
        return {
            'schema': FANOUT_REPORT_SCHEMA,
            'round_start_ts': self.round_start_ts,
            'skill_dir': self.skill_dir,
            'generated_at': self.generated_at,
            'stage_id': self.stage_id,
            'stage_label': self.stage_label,
            'source_report_path': self.source_report_path,
            'config': dict(self.config),
            'summary': dict(self.summary),
            'gate': dict(self.gate),
            'families': list(self.families),
            'occurrences': list(self.occurrences),
            'degraded_seeds': list(self.degraded_seeds),
            'errors': list(self.errors),
            'file_universe': list(self.file_universe),
            'module_fanout': dict(self.module_fanout),
            'evolution': dict(self.evolution),
        }
def fanout_module_counts(report: dict) -> list[dict]:
    data = dict_or_empty(report)
    occurrences = [dict_or_empty(item)
                   for item in as_list(data.get('occurrences'))]
    occurrences = [item for item in occurrences if item]
    frozen = _frozen_module_index(data)
    skill_root = str_or(data.get('skill_dir'))
    buckets: dict[str, dict] = {}
    for item in occurrences:
        raw_path = str_or(item.get('file'))
        if _is_excluded_occurrence(item):
            continue
        key = (finding_file_key(path_key(raw_path, skill_root))
               or finding_file_key(raw_path))
        if not key:
            continue
        bucket = buckets.setdefault(key, {
            'module': raw_path,
            'module_key': key,
            'total': 0,
            'treatable': 0,
            **dict.fromkeys(_OCCURRENCE_LEVELS, 0),
            'new_sites': 0,
            'guarded': 0,
            'families': [],
            'dependency_fanout': None,
            'governance_tier': '',
            'governance_level': '',
            'governance_label': '',
            'module_role': '',
            'module_role_label': '',
        })
        bucket['total'] += 1
        level = _fanout_level(item.get('level'))
        bucket[level] = int_or(bucket.get(level)) + 1
        if level in _TREATABLE_LEVELS and not _is_guarded(item):
            bucket['treatable'] += 1
        bucket['new_sites'] += int(signal_bool(item.get('is_new_site')))
        bucket['guarded'] += int(_is_guarded(item))
        family_id = str_or(item.get('family_id'))
        if family_id and family_id not in bucket['families']:
            bucket['families'].append(family_id)
        _merge_frozen_module(bucket, item, frozen.get(key))
    rows = list(buckets.values())
    bucketed = sum(row['total'] for row in rows)
    for row in rows:
        row['family_count'] = len(row['families'])
        row['share'] = (round(row['total'] / bucketed * 100, 1)
                        if bucketed else 0.0)
        finalize_fanout_module_governance(row)
    rows.sort(key=lambda row: (-row['total'], row['module']))
    return rows
def _fanout_level(raw) -> str:
    level = str_or(raw).strip().lower()
    return level if level in _FANOUT_LEVELS else _DEFAULT_MIN_LEVEL
def _frozen_module_index(report: dict) -> dict:
    section = dict_or_empty(dict_or_empty(report).get('module_fanout'))
    by_key = dict_or_empty(section.get('by_key'))
    if by_key:
        return {str(key): dict_or_empty(value)
                for key, value in by_key.items() if dict_or_empty(value)}
    index: dict[str, dict] = {}
    for raw in as_list(section.get('modules')):
        record = dict_or_empty(raw)
        key = str_or(record.get('module_key'))
        if key:
            index[key] = record
    return index
_GOVERNANCE_FIELD_MAP: tuple[tuple[str, str, str], ...] = (
    ('module_dependency_fanout', 'dependency_fanout', 'dependency_fanout'),
    ('module_governance_tier', 'governance_tier', 'governance_tier'),
    ('module_governance_level', 'governance_level', 'governance_level'),
    ('module_governance_label', 'governance_label', 'governance_label'),
    ('module_role', 'module_role', 'module_role'),
    ('module_role_label', 'module_role_label', 'module_role_label'),
)
def _merge_frozen_module(bucket: dict, item: dict, frozen: dict | None) -> None:
    for occurrence_key, frozen_key, row_key in _GOVERNANCE_FIELD_MAP:
        if bucket.get(row_key) not in (None, ''):
            continue
        value = item.get(occurrence_key)
        if value in (None, ''):
            value = dict_or_empty(frozen).get(frozen_key)
        if value not in (None, ''):
            bucket[row_key] = value
def _report_files(temp_dir: str) -> list[str]:
    if not os.path.isdir(temp_dir):
        return []
    try:
        names = os.listdir(temp_dir)
    except OSError as exc:
        log_swallowed(__name__, exc, context='_report_files')
        return []
    matched = [
        name for name in names
        if name.startswith(_REPORT_PREFIX) and name.endswith(_REPORT_SUFFIX)
    ]
    return [os.path.join(temp_dir, name)
            for name in sorted(matched, reverse=True)]
def _report_candidates(skill_dir: str) -> list[str]:
    current_dir = json_artifact_dir(skill_dir)
    files: list[str] = []
    seen_files: set[str] = set()
    seen_dirs: set[str] = set()
    for directory in (current_dir, *legacy_report_dirs(skill_dir)):
        directory_key = os.path.normcase(os.path.realpath(directory))
        if directory_key in seen_dirs:
            continue
        seen_dirs.add(directory_key)
        directory_files = _report_files(directory)
        ordered = [
            *(path for path in directory_files
              if os.path.basename(path) != _LATEST_NAME),
            *(path for path in directory_files
              if os.path.basename(path) == _LATEST_NAME),
        ]
        for path in ordered:
            key = os.path.normcase(os.path.realpath(path))
            if key in seen_files:
                continue
            seen_files.add(key)
            files.append(path)
    return files
def _read_report_payload(path: str) -> dict | None:
    try:
        with open(path, encoding='utf-8') as handle:
            payload = json.load(handle)
    except (OSError, ValueError, RecursionError) as exc:
        log_swallowed(__name__, exc, context='_read_report_payload')
        return None
    if not isinstance(payload, dict) or not payload:
        return None
    payload.setdefault('report_path', path)
    return payload
def load_fanout_report(skill_dir: str) -> dict:
    sd = normalize_skill_dir(skill_dir)
    for path in _report_candidates(sd):
        payload = _read_report_payload(path)
        if payload is not None:
            return payload
    return {}
def fanout_report_path(skill_dir: str, ts: str | None = None) -> str:
    sd = normalize_skill_dir(skill_dir)
    stamp = ts or timestamp_ms()
    return json_artifact_path(sd, f'{_REPORT_PREFIX}{stamp}{_REPORT_SUFFIX}')
def _unused_report_path(skill_dir: str) -> str:
    directory = json_artifact_dir(skill_dir)
    stamp = timestamp_ms()
    stem = f'{_REPORT_PREFIX}{stamp}'
    occupied: list[int] = []
    for path in _report_files(directory):
        name = os.path.basename(path)
        if not name.startswith(stem) or not name.endswith(_REPORT_SUFFIX):
            continue
        tail = name[len(stem):-len(_REPORT_SUFFIX)]
        if tail == '':
            occupied.append(-1)
        elif len(tail) == 3 and tail.isdigit():
            occupied.append(int(tail))
    if not occupied:
        return fanout_report_path(skill_dir, stamp)
    sequence = max(occupied) + 1
    if sequence > 999:
        raise FileExistsError(
            f'同一时间戳的报告快照序号已耗尽: {stamp}')
    return json_artifact_path(
        skill_dir, f'{stem}{sequence:03d}{_REPORT_SUFFIX}')
def _prune_reports(skill_dir: str, keep: int = FANOUT_REPORT_KEEP) -> None:
    paths = [path for path in _report_files(json_artifact_dir(skill_dir))
             if os.path.basename(path) != _LATEST_NAME]
    for path in paths[keep:]:
        try:
            safe_delete(path)
        except OSError as exc:
            log_swallowed(__name__, exc, context='_prune_reports')
def save_fanout_report(skill_dir: str, report: FanoutReport | dict) -> str:
    sd = normalize_skill_dir(skill_dir)
    payload = report.to_dict() if isinstance(report, FanoutReport) else dict(report)
    payload.pop('report_hash', None)
    payload.pop('report_path', None)
    payload['report_hash'] = hashlib.sha256(
        json.dumps(payload, ensure_ascii=False, sort_keys=True).encode('utf-8')
    ).hexdigest()
    latest = json_artifact_path(sd, _LATEST_NAME)
    try:
        while True:
            path = _unused_report_path(sd)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            try:
                with guarded_open(path, 'x', encoding='utf-8') as handle:
                    json.dump(payload, handle, ensure_ascii=False, indent=2)
                break
            except FileExistsError:
                continue
        with guarded_open(latest, 'w', encoding='utf-8') as handle:
            json.dump(payload, handle, ensure_ascii=False, indent=2)
        _prune_reports(sd)
    except OSError as exc:
        log_swallowed(__name__, exc, context='save_fanout_report')
        raise
    logger.info('[FanoutDiag] 报告已保存: %s', path)
    return path
def _normalize_finding(raw: Any) -> dict | None:
    data = dict_or_empty(raw)
    if not data:
        return None
    rule_id = (str_or(data.get('rule_id')) or str_or(data.get('rule'))
               or str_or(data.get('rule_applied')))
    if not rule_id:
        return None
    file_path = str_or(data.get('file')) or str_or(data.get('file_path'))
    line = int_or(data.get('line'))
    locator = str_or(data.get('locator'))
    if not locator and file_path:
        locator = f'{file_path}:{line}:{rule_id}'
    return {
        'rule_id': rule_id,
        'rule_applied': str_or(data.get('rule_applied')) or rule_id,
        'file': file_path,
        'line': line,
        'severity': _normalized_severity(data.get('severity')),
        'conclusion': (
            str_or(data.get('conclusion')).strip().lower() or 'uncertain'),
        'message': (str_or(data.get('message'))
                    or str_or(data.get('sample_message'))),
        'code_snippet': str_or(data.get('code_snippet')),
        'locator': locator,
        'sources': [item for item in as_list(data.get('sources'))
                    if isinstance(item, str)],
        'adjusted_confidence': data.get('adjusted_confidence'),
        'finding_id': str_or(data.get('finding_id')),
    }
def _iter_raw_findings(report: dict) -> Iterator[Any]:
    data = dict_or_empty(report)
    for key in ('findings_index', 'findings'):
        items = data.get(key)
        if isinstance(items, list):
            yield from items
    for bucket in ('confirmed', 'likely', 'uncertain', 'investigated'):
        items = data.get(bucket)
        if not isinstance(items, list):
            continue
        for item in items:
            if isinstance(item, dict) and not str_or(item.get('conclusion')):
                yield {**item, 'conclusion': bucket}
            else:
                yield item
    nested = data.get('cross_validation')
    if isinstance(nested, dict):
        yield from _iter_raw_findings(nested)
def select_seed_findings(report: dict, *,
                          min_severity: str = _DEFAULT_MIN_SEVERITY,
                          limit: int = _DEFAULT_SEED_LIMIT,
                          skill_dir: str = '') -> list[dict]:
    threshold = str_or(min_severity).strip().upper() or _DEFAULT_MIN_SEVERITY
    if threshold not in SEVERITY_RANK:
        raise ValueError(
            f'select_seed_findings.min_severity 非法严重度: {min_severity!r}'
            '（可选 P0-P4 或等价别名）')
    cap = int_or(limit, _DEFAULT_SEED_LIMIT)
    root = skill_dir or str_or(dict_or_empty(report).get('skill_dir'))
    if cap <= 0:
        return []
    seeds_by_key: dict[str, dict] = {}
    for raw in _iter_raw_findings(report):
        finding = _normalize_finding(raw)
        if finding is None:
            continue
        if finding['conclusion'] not in _CONCLUSION_SEEDABLE:
            continue
        if not is_high_severity(finding['severity'], threshold):
            continue
        key = '|'.join((
            finding['rule_id'],
            finding_file_key(path_key(finding['file'], root)),
            str(finding['line']),
        ))
        previous = seeds_by_key.get(key)
        if (previous is None
                or normalize_severity_rank(finding['severity'])
                < normalize_severity_rank(previous['severity'])):
            seeds_by_key[key] = finding
    seeds = list(seeds_by_key.values())
    seeds.sort(key=lambda item: (
        normalize_severity_rank(item['severity']),
        str_or(item['file']),
        int_or(item['line']),
        str_or(item['rule_id']),
    ))
    return seeds[:cap]
def _basename_of(path: str) -> str:
    return str_or(path).rsplit('/', 1)[-1]
def _known_locations(
        report: dict, skill_dir: str = '',
        ) -> dict[tuple[str, str], list[tuple[str, int]]]:
    index: dict[tuple[str, str], list[tuple[str, int]]] = {}
    seen: set[tuple[str, str, int]] = set()
    for raw in _iter_raw_findings(report):
        finding = _normalize_finding(raw)
        if finding is None:
            continue
        key = path_key(str_or(finding['file']), skill_dir)
        line = int_or(finding['line'])
        if not key or line <= 0:
            continue
        rule_id = str_or(finding['rule_id'])
        identity = (rule_id, key, line)
        if identity in seen:
            continue
        seen.add(identity)
        index_key = (rule_id, _basename_of(key))
        index.setdefault(index_key, []).append((key, line))
    return index
def _claim_known_site(
        occurrence: FanoutOccurrence,
        known: dict[tuple[str, str], list[tuple[str, int]]],
        skill_dir: str = '', *, exact_only: bool = False) -> bool:
    key = path_key(str_or(occurrence.file), skill_dir)
    if not key:
        return False
    index_key = (str_or(occurrence.rule_id), _basename_of(key))
    candidates = known.get(index_key)
    if not candidates:
        return False
    occurrence_line = int_or(occurrence.line)
    ordered = list(enumerate(candidates))
    if not exact_only:
        ordered.sort(key=lambda item: item[1][1])
    for position, (known_key, known_line) in ordered:
        if not same_file(known_key, key, skill_dir):
            continue
        if exact_only:
            if known_line != occurrence_line:
                continue
        elif abs(known_line - occurrence_line) > _KNOWN_LINE_TOLERANCE:
            continue
        candidates.pop(position)
        return True
    return False
def _family_payload(signature: FanoutSignature,
                    occurrences: Sequence[FanoutOccurrence],
                    module_fanout: dict | None = None,
                    skill_dir: str = '',
                    degrees: dict | None = None,
                    orchestrator_roster: Any = _ROSTER_UNSET,
                    additional_signatures: Sequence[FanoutSignature] = (),
                    ) -> dict:
    seed_payloads: list[dict] = []
    for item in (signature, *additional_signatures):
        seed = item.to_dict()
        seed.update(_seed_module_governance(
            item.seed_file, module_fanout, skill_dir, degrees,
            orchestrator_roster))
        seed_payloads.append(seed)
    payload = {
        'family_id': signature.family_id,
        'rule_id': signature.rule_id,
        'rule_family': signature.rule_family,
        'pattern_key': signature.pattern_key,
        'description': describe_signature(signature),
        'seed': seed_payloads[0],
        'occurrences': [item.to_dict() for item in occurrences],
    }
    if additional_signatures:
        payload['signatures'] = seed_payloads
    payload = _refresh_family_occurrences(payload, payload['occurrences'])
    payload['governance'] = select_fanout_strategy(
        payload, skill_dir=skill_dir).to_dict()
    return payload
def _family_signature_payloads(family: dict) -> list[dict]:
    data = dict_or_empty(family)
    payloads = [dict_or_empty(raw)
                for raw in as_list(data.get('signatures'))]
    payloads = [item for item in payloads if item]
    if payloads:
        return payloads
    seed = dict_or_empty(data.get('seed'))
    return [seed] if seed else []
def _module_governance_fields(record: dict) -> dict:
    values: dict = {}
    for occurrence_key, record_key, _row_key in _GOVERNANCE_FIELD_MAP:
        value = dict_or_empty(record).get(record_key)
        if value not in (None, ''):
            values[occurrence_key] = value
    return values
def _role_label(role: str) -> str:
    normalized = coerce_fanout_role(role) or FANOUT_ROLE_UNMAPPED
    return FANOUT_ROLE_LABELS[normalized]
def _seed_module_governance(file_path: str, module_fanout: dict | None,
                            skill_dir: str,
                            degrees: dict | None = None,
                            orchestrator_roster: Any = _ROSTER_UNSET,
                            ) -> dict:
    section = dict_or_empty(module_fanout)
    key = finding_file_key(path_key(file_path, skill_dir))
    record = dict_or_empty(dict_or_empty(section.get('by_key')).get(key))
    if record:
        values = _module_governance_fields(record)
        role = coerce_fanout_role(values.get('module_role')) or FANOUT_ROLE_MODULE
        level = (coerce_fanout_level(values.get('module_governance_level'))
                 or FANOUT_LEVEL_UNKNOWN)
        return {
            'module_name': str_or(record.get('module_name')),
            'module_role': role,
            'module_role_label': (str_or(values.get('module_role_label'))
                                  or _role_label(role)),
            'module_dependency_fanout': values.get(
                'module_dependency_fanout'),
            'module_governance_level': level,
            'module_governance_label': fanout_level_label(level),
            'module_governance_tier': (
                str_or(values.get('module_governance_tier'))
                or _governance_tier_of(level)),
        }
    rel = path_key(file_path, skill_dir)
    name = module_name_of(file_path, skill_dir)
    if is_fanout_excluded_file(rel):
        return {
            'module_name': name,
            **_excluded_occurrence_governance(),
        }
    roster = (_orchestrator_roster(skill_dir)
              if orchestrator_roster is _ROSTER_UNSET
              else orchestrator_roster)
    role = _module_role(name, rel, roster)
    degree = fanout_degree_of(
        dict_or_empty(degrees).get(name)) if name else None
    level = classify_fanout_level(degree, role)
    return {
        'module_name': name,
        'module_role': role,
        'module_role_label': _role_label(role),
        'module_dependency_fanout': degree,
        'module_governance_level': level,
        'module_governance_label': fanout_level_label(level),
        'module_governance_tier': _governance_tier_of(level),
    }
def fanout_treatment_handoff(fanout_report: dict, *,
                             skill_dir: str = '') -> dict:
    data = dict_or_empty(fanout_report)
    findings = build_fanout_findings(data, skill_dir=skill_dir)
    plan_summary = fanout_plan_summary({'items': findings})
    strategy_summary = summarize_fanout_strategies(data)
    strategies = dict_or_empty(strategy_summary.get('strategies'))
    item_strategies = dict_or_empty(plan_summary.get('strategies'))
    governance_methods = sorted({
        FANOUT_STRATEGY_GOVERNANCE[strategy]
        for strategy, count in strategies.items()
        if int_or(count) > 0 and strategy in FANOUT_STRATEGY_GOVERNANCE
    })
    return {
        'status': 'ready' if findings else 'empty',
        'site_candidates': len(findings),
        'groups': int_or(plan_summary.get('groups')),
        'members': int_or(plan_summary.get('members')),
        'seeds': int_or(plan_summary.get('seeds')),
        'strategies': strategies,
        'item_strategies': item_strategies,
        'strategy_priority': [
            item['strategy'] for item in strategy_summary.get('ordered', [])
        ],
        'governance_methods': governance_methods,
        'forbidden_actions': list(FANOUT_FORBIDDEN_ACTIONS),
        'summary': strategy_summary,
    }
MAX_ERRORS = 20
SNIPPET_MAX_CHARS = 300
def _rel_path(skill_dir: str, path: str) -> str:
    try:
        return os.path.relpath(path, skill_dir).replace('\\', '/')
    except ValueError as exc:
        log_swallowed(__name__, exc, context='_rel_path')
        return path.replace('\\', '/')
def _occurrence_id(family_id: str, rel_path: str, line: int, col: int) -> str:
    digest = hashlib.sha1(
        f'{family_id}|{rel_path}|{line}|{col}'.encode(),
        usedforsecurity=False,
    ).hexdigest()
    return digest[:12]
def _snippet_of(lines: Sequence[str], line: int, end_line: int,
                context_lines: int) -> str:
    if not lines or line <= 0:
        return ''
    start = max(line - 1 - context_lines, 0)
    stop = min(max(end_line, line) + context_lines, len(lines))
    text = '\n'.join(item.rstrip() for item in lines[start:stop])
    return text[:SNIPPET_MAX_CHARS]
def _statement_kinds(signatures: Iterable[FanoutSignature]) -> set[str]:
    return {sig.node_kind for sig in signatures if sig.node_kind}
def _is_seed_site(signature: FanoutSignature, rel_path: str,
                   line: int, skill_dir: str = '') -> bool:
    seed_file = str_or(signature.seed_file)
    if not seed_file:
        return False
    if not same_file(seed_file, rel_path, skill_dir):
        return False
    return int_or(signature.seed_line) == line
def _best_match(signatures: Sequence[FanoutSignature], ctx: NodeContext,
                max_rank: int | None = None,
                ) -> tuple[FanoutSignature, MatchResult] | None:
    best = None
    for signature in signatures:
        if signature.node_kind and signature.node_kind != ctx.kind:
            continue
        result = match_occurrence(signature, ctx)
        if result.level == 'none':
            continue
        rank = match_level_rank(result.level)
        if max_rank is not None and rank > max_rank:
            continue
        if best is None or (rank, -result.score) < (
                match_level_rank(best[1].level), -best[1].score):
            best = (signature, result)
    return best
def _coerce_signatures(value: Any) -> list[FanoutSignature]:
    if isinstance(value, FanoutSignature):
        items: Iterable[Any] = (value,)
    elif isinstance(value, (str, bytes, dict)):
        return []
    else:
        try:
            items = list(value)
        except TypeError as exc:
            log_swallowed(__name__, exc, context='_coerce_signatures')
            return []
    return [sig for sig in items
            if isinstance(sig, FanoutSignature) and not sig.degraded]
def _occurrence_from_match(signature: FanoutSignature, match: MatchResult,
                           ctx: NodeContext, rel_path: str, abs_path: str,
                           lines: Sequence[str], context_lines: int,
                           ) -> FanoutOccurrence:
    return FanoutOccurrence(
        occurrence_id=_occurrence_id(
            signature.family_id, rel_path, ctx.line, ctx.col),
        family_id=signature.family_id,
        rule_id=signature.rule_id,
        rule_family=signature.rule_family,
        file=rel_path,
        abs_path=abs_path,
        line=ctx.line,
        col=ctx.col,
        end_line=ctx.end_line,
        level=match.level,
        score=float(match.score),
        reasons=tuple(match.reasons),
        snippet=_snippet_of(lines, ctx.line, ctx.end_line, context_lines),
        scope_kind=ctx.scope_kind,
        qualname=ctx.qualname,
        guarded=ctx.guarded,
        node_kind=ctx.kind,
        seed_locator=signature.seed_locator,
    )
def _accepted_matches(signatures: Sequence[FanoutSignature], ctx: NodeContext,
                      rel_path: str, skill_dir: str, min_rank: int,
                      claimed_seed_sites: set[tuple[str, str, int]] | None = None,
                      ) -> list[tuple[FanoutSignature, MatchResult]]:
    seed_families = {
        signature.family_id for signature in signatures
        if _is_seed_site(signature, rel_path, ctx.line, skill_dir)
    }
    by_family: dict[str, list[FanoutSignature]] = {}
    for signature in signatures:
        by_family.setdefault(signature.family_id, []).append(signature)
    matches: list[tuple[FanoutSignature, MatchResult]] = []
    for family_id, family_signatures in by_family.items():
        matched = _best_match(family_signatures, ctx, min_rank)
        if matched is None:
            continue
        if family_id in seed_families:
            if claimed_seed_sites is None:
                continue
            seed_key = (family_id, rel_path, ctx.line)
            if seed_key not in claimed_seed_sites:
                claimed_seed_sites.add(seed_key)
                continue
        matches.append(matched)
    return matches
def scan_signatures(skill_dir: str,
                    signatures: Iterable[FanoutSignature],
                    config: FanoutConfig | None = None) -> FanoutScanResult:
    started = time.monotonic()
    cfg = (config if isinstance(config, FanoutConfig)
           else FanoutConfig.from_report({}, config))
    root = normalize_skill_dir(skill_dir, require_valid=True)
    _signatures = _coerce_signatures(signatures)
    result = FanoutScanResult()
    if not _signatures:
        result.duration_s = time.monotonic() - started
        return result
    kinds = _statement_kinds(_signatures)
    min_rank = match_level_rank(cfg.normalized_min_level())
    files = collect_python_files(root, include_tests=cfg.include_tests,
                                 max_files=cfg.max_files)
    seen: dict[tuple[str, str, int, int], FanoutOccurrence] = {}
    per_family: dict[str, int] = {}
    claimed_seed_sites: set[tuple[str, str, int]] = set()
    truncated: set[str] = set()
    result.files_scanned = len(files)
    result.files = tuple(_rel_path(root, path) for path in files)
    for path in files:
        try:
            loaded = read_file_contexts(path, kinds)
        except (SyntaxError, ValueError, RecursionError) as exc:
            log_swallowed(__name__, exc, context='scan_signatures:parse')
            result.files_failed += 1
            if len(result.errors) < MAX_ERRORS:
                result.errors.append({
                    'file': _rel_path(root, path),
                    'error': f'{type(exc).__name__}: {exc}'[:300],
                })
            continue
        if loaded is None:
            result.files_failed += 1
            if len(result.errors) < MAX_ERRORS:
                result.errors.append({
                    'file': _rel_path(root, path),
                    'error': 'source_unreadable',
                })
            continue
        lines, contexts = loaded
        rel_path = _rel_path(root, path)
        for ctx in contexts:
            matches = _accepted_matches(
                _signatures, ctx, rel_path, root, min_rank,
                claimed_seed_sites=claimed_seed_sites)
            for signature, match in matches:
                family_id = signature.family_id
                key = (family_id, rel_path, ctx.line, ctx.col)
                previous = seen.get(key)
                if (previous is None
                        and per_family.get(family_id, 0)
                        >= cfg.max_occurrences_per_signature):
                    truncated.add(family_id)
                    continue
                occurrence = _occurrence_from_match(
                    signature, match, ctx, rel_path, path, lines,
                    cfg.snippet_context_lines)
                if previous is None:
                    per_family[family_id] = per_family.get(family_id, 0) + 1
                    seen[key] = occurrence
                elif occurrence.score > previous.score:
                    seen[key] = occurrence
    result.occurrences = sorted(
        seen.values(),
        key=lambda item: (item.family_id, item.file, item.line, item.col))
    result.truncated_families = tuple(sorted(truncated))
    result.duration_s = time.monotonic() - started
    logger.info(
        '[FanoutScan] 扫描完成: 文件 %d（失败 %d），签名 %d，位点 %d，'
        '截断族 %d，耗时 %.2fs',
        result.files_scanned, result.files_failed, len(_signatures),
        len(result.occurrences), len(truncated), result.duration_s)
    return result
def _enrich_scan_occurrences(scan: FanoutScanResult, report: dict,
                             skill_dir: str, *,
                             degrees: dict | None = None,
                             orchestrator_roster: Any = _ROSTER_UNSET,
                             ) -> dict:
    known = _known_locations(report, skill_dir)
    ordered = sorted(
        scan.occurrences,
        key=lambda item: (
            str_or(item.rule_id), path_key(str_or(item.file), skill_dir),
            int_or(item.line)),
    )
    for occurrence in ordered:
        occurrence.is_new_site = not _claim_known_site(
            occurrence, known, skill_dir)
    return _attach_module_governance(
        scan.occurrences, skill_dir, file_universe=scan.files,
        degrees=degrees, orchestrator_roster=orchestrator_roster)
def build_fanout_report(skill_dir: str, report: dict, *,
                        config: FanoutConfig | None = None,
                        round_start_ts: str = '',
                        source_report_path: str = '') -> FanoutReport:
    sd = normalize_skill_dir(skill_dir)
    cfg = FanoutConfig.from_report(report, config)
    seeds = select_seed_findings(report, min_severity=cfg.min_severity,
                                 limit=cfg.seed_limit, skill_dir=sd)
    signatures, degraded = build_signatures(seeds, sd)
    scan: FanoutScanResult = scan_signatures(sd, signatures, cfg)
    degrees = _module_degrees(sd) if signatures else {}
    roster = _orchestrator_roster(sd) if signatures else None
    module_fanout = _enrich_scan_occurrences(
        scan, report, sd, degrees=degrees, orchestrator_roster=roster)
    by_family: dict[str, list[FanoutOccurrence]] = {}
    for occurrence in scan.occurrences:
        by_family.setdefault(occurrence.family_id, []).append(occurrence)
    signature_groups: dict[str, list[FanoutSignature]] = {}
    for signature in signatures:
        signature_groups.setdefault(signature.family_id, []).append(signature)
    families = [
        _family_payload(group[0], by_family.get(group[0].family_id, ()),
                        module_fanout, sd, degrees=degrees,
                        orchestrator_roster=roster,
                        additional_signatures=group[1:])
        for group in signature_groups.values()
    ]
    summary = _refresh_report_summary(
        {
            'seeds': len(seeds),
            'signatures': len(signatures),
            'degraded_seeds': len(degraded),
        },
        families, [item.to_dict() for item in scan.occurrences], scan,
        sd, module_fanout)
    summary['stage_id'] = FANOUT_STAGE_ID
    summary['stage_label'] = FANOUT_STAGE_LABEL
    summary['treatment_handoff'] = fanout_treatment_handoff(
        {'families': families}, skill_dir=sd)
    return FanoutReport(
        round_start_ts=round_start_ts,
        skill_dir=sd,
        generated_at=timestamp_ms(),
        source_report_path=str_or(source_report_path),
        config=asdict(cfg),
        summary=summary,
        families=families,
        occurrences=[item.to_dict() for item in scan.occurrences],
        degraded_seeds=degraded,
        errors=list(scan.errors),
        file_universe=list(scan.files),
        module_fanout=module_fanout,
    )
def summarize_fanout_report(report: dict) -> str:
    data = dict_or_empty(report)
    summary = dict_or_empty(data.get('summary'))
    if not summary:
        return '扇出报告为空'
    return (f"族 {summary.get('families', 0)} / 位点 "
            f"{summary.get('occurrences', 0)}（exact "
            f"{summary.get('exact', 0)}, variant {summary.get('variant', 0)}, "
            f"weak {summary.get('weak', 0)}）/ 新增 "
            f"{summary.get('new_sites', 0)} / 文件 "
            f"{summary.get('files_scanned', 0)}")
FANOUT_SOURCE_ID = 'fanout'
def _item_key(rule_id: str, file_path: str, line: int) -> str:
    basename = os.path.basename(str_or(file_path).replace('\\', '/'))
    return f'{str_or(rule_id)}|{basename}|{int_or(line)}'
def _plan_items(plan: dict) -> list:
    data = dict_or_empty(plan)
    for key in ('items', 'treatment_items'):
        items = data.get(key)
        if isinstance(items, list) and items:
            return items
    return []
def _existing_index(items: Iterable[dict] | dict | None,
                    ) -> dict[str, list[str]]:
    if isinstance(items, dict):
        existing_items: Iterable[Any] = _plan_items(items)
    elif items is None or isinstance(items, (str, bytes, bytearray)):
        existing_items = ()
    else:
        existing_items = items
    index: dict[str, list[str]] = {}
    for raw in existing_items:
        item = dict_or_empty(raw)
        if not item:
            continue
        file_path = (str_or(item.get('file_path'))
                     or str_or(item.get('file')))
        key = _item_key(str_or(item.get('rule_id')), file_path,
                        int_or(item.get('line')))
        index.setdefault(key, []).append(file_path)
    return index
def _has_existing(index: dict[str, list[str]], rule_id: str,
                  file_path: str, line: int,
                  skill_dir: str = '') -> bool:
    paths = index.get(_item_key(rule_id, file_path, line)) or ()
    return any(same_file(path, file_path, skill_dir) for path in paths)
def _occurrence_seed(occurrence: dict, family: dict) -> dict:
    seed_locator = str_or(occurrence.get('seed_locator'))
    for seed in _family_signature_payloads(family):
        if (seed_locator
                and str_or(seed.get('seed_locator')) == seed_locator):
            return seed
    return dict_or_empty(family.get('seed'))
def _severity_of(occurrence: dict, family: dict) -> str:
    if _fanout_level(occurrence.get('level')) == 'exact':
        return _normalized_severity(
            _occurrence_seed(occurrence, family).get('severity'),
            _DEFAULT_MIN_SEVERITY)
    return _DEFAULT_OCCURRENCE_SEVERITY
def _governance_finding_fields(source: dict, family: dict,
                               fanout_level: str, seed_locator: str) -> dict:
    degree = resolve_fanout_degree(source)
    role = coerce_fanout_role(source.get('module_role')) or FANOUT_ROLE_MODULE
    level = resolve_fanout_governance_level(source)
    tier = (_normalized_tier(source.get('module_governance_tier'))
            or _governance_tier_of(level))
    governance = dict_or_empty(family.get('governance'))
    return {
        'fanout_group': str_or(family.get('family_id')),
        'fanout_seed': str_or(seed_locator),
        'fanout_level': fanout_level,
        'fanout_governance_level': level,
        'fanout_governance_label': fanout_level_label(level),
        'fanout_module_role': role,
        'fanout_module_role_label': _role_label(role),
        'fanout_module_tier': tier,
        'fanout_module_fanout': degree,
        'fanout_mandatory': fanout_level_is_mandatory(level),
        'fanout_benefit_required': True,
        'governance_method': str_or(governance.get('governance_method')),
        'fanout_strategy': str_or(governance.get('strategy')),
        'forbidden_actions': list(
            as_list(governance.get('forbidden_actions'))
            or FANOUT_FORBIDDEN_ACTIONS),
    }
def _finding_of(occurrence: dict, family: dict) -> dict:
    rule_id = str_or(occurrence.get('rule_id')) or str_or(family.get('rule_id'))
    file_path = str_or(occurrence.get('file'))
    line = int_or(occurrence.get('line'))
    seed = _occurrence_seed(occurrence, family)
    seed_locator = (str_or(occurrence.get('seed_locator'))
                    or str_or(seed.get('seed_locator')))
    return {
        'locator': f'{file_path}:{line}:{rule_id}',
        'rule_id': rule_id,
        'rule_applied': rule_id,
        'conclusion': 'confirmed',
        'severity': _severity_of(occurrence, family),
        'file': file_path,
        'line': line,
        'message': (
            f"扇出同族位点（{_fanout_level(occurrence.get('level'))}，"
            f"score={occurrence.get('score')}）："
            f"种子 {seed_locator}"),
        'code_snippet': str_or(occurrence.get('snippet')),
        'sources': [FANOUT_SOURCE_ID],
        'evidence_type': 'fanout',
        'adjusted_confidence': occurrence.get('score'),
        'evidence_strength': occurrence.get('score'),
        **_governance_finding_fields(
            occurrence, family, _fanout_level(occurrence.get('level')),
            seed_locator),
    }
def _seed_finding_of(family: dict) -> dict | None:
    seed = dict_or_empty(family.get('seed'))
    if not seed:
        return None
    rule_id = str_or(seed.get('rule_id')) or str_or(family.get('rule_id'))
    file_path = str_or(seed.get('seed_file'))
    line = int_or(seed.get('seed_line'))
    return {
        'locator': str_or(seed.get('seed_locator')) or f'{file_path}:{line}:{rule_id}',
        'rule_id': rule_id,
        'rule_applied': rule_id,
        'conclusion': 'confirmed',
        'severity': _normalized_severity(
            seed.get('severity'), _DEFAULT_MIN_SEVERITY),
        'file': file_path,
        'line': line,
        'message': f"扇出种子：{str_or(family.get('description'))}",
        'code_snippet': str_or(seed.get('snippet')),
        'sources': [FANOUT_SOURCE_ID],
        'evidence_type': 'fanout',
        **_governance_finding_fields(
            seed, family, _SEED_LEVEL, seed.get('seed_locator')),
    }
def _append_new_finding(findings: list[dict], index: dict,
                        finding: dict | None, skill_dir: str) -> None:
    if finding is None or is_fanout_excluded_file(finding['file']):
        return
    rule_id = finding['rule_id']
    file_path = finding['file']
    line = int_or(finding['line'])
    if _has_existing(index, rule_id, file_path, line, skill_dir):
        return
    index.setdefault(_item_key(rule_id, file_path, line), []).append(file_path)
    findings.append(finding)
def build_fanout_findings(fanout_report: dict, *,
                          existing_items: (
                              Iterable[dict] | dict | None) = (),
                          skill_dir: str = '') -> list[dict]:
    data = dict_or_empty(fanout_report)
    index = _existing_index(existing_items)
    findings: list[dict] = []
    for raw_family in as_list(data.get('families')):
        family = dict_or_empty(raw_family)
        if not family:
            continue
        for seed in _family_signature_payloads(family):
            if _is_excluded_occurrence(seed):
                continue
            seed_family = dict(family)
            seed_family['seed'] = seed
            _append_new_finding(
                findings, index, _seed_finding_of(seed_family), skill_dir)
        for raw_occurrence in as_list(family.get('occurrences')):
            occurrence = dict_or_empty(raw_occurrence)
            if not _is_treatable_occurrence(occurrence):
                continue
            if _is_excluded_occurrence(occurrence):
                continue
            _append_new_finding(
                findings, index, _finding_of(occurrence, family), skill_dir)
    if findings:
        logger.info('[FanoutTreat] 扩族 finding: %d 条（family=%d）',
                    len(findings), len(as_list(data.get('families'))))
    return findings
def load_fanout_findings(skill_dir: str, *,
                          round_start_ts: str = '') -> list[dict]:
    sd = normalize_skill_dir(skill_dir)
    report = load_fanout_report(sd)
    if not report:
        return []
    report_round = str_or(report.get('round_start_ts'))
    current_round = str_or(round_start_ts)
    if not round_anchor_matches(report_round, current_round):
        logger.info('[FanoutTreat] 扇出报告轮次锚不完整或不匹配(跳过): %s != %s',
                    report_round, current_round)
        return []
    return build_fanout_findings(report, skill_dir=sd)
def fanout_plan_summary(plan_dict: dict) -> dict:
    items = _plan_items(plan_dict)
    groups: dict[str, int] = {}
    strategies: dict[str, int] = {}
    seeds = 0
    for raw in items:
        item = dict_or_empty(raw)
        group = str_or(item.get('fanout_group'))
        if not group:
            continue
        groups[group] = groups.get(group, 0) + 1
        seeds += int(str_or(item.get('fanout_level')).strip().lower()
                     == _SEED_LEVEL)
        strategy = str_or(item.get('fanout_strategy'))
        if strategy:
            strategies[strategy] = strategies.get(strategy, 0) + 1
    return {
        'groups': len(groups),
        'members': sum(groups.values()),
        'seeds': seeds,
        'group_sizes': dict(sorted(groups.items())),
        'strategies': dict(sorted(strategies.items())),
    }
def summarize_fanout_strategies(report: dict) -> dict:
    data = dict_or_empty(report)
    counts = {strategy: 0 for strategy in FANOUT_STRATEGIES}
    families = 0
    unclassified = 0
    for raw_family in as_list(data.get('families')):
        family = dict_or_empty(raw_family)
        if not family:
            continue
        families += 1
        governance = dict_or_empty(family.get('governance'))
        strategy = str_or(governance.get('strategy'))
        if strategy in counts:
            counts[strategy] += 1
        else:
            unclassified += 1
    ordered = [
        {
            'strategy': strategy,
            'label': FANOUT_STRATEGY_LABELS[strategy],
            'governance_method': FANOUT_STRATEGY_GOVERNANCE[strategy],
            'families': counts[strategy],
        }
        for strategy in FANOUT_STRATEGIES
    ]
    return {
        'strategies': counts,
        'ordered': ordered,
        'forbidden_actions': list(FANOUT_FORBIDDEN_ACTIONS),
        'total_families': families,
        'unclassified_families': unclassified,
    }
def _refresh_family_occurrences(family: dict,
                                occurrences: Sequence[dict]) -> dict:
    family_id = str_or(family.get('family_id'))
    members = [
        item for item in occurrences
        if str_or(item.get('family_id')) == family_id
    ]
    counts = dict.fromkeys(_OCCURRENCE_LEVELS, 0)
    files: set[str] = set()
    guarded = 0
    new_sites = 0
    for item in members:
        level = _fanout_level(item.get('level'))
        counts[level] = counts.get(level, 0) + 1
        file_path = str_or(item.get('file'))
        if file_path:
            files.add(file_path)
        guarded += int(_is_guarded(item))
        new_sites += int(signal_bool(item.get('is_new_site')))
    if counts['exact']:
        evidence_level = 'high'
    elif counts['variant']:
        evidence_level = 'medium'
    else:
        evidence_level = 'low'
    updated = dict(family)
    updated.update({
        'occurrences': list(members),
        'occurrence_count': len(members),
        'counts': counts,
        'new_site_count': new_sites,
        'guarded_count': guarded,
        'files': sorted(files),
        'evidence_level': evidence_level,
    })
    return updated
def _excluded_governance_counts(occurrences: Sequence[dict],
                                skill_dir: str = '') -> dict:
    modules: set[str] = set()
    sites = 0
    treatable = 0
    for raw in occurrences:
        item = dict_or_empty(raw)
        if not _is_excluded_occurrence(item):
            continue
        name = module_name_of(str_or(item.get('file')), skill_dir)
        if name:
            modules.add(name)
        sites += 1
        if _is_treatable_occurrence(item):
            treatable += 1
    return {'modules': len(modules), 'sites': sites,
            'treatable': treatable}
def _refresh_report_summary(summary: dict, families: Sequence[dict],
                            occurrences: Sequence[dict],
                            scan: FanoutScanResult,
                            skill_dir: str = '',
                            module_fanout: dict | None = None) -> dict:
    counts = dict.fromkeys(_OCCURRENCE_LEVELS, 0)
    new_sites = 0
    guarded = 0
    for item in occurrences:
        level = _fanout_level(item.get('level'))
        counts[level] = counts.get(level, 0) + 1
        new_sites += int(signal_bool(item.get('is_new_site')))
        guarded += int(_is_guarded(item))
    strategy_summary = summarize_fanout_strategies({'families': families})
    module_rows = fanout_module_counts(
        {'occurrences': occurrences, 'skill_dir': skill_dir})
    governance_tiers = _tier_summary(module_rows)
    excluded_section = dict_or_empty(
        dict_or_empty(module_fanout).get('excluded'))
    if excluded_section:
        excluded = {
            'modules': int_or(excluded_section.get('module_count')),
            'sites': int_or(excluded_section.get('site_count')),
        }
        excluded_treatable = int_or(dict_or_empty(
            dict_or_empty(dict_or_empty(module_fanout).get('levels')).get(
                FANOUT_LEVEL_EXCLUDED)).get('sites'))
    else:
        excluded = _excluded_governance_counts(occurrences, skill_dir)
        excluded_treatable = int_or(excluded.get('treatable'))
    governance_tiers['excluded_modules'] = excluded['modules']
    governance_tiers['excluded_sites'] = excluded['sites']
    governance_tiers['levels'][FANOUT_LEVEL_EXCLUDED] = {
        'modules': excluded['modules'], 'sites': excluded_treatable}
    updated = dict(summary)
    updated.update({
        'families': len(families),
        'occurrences': len(occurrences),
        'exact': counts['exact'],
        'variant': counts['variant'],
        'weak': counts['weak'],
        'new_sites': new_sites,
        'guarded': guarded,
        'strategies': dict_or_empty(strategy_summary.get('strategies')),
        'unclassified_families': int_or(
            strategy_summary.get('unclassified_families')),
        'module_counts': module_rows,
        'governance_tiers': governance_tiers,
        'files_scanned': scan.files_scanned,
        'files_failed': scan.files_failed,
        'truncated_families': list(scan.truncated_families),
        'duration_s': round(scan.duration_s, 4),
    })
    return updated
def _tier_summary(module_rows: Sequence[dict]) -> dict:
    buckets = {
        FANOUT_TIER_MANDATORY: {'modules': 0, 'sites': 0},
        FANOUT_TIER_ADVISORY: {'modules': 0, 'sites': 0},
        FANOUT_TIER_UNKNOWN: {'modules': 0, 'sites': 0},
        FANOUT_TIER_EXCLUDED: {'modules': 0, 'sites': 0},
    }
    level_buckets = {
        level: {'modules': 0, 'sites': 0} for level in FANOUT_LEVELS
    }
    level_buckets[FANOUT_LEVEL_UNKNOWN] = {'modules': 0, 'sites': 0}
    level_buckets[FANOUT_LEVEL_EXCLUDED] = {'modules': 0, 'sites': 0}
    for raw in module_rows:
        row = dict_or_empty(raw)
        level = coerce_fanout_level(row.get('governance_level'))
        if level not in level_buckets:
            level = FANOUT_LEVEL_UNKNOWN
        level_buckets[level]['modules'] += 1
        level_buckets[level]['sites'] += int_or(row.get('treatable'))
        tier = _normalized_tier(row.get('governance_tier'))
        if tier not in buckets:
            tier = _governance_tier_of(level)
        buckets[tier]['modules'] += 1
        buckets[tier]['sites'] += int_or(row.get('treatable'))
    return {
        'threshold': FANOUT_DEPENDENCY_THRESHOLD,
        'thresholds': dict(FANOUT_THRESHOLD_PROFILE),
        'basis': 'module_import_fanout',
        'rule': FANOUT_GOVERNANCE_RULE,
        'levels': {
            level: dict(level_buckets[level])
            for level in (*FANOUT_LEVELS, FANOUT_LEVEL_UNKNOWN,
                          FANOUT_LEVEL_EXCLUDED)
        },
        'level_modules': {
            level: level_buckets[level]['modules']
            for level in FANOUT_LEVELS
        },
        'level_sites': {
            level: level_buckets[level]['sites']
            for level in FANOUT_LEVELS
        },
        'mandatory_modules': buckets[FANOUT_TIER_MANDATORY]['modules'],
        'advisory_modules': buckets[FANOUT_TIER_ADVISORY]['modules'],
        'unknown_modules': buckets[FANOUT_TIER_UNKNOWN]['modules'],
        'mandatory_sites': buckets[FANOUT_TIER_MANDATORY]['sites'],
        'advisory_sites': buckets[FANOUT_TIER_ADVISORY]['sites'],
        'unknown_sites': buckets[FANOUT_TIER_UNKNOWN]['sites'],
        'excluded_modules': buckets[FANOUT_TIER_EXCLUDED]['modules'],
        'excluded_sites': buckets[FANOUT_TIER_EXCLUDED]['sites'],
        'enforced_sites': buckets[FANOUT_TIER_MANDATORY]['sites'],
    }

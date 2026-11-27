from __future__ import annotations

import ast
import hashlib
import logging
import os
import re as _re
from collections import defaultdict, deque
from collections.abc import Iterable, Iterator, Sequence
from dataclasses import dataclass, field
from enum import Enum
from functools import lru_cache
from typing import Any

import jwsgj.fix_guide_knowledge as _corpus
from jwsgj.diag_shared_ast_views import (
    compute_code_region,
    parent_map,
    register_cache_release,
)
from jwsgj.diag_shared_source_core import parse_cached, read_source
from jwsgj.diag_types_normalize import (
    as_sequence,
    canonical_rule_key,
    coerce_line,
    dict_or_empty,
    finding_file_key,
    findings_container,
    identifier_text,
    int_or,
    make_locator,
    norm_dict,
    normalize_target_path,
    safe_rule_id,
    same_file,
    seed_key,
    str_or,
)
from jwsgj.diag_types_vocab import (
    CV_RULES,
    FANOUT_TIER_UNKNOWN,
    RULE_BROAD_EXCEPTION,
    RULE_FAMILY_MAP,
    RULE_HIGH_COMPLEXITY,
    RULE_ID_PREFIX_CATEGORY,
    RULE_MISSING_DOCSTRING,
    SOURCE_SEQUENCE_TYPES,
    CodeRegion,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    'ANCHOR_LIMIT',
    'CONFLICTING_PAIRS',
    'CONFLICT_COMPLEXITY_FAMILIES',
    'CONFLICT_DEAD_CODE_FAMILIES',
    'CONFLICT_FIX_SAFETY_FAMILIES',
    'CONFLICT_LOW_COMPLEXITY_FAMILIES',
    'CONFLICT_RESOURCE_LEAK_FAMILIES',
    'CONFLICT_SYNTAX_ERROR_FAMILIES',
    'CONFLICT_TEST_FAILURE_FAMILIES',
    'CONFLICT_TYPE_ANNOTATION_FAMILIES',
    'DEAD_CODE_FAMILIES',
    'FILE_LEVEL_FAMILIES',
    'KNOWN_HIGH_FP_FAMILIES',
    'MATCH_LEVELS',
    'RULE_FAMILY_SETS',
    'RULE_ID_ALIASES',
    'SECURITY_FAMILY_UNION',
    'SHAPE_MAX_DEPTH',
    'SHAPE_MAX_NODES',
    'ConflictReport',
    'DependencyEdge',
    'DependencyGraph',
    'DependencyType',
    'FanoutOccurrence',
    'FanoutScanResult',
    'FanoutSignature',
    'MatchResult',
    'NodeContext',
    'analyze_conflicts',
    'build_dependency_graph',
    'build_signature',
    'build_signatures',
    'canonical_rule_id',
    'check_rule_exclusion',
    'clear_rule_match_caches',
    'clear_rule_metadata_cache',
    'describe_signature',
    'extract_anchors',
    'extract_bandit_id',
    'extract_shape',
    'finding_family',
    'get_bandit_fix_suggestion',
    'get_fix_guidance',
    'get_fix_order',
    'get_fix_order_for_findings',
    'get_ruff_delegation_hint',
    'get_rule_family_set',
    'get_rule_metadata',
    'get_rule_semantic',
    'get_se_fix_suggestion',
    'is_dead_code_finding',
    'is_family_member',
    'iter_file_contexts',
    'locate_seed_node',
    'lookup_rule_family',
    'make_locator_from_finding',
    'match_level_rank',
    'match_occurrence',
    'match_rule_families',
    'matches_dead_code_signal',
    'matches_rule_family',
    'node_context_of',
    'normalize_rule',
    'normalize_se_rule_id',
    'read_file_contexts',
    'resolve_rule_alias',
    'rule_fix_priority',
    'rules_are_mutex',
    'signature_from_dict',
]
_log = logging.getLogger(__name__)
_log.info("fix_guide_rule_identity 规则身份与族谱域已加载: %d 项导出", len(__all__))
_DEFAULT_SKILL_DIR = ""
_DEFAULT_RULE_ID_FIRST = False
RULE_ID_ALIASES: dict[str, str] = {
    "lazy_import": "AP-C2",
    "C8_dead_code": "dead_code",
    "nested_loop": "high_complexity",
    "string_concat_in_loop": "B09",
    "dead_code": "AP-C8",
    "orphan": "dead_code",
    "untested_function": "low_coverage",
    "public_untested": "low_coverage",
    "none_comparison": "NC-01",
    "bare_except": "BE-01",
    "broad_except": "BE-01",
    "empty_except": "BE-01",
    "mutable_default_arg": "MDA-01",
    "mutable_default": "MDA-01",
    "pure_forward": "PF01",
    "trivial_wrapper": "PF01",
    "thin_wrapper": "PF01",
    "delegation": "PF01",
    "duplicate_default": "AP-C18",
    "default_duplication": "AP-C18",
    "C18_default_duplication": "AP-C18",
    "passthrough_layer": "AP-C19",
    "pure_forward_layer": "AP-C19",
    "C19_passthrough_layer": "AP-C19",
    "high_complexity": "DP-16",
    "complexity": "high_complexity",
    "type_hint": "TY-01",
    "missing_annotations": "TY-01",
    "rule15": "high_complexity",
    "code_injection": "SEC-01",
    "sql_injection": "SEC-02",
    "hardcoded_credential": "SEC-03",
    "weak_crypto": "SEC-04",
    "weak_random": "SEC-05",
    "path_traversal": "SEC-06",
    "assert_usage": "B101",
    "security_issues": "SEC-GEN",
    "broken_call": "BC-01",
    "shadowing_builtin": "SB-01",
    "规则1": "AP-C8",
    "规则2": "SEC-GEN",
    "规则3": "DP-16",
    "规则13": "SZ-02",
}
@lru_cache(maxsize=1024)
def _normalize_rule_for_match_cached(rule_id: str) -> str:
    return canonical_rule_key(rule_id)
def _normalize_rule_for_match(rule_id) -> str:
    return (_normalize_rule_for_match_cached(rule_id)
            if isinstance(rule_id, str) else "")
_FAMILY_SENTINELS = frozenset({"NONE"})
def _family_text(value) -> str:
    text = str_or(value).strip()
    return "" if text.upper() in _FAMILY_SENTINELS else text
_MAX_ALIAS_DEPTH = 3
def _next_alias(current: str) -> str:
    mapped = RULE_ID_ALIASES.get(current)
    if isinstance(mapped, str) and mapped and mapped != current:
        return mapped
    _key = _normalize_rule_for_match(current)
    for alias, target in RULE_ID_ALIASES.items():
        if (isinstance(target, str) and target and target != current
                and _normalize_rule_for_match(alias) == _key):
            return target
    return ""
def resolve_rule_alias(rule_id: str) -> str:
    if not isinstance(rule_id, str) or not rule_id:
        return ""
    current = rule_id.strip()
    for _ in range(_MAX_ALIAS_DEPTH):
        mapped = _next_alias(current)
        if not mapped:
            break
        current = mapped
    return current
_KNOWN_CANONICAL_CACHE: dict[str, str] | None = None
def _known_canonical_index() -> dict[str, str]:
    global _KNOWN_CANONICAL_CACHE
    if _KNOWN_CANONICAL_CACHE is None:
        forms: dict[str, str] = {}
        for _table in (_corpus.RULE_FIX_KNOWLEDGE, _corpus.BANDIT_FIX_SUGGESTIONS,
                       _corpus.SE_FIX_KNOWLEDGE):
            for _key in _table:
                forms.setdefault(_normalize_rule_for_match(_key), _key)
        for _value in RULE_ID_ALIASES.values():
            if isinstance(_value, str) and _value:
                forms.setdefault(_normalize_rule_for_match(_value), _value)
        _KNOWN_CANONICAL_CACHE = forms
    return _KNOWN_CANONICAL_CACHE
def _known_canonical_form(rule_id: str) -> str:
    return _known_canonical_index().get(
        _normalize_rule_for_match(rule_id), rule_id)
def canonical_rule_id(rule_id: str) -> str:
    if not isinstance(rule_id, str):
        return ""
    _resolved = resolve_rule_alias(rule_id)
    return (normalize_se_rule_id(_resolved)
            or _known_canonical_form(_resolved))
_PRIORITY_ORDER: dict[str, int] = {
    "syntax_error": 0,
    "import_error": 1,
    "dead_code": 2,
    "unused_import": 2,
    RULE_BROAD_EXCEPTION: 3,
    RULE_HIGH_COMPLEXITY: 4,
    "naming_convention": 5,
    RULE_MISSING_DOCSTRING: 6,
    "type_hint": 6,
}
_MUTEX_PAIRS: list[tuple[str, str]] = [
    ("dead_code", RULE_HIGH_COMPLEXITY),
    ("dead_code", "naming_convention"),
    ("unused_import", "import_error"),
]
_PRIORITY_ALIASES: dict[str, tuple[str, ...]] = {
    "syntax_error": ("syntax_error",),
    "import_error": ("import_error", "broken_import"),
    "dead_code": ("dead_code", "dead_func", "dead_class", "dead_method",
                  "dead_var", "dead_branch", "quadrant_dead"),
    "unused_import": ("unused_import",),
    "naming_convention": ("naming_convention", "naming_violation"),
    "type_hint": ("type_hint",),
    RULE_BROAD_EXCEPTION: ("broad_exception", "exception_handling"),
    RULE_HIGH_COMPLEXITY: ("high_complexity", "complexity"),
}
def _build_canonical_category_index() -> dict[str, str]:
    index: dict[str, str] = {}
    for category in _PRIORITY_ALIASES:
        canonical = resolve_rule_alias(category)
        if canonical and canonical != category:
            index[_normalize_rule_for_match(canonical)] = category
    return index
_CANONICAL_CATEGORY: dict[str, str] = _build_canonical_category_index()
def _resolve_prefixed_category(rid: str) -> str:
    prefix, _, suffix = rid.partition("_")
    if not prefix or not suffix.isdigit():
        return ""
    return RULE_ID_PREFIX_CATEGORY.get(prefix.upper(), "")
_PRIORITY_FAMILY_CATEGORIES: dict[str, str] = {
    "dead_code": "dead_code",
    "complexity": RULE_HIGH_COMPLEXITY,
    "high_complexity": RULE_HIGH_COMPLEXITY,
    "broad_except": RULE_BROAD_EXCEPTION,
    "broad_exception": RULE_BROAD_EXCEPTION,
    "exception_handling": RULE_BROAD_EXCEPTION,
}
_PRIORITY_FAMILY_SETS: tuple[str, ...] = (
    "dead_code", "complexity", "broad_except")
_PRIORITY_FAMILY_INDEX: dict[str, str] | None = None
def _priority_family_index() -> dict[str, str]:
    global _PRIORITY_FAMILY_INDEX
    if _PRIORITY_FAMILY_INDEX is None:
        index: dict[str, str] = {}
        for rule_key, family in RULE_FAMILY_MAP.items():
            category = _PRIORITY_FAMILY_CATEGORIES.get(family)
            if category:
                index.setdefault(
                    _normalize_rule_for_match(rule_key), category)
        for family in _PRIORITY_FAMILY_SETS:
            category = _PRIORITY_FAMILY_CATEGORIES[family]
            for member in RULE_FAMILY_SETS.get(family, ()):
                index.setdefault(_normalize_rule_for_match(member), category)
        _PRIORITY_FAMILY_INDEX = index
    return _PRIORITY_FAMILY_INDEX
def _rule_semantic_id(rule_id: str) -> str:
    rid = _normalize_rule_for_match(resolve_rule_alias(rule_id))
    if not rid:
        return ""
    category = (_CANONICAL_CATEGORY.get(rid)
                or _resolve_prefixed_category(rid))
    return category or _priority_family_index().get(rid) or rid
def _alias_keys(key: str) -> set:
    return {key, *_PRIORITY_ALIASES.get(key, ())}
_PRIORITY_MATCH_ITEMS = tuple(
    (prio, _alias_keys(key)) for key, prio in _PRIORITY_ORDER.items())
_MUTEX_KEY_PAIRS = tuple(
    (_alias_keys(a), _alias_keys(b)) for a, b in _MUTEX_PAIRS)
def _both_hit(rid_a: str, keys_a: set, rid_b: str, keys_b: set) -> bool:
    return rid_a in keys_a and rid_b in keys_b
@lru_cache(maxsize=4096)
def _rule_fix_priority_cached(rule_id: str) -> int:
    rid = _rule_semantic_id(rule_id)
    if not rid:
        return 99
    for prio, keys in _PRIORITY_MATCH_ITEMS:
        if rid in keys:
            return prio
    return 99
def rule_fix_priority(rule_id) -> int:
    return _rule_fix_priority_cached(
        rule_id if isinstance(rule_id, str) else "")
@lru_cache(maxsize=65536)
def _rules_are_mutex_cached(rule_a: str, rule_b: str) -> bool:
    ra = _rule_semantic_id(rule_a)
    rb = _rule_semantic_id(rule_b)
    if not ra or not rb:
        return False
    for a_keys, b_keys in _MUTEX_KEY_PAIRS:
        if _both_hit(ra, a_keys, rb, b_keys) or _both_hit(rb, a_keys, ra, b_keys):
            return True
    return False
def rules_are_mutex(rule_a, rule_b) -> bool:
    return _rules_are_mutex_cached(
        rule_a if isinstance(rule_a, str) else "",
        rule_b if isinstance(rule_b, str) else "")
def clear_rule_match_caches() -> int:
    global _KNOWN_CANONICAL_CACHE, _PRIORITY_FAMILY_INDEX
    global _RULE_FAMILY_CANON, _FAMILY_OWNER_INDEX
    _n = (_rule_fix_priority_cached.cache_info().currsize
          + _rules_are_mutex_cached.cache_info().currsize
          + _normalize_rule_for_match_cached.cache_info().currsize
          + _normalized_rule_identity.cache_info().currsize
          + len(_KNOWN_CANONICAL_CACHE or {})
          + len(_PRIORITY_FAMILY_INDEX or {})
          + len(_RULE_FAMILY_CANON)
          + len(_FAMILY_OWNER_INDEX or {}))
    _rule_fix_priority_cached.cache_clear()
    _rules_are_mutex_cached.cache_clear()
    _normalize_rule_for_match_cached.cache_clear()
    _normalized_rule_identity.cache_clear()
    _KNOWN_CANONICAL_CACHE = None
    _PRIORITY_FAMILY_INDEX = None
    _RULE_FAMILY_CANON = _build_rule_family_canon()
    _FAMILY_OWNER_INDEX = None
    return _n or 0
class DependencyType(str, Enum):
    MUST_BEFORE = "must_before"
    MUTUALLY_EXCLUSIVE = "exclusive"
    SAME_REGION = "same_region"
    PARENT_CHILD = "parent_child"
@dataclass
class DependencyEdge:
    source: str
    target: str
    dep_type: DependencyType
    reason: str = ""
    confidence: float = 1.0
@dataclass
class ConflictReport:
    finding_a: str
    finding_b: str
    conflict_type: DependencyType
    reason: str
    severity: str = "warning"
    recommendation: str = ""
class DependencyGraph:
    def __init__(self):
        self._nodes: set[str] = set()
        self._edges: list[DependencyEdge] = []
        self._adjacency: dict[str, list[DependencyEdge]] = defaultdict(list)
        self._reverse_adjacency: dict[str, list[DependencyEdge]] = defaultdict(list)
        self._regions: dict[str, CodeRegion] = {}
    def add_node(self, node_id: str, region: CodeRegion | None = None) -> None:
        self._nodes.add(node_id)
        if region:
            self._regions[node_id] = region
    def add_edge(self, edge: DependencyEdge) -> None:
        self._edges.append(edge)
        self._adjacency[edge.source].append(edge)
        self._reverse_adjacency[edge.target].append(edge)
        self._nodes.add(edge.source)
        self._nodes.add(edge.target)
    @property
    def nodes(self) -> set[str]:
        return set(self._nodes)
    @property
    def edges(self) -> list[DependencyEdge]:
        return list(self._edges)
    def get_region(self, node_id: str) -> CodeRegion | None:
        return self._regions.get(node_id)
    def get_dependencies(self, node_id: str) -> list[DependencyEdge]:
        return list(self._reverse_adjacency.get(node_id, []))
    def get_dependents(self, node_id: str) -> list[DependencyEdge]:
        return list(self._adjacency.get(node_id, []))
    def get_must_before(self, node_id: str) -> list[str]:
        return [edge.source
                for edge in self._reverse_adjacency.get(node_id, [])
                if edge.dep_type == DependencyType.MUST_BEFORE]
    def get_conflicts(self, node_id: str) -> list[str]:
        result = []
        for edge in self._adjacency.get(node_id, []):
            if (edge.dep_type == DependencyType.MUTUALLY_EXCLUSIVE
                    and edge.target not in result):
                result.append(edge.target)
        for edge in self._reverse_adjacency.get(node_id, []):
            if (edge.dep_type == DependencyType.MUTUALLY_EXCLUSIVE
                    and edge.source not in result):
                result.append(edge.source)
        return result
    @staticmethod
    def _reaches_self_within(node: str, residual: set[str],
                            adj: dict[str, list[str]]) -> bool:
        stack = [succ for succ in adj.get(node, []) if succ in residual]
        seen = set(stack)
        while stack:
            cur = stack.pop()
            if cur == node:
                return True
            unseen = (set(adj.get(cur, [])) & residual) - seen
            seen.update(unseen)
            stack.extend(unseen)
        return False
    def _must_before_index(self) -> tuple[dict[str, int], dict[str, list[str]]]:
        in_degree: dict[str, int] = dict.fromkeys(self.nodes, 0)
        adj: dict[str, list[str]] = defaultdict(list)
        for edge in self.edges:
            if edge.dep_type == DependencyType.MUST_BEFORE:
                adj[edge.source].append(edge.target)
                in_degree[edge.target] += 1
        return in_degree, adj
    @staticmethod
    def _kahn_order(nodes, in_degree: dict[str, int],
                    adj: dict[str, list[str]]) -> list[str]:
        queue = deque(sorted(n for n in nodes if in_degree[n] == 0))
        ordered: list[str] = []
        while queue:
            node = queue.popleft()
            ordered.append(node)
            for neighbor in adj.get(node, []):
                in_degree[neighbor] -= 1
                if in_degree[neighbor] == 0:
                    queue.append(neighbor)
        return ordered
    def topological_sort(self) -> tuple[list[str], list[str]]:
        nodes = self.nodes
        in_degree, adj = self._must_before_index()
        sorted_nodes = self._kahn_order(nodes, in_degree, adj)
        residual = {n for n in nodes if in_degree[n] > 0}
        cyclic_nodes = sorted(
            n for n in residual if self._reaches_self_within(n, residual, adj)
        )
        return sorted_nodes, cyclic_nodes
    def _has_mutex_edge(self, a: str, b: str) -> bool:
        return b in self.get_conflicts(a)
    def _pending_nodes(self, sorted_nodes: list[str]) -> list[str]:
        completed = set(sorted_nodes)
        return list(dict.fromkeys(
            list(sorted_nodes)
            + sorted(n for n in self.nodes if n not in completed)
        ))
    def _next_batch(self, remaining: list[str], processed: set[str]) -> list[str]:
        batch: list[str] = []
        for node in remaining:
            prereqs = self.get_must_before(node)
            if not all(p in processed for p in prereqs):
                continue
            if any(self._has_mutex_edge(node, other) for other in batch):
                continue
            batch.append(node)
        return batch
    def get_execution_groups(self) -> list[list[str]]:
        sorted_nodes, cyclic = self.topological_sort()
        if cyclic:
            _log.warning(
                "[DepGraph] 检测到环路，环上及被阻塞节点经批次兜底覆盖: %s", cyclic)
        groups: list[list[str]] = []
        processed: set[str] = set()
        remaining = self._pending_nodes(sorted_nodes)
        while remaining:
            batch = self._next_batch(remaining, processed)
            if not batch:
                batch = [remaining[0]]
            processed.update(batch)
            groups.append(batch)
            remaining = [n for n in remaining if n not in processed]
        return groups
    def has_cycle(self) -> bool:
        _, cyclic = self.topological_sort()
        return len(cyclic) > 0
    def node_count(self) -> int:
        return len(self._nodes)
    def edge_count(self) -> int:
        return len(self._edges)
def _is_sentinel_region(r: CodeRegion) -> bool:
    return not r.file or r.start_line <= 0
def _same_region_file(left: str, right: str) -> bool:
    left_key = finding_file_key(left)
    right_key = finding_file_key(right)
    return bool(left_key) and left_key == right_key
def _regions_overlap(a: CodeRegion, b: CodeRegion) -> bool:
    if not _same_region_file(a.file, b.file):
        return False
    if _is_sentinel_region(a) or _is_sentinel_region(b):
        return False
    return not (a.end_line < b.start_line or b.end_line < a.start_line)
def _region_contains(parent: CodeRegion, child: CodeRegion) -> bool:
    if not _same_region_file(parent.file, child.file):
        return False
    if _is_sentinel_region(parent) or _is_sentinel_region(child):
        return False
    return (parent.start_line <= child.start_line
            and parent.end_line >= child.end_line)
_SEED_LINE_WINDOW = 30
_LOCATOR_TAIL_RE = _re.compile(
    r"^(?P<file>.+):(?P<line>\d+):(?P<rule>.*)$")
def _locator_coords(locator) -> tuple[str, int]:
    loc = str(locator or "")
    match = _LOCATOR_TAIL_RE.match(loc)
    if match is None:
        return "", 0
    file_part = match.group("file")
    try:
        line_no = int(match.group("line"))
    except ValueError:
        _log.warning("[Locator] 行号不可解析(%d 位数字)，按无坐标降级",
                     len(match.group("line")))
        return "", 0
    return (file_part, line_no) if file_part else ("", 0)
def _add_priority_order_edges(
    graph: DependencyGraph,
    a_id: str,
    a_rule: str,
    b_id: str,
    b_rule: str,
    reason_fmt: str,
    confidence: float,
) -> None:
    prio_a = rule_fix_priority(a_rule)
    prio_b = rule_fix_priority(b_rule)
    if prio_a < prio_b:
        graph.add_edge(DependencyEdge(
            source=a_id, target=b_id,
            dep_type=DependencyType.MUST_BEFORE,
            reason=reason_fmt.format(
                first=a_rule, first_prio=prio_a,
                second=b_rule, second_prio=prio_b),
            confidence=confidence,
        ))
    elif prio_b < prio_a:
        graph.add_edge(DependencyEdge(
            source=b_id, target=a_id,
            dep_type=DependencyType.MUST_BEFORE,
            reason=reason_fmt.format(
                first=b_rule, first_prio=prio_b,
                second=a_rule, second_prio=prio_a),
            confidence=confidence,
        ))
def _add_parent_child_edges(
    graph: DependencyGraph,
    parent_id: str,
    parent_region: CodeRegion,
    parent_rule: str,
    child_id: str,
    child_rule: str,
) -> None:
    graph.add_edge(DependencyEdge(
        source=parent_id, target=child_id,
        dep_type=DependencyType.PARENT_CHILD,
        reason=f"{parent_region.node_type} {parent_region.node_name} 包含 {child_id} 所在区域",
        confidence=0.9,
    ))
    _add_priority_order_edges(
        graph, parent_id, parent_rule, child_id, child_rule,
        "{first} (优先级 {first_prio}) 应在 {second} (优先级 {second_prio}) 之前修复",
        0.7,
    )
def _prepare_finding_ids(findings: list[dict]) -> list[str]:
    seen_ids: set[str] = set()
    fid_list: list[str] = []
    for i, f in enumerate(findings):
        if not isinstance(f, dict):
            _log.warning("[DepGraph] findings[%d] 非 dict，跳过: %r", i, f)
            fid_list.append("")
            continue
        raw_id = f.get("id")
        fid = str(raw_id).strip() if raw_id not in (None, "") else ""
        if not fid:
            fid = f"finding_{i}"
        if fid in seen_ids:
            base, _suffix = fid, i
            fid = f"{base}#{_suffix}"
            while fid in seen_ids:
                _suffix += 1
                fid = f"{base}#{_suffix}"
        seen_ids.add(fid)
        fid_list.append(fid)
    return fid_list
_FINDING_FILE_KEYS = ("file_path", "file", "path", "filepath")
_FINDING_LINE_KEYS = ("line", "lineno", "start_line")
_FINDING_RULE_KEYS = ("rule_id", "rule_applied", "type", "check_id")
_FINDING_SNIPPET_KEYS = ("code_snippet", "snippet", "code")
def _finding_first(f: dict, keys: tuple[str, ...], default=""):
    for key in keys:
        value = f.get(key)
        if value:
            return value
    return default
def _finding_text(f: dict, keys: tuple[str, ...], *,
                  family: bool = False) -> str:
    for key in keys:
        value = f.get(key)
        if not isinstance(value, str):
            continue
        usable = _family_text(value) if family else value.strip()
        if usable:
            return usable if family else value
    return ''
_LINE_CLEAN_SENTINELS = (None, 0, 0.0, '', '0')
def _line_value_unusable(value) -> bool:
    if value in _LINE_CLEAN_SENTINELS:
        return False
    return str(value).strip() not in ('', '0')
def _finding_coords(f: dict, idx: int | None = None, *,
                    skill_dir: str = _DEFAULT_SKILL_DIR) -> tuple[str, int]:
    filepath = _finding_text(f, _FINDING_FILE_KEYS)
    raw_line = _finding_first(f, _FINDING_LINE_KEYS, 0)
    line = coerce_line(raw_line)
    if line <= 0:
        line = next((candidate for candidate in (
            coerce_line(f.get(key)) for key in _FINDING_LINE_KEYS)
            if candidate > 0), 0)
    if idx is not None and line == 0 and _line_value_unusable(raw_line):
        _log.warning('[FindingCoords] findings[%d] line 字段不可用(%r)，降级为 0',
                     idx, raw_line)
    if filepath and line > 0:
        return filepath, line
    loc_file, loc_line = _locator_coords(f.get("locator"))
    if not filepath:
        return loc_file, line if line > 0 else loc_line
    if (line <= 0 and loc_line > 0
            and same_file(loc_file, filepath, skill_dir)):
        line = loc_line
    return filepath, line
def _finding_rule_id(f: dict) -> str:
    rule_id = _finding_text(f, _FINDING_RULE_KEYS, family=True)
    if rule_id:
        return rule_id
    match = _LOCATOR_TAIL_RE.match(
        str_or(dict_or_empty(f).get('locator')))
    return _family_text(match.group('rule')) if match is not None else ''
def _build_graph_nodes(
    graph: DependencyGraph,
    findings: list[dict],
    fid_list: list[str],
    skill_dir: str,
) -> None:
    source_cache: dict[str, Any] = {}
    for i, f in enumerate(findings):
        fid = fid_list[i]
        if not fid:
            continue
        filepath, line = _finding_coords(f, i, skill_dir=skill_dir)
        full_path = (os.path.join(skill_dir, filepath)
                     if skill_dir and filepath else filepath)
        region = compute_code_region(
            full_path if filepath else "", line, source_cache=source_cache)
        graph.add_node(fid, region)
def _build_graph_edges(
    graph: DependencyGraph,
    findings: list[dict],
    fid_list: list[str],
) -> None:
    for i, fa_id in enumerate(fid_list):
        if not fa_id:
            continue
        fa_region = graph.get_region(fa_id)
        if fa_region is None:
            continue
        fa_rule = _finding_rule_id(findings[i])
        for j in range(i + 1, len(fid_list)):
            fb_id = fid_list[j]
            if not fb_id:
                continue
            fb_region = graph.get_region(fb_id)
            if fb_region is None:
                continue
            fb_rule = _finding_rule_id(findings[j])
            _add_pair_relation(graph, fa_id, fa_region, fa_rule,
                               fb_id, fb_region, fb_rule)
def _add_same_region_edges(
    graph: DependencyGraph,
    fa_id: str, fa_region: CodeRegion, fa_rule: str,
    fb_id: str, fb_rule: str,
) -> None:
    graph.add_edge(DependencyEdge(
        source=fa_id, target=fb_id,
        dep_type=DependencyType.SAME_REGION,
        reason=f"两个问题影响相同代码区域 ({fa_region.node_type} {fa_region.node_name} L{fa_region.start_line}-{fa_region.end_line})",
        confidence=0.9,
    ))
    _add_priority_order_edges(
        graph, fa_id, fa_rule, fb_id, fb_rule,
        "同区域内 {first} 应先于 {second} 修复",
        0.6,
    )
def _add_pair_relation(
    graph: DependencyGraph,
    fa_id: str, fa_region: CodeRegion, fa_rule: str,
    fb_id: str, fb_region: CodeRegion, fb_rule: str,
) -> None:
    if not _same_region_file(fa_region.file, fb_region.file):
        return
    a_contains_b = _region_contains(fa_region, fb_region)
    b_contains_a = _region_contains(fb_region, fa_region)
    overlaps = _regions_overlap(fa_region, fb_region)
    if not (overlaps or a_contains_b or b_contains_a):
        return
    if rules_are_mutex(fa_rule, fb_rule):
        graph.add_edge(DependencyEdge(
            source=fa_id, target=fb_id,
            dep_type=DependencyType.MUTUALLY_EXCLUSIVE,
            reason=f"规则 {fa_rule} 与 {fb_rule} 互斥",
            confidence=0.8,
        ))
        return
    if a_contains_b == b_contains_a:
        if overlaps:
            _add_same_region_edges(
                graph, fa_id, fa_region, fa_rule, fb_id, fb_rule)
    elif a_contains_b:
        _add_parent_child_edges(graph, fa_id, fa_region, fa_rule, fb_id, fb_rule)
    else:
        _add_parent_child_edges(graph, fb_id, fb_region, fb_rule, fa_id, fa_rule)
def build_dependency_graph(
    findings: list[dict],
    skill_dir: str = _DEFAULT_SKILL_DIR,
) -> DependencyGraph:
    skill_dir = normalize_target_path(skill_dir)
    if not isinstance(findings, (list, tuple)):
        if findings is not None:
            _log.warning("[DepGraph] findings 非列表(%s)，按空输入处理",
                           type(findings).__name__)
        findings = []
    else:
        findings = list(findings)
    graph = DependencyGraph()
    fid_list = _prepare_finding_ids(findings)
    _build_graph_nodes(graph, findings, fid_list, skill_dir)
    _build_graph_edges(graph, findings, fid_list)
    _log.info("[DepGraph] 构建完成: %d 节点, %d 边",
                graph.node_count(), graph.edge_count())
    return graph
def analyze_conflicts(graph: DependencyGraph) -> list[ConflictReport]:
    conflicts: list[ConflictReport] = []
    for edge in graph.edges:
        if edge.dep_type == DependencyType.MUTUALLY_EXCLUSIVE:
            conflicts.append(ConflictReport(
                finding_a=edge.source,
                finding_b=edge.target,
                conflict_type=DependencyType.MUTUALLY_EXCLUSIVE,
                reason=edge.reason,
                severity="error",
                recommendation="仅修复其中一个，或分两轮处理",
            ))
        elif edge.dep_type == DependencyType.SAME_REGION:
            conflicts.append(ConflictReport(
                finding_a=edge.source,
                finding_b=edge.target,
                conflict_type=DependencyType.SAME_REGION,
                reason=edge.reason,
                severity="warning",
                recommendation="按拓扑顺序依次修复，修复后重新诊断",
            ))
    return conflicts
def get_fix_order(graph: DependencyGraph) -> dict:
    ordered, cyclic = graph.topological_sort()
    groups = graph.get_execution_groups()
    conflicts = analyze_conflicts(graph)
    conflict_dicts = [
        {
            "finding_a": c.finding_a,
            "finding_b": c.finding_b,
            "type": c.conflict_type.value,
            "reason": c.reason,
            "severity": c.severity,
            "recommendation": c.recommendation,
        }
        for c in conflicts
    ]
    return {
        "ordered": ordered,
        "groups": groups,
        "conflicts": conflict_dicts,
        "has_cycle": len(cyclic) > 0,
        "cyclic_nodes": cyclic,
        "total_nodes": graph.node_count(),
        "total_edges": graph.edge_count(),
    }
def get_fix_order_for_findings(
    findings: list[dict],
    skill_dir: str = _DEFAULT_SKILL_DIR,
) -> dict:
    graph = build_dependency_graph(findings, skill_dir)
    return get_fix_order(graph)
_GENERIC_GUIDANCE = "建议手动检查并修正相关代码"
def _rule_family(rule_id: str) -> str:
    if not isinstance(rule_id, str) or not rule_id:
        return ""
    rule_id = canonical_rule_id(rule_id)
    if "-" in rule_id:
        return rule_id.split("-")[0].upper()
    if rule_id in _corpus.RULE_FAMILY_GUIDANCE:
        return rule_id
    _upper = rule_id.upper()
    if _upper in _corpus.RULE_FAMILY_GUIDANCE:
        return _upper
    return rule_id[:2]
def _base_fix_guidance(rule_id: str) -> str:
    guidance = _corpus.RULE_FIX_KNOWLEDGE.get(rule_id, "")
    if not guidance:
        guidance = get_se_fix_suggestion(rule_id)
    if not guidance:
        guidance = _corpus.RULE_FAMILY_GUIDANCE.get(_rule_family(rule_id),
                                            _GENERIC_GUIDANCE)
    return guidance
_BANDIT_ID_PATTERN = _re.compile(
    r"(?<![A-Za-z0-9_])(B[0-9]{3})(?![A-Za-z0-9_])")
def extract_bandit_id(message: str) -> str:
    if not isinstance(message, str):
        return ""
    m = _BANDIT_ID_PATTERN.search(message)
    return m.group(1) if m else ""
def get_bandit_fix_suggestion(test_id: str) -> str:
    if not isinstance(test_id, str):
        return ""
    return _corpus.BANDIT_FIX_SUGGESTIONS.get(test_id.strip().upper(), "")
def _ruff_rule_code(rule_id: str) -> str:
    if not isinstance(rule_id, str):
        return ""
    text = rule_id.strip()
    if not text.upper().startswith("RUFF-"):
        return ""
    return text.split("-", 1)[1].strip().upper()
def _delegation_message(code: str) -> str:
    safe = _corpus.RUFF_DELEGATION_KNOWLEDGE[
        _corpus.RUFF_DELEGATION_SAFE_KEY]
    unsafe = _corpus.RUFF_DELEGATION_KNOWLEDGE[
        _corpus.RUFF_DELEGATION_UNSAFE_KEY]
    if code in safe:
        return (f"该规则历史验证为等价机械转换，可委托 ruff --fix "
                f"--select {code} --no-cache 执行（{safe[code]}）")  # jwsgj:suppress SE-37 — --select 后为 ruff 目标代码，非 SQL 注释
    if code in unsafe:
        return f"勿机械替换：{unsafe[code]}"
    return "该规则历史归为需人工审查类，不建议直接委托 ruff --fix"
def get_ruff_delegation_hint(rule_id: str) -> str:
    code = _ruff_rule_code(rule_id)
    if not code:
        return ""
    return _delegation_message(code)
_SECURITY_RULE_PREFIXES = frozenset(
    prefix for prefix, category in RULE_ID_PREFIX_CATEGORY.items()
    if category == "security")
def _is_security_rule_id(rule_id: str) -> bool:
    upper = rule_id.upper()
    if upper.startswith("BANDIT-"):
        return True
    return _re.split(r"[-_]", upper, maxsplit=1)[0] in _SECURITY_RULE_PREFIXES
def _with_bandit_hint(guidance: str, rule_id: str, message: str) -> str:
    direct_bandit_id = extract_bandit_id(rule_id.upper())
    if not direct_bandit_id and not _is_security_rule_id(rule_id):
        return guidance
    bandit_id = direct_bandit_id or extract_bandit_id(str(message))
    if not bandit_id:
        return guidance
    bandit_hint = get_bandit_fix_suggestion(bandit_id)
    if not bandit_hint:
        return guidance
    hint = f"bandit {bandit_id} 修复建议: {bandit_hint}"
    return _merge_guidance_hint(guidance, hint)
def _with_ruff_hint(guidance: str, rule_id: str) -> str:
    ruff_hint = get_ruff_delegation_hint(rule_id)
    if not ruff_hint:
        return guidance
    return _merge_guidance_hint(guidance, ruff_hint)
def _merge_guidance_hint(guidance: str, hint: str) -> str:
    if hint in guidance:
        return guidance
    if guidance in hint:
        return hint
    return f"{guidance}；{hint}"
def _with_context_line(guidance: str, context_line: str) -> str:
    if not context_line:
        return guidance
    return f"{guidance}；相关代码: {str(context_line)[:80]}"
def get_fix_guidance(rule_id: str, message: str = "", context_line: str = "") -> str:
    rule_id = canonical_rule_id(rule_id)
    guidance = _base_fix_guidance(rule_id)
    guidance = _with_bandit_hint(guidance, rule_id, message)
    guidance = _with_ruff_hint(guidance, rule_id)
    return _with_context_line(guidance, context_line)
def finding_family(ff: dict, *, rule_id_first: bool = _DEFAULT_RULE_ID_FIRST) -> str:
    ff = norm_dict(ff)
    primary, secondary = (("rule_id", "rule_family") if rule_id_first
                         else ("rule_family", "rule_id"))
    return _finding_text(ff, (primary, secondary), family=True)
def _family_hit(ff: dict, rule_id_first: bool,
                normalize: bool, families) -> bool:
    rf = finding_family(ff, rule_id_first=rule_id_first)
    if not rf:
        return False
    if normalize:
        rf = normalize_rule(rf)
    return rf in families
def match_rule_families(sources: Any, data: Any, gate: Any, families: Any, *, normalize: Any=False, rule_id_first: Any=_DEFAULT_RULE_ID_FIRST, log_name: Any='match_rule_families') -> Any:
    try:
        src = {source for source in as_sequence(sources)
               if isinstance(source, str)}
        if not gate(src):
            return False
        return any(
            _family_hit(ff, rule_id_first, normalize, families)
            for ff in findings_container(data) if isinstance(ff, dict))
    except Exception as e:  # noqa: BLE001
        _log.warning("%s: %s", log_name, e)
        return False
def make_locator_from_finding(f: dict) -> str:
    try:
        _finding = dict_or_empty(f)
        filepath, line = _finding_coords(_finding)
        rule_family = _family_text(_finding_first(_finding, ("rule_family",)))
        if not rule_family:
            rule_id = _family_text(_finding_rule_id(_finding))
            rule_family = normalize_rule(rule_id) if rule_id else ""
        return make_locator(filepath, line, rule_family)
    except Exception as e:  # noqa: BLE001 -- 病态 finding 不得击穿定位器调用链
        _log.warning("make_locator_from_finding: %s", e, exc_info=True)
        return "unknown:0:unknown"
KNOWN_HIGH_FP_FAMILIES: frozenset = frozenset({
    "code_smell", "none_comparison", "shadowing_builtin",
    "missing_docstring", "todo_marker",
})
FILE_LEVEL_FAMILIES = frozenset({
    "god_file", "high_complexity", "high_coupling",
    "architecture", "large_codebase", "empty_project",
    "low_coverage", "health_score", "quality_score",
    "gate_issue", "gate_failed", "dead_code",
    "method_anomaly", "method_pass",
})
def _build_rule_family_canon() -> dict[str, str]:
    canon: dict[str, str] = {}
    for rule_key, fam_value in RULE_FAMILY_MAP.items():
        canon.setdefault(canonical_rule_key(rule_key), fam_value)
    for fam_value in RULE_FAMILY_MAP.values():
        canon.setdefault(canonical_rule_key(fam_value), fam_value)
    for group_name, group_members in RULE_FAMILY_SETS.items():
        canon.setdefault(canonical_rule_key(group_name), group_name)
        for member in group_members:
            canon.setdefault(canonical_rule_key(member), member)
    for alias, target in RULE_ID_ALIASES.items():
        if not isinstance(target, str) or not target:
            continue
        family = (RULE_FAMILY_MAP.get(alias)
                  or canon.get(canonical_rule_key(alias)))
        if family:
            canon.setdefault(canonical_rule_key(target), family)
    return canon
def _mapped_family(candidate: str) -> str | None:
    mapped = RULE_FAMILY_MAP.get(candidate)
    if mapped is not None:
        return mapped
    canon = _RULE_FAMILY_CANON.get(canonical_rule_key(candidate))
    if canon is not None:
        return canon
    bridged = normalize_se_rule_id(candidate)
    if bridged and bridged != candidate:
        bridged_family = (RULE_FAMILY_MAP.get(bridged)
                          or _RULE_FAMILY_CANON.get(
                              canonical_rule_key(bridged)))
        if bridged_family is not None:
            return bridged_family
    resolved = resolve_rule_alias(candidate)
    if resolved and resolved != candidate:
        return (RULE_FAMILY_MAP.get(resolved)
                or _RULE_FAMILY_CANON.get(canonical_rule_key(resolved))
                or resolved)
    return None
@lru_cache(maxsize=8192)
def _normalized_rule_identity(normalized: str) -> str:
    family = _mapped_family(normalized)
    if family is not None:
        return family
    return resolve_rule_alias(normalized) or normalized
def normalize_rule(rule_id: str) -> str:
    try:
        if not rule_id:
            return "unknown"
        normalized = str(rule_id).strip()
        if not normalized:
            return "unknown"
        return _normalized_rule_identity(normalized)
    except Exception as e:  # noqa: BLE001 -- 非受信规则标识归一失败必须安全回退
        _log.warning("normalize_rule: %s", e, exc_info=True)
        return "unknown"
RULE_FAMILY_SETS: dict[str, frozenset[str]] = {
    "dead_code": frozenset({
        "dead_code", "DC-01", "DC-03",
        "unreachable_code", "unused_definition",
        "orphan_module", "orphan_function",
        "dead_function", "orphaned", "unused",
        "unreachable",
    }),
    "security": frozenset({
        "sql_injection", "path_traversal", "hardcoded_credential",
        "danger_pattern", "security", "SE-06", "SE-20",
        "unsafe_eval", "command_injection",
        "xxe", "ssrf", "csrf", "weak_crypto", "insecure_random",
        "injection", "xss", "hardcoded_secret", "PT-01",
        "insecure_deserialization",
        "SEC-01", "SEC-02", "SEC-03", "SEC-04", "SEC-05", "SEC-06",
        "SEC-GEN",
    }),
    "complexity": frozenset({
        "high_complexity", "SZ-02", "long_function",
        "deep_nesting", "nested_loop", "too_many_params",
        "high_rfc", "C2",
    }),
    "broad_except": frozenset({
        "broad_except", "bare_except", "empty_except", "silent_swallow",
    }),
    "circular_dep": frozenset({
        "circular_dep", "circular_dependency",
        "cycle", "import_cycle", "CP-01",
    }),
    "mutable_global": frozenset({
        "mutable_global", "global_statement", "shared_mutable_state",
        "excessive_global_state",
    }),
    "mutable_default": frozenset({
        "mutable_default", "RB-01",
    }),
    "trivial_delegation": frozenset({
        "trivial_delegation", "PF01", "O04", "D50", "D51",
        "C19_passthrough_layer", "AP-C19",
        "thin_wrapper", "pure_forward", "facade_reexport",
    }),
    "recursion": frozenset({
        "unbounded_recursion", "deep_recursion", "excessive_recursion",
        "recursion", "infinite_loop",
    }),
    "broken_call": frozenset({
        "broken_call", "orphan_call", "missing_import",
    }),
    "god_file": frozenset({
        "god_file", "GF-07", "high_complexity", "large_file", "large_codebase",
        "architecture", "god_module",
    }),
    "test_quality": frozenset({
        "test_quality",
        "test_failure", "test_error", "test_smell", "method_anomaly",
        "undertested", "quadrant_dead", "dead_code",
    }),
    "perf_hotspot": frozenset({
        "perf_hotspot", "infinite_loop",
    }),
    "resource_leak": frozenset({
        "resource_leak", "memory_leak", "file_leak", "connection_leak",
    }),
    "api_compat": frozenset({
        "compatibility", "api_change", "api_issue", "breaking_change",
    }),
    "maintainability": frozenset({
        "high_coupling", "low_quality_score", "low_health_score",
        "quality_score", "health_score",
        "deep_nesting", "god_file", "high_complexity",
    }),
    "config_security": frozenset({
        "config_drift", "insecure_config", "missing_config", "config_error",
    }),
    "regression": frozenset({
        "regression", "baseline_degradation", "degraded",
        "score_regression", "blindspot_increase",
    }),
    "fix_related": frozenset({
        "fix_safety", "fix_gate", "auto_fix", "repair",
    }),
    "doc_consistency": frozenset({
        "doc_consistency", "doc_orphan", "DOC-ORPHAN",
        "all_ghost", "DOC-ALL-GHOST",
    }),
    "hallucination": frozenset({
        "hallucination", "hallucinated_api", "hallucinated_import",
        "hallucinated_exception", "context_contradiction",
        "ai_slop", "test_illusion", "memory_hallucination",
        "sandbox_reflection", "hallucination_general",
    }),
    "concurrency": frozenset({
        "race_condition", "deadlock", "thread_unsafe",
        "liveness_probe", "concurrency_bug",
    }),
    "unused_symbols": frozenset({
        "unused_import", "unused_definition", "unused_variable",
        "unused_parameter", "unused_assignment",
    }),
    "syntax_runtime": frozenset({
        "syntax_error", "import_error", "name_error",
        "type_error", "attribute_error",
    }),
    "security_extended": frozenset({
        "dependency_vulnerability", "open_redirect",
        "sensitive_data_exposure", "insecure_deserialization",
        "handle_leak",
    }),
}
_RULE_FAMILY_CANON = _build_rule_family_canon()
_FAMILY_OWNER_INDEX: dict[str, str] | None = None
def _build_family_owner_index() -> dict[str, str]:
    known: set[str] = set()
    for _key in RULE_FAMILY_MAP:
        known.add(canonical_rule_key(_key))
    for _value in RULE_FAMILY_MAP.values():
        known.add(canonical_rule_key(_value))
    for _group in RULE_FAMILY_SETS:
        known.add(canonical_rule_key(_group))
    index: dict[str, str] = {}
    for group_name, members in RULE_FAMILY_SETS.items():
        for member in members:
            key = canonical_rule_key(member)
            if key in known:
                continue
            index.setdefault(key, group_name)
    return index
def _family_owner_index() -> dict[str, str]:
    global _FAMILY_OWNER_INDEX
    if _FAMILY_OWNER_INDEX is None:
        _FAMILY_OWNER_INDEX = _build_family_owner_index()
    return _FAMILY_OWNER_INDEX
def _family_members(family_name: object) -> frozenset[str] | None:
    if not isinstance(family_name, str) or not family_name:
        return None
    direct = RULE_FAMILY_SETS.get(family_name)
    if direct is not None:
        return direct | {family_name}
    canonical = _RULE_FAMILY_CANON.get(canonical_rule_key(family_name))
    if canonical and canonical in RULE_FAMILY_SETS:
        return RULE_FAMILY_SETS[canonical] | {canonical}
    owner = _family_owner_index().get(canonical_rule_key(family_name))
    if owner:
        return RULE_FAMILY_SETS[owner] | {owner}
    return None
def get_rule_family_set(family_name: str) -> frozenset[str]:
    family_set = _family_members(family_name)
    return family_set if family_set is not None else frozenset()
CONFLICT_DEAD_CODE_FAMILIES = frozenset(
    get_rule_family_set("dead_code")
    | get_rule_family_set("unused_symbols")
    | {"quadrant_dead", "low_coverage", "quadrant_undertested", "DC-02"})
CONFLICT_COMPLEXITY_FAMILIES = frozenset(
    get_rule_family_set("complexity") | {"SZ-01"})
CONFLICT_TEST_FAILURE_FAMILIES = frozenset(
    {"test_failure", "test_error", "test_smell", "method_anomaly",
     "e2e_failure", "smoke_failure"})
CONFLICT_SYNTAX_ERROR_FAMILIES = frozenset({
    "syntax_error", "import_error", "name_error",
})
CONFLICT_LOW_COMPLEXITY_FAMILIES = frozenset({"low_complexity", "simple_code"})
CONFLICT_RESOURCE_LEAK_FAMILIES = frozenset({
    "resource_leak", "memory_leak", "file_leak", "connection_leak",
})
CONFLICT_FIX_SAFETY_FAMILIES = frozenset({"fix_safety", "fix_safety_issue"})
CONFLICT_TYPE_ANNOTATION_FAMILIES = frozenset({
    "missing_annotations", "type_check", "type_error",
})
CONFLICTING_PAIRS: list[tuple[frozenset[str], frozenset[str], str]] = [
    (frozenset({"dead_code", "low_coverage", "quadrant_dead",
                "orphan_function", "orphan_module"}),
     CONFLICT_COMPLEXITY_FAMILIES,
     "dead_vs_complex"),
    (CONFLICT_FIX_SAFETY_FAMILIES,
     frozenset({"gate_failed", "gate_issue"}),
     "fix_safety_vs_gate"),
    (CONFLICT_TEST_FAILURE_FAMILIES - {"test_smell"},
     frozenset({"test_smell"}),
     "test_fail_vs_smell"),
    (frozenset({"mutable_global", "global_statement"}),
     frozenset({"code_smell"}),
     "global_vs_smell"),
    (frozenset({"syntax_error"}),
     frozenset({"high_complexity", "long_function", "deep_nesting"}),
     "syntax_vs_complex"),
    (CONFLICT_LOW_COMPLEXITY_FAMILIES,
     frozenset({"high_complexity"}),
     "low_vs_high_complexity"),
    (CONFLICT_RESOURCE_LEAK_FAMILIES,
     CONFLICT_DEAD_CODE_FAMILIES,
     "resource_leak_vs_dead_code"),
    (CONFLICT_SYNTAX_ERROR_FAMILIES,
     CONFLICT_DEAD_CODE_FAMILIES | frozenset({
         "high_complexity", "long_function", "deep_nesting"}),
     "syntax_vs_analysis"),
    (CONFLICT_TEST_FAILURE_FAMILIES,
     CONFLICT_DEAD_CODE_FAMILIES,
     "test_fail_vs_dead_code"),
    (CONFLICT_LOW_COMPLEXITY_FAMILIES,
     CONFLICT_COMPLEXITY_FAMILIES,
     "low_complexity_vs_long_function"),
    (CONFLICT_FIX_SAFETY_FAMILIES,
     frozenset({"dead_code", "unreachable_code", "unused_definition"}),
     "fix_vs_dead_code"),
    (CONFLICT_RESOURCE_LEAK_FAMILIES,
     CONFLICT_SYNTAX_ERROR_FAMILIES,
     "resource_leak_vs_syntax_error"),
    (frozenset({"perf_hotspot", "infinite_loop"}),
     CONFLICT_DEAD_CODE_FAMILIES,
     "perf_hotspot_vs_dead_code"),
    (frozenset({"mutable_global", "global_statement", "shared_mutable_state"}),
     CONFLICT_DEAD_CODE_FAMILIES,
     "global_vs_dead_code"),
    (frozenset({"config_drift", "insecure_config",
                "missing_config", "config_error"}),
     CONFLICT_DEAD_CODE_FAMILIES,
     "config_vs_dead_code"),
    (frozenset({"dead_code", "unreachable_code", "orphan_function"}),
     frozenset({"race_condition", "deadlock", "thread_unsafe",
                "liveness_probe", "concurrency_bug"}),
     "dead_code_vs_concurrency"),
    (frozenset({"dead_code", "unused_definition", "orphan_module"}),
     frozenset({"compatibility", "breaking_change", "api_compat"}),
     "dead_code_vs_api_compat"),
    (CONFLICT_SYNTAX_ERROR_FAMILIES,
     frozenset({"sql_injection", "path_traversal", "hardcoded_credential",
                "danger_pattern", "unsafe_eval", "command_injection",
                "xxe", "ssrf", "csrf", "weak_crypto"}),
     "syntax_vs_security"),
    (frozenset({"test_failure", "test_error", "smoke_failure", "e2e_failure"}),
     frozenset({"test_quality"}),
     "test_fail_vs_quality"),
    (frozenset({"high_coupling"}),
     CONFLICT_LOW_COMPLEXITY_FAMILIES,
     "high_coupling_vs_low_complexity"),
    (frozenset({"api_change", "api_issue"}),
     frozenset({"compatibility", "api_compat"}),
     "api_change_vs_compat"),
    (CONFLICT_TYPE_ANNOTATION_FAMILIES,
     frozenset({"dead_code", "unreachable_code"}),
     "type_annotation_vs_dead_code"),
    (CONFLICT_TYPE_ANNOTATION_FAMILIES,
     CONFLICT_LOW_COMPLEXITY_FAMILIES,
     "type_annotation_vs_simple_code"),
    (frozenset({"dynamic_import", "implicit_dep", "broken_call"}),
     frozenset({"dead_code", "unreachable_code"}),
     "implicit_dep_vs_dead_code"),
    (frozenset({"dynamic_import"}),
     frozenset({"import_error"}),
     "dynamic_import_vs_import_error"),
    (frozenset({"doc_consistency"}),
     frozenset({"config_drift"}),
     "doc_consistency_vs_config_drift"),
]
SECURITY_FAMILY_UNION: frozenset[str] = (
    get_rule_family_set('security') | get_rule_family_set('security_extended'))
def is_family_member(rule_family: str, families) -> bool:
    if (not isinstance(rule_family, str) or not rule_family
            or not isinstance(families, SOURCE_SEQUENCE_TYPES)):
        return False
    return rule_family in families or normalize_rule(rule_family) in families
def matches_rule_family(rule_id_or_family: str, family_name: str) -> bool:
    family_set = _family_members(family_name)
    if family_set is None:
        return False
    if normalize_rule(rule_id_or_family) in family_set:
        return True
    return isinstance(rule_id_or_family, str) and rule_id_or_family in family_set
_DEAD_CODE_SIGNALS: tuple[str, ...] = (
    "dead", "unused", "orphan", "orphaned",
    "unreachable", "no_reference", "dc-",
)
_DEAD_CODE_SIGNAL_SEPARATORS = frozenset("-_")
def matches_dead_code_signal(value: object) -> bool:
    text = str(value or "").strip().lower()
    if not text:
        return False
    for signal in _DEAD_CODE_SIGNALS:
        start = text.find(signal)
        while start != -1:
            if (start == 0
                    or text[start - 1] in _DEAD_CODE_SIGNAL_SEPARATORS):
                if signal[-1] in _DEAD_CODE_SIGNAL_SEPARATORS:
                    return True
                end = start + len(signal)
                tail = text[end:end + 1]
                if not tail or tail in _DEAD_CODE_SIGNAL_SEPARATORS:
                    return True
            start = text.find(signal, start + 1)
    return False
_METHOD_PREFIX_RE = _re.compile(r"^[A-F][0-9][-_]", _re.IGNORECASE)
_MAX_METHOD_PREFIX_DEPTH = 8
def _map_rule_family_exact(candidate: str) -> str | None:
    current = str_or(candidate)
    for _ in range(_MAX_METHOD_PREFIX_DEPTH):
        if not current:
            return None
        owner = _family_owner_index().get(canonical_rule_key(current))
        if owner:
            return owner
        mapped = _mapped_family(current)
        if mapped is not None:
            return mapped
        m = _METHOD_PREFIX_RE.match(current)
        if m is None:
            return None
        stripped = current[m.end():]
        if not stripped or stripped == current:
            return None
        current = stripped
    return None
def lookup_rule_family(candidate: str) -> str:
    if candidate is None:
        return ""
    if not isinstance(candidate, str):
        candidate = str(candidate)
    candidate = _family_text(candidate)
    if not candidate:
        return ""
    mapped = _map_rule_family_exact(candidate)
    if mapped is not None:
        return mapped
    return candidate
_log.info(
    "fix_guide_rule_identity: 规则族映射加载 map=%d entries / sets=%d families / "
    "file_level_families=%d",
    len(RULE_FAMILY_MAP), len(RULE_FAMILY_SETS), len(FILE_LEVEL_FAMILIES))
_SE_RULE_ID_PATTERN = _re.compile(
    r"^(?:check_?)?se[-_.]?(\d{1,2})([a-z])?$", _re.IGNORECASE)
def normalize_se_rule_id(rule_id: str) -> str | None:
    if not isinstance(rule_id, str):
        return None
    text = rule_id.strip()
    m = _SE_RULE_ID_PATTERN.match(text)
    if m:
        suffix = (m.group(2) or "").lower()
        return f"SE-{int(m.group(1)):02d}{suffix}"
    return None
def get_se_fix_suggestion(rule_id: str) -> str:
    se_key = normalize_se_rule_id(rule_id)
    if se_key is None:
        return ""
    return _corpus.SE_FIX_KNOWLEDGE.get(se_key, "")
DEAD_CODE_FAMILIES: tuple[str, ...] = ("dead_code", "unused_symbols")
def is_dead_code_finding(rule_id: str, f: dict) -> bool:
    if not isinstance(f, dict):
        f = {}
    rule_family = identifier_text(f.get("rule_family")).lower()
    if rule_family and (
            any(matches_rule_family(rule_family, family)
                for family in DEAD_CODE_FAMILIES)
            or matches_dead_code_signal(rule_family)):
        return True
    rule_text = identifier_text(rule_id)
    return (matches_dead_code_signal(rule_text)
            or any(matches_rule_family(rule_text, family)
                   for family in DEAD_CODE_FAMILIES))
_RULE_EXCLUSIVE_PAIRS: list[tuple[str, str]] = [
    ("规则1", "规则3"),
    ("规则1", "规则13"),
    ("规则18", "规则20"),
    ("规则3", "规则36"),
    ("规则9", "规则17"),
    ("规则1", "规则42"),
    ("规则4", "规则15"),
    ("规则9", "规则26"),
    ("规则1", "规则43"),
    ("规则1", "规则5"),
    ("规则6", "规则3"),
    ("规则6", "规则36"),
    ("规则1", "规则7"),
    ("规则1", "规则8"),
    ("规则1", "规则17"),
    ("规则1", "规则46"),
    ("规则1", "规则47"),
    ("规则6", "规则7"),
    ("规则6", "规则8"),
    ("规则6", "规则13"),
    ("规则6", "规则42"),
    ("规则6", "规则43"),
    ("规则6", "规则46"),
    ("规则14", "规则15"),
    ("规则44", "规则25"),
    ("规则51", "规则32"),
    ("规则49", "规则33"),
    ("规则37", "规则19"),
    ("规则47", "规则22"),
    ("规则48", "规则12"),
    ("规则42", "规则13"),
    ("规则1", "规则10"),
    ("规则1", "规则12"),
    ("规则1", "规则22"),
    ("规则1", "规则26"),
    ("规则6", "规则9"),
    ("规则6", "规则10"),
    ("规则6", "规则11"),
    ("规则6", "规则12"),
    ("规则6", "规则17"),
    ("规则6", "规则22"),
    ("规则6", "规则26"),
    ("规则6", "规则47"),
]
_RULE_SEMANTICS: dict[str, str] = {
    "规则1": "confirm", "规则2": "confirm", "规则3": "confirm", "规则4": "suppress",
    "规则5": "confirm", "规则6": "confirm", "规则7": "confirm", "规则8": "confirm",
    "规则9": "confirm", "规则10": "confirm", "规则11": "confirm", "规则12": "confirm",
    "规则13": "confirm", "规则14": "confirm", "规则15": "confirm", "规则17": "confirm",
    "规则18": "confirm", "规则19": "confirm", "规则20": "confirm", "规则21": "confirm",
    "规则22": "confirm", "规则23": "confirm", "规则24": "confirm", "规则25": "confirm",
    "规则26": "confirm", "规则27": "confirm", "规则28": "confirm", "规则29": "confirm",
    "规则30": "confirm", "规则32": "confirm", "规则33": "confirm", "规则34": "confirm",
    "规则35": "confirm", "规则36": "confirm", "规则16": "arbitrate", "规则31": "arbitrate",
    "规则37": "confirm", "规则38": "confirm", "规则39": "confirm", "规则40": "confirm",
    "规则41": "confirm", "规则42": "confirm", "规则43": "confirm", "规则44": "confirm",
    "规则45": "confirm", "规则46": "confirm", "规则47": "confirm", "规则48": "confirm",
    "规则49": "confirm", "规则50": "confirm", "规则51": "confirm", "规则52": "confirm",
    "规则53": "confirm", "规则54": "confirm", "规则55": "confirm", "规则56": "confirm",
    "规则57": "confirm",
    "规则58": "confirm", "规则59": "confirm", "规则60": "confirm", "规则61": "confirm",
    "规则H1": "confirm", "规则H2": "confirm", "规则H4": "confirm", "规则H6": "confirm",
    "规则H7": "confirm", "规则H8": "confirm",
}
_REGISTERED_RULE_IDS = {
    rid.replace("规则", ""): rid for rid in _RULE_SEMANTICS}
_REGISTERED_RULE_IDS.update({"降级": "降级", "通用": "通用"})
def _registered_rule_id(rule_id: str) -> str:
    rid = safe_rule_id(rule_id)
    normalized = rid.strip()
    return _REGISTERED_RULE_IDS.get(normalized.replace("规则", ""), rid)
def get_rule_semantic(rule_id: str) -> str:
    try:
        return _RULE_SEMANTICS.get(_registered_rule_id(rule_id), "confirm")
    except Exception as e:  # noqa: BLE001 — 语义查询失败回退默认 confirm
        _log.warning("get_rule_semantic: %s", e)
        return "confirm"
def check_rule_exclusion(rule_id: str, matched_rules: set[str]) -> str | None:
    try:
        rid = _registered_rule_id(rule_id)
        matched_rules = {_registered_rule_id(item) for item in matched_rules}
        for a, b in _RULE_EXCLUSIVE_PAIRS:
            if rid in (a, b):
                other = b if rid == a else a
                if other in matched_rules:
                    return other
        return None
    except Exception as e:  # noqa: BLE001 — 互斥检查失败返回 None
        _log.warning("[XV] 规则互斥检查失败 in check_rule_exclusion(): %s", e)
        return None
_RULE_PRIORITY_TABLE = [
    {"id": "规则1",  "priority": 1,  "type": "confirm",    "desc": "死代码确认"},
    {"id": "规则2",  "priority": 2,  "type": "confirm",    "desc": "安全确认"},
    {"id": "规则3",  "priority": 3,  "type": "confirm",    "desc": "复杂度确认"},
    {"id": "规则4",  "priority": 4,  "type": "suppress",   "desc": "误报抑制"},
    {"id": "规则5",  "priority": 5,  "type": "confirm",    "desc": "隐藏问题"},
    {"id": "规则6",  "priority": 6,  "type": "confirm",    "desc": "语法错误"},
    {"id": "规则7",  "priority": 7,  "type": "confirm",    "desc": "循环依赖"},
    {"id": "规则8",  "priority": 8,  "type": "confirm",    "desc": "宽泛异常"},
    {"id": "规则9",  "priority": 9,  "type": "confirm",    "desc": "全局变量"},
    {"id": "规则10", "priority": 10, "type": "confirm",    "desc": "递归"},
    {"id": "规则11", "priority": 11, "type": "confirm",    "desc": "调用断裂"},
    {"id": "规则12", "priority": 12, "type": "confirm",    "desc": "路径穿越"},
    {"id": "规则13", "priority": 13, "type": "confirm",    "desc": "大文件"},
    {"id": "规则14", "priority": 14, "type": "confirm",    "desc": "文件级多源确认"},
    {"id": "规则17", "priority": 15, "type": "confirm",    "desc": "指标越界确认"},
    {"id": "规则18", "priority": 16, "type": "confirm",    "desc": "门禁失败确认"},
    {"id": "规则19", "priority": 17, "type": "confirm",    "desc": "基线退化确认"},
    {"id": "规则20", "priority": 18, "type": "confirm",    "desc": "修复安全验证"},
    {"id": "规则16", "priority": 19, "type": "arbitrate",  "desc": "矛盾检测"},
    {"id": "规则21", "priority": 20, "type": "confirm",    "desc": "动态导入确认"},
    {"id": "规则22", "priority": 21, "type": "confirm",    "desc": "污点路径可行性"},
    {"id": "规则23", "priority": 22, "type": "confirm",    "desc": "修复等价性"},
    {"id": "规则24", "priority": 23, "type": "confirm",    "desc": "日志异常确认"},
    {"id": "规则25", "priority": 24, "type": "confirm",    "desc": "API兼容性确认"},
    {"id": "规则26", "priority": 25, "type": "confirm",    "desc": "并发安全确认"},
    {"id": "规则27", "priority": 26, "type": "confirm",    "desc": "文档一致性确认"},
    {"id": "规则28", "priority": 27, "type": "confirm",    "desc": "历史缺陷确认"},
    {"id": "规则29", "priority": 28, "type": "confirm",    "desc": "突变覆盖确认"},
    {"id": "规则30", "priority": 29, "type": "confirm",    "desc": "历史趋势确认"},
    {"id": "规则31", "priority": 30, "type": "arbitrate",  "desc": "人工确认闭环"},
    {"id": "规则32", "priority": 31, "type": "confirm",    "desc": "配置漂移确认"},
    {"id": "规则33", "priority": 32, "type": "confirm",    "desc": "类型与测试质量"},
    {"id": "规则34", "priority": 33, "type": "confirm",    "desc": "隐式依赖确认"},
    {"id": "规则35", "priority": 34, "type": "confirm",    "desc": "多源降权确认"},
    {"id": "规则36", "priority": 35, "type": "confirm",    "desc": "语义级矛盾检测"},
    {"id": "规则37", "priority": 36, "type": "confirm",    "desc": "历史基线差异对比"},
    {"id": "规则38", "priority": 37, "type": "confirm",    "desc": "业务流追踪验证"},
    {"id": "规则39", "priority": 38, "type": "confirm",    "desc": "引用深度加权排序"},
    {"id": "规则40", "priority": 39, "type": "confirm",    "desc": "集群共识验证"},
    {"id": "规则41", "priority": 40, "type": "confirm",    "desc": "变异测试确认"},
    {"id": "规则42", "priority": 41, "type": "confirm",    "desc": "性能热点确认"},
    {"id": "规则43", "priority": 42, "type": "confirm",    "desc": "内存泄漏确认"},
    {"id": "规则44", "priority": 43, "type": "confirm",    "desc": "API向后兼容"},
    {"id": "规则45", "priority": 44, "type": "confirm",    "desc": "测试有效性确认"},
    {"id": "规则46", "priority": 45, "type": "confirm",    "desc": "代码可维护性"},
    {"id": "规则47", "priority": 46, "type": "confirm",    "desc": "安全漏洞深度确认"},
    {"id": "规则48", "priority": 47, "type": "confirm",    "desc": "配置安全确认"},
    {"id": "规则49", "priority": 48, "type": "confirm",    "desc": "类型注解交叉确认"},
    {"id": "规则50", "priority": 49, "type": "confirm",    "desc": "隐式依赖确认"},
    {"id": "规则51", "priority": 50, "type": "confirm",    "desc": "配置漂移交叉确认"},
    {"id": "规则52", "priority": 59, "type": "confirm",    "desc": "文件健康评分确认"},
    {"id": "规则53", "priority": 61, "type": "confirm",    "desc": "结构性缺陷确认"},
    {"id": "规则54", "priority": 62, "type": "confirm",    "desc": "拆分推荐确认"},
    {"id": "规则55", "priority": 63, "type": "confirm",    "desc": "模块循环结构确认"},
    {"id": "规则56", "priority": 64, "type": "confirm",    "desc": "模块拆分候选确认"},
    {"id": "规则57", "priority": 65, "type": "confirm",    "desc": "模块迁移/合并候选确认"},
    {"id": "规则58", "priority": 66, "type": "confirm",    "desc": "VCS近变证据"},
    {"id": "规则59", "priority": 67, "type": "confirm",    "desc": "反驳负证据分析"},
    {"id": "规则60", "priority": 68, "type": "confirm",    "desc": "测试触发定向冒烟"},
    {"id": "规则61", "priority": 69, "type": "confirm",    "desc": "反向可证伪验证"},
    {"id": "规则H1", "priority": 51, "type": "confirm",    "desc": "幻觉检测确认(综合)"},
    {"id": "规则H2", "priority": 52, "type": "confirm",    "desc": "幻觉导入链确认(H02)"},
    {"id": "规则H4", "priority": 54, "type": "confirm",    "desc": "幻觉上下文矛盾确认(H04)"},
    {"id": "规则H6", "priority": 56, "type": "confirm",    "desc": "测试幻觉确认(H06)"},
    {"id": "规则H7", "priority": 57, "type": "confirm",    "desc": "记忆幻觉确认(H07)"},
    {"id": "规则H8", "priority": 58, "type": "confirm",    "desc": "幻觉安全防护确认(H08)"},
    {"id": "规则15", "priority": 60, "type": "single",     "desc": "单源自验证"},
    {"id": "降级",   "priority": 90, "type": "fallback",   "desc": "降级规则匹配"},
    {"id": "通用",   "priority": 99, "type": "general",    "desc": "通用交叉验证"},
]
def _get_rule_metadata_uncached(rule_id: str) -> dict:
    rid = _registered_rule_id(rule_id)
    try:
        rid_bare = rid.replace("规则", "")
        for entry in _RULE_PRIORITY_TABLE:
            if entry["id"].replace("规则", "") != rid_bare:
                continue
            result = dict(entry)
            _desc = CV_RULES.get(entry["id"])
            result["methods"] = (
                list(dict.fromkeys(_desc.source_methods))
                if _desc is not None else [])
            return result
        return {"id": rid, "priority": 50, "type": "unknown", "desc": rid, "methods": []}
    except Exception as e:  # noqa: BLE001 — 元数据获取异常返回结构化错误标记
        _log.warning(
            "[XV] 规则元数据获取失败 in _get_rule_metadata_uncached(): %s", e)
        return {"id": rid, "priority": 50, "type": "unknown",
                "desc": rid, "methods": [],
                "_error": True, "_partial": True}
_RULE_META_TABLE_ORIG = _RULE_PRIORITY_TABLE
_RULE_META_CVRULES_ORIG = CV_RULES
_RULE_META_CACHE: dict[str, dict] = {}
_RULE_META_CACHE_MAX = 512
def _copy_rule_meta(meta: dict) -> dict:
    return {k: (list(v) if isinstance(v, list) else v)
            for k, v in meta.items()}
def clear_rule_metadata_cache() -> int:
    _n = len(_RULE_META_CACHE)
    _RULE_META_CACHE.clear()
    return _n
def get_rule_metadata(rule_id: str) -> dict:
    if (_RULE_PRIORITY_TABLE is _RULE_META_TABLE_ORIG
            and CV_RULES is _RULE_META_CVRULES_ORIG):
        rid = _registered_rule_id(rule_id)
        _hit = _RULE_META_CACHE.get(rid)
        if _hit is not None:
            return _copy_rule_meta(_hit)
        _result = _get_rule_metadata_uncached(rule_id)
        if (not _result.get("_error")
                and len(_RULE_META_CACHE) < _RULE_META_CACHE_MAX):
            _RULE_META_CACHE[rid] = _copy_rule_meta(_result)
        return _result
    return _get_rule_metadata_uncached(rule_id)
_RULE_METADATA_AUXILIARY_IDS = frozenset({"通用", "降级"})
def _validate_three_source_coverage(all_rule_ids: set, semantic_ids: set,
                                    priority_ids: set) -> list:
    cv_ids = set(all_rule_ids)
    semantic_ids = set(semantic_ids)
    priority_ids = set(priority_ids) - _RULE_METADATA_AUXILIARY_IDS
    issues = []
    sources = (
        (cv_ids, "CV_RULES", "规则定义"),
        (semantic_ids, "_RULE_SEMANTICS", "语义定义"),
        (priority_ids, "_RULE_PRIORITY_TABLE", "优先级定义"),
    )
    for rid in sorted(cv_ids | semantic_ids | priority_ids):
        for known_ids, source, missing in sources:
            if rid not in known_ids:
                issues.append(f"[MISSING] 规则 {rid} 在 {source} 中缺少{missing}")
    return issues
_SEMANTIC_TYPE_DOMAIN: tuple[str, ...] = ("confirm", "suppress", "arbitrate")
def _validate_semantic_type_alignment() -> list:
    return [
        f"[CONFLICT] 规则 {entry['id']}: type={entry.get('type', '')} "
        f"但 SEMANTICS={_RULE_SEMANTICS.get(entry['id'], '')}"
        for entry in _RULE_PRIORITY_TABLE
        if entry.get("type", "") in _SEMANTIC_TYPE_DOMAIN
        and _RULE_SEMANTICS.get(entry["id"], "") != entry.get("type", "")]
def _validate_rule_metadata_consistency():
    all_rule_ids = set(CV_RULES.keys())
    semantic_ids = set(_RULE_SEMANTICS.keys())
    priority_ids = {e["id"] for e in _RULE_PRIORITY_TABLE}
    return (
        _validate_three_source_coverage(all_rule_ids, semantic_ids,
                                        priority_ids)
        + _validate_semantic_type_alignment()
    )
try:
    _meta_issues = _validate_rule_metadata_consistency()
    if _meta_issues:
        for _issue in _meta_issues:
            _log.warning("[RuleMetaValidator] %s", _issue)
        _log.info("[RuleMetaValidator] 发现 %d 个元数据不一致项", len(_meta_issues))
    else:
        _log.info("[RuleMetaValidator] 三源元数据一致性校验通过")
except Exception as _e:  # noqa: BLE001 — 校验器任何异常降级为告警
    _log.warning("[RuleMetaValidator] 校验异常: %s", _e)
register_cache_release(
    "rule_metadata_cache", clear_rule_metadata_cache,
    "规则元数据共享缓存", order=100)
register_cache_release(
    "rule_match_caches", clear_rule_match_caches, "规则判定共享缓存", order=90)
MATCH_LEVELS: tuple[str, ...] = ('exact', 'variant', 'weak', 'none')
SHAPE_MAX_DEPTH = 4
SHAPE_MAX_NODES = 24
ANCHOR_LIMIT = 12
_DEFAULT_SCOPE_KIND = 'module'
_DEFAULT_SEVERITY = 'P2'
_TRUE_TOKENS = frozenset({'1', 'true', 'yes', 'y', 'on'})
_ANCHOR_STOPWORDS = frozenset({
    'self', 'cls', 'None', 'True', 'False', 'args', 'kwargs',
})
_IGNORED_SHAPE_FIELDS = frozenset({
    'ctx', 'type_comment', 'lineno', 'col_offset', 'end_lineno',
    'end_col_offset', 'kind', 'type_params', 'name', 'id', 'attr', 'arg',
    'value',
})
_EXACT_ANCHOR_JACCARD = 0.6
_SHAPE_ONLY_MIN_CHARS = 24
_VARIANT_ANCHOR_JACCARD = 0.25
_WEAK_ANCHOR_JACCARD = 0.1
_EXACT_ANCHOR_MIN = 2
_VARIANT_ANCHOR_MIN = 2
_WEAK_ANCHOR_MIN = 1
_GUARD_PENALTY = 0.1
_IDENTIFIER_TOKEN_RE = _re.compile(r'[A-Za-z_][A-Za-z0-9_]{2,}')
_TRY_NODE_TYPES = (ast.Try, getattr(ast, "TryStar", ast.Try))
@dataclass(frozen=True)
class NodeContext:
    node: ast.AST
    kind: str
    shape: str
    anchors: tuple[str, ...]
    scope_kind: str = _DEFAULT_SCOPE_KIND
    qualname: str = ''
    context_flags: tuple[str, ...] = ()
    guarded: bool = False
    line: int = 0
    col: int = 0
    end_line: int = 0
@dataclass(frozen=True)
class MatchResult:
    level: str
    score: float
    anchor_overlap: int = 0
    anchor_jaccard: float = 0.0
    shape_match: bool = False
    reasons: tuple[str, ...] = ()
    def to_dict(self) -> dict:
        return {
            'level': self.level,
            'score': round(self.score, 4),
            'anchor_overlap': self.anchor_overlap,
            'anchor_jaccard': round(self.anchor_jaccard, 4),
            'shape_match': self.shape_match,
            'reasons': list(self.reasons),
        }
@dataclass
class FanoutSignature:
    rule_id: str
    rule_family: str
    pattern_key: str
    shape: str
    anchors: tuple[str, ...]
    scope_kind: str
    context_flags: tuple[str, ...]
    seed_file: str
    seed_line: int
    seed_locator: str = ''
    seed_message: str = ''
    snippet: str = ''
    degraded: bool = False
    degrade_reason: str = ''
    node_kind: str = ''
    severity: str = _DEFAULT_SEVERITY
    def to_dict(self) -> dict:
        return {
            'rule_id': self.rule_id,
            'rule_family': self.rule_family,
            'pattern_key': self.pattern_key,
            'shape': self.shape,
            'anchors': list(self.anchors),
            'scope_kind': self.scope_kind,
            'context_flags': list(self.context_flags),
            'seed_file': self.seed_file,
            'seed_line': self.seed_line,
            'seed_locator': self.seed_locator,
            'seed_message': str_or(self.seed_message)[:200],
            'snippet': self.snippet,
            'degraded': self.degraded,
            'degrade_reason': self.degrade_reason,
            'node_kind': self.node_kind,
            'severity': self.severity,
        }
    @property
    def family_id(self) -> str:
        return f"{self.rule_family}:{self.pattern_key}"
def _type_name(node: Any) -> str:
    return type(node).__name__
@lru_cache(maxsize=256)
def _shape_fields(node_type: type) -> tuple[str, ...]:
    _fixed = _FIXED_SHAPE_FIELDS.get(node_type)
    if _fixed is not None:
        return _fixed
    return tuple(sorted(
        name for name in getattr(node_type, '_fields', ())
        if name not in _IGNORED_SHAPE_FIELDS
    ))
_FIXED_SHAPE_FIELDS: dict[type, tuple[str, ...]] = {
    ast.FunctionDef: ('args', 'body', 'decorator_list'),
    ast.AsyncFunctionDef: ('args', 'body', 'decorator_list'),
    ast.ClassDef: ('bases', 'body', 'decorator_list'),
    ast.Lambda: ('args', 'body'),
    ast.If: ('test', 'body', 'orelse'),
    ast.For: ('target', 'iter', 'body', 'orelse'),
    ast.AsyncFor: ('target', 'iter', 'body', 'orelse'),
    ast.While: ('test', 'body', 'orelse'),
    ast.Try: ('body', 'handlers', 'orelse', 'finalbody'),
    ast.ExceptHandler: ('type', 'body'),
    ast.With: ('items', 'body'),
    ast.AsyncWith: ('items', 'body'),
    ast.Return: ('value',),
    ast.Assign: ('targets', 'value'),
    ast.AugAssign: ('target', 'value'),
    ast.AnnAssign: ('target', 'annotation', 'value'),
    ast.Expr: ('value',),
    ast.Raise: ('exc', 'cause'),
    ast.Assert: ('test', 'msg'),
    ast.Delete: ('targets',),
    ast.Call: ('func', 'args', 'keywords'),
    ast.Attribute: ('value',),
    ast.Subscript: ('value', 'slice'),
    ast.BinOp: ('left', 'op', 'right'),
    ast.BoolOp: ('op', 'values'),
    ast.UnaryOp: ('op', 'operand'),
    ast.Compare: ('left', 'ops', 'comparators'),
    ast.IfExp: ('test', 'body', 'orelse'),
    ast.Dict: ('keys', 'values'),
    ast.List: ('elts',),
    ast.Tuple: ('elts',),
    ast.Set: ('elts',),
    ast.JoinedStr: ('values',),
    ast.FormattedValue: ('value', 'format_spec'),
    ast.NamedExpr: ('target', 'value'),
    ast.Await: ('value',),
    ast.Yield: ('value',),
    ast.YieldFrom: ('value',),
    ast.comprehension: ('target', 'iter', 'ifs'),
    ast.Import: (),
    ast.ImportFrom: (),
    ast.Global: (),
    ast.Nonlocal: (),
    ast.Name: (),
    ast.Constant: (),
}
try:
    _FIXED_SHAPE_FIELDS[ast.TryStar] = (
        'body', 'handlers', 'orelse', 'finalbody')
except AttributeError:  # pragma: no cover — Python < 3.11 无 TryStar
    _log.debug('当前解释器无 ast.TryStar，形态表跳过该节点')
def _shape_scalar(value: Any) -> str:
    if isinstance(value, ast.AST):
        return type(value).__name__
    if isinstance(value, list):
        return f'[{len(value)}]'
    return ''
def _shape_of(node: Any, depth: int, budget: list[int]) -> str:
    if node is None:
        return 'None'
    name = _type_name(node)
    if budget[0] <= 0:
        return f'{name}~'
    budget[0] -= 1
    if isinstance(node, ast.Constant):
        return f'{name}:{type(node.value).__name__}'
    if isinstance(node, (ast.Name, ast.arg, ast.alias)):
        return name
    if depth <= 0:
        return f'{name}~'
    fields = _shape_fields(type(node))
    parts: list[str] = []
    for fname in fields:
        value = getattr(node, fname, None)
        if value is None:
            continue
        if isinstance(value, list):
            rendered = ''.join(_shape_of(item, depth - 1, budget)
                               for item in value if isinstance(item, ast.AST))
            if rendered:
                parts.append(f'{fname}:{rendered}')
            elif value:
                parts.append(f'{fname}:{_shape_scalar(value)}')
            continue
        if isinstance(value, ast.AST):
            parts.append(f'{fname}:{_shape_of(value, depth - 1, budget)}')
            continue
        parts.append(f'{fname}:{_shape_scalar(value)}')
    if isinstance(node, ast.Call):
        parts.append(f'argc:{_arg_bucket(len(node.args))}')
        kw_names = sorted(kw.arg for kw in node.keywords if kw.arg)
        parts.append(f'kw:{",".join(kw_names)}')
    return f'{name}({",".join(parts)})'
def _arg_bucket(count: int) -> str:
    if count <= 0:
        return '0'
    if count == 1:
        return '1'
    if count <= 3:
        return '2-3'
    return '4+'
def extract_shape(node: ast.AST) -> str:
    try:
        budget = [SHAPE_MAX_NODES]
        return _shape_of(node, SHAPE_MAX_DEPTH, budget)
    except (AttributeError, TypeError, ValueError, RecursionError) as exc:
        log_swallowed(__name__, exc, context='extract_shape')
        return _type_name(node)
def _dotted_name(node: ast.AST | None) -> str:
    if node is None:
        return ''
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        base = _dotted_name(node.value)
        return f'{base}.{node.attr}' if base else node.attr
    return ''
def _anchor_usable(anchor: str) -> bool:
    if not isinstance(anchor, str) or not anchor:
        return False
    if anchor in _ANCHOR_STOPWORDS:
        return False
    return all(part.isidentifier() for part in anchor.split('.'))
def _collect_anchor(node: ast.AST, bag: set[str]) -> None:
    if isinstance(node, ast.Name):
        bag.add(node.id)
    elif isinstance(node, ast.Attribute):
        bag.add(node.attr)
    elif isinstance(node, ast.Call):
        dotted = _dotted_name(node.func)
        if dotted:
            bag.add(dotted)
            bag.add(dotted.rsplit('.', 1)[-1])
    elif isinstance(node, ast.keyword):
        if node.arg:
            bag.add(node.arg)
    elif isinstance(node, ast.ExceptHandler):
        dotted = _dotted_name(node.type)
        if dotted:
            bag.add(dotted)
    elif isinstance(node, ast.Constant):
        if isinstance(node.value, str) and node.value.isidentifier():
            bag.add(node.value)
    elif isinstance(node, ast.Compare):
        for op in node.ops:
            bag.add(_type_name(op))
    elif isinstance(node, (ast.Import, ast.ImportFrom)):
        for alias in node.names:
            if alias.name:
                bag.add(alias.name.rsplit('.', 1)[-1])
    elif isinstance(node, ast.arg):
        bag.add(node.arg)
    elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        bag.add(node.name)
    elif isinstance(node, (ast.Global, ast.Nonlocal)):
        bag.update(node.names)
def extract_anchors(node: ast.AST) -> tuple[str, ...]:
    bag: set[str] = set()
    for sub in walk_nodes(node):
        _collect_anchor(sub, bag)
    cleaned = [anchor for anchor in bag if _anchor_usable(anchor)]
    cleaned.sort(key=lambda item: (-len(item), item))
    return tuple(cleaned[:ANCHOR_LIMIT])
def _anchors_from_text(text: str) -> tuple[str, ...]:
    if not isinstance(text, str) or not text:
        return ()
    tokens = {token for token in _IDENTIFIER_TOKEN_RE.findall(text)
              if token not in _ANCHOR_STOPWORDS}
    ordered = sorted(tokens, key=lambda item: (-len(item), item))
    return tuple(ordered[:ANCHOR_LIMIT])
def _context_flags(node: ast.AST, parents: dict[ast.AST, ast.AST]) -> tuple[str, ...]:
    flags: set[str] = set()
    current = parents.get(node)
    while current is not None:
        if isinstance(current, _TRY_NODE_TYPES):
            flags.add('try')
        elif isinstance(current, ast.ExceptHandler):
            flags.add('except')
        elif isinstance(current, (ast.For, ast.AsyncFor, ast.While)):
            flags.add('loop')
        elif isinstance(current, ast.If):
            flags.add('conditional')
        elif isinstance(current, (ast.With, ast.AsyncWith)):
            flags.add('with')
        elif isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            flags.add('function')
            break
        elif isinstance(current, ast.ClassDef):
            flags.add('class')
            break
        current = parents.get(current)
    return tuple(sorted(flags))
def _scope_kind_of(node: ast.AST, parents: dict[ast.AST, ast.AST]) -> str:
    current = parents.get(node)
    while current is not None:
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return 'function'
        if isinstance(current, ast.Lambda):
            return 'lambda'
        if isinstance(current, ast.ClassDef):
            return 'class'
        current = parents.get(current)
    return _DEFAULT_SCOPE_KIND
def _qualname_of(node: ast.AST, parents: dict[ast.AST, ast.AST]) -> str:
    parts: list[str] = []
    current = parents.get(node)
    while current is not None:
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            parts.append(current.name)
        current = parents.get(current)
    return '.'.join(reversed(parts))
def _is_guarded(node: ast.AST, parents: dict[ast.AST, ast.AST]) -> bool:
    current = parents.get(node)
    child = node
    while current is not None:
        if isinstance(current, ast.If) and any(
                item is child
                for branch in (current.body, current.orelse)
                for item in branch):
            return True
        if isinstance(current, ast.ExceptHandler) and _handler_swallows(current):
            return True
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda)):
            break
        child = current
        current = parents.get(current)
    return False
def _handler_swallows(handler: ast.ExceptHandler) -> bool:
    for stmt in handler.body:
        if isinstance(stmt, ast.Pass):
            continue
        if isinstance(stmt, ast.Return):
            continue
        if isinstance(stmt, (ast.Continue, ast.Break)):
            continue
        return False
    return True
def node_context_of(node: ast.AST, *,
                    parents: dict[ast.AST, ast.AST] | None = None,
                    shape: str | None = None,
                    anchors: Sequence[str] | None = None) -> NodeContext:
    _parents = parents if parents is not None else {}
    line = int_or(getattr(node, 'lineno', 0), 0)
    end_line = int_or(getattr(node, 'end_lineno', line), line)
    col = int_or(getattr(node, 'col_offset', 0), 0)
    return NodeContext(
        node=node,
        kind=_type_name(node),
        shape=shape if shape is not None else extract_shape(node),
        anchors=tuple(anchors) if anchors is not None else extract_anchors(node),
        scope_kind=_scope_kind_of(node, _parents),
        qualname=_qualname_of(node, _parents),
        context_flags=_context_flags(node, _parents),
        guarded=_is_guarded(node, _parents),
        line=line,
        col=col,
        end_line=end_line,
    )
def _statement_nodes(tree: ast.AST) -> list[ast.AST]:
    return [node for node in walk_nodes(tree) if isinstance(node, ast.stmt)]
def _snippet_first_line(snippet: str) -> str:
    for line in str_or(snippet).splitlines():
        stripped = line.strip()
        if stripped:
            return stripped
    return ''
def _calibrate_line(source_lines: Sequence[str], line: int,
                    snippet: str) -> int:
    probe = _snippet_first_line(snippet)
    if not probe or not source_lines:
        return line
    if 1 <= line <= len(source_lines):
        current = source_lines[line - 1].strip()
        snippet_lines = {text.strip() for text in str_or(snippet).splitlines()
                         if text.strip()}
        if current and current in snippet_lines:
            return line
    hits = [idx + 1 for idx, text in enumerate(source_lines)
            if text.strip() == probe]
    if len(hits) != 1:
        return line
    return hits[0]
def _statement_start_line(node: ast.AST) -> int:
    line = int_or(getattr(node, 'lineno', 0), 0)
    for decorator in getattr(node, 'decorator_list', ()) or ():
        decorator_line = int_or(getattr(decorator, 'lineno', 0), 0)
        if decorator_line > 0:
            line = min(line, decorator_line) if line > 0 else decorator_line
    return line
def locate_seed_node(tree: ast.AST | None, line: int,
                     snippet: str = '',
                     source_lines: Sequence[str] | None = None) -> ast.AST | None:
    if tree is None:
        return None
    _line = _calibrate_line(source_lines or (), line, snippet)
    statements = [node for node in _statement_nodes(tree)
                  if _statement_start_line(node) > 0]
    if not statements or _line <= 0:
        return None
    containing = [
        node for node in statements
        if _statement_start_line(node) <= _line
        <= int_or(getattr(node, 'end_lineno', 0), _line)
    ]
    if containing:
        probe = _snippet_first_line(snippet)
        source_text = ('\n'.join(source_lines)
                       if source_lines is not None else '')
        def _containing_rank(node: ast.AST) -> tuple[int, int, int]:
            line_span = (int_or(getattr(node, 'end_lineno', 0), 0)
                         - _statement_start_line(node))
            snippet_mismatch = 1
            if probe and source_text:
                segment = ast.get_source_segment(source_text, node)
                if segment and segment.strip() == probe:
                    snippet_mismatch = 0
            return (line_span, snippet_mismatch,
                    -_statement_start_line(node))
        containing.sort(key=_containing_rank)
        return containing[0]
    probe_tokens = {token for token in _IDENTIFIER_TOKEN_RE.findall(
        _snippet_first_line(snippet))}
    if not probe_tokens:
        return None
    best: tuple[int, int, ast.AST] | None = None
    for node in statements:
        node_line = _statement_start_line(node)
        distance = abs(node_line - _line)
        if distance > _SEED_LINE_WINDOW:
            continue
        node_text = ' '.join(
            text.strip() for text in (source_lines or [])[
                max(node_line - 1, 0):
                int_or(getattr(node, 'end_lineno', node_line), node_line)]
        )
        node_tokens = set(_IDENTIFIER_TOKEN_RE.findall(node_text))
        hit = len(probe_tokens & node_tokens)
        if hit <= 0:
            continue
        rank = (-hit, distance, node)
        if best is None or rank[:2] < best[:2]:
            best = rank
    return best[2] if best is not None else None
def _pattern_key(rule_family: str, shape: str, node_kind: str) -> str:
    digest = hashlib.sha256(
        f'{rule_family}|{node_kind}|{shape}'.encode()
    ).hexdigest()[:12]
    return digest
def build_signature(finding: dict, *,
                    source: str | None = None,
                    tree: ast.AST | None = None,
                    source_lines: Sequence[str] | None = None,
                    skill_dir: str = _DEFAULT_SKILL_DIR) -> FanoutSignature:
    _finding = dict_or_empty(finding)
    rule_id = _finding_rule_id(_finding)
    family = normalize_rule(
        _family_text(finding_family(_finding))
        or _family_text(rule_id) or 'unknown')
    file_path, line = _finding_coords(_finding, skill_dir=skill_dir)
    snippet = str_or(_finding_first(_finding, _FINDING_SNIPPET_KEYS))
    message = str_or(_finding.get('message')) or str_or(_finding.get('sample_message'))
    locator = (str_or(_finding.get('locator'))
               or make_locator_from_finding(_finding))
    severity = (str_or(_finding.get('severity')).strip().upper()
                or _DEFAULT_SEVERITY)
    _source = str_or(source)
    _tree = tree
    _parse_failed = False
    if _tree is None and _source:
        try:
            _tree = parse_cached(_source, file_path or '<seed>')
        except (SyntaxError, ValueError, RecursionError) as exc:
            log_swallowed(__name__, exc, context='build_signature:parse')
            _tree = None
            _parse_failed = True
    _lines = list(source_lines) if source_lines is not None else (
        _source.splitlines() if _source else [])
    node = locate_seed_node(_tree, line, snippet or message, _lines)
    if node is None:
        return FanoutSignature(
            rule_id=rule_id or 'unknown',
            rule_family=family,
            pattern_key=_pattern_key(family, '', ''),
            shape='',
            anchors=_anchors_from_text(snippet or message),
            scope_kind=_DEFAULT_SCOPE_KIND,
            context_flags=(),
            seed_file=file_path,
            seed_line=line,
            seed_locator=locator,
            seed_message=message,
            snippet=snippet,
            degraded=True,
            degrade_reason=('seed_source_unparseable' if _parse_failed
                            else 'seed_source_missing' if _tree is None
                            else 'seed_node_not_located'),
            node_kind='',
            severity=severity,
        )
    parents = parent_map(_tree) if _tree is not None else {}
    ctx = node_context_of(node, parents=parents)
    if not ctx.anchors:
        return FanoutSignature(
            rule_id=rule_id or 'unknown',
            rule_family=family,
            pattern_key=_pattern_key(family, '', ctx.kind),
            shape='',
            anchors=_anchors_from_text(snippet or message),
            scope_kind=ctx.scope_kind,
            context_flags=ctx.context_flags,
            seed_file=file_path,
            seed_line=ctx.line or line,
            seed_locator=locator,
            seed_message=message,
            snippet=snippet,
            degraded=True,
            degrade_reason='seed_anchors_empty',
            node_kind=ctx.kind,
            severity=severity,
        )
    return FanoutSignature(
        rule_id=rule_id or 'unknown',
        rule_family=family,
        pattern_key=_pattern_key(family, ctx.shape, ctx.kind),
        shape=ctx.shape,
        anchors=ctx.anchors,
        scope_kind=ctx.scope_kind,
        context_flags=ctx.context_flags,
        seed_file=file_path,
        seed_line=ctx.line or line,
        seed_locator=locator,
        seed_message=message,
        snippet=snippet,
        node_kind=ctx.kind,
        severity=severity,
    )
def _statement_kind(shape: str) -> str:
    if not isinstance(shape, str) or not shape:
        return ''
    head = shape.split('(', 1)[0]
    return head.rstrip('~')
def _context_similarity(seed_flags: Sequence[str],
                        candidate_flags: Sequence[str]) -> float:
    seed_set = set(seed_flags)
    candidate_set = set(candidate_flags)
    if seed_set == candidate_set:
        return 1.0
    if seed_set & candidate_set:
        return 0.5
    return 0.0
def _level_of(shape_match: bool, statement_match: bool,
              jaccard: float, overlap: int, shape_only: bool) -> str:
    if (shape_match and overlap >= _EXACT_ANCHOR_MIN
            and jaccard >= _EXACT_ANCHOR_JACCARD):
        return 'exact'
    if shape_match and overlap >= _VARIANT_ANCHOR_MIN and (
            jaccard >= _VARIANT_ANCHOR_JACCARD):
        return 'variant'
    if (statement_match and overlap >= _VARIANT_ANCHOR_MIN
            and jaccard >= 0.5):
        return 'variant'
    if statement_match and overlap >= _WEAK_ANCHOR_MIN and (
            jaccard >= _WEAK_ANCHOR_JACCARD):
        return 'weak'
    if shape_only and shape_match:
        return 'weak'
    return 'none'
def match_occurrence(signature: FanoutSignature,
                     ctx: NodeContext) -> MatchResult:
    if not isinstance(signature, FanoutSignature) or not isinstance(ctx, NodeContext):
        return MatchResult(level='none', score=0.0)
    seed_anchors = set(signature.anchors)
    cand_anchors = set(ctx.anchors)
    if seed_anchors:
        overlap = len(seed_anchors & cand_anchors)
        union = len(seed_anchors | cand_anchors)
        jaccard = overlap / union if union else 0.0
    else:
        overlap = 0
        jaccard = 0.0
    shape_match = bool(signature.shape) and signature.shape == ctx.shape
    statement_match = (
        bool(signature.node_kind) and signature.node_kind == ctx.kind)
    if not seed_anchors and not shape_match:
        return MatchResult(level='none', score=0.0)
    if not seed_anchors and len(signature.shape) < _SHAPE_ONLY_MIN_CHARS:
        return MatchResult(level='none', score=0.0,
                           reasons=('signature_too_weak',))
    context_sim = _context_similarity(
        signature.context_flags, ctx.context_flags)
    shape_sim = 1.0 if shape_match else (0.6 if statement_match else 0.0)
    score = 0.55 * jaccard + 0.30 * shape_sim + 0.15 * context_sim
    if ctx.guarded:
        score -= _GUARD_PENALTY
    shape_only = not seed_anchors and shape_match
    level = _level_of(
        shape_match, statement_match, jaccard, overlap, shape_only)
    reasons: list[str] = []
    if shape_match:
        reasons.append('shape_exact')
    if shape_only:
        reasons.append('shape_only')
    elif statement_match:
        reasons.append('statement_kind')
    if overlap:
        reasons.append(f'anchors:{overlap}')
    if ctx.guarded:
        reasons.append('local_guard')
    return MatchResult(level=level, score=max(score, 0.0),
                       anchor_overlap=overlap, anchor_jaccard=jaccard,
                       shape_match=shape_match, reasons=tuple(reasons))
def describe_signature(signature: FanoutSignature) -> str:
    if not isinstance(signature, FanoutSignature):
        return ''
    kind = _statement_kind(signature.shape) or signature.node_kind or '?'
    return (f'{signature.rule_family}<{kind}> anchors={len(signature.anchors)}'
            f'@{signature.seed_file}:{signature.seed_line}')
def _flag_of(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        return value.strip().lower() in _TRUE_TOKENS
    if isinstance(value, (int, float)):
        return value == 1
    return False
def _tuple_of_str(value: Any) -> tuple[str, ...]:
    return tuple(item for item in as_sequence(value)
                 if isinstance(item, str) and item)
_STATEMENT_NODE_KINDS = frozenset(
    node_type.__name__ for node_type in ast.stmt.__subclasses__())
def _signature_evidence_error(signature: FanoutSignature) -> str:
    if not signature.pattern_key:
        return 'signature_pattern_key_missing'
    if not signature.shape and not signature.anchors:
        return 'signature_evidence_empty'
    usable_anchors = {
        anchor for anchor in signature.anchors if _anchor_usable(anchor)}
    if signature.anchors and not usable_anchors:
        return 'signature_anchors_unusable'
    if not signature.shape and not signature.node_kind:
        return 'signature_node_kind_missing'
    shape_kind = _statement_kind(signature.shape)
    shape_possible = shape_kind in _STATEMENT_NODE_KINDS
    statement_possible = signature.node_kind in _STATEMENT_NODE_KINDS
    if (signature.anchors and not statement_possible
            and len(usable_anchors) < _EXACT_ANCHOR_MIN):
        return 'signature_node_kind_missing'
    if (not signature.anchors
            and len(signature.shape) < _SHAPE_ONLY_MIN_CHARS):
        return 'signature_too_weak'
    if signature.node_kind and not statement_possible:
        return 'signature_node_kind_invalid'
    if (not signature.anchors and signature.node_kind
            and shape_kind != signature.node_kind):
        return 'signature_evidence_unmatchable'
    if not signature.anchors and not shape_possible:
        return 'signature_evidence_unmatchable'
    seed_anchors = set(signature.anchors)
    if seed_anchors:
        max_overlap = len(usable_anchors)
        max_jaccard = max_overlap / len(seed_anchors)
        if _level_of(
                shape_possible, statement_possible,
                max_jaccard, max_overlap, False) == 'none':
            return 'signature_evidence_unmatchable'
    return ''
def signature_from_dict(payload: dict) -> FanoutSignature | None:
    data = dict_or_empty(payload)
    if not data:
        return None
    try:
        signature = FanoutSignature(
            rule_id=_family_text(data.get('rule_id')) or 'unknown',
            rule_family=_family_text(data.get('rule_family')) or 'unknown',
            pattern_key=str_or(data.get('pattern_key')),
            shape=str_or(data.get('shape')),
            anchors=_tuple_of_str(data.get('anchors')),
            scope_kind=str_or(data.get('scope_kind')) or _DEFAULT_SCOPE_KIND,
            context_flags=_tuple_of_str(data.get('context_flags')),
            seed_file=str_or(data.get('seed_file')),
            seed_line=int_or(data.get('seed_line'), 0),
            seed_locator=str_or(data.get('seed_locator')),
            seed_message=str_or(data.get('seed_message')),
            snippet=str_or(data.get('snippet')),
            degraded=_flag_of(data.get('degraded')),
            degrade_reason=str_or(data.get('degrade_reason')),
            node_kind=str_or(data.get('node_kind')),
            severity=(str_or(data.get('severity')).strip().upper()
                      or _DEFAULT_SEVERITY),
        )
    except (TypeError, ValueError) as exc:
        log_swallowed(__name__, exc, context='signature_from_dict')
        return None
    if not signature.degraded:
        evidence_error = _signature_evidence_error(signature)
        if evidence_error:
            signature.degraded = True
            signature.degrade_reason = evidence_error
    return signature
_LEVEL_RANK = {level: index for index, level in enumerate(MATCH_LEVELS)}
def match_level_rank(level: str) -> int:
    return _LEVEL_RANK.get(level, 99)
@dataclass
class FanoutOccurrence:
    occurrence_id: str
    family_id: str
    rule_id: str
    rule_family: str
    file: str
    abs_path: str
    line: int
    col: int
    end_line: int
    level: str
    score: float
    reasons: tuple[str, ...] = ()
    snippet: str = ''
    scope_kind: str = _DEFAULT_SCOPE_KIND
    qualname: str = ''
    guarded: bool = False
    node_kind: str = ''
    seed_locator: str = ''
    is_new_site: bool = False
    module_dependency_fanout: int | None = None
    module_governance_tier: str = FANOUT_TIER_UNKNOWN
    module_governance_level: str = ''
    module_governance_label: str = ''
    module_role: str = ''
    module_role_label: str = ''
    def to_dict(self) -> dict:
        return {
            'occurrence_id': self.occurrence_id,
            'family_id': self.family_id,
            'rule_id': self.rule_id,
            'rule_family': self.rule_family,
            'file': self.file,
            'abs_path': self.abs_path,
            'line': self.line,
            'col': self.col,
            'end_line': self.end_line,
            'level': self.level,
            'score': round(self.score, 4),
            'reasons': list(self.reasons),
            'snippet': self.snippet,
            'scope_kind': self.scope_kind,
            'qualname': self.qualname,
            'guarded': self.guarded,
            'node_kind': self.node_kind,
            'seed_locator': self.seed_locator,
            'is_new_site': self.is_new_site,
            'module_dependency_fanout': self.module_dependency_fanout,
            'module_governance_tier': self.module_governance_tier,
            'module_governance_level': self.module_governance_level,
            'module_governance_label': self.module_governance_label,
            'module_role': self.module_role,
            'module_role_label': self.module_role_label,
        }
@dataclass
class FanoutScanResult:
    occurrences: list[FanoutOccurrence] = field(default_factory=list)
    files_scanned: int = 0
    files_failed: int = 0
    errors: list[dict] = field(default_factory=list)
    duration_s: float = 0.0
    truncated_families: tuple[str, ...] = ()
    files: tuple[str, ...] = ()
    def to_dict(self) -> dict:
        return {
            'occurrences': [item.to_dict() for item in self.occurrences],
            'files_scanned': self.files_scanned,
            'files_failed': self.files_failed,
            'errors': list(self.errors),
            'duration_s': round(self.duration_s, 4),
            'truncated_families': list(self.truncated_families),
            'files': list(self.files),
        }
def _kind_set(kinds: Iterable[str] | None) -> set[str]:
    if kinds is None:
        return set()
    if isinstance(kinds, str):
        return {kinds} if kinds else set()
    try:
        items = list(kinds)
    except TypeError as exc:
        log_swallowed(__name__, exc, context='_kind_set')
        return set()
    return {item for item in items if isinstance(item, str) and item}
def _candidate_contexts(tree: ast.AST,
                        kinds: set[str]) -> Iterator[NodeContext]:
    parents = parent_map(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.stmt):
            continue
        if kinds and type(node).__name__ not in kinds:
            continue
        yield node_context_of(node, parents=parents)
def iter_file_contexts(source: str, path: str,
                       kinds: Iterable[str] | None = None) -> Iterator[NodeContext]:
    tree = parse_cached(source, path)
    yield from _candidate_contexts(tree, _kind_set(kinds))
def read_file_contexts(path: str, kinds: Iterable[str]) -> tuple[
        list[str], list[NodeContext]] | None:
    source = read_source(path)
    if source is None:
        return None
    return source.splitlines(), list(iter_file_contexts(source, path, kinds))
def build_signatures(seeds: Sequence[dict], skill_dir: str) -> tuple[
        list[FanoutSignature], list[dict]]:
    skill_dir = normalize_target_path(skill_dir)
    signatures: list[FanoutSignature] = []
    degraded: list[dict] = []
    for raw in as_sequence(seeds):
        finding = dict_or_empty(raw)
        if not finding:
            degraded.append({
                'seed': '',
                'reason': 'seed_payload_invalid',
                'description': f'<{type(raw).__name__}>',
            })
            continue
        file_path, _line = _finding_coords(
            finding, skill_dir=skill_dir)
        abs_path = file_path
        if file_path and not os.path.isabs(file_path):
            abs_path = os.path.join(skill_dir, file_path)
        source = read_source(abs_path) if abs_path else None
        signature = build_signature(
            finding,
            source=source,
            source_lines=source.splitlines() if source else None,
            skill_dir=skill_dir,
        )
        if signature.degraded:
            degraded.append({
                'seed': seed_key(finding),
                'reason': signature.degrade_reason,
                'description': describe_signature(signature),
            })
            continue
        signatures.append(signature)
    return signatures, degraded

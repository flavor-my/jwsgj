from __future__ import annotations

import argparse
import hashlib
import json
import logging
import os
import re
import tempfile
import time
from collections import Counter
from collections.abc import Callable, Iterator
from dataclasses import dataclass, field
from enum import Enum
from itertools import count
from pathlib import Path
from typing import Any, Self

from jwsgj.build_contract import (
    cli_boundary,
    dump_json_report_checked,
    fail_cli,
    finish_cli_command,
    json_text,
    load_json_file,
    run_cli_action,
)
from jwsgj.diag_types_defs import ContractViolationError
from jwsgj.diag_types_normalize import (
    FALSE_SIGNAL_TEXT,
    is_finite_num,
    timestamp_ms,
)
from jwsgj.engine_a3_silent_degrade import run_a3_silent_degrade
from jwsgj.log_config import log_swallowed, now_iso_seconds
from jwsgj.refactor_post_validation import (
    API_RETENTION_FLOOR,
    COPY_SUSPECT_SIMILARITY,
    DEFAULT_GUARD_STAGE,
    assess_honest_progress,
    check_lazy_loading,
    check_version_uniformity,
    collect_py_source_files,
    count_import_cycles,
    format_guard_report,
    run_guard,
)
from jwsgj.runtime_scope import (
    SCAN_IGNORE_DIRS,
    iter_prod_py_files,
)
from jwsgj.shared_cache import CacheNotWarmedError, get_warmed_cache

__all__ = [
    'ALL_CONSTRAINTS',
    'BOUNDARY_COMPLIANCE_VALUES',
    'COHESION_STRONG_SIGNAL',
    'CONSTRAINT_ALL_PY_ANALYZED',
    'CONSTRAINT_BACKUP_BEFORE_MODIFY',
    'CONSTRAINT_MERGE_ARGUMENT',
    'CONSTRAINT_MERGE_COHESION_ONLY',
    'CONSTRAINT_MIGRATION_DONE',
    'CONSTRAINT_MIGRATION_NO_RESIDUAL',
    'CONSTRAINT_NEXT_PHASE',
    'CONSTRAINT_NO_BATCH_FIX',
    'CONSTRAINT_NO_PATCH_FIX',
    'CONSTRAINT_NO_SIZE_ONLY_MERGE',
    'CONSTRAINT_NO_SIZE_ONLY_SPLIT',
    'CONSTRAINT_NO_SPLIT_AS_GOVERNANCE',
    'CONSTRAINT_PHASE_ORDER',
    'CONSTRAINT_PLAN_BEFORE_EXECUTE',
    'CONSTRAINT_REWRITE_DONE',
    'CONSTRAINT_REWRITE_PRECONDITIONS',
    'CONSTRAINT_STEP_VALIDATION',
    'FIX_APPROACH_ROOT_CAUSE',
    'FORBIDDEN_GOVERNANCE_METHODS',
    'GOVERNANCE_CONSTRAINTS',
    'GOVERNANCE_DECISION_KINDS',
    'GOVERNANCE_METHODS',
    'GOVERNANCE_METHOD_KEYWORDS',
    'GOVERNANCE_METHOD_LABELS',
    'GOVERNANCE_PRINCIPLES',
    'MERGE_COHESION_KEYWORDS',
    'MERGE_NET_BENEFIT_VALUES',
    'METHOD_COMPLIANCE_VALUES',
    'PHASE_ORDER',
    'REFACTOR_DISCIPLINE_COMMANDS',
    'SIX_CONSTRAINTS',
    'SPLIT_BOUNDARY_KEYWORDS',
    'TEST_CONFIG_FILES',
    'TEST_EXCLUDE_PATTERNS',
    'TEST_EXCLUDE_PREFIXES',
    'TEST_EXCLUDE_SUFFIXES',
    'BoundaryAnalysisResult',
    'DisciplineReport',
    'FileAnalysis',
    'MergeArgument',
    'ModuleBoundary',
    'RefactoringConstraint',
    'RefactoringPhase',
    'RefactoringRoute',
    'RefactoringRoutePlanner',
    'SplitMergeAction',
    'action_field',
    'approved_split_actions',
    'build_decision_record',
    'check_refactoring_discipline',
    'classify_governance_method',
    'cmd_assess_migration',
    'cmd_refactor_guard',
    'collect_modified_files',
    'count_executed_actions',
    'decision_target_key',
    'detect_forbidden_method',
    'effective_governance_action_type',
    'format_assessment_report',
    'governance_constraint_ids',
    'governance_proposal',
    'governance_review_projection',
    'governance_scope',
    'is_excluded_file',
    'is_governance_method',
    'is_split_exception_valid',
    'merge_argument_of',
    'merge_argument_payload',
    'migration_decoupling_errors',
    'normalize_executed_action_ids',
    'normalize_governance_method',
    'normalized_governance_action_type',
    'read_modified_files',
    'reconcile_governance_proposals',
    'register_refactor_discipline',
    'require_boundary_value',
    'require_deep_analysis',
    'require_route_value',
    'rewrite_split_to_governance',
    'suggest_governance_methods',
    'validate_merge_argument',
    'validate_refactoring_action',
]
_log = logging.getLogger(__name__)
_log.info("build_refactor_policy 已加载: %d 项导出", len(__all__))
_DECISION_SEQ = count()
METHOD_COMPLIANCE_VALUES: tuple[str, ...] = (
    "compliant",
    "rewrite_required",
    "not_applicable",
)
BOUNDARY_COMPLIANCE_VALUES: tuple[str, ...] = (
    "compliant",
    "violation",
    "unverified",
    "not_applicable",
)
_GOVERNANCE_ACTION_TYPES: tuple[str, ...] = (
    "governance",
    "split",
    "merge",
    "migrate",
)
_AMBIGUOUS_ACTION_TYPE = "ambiguous"
def _normalize_action_type(value: Any) -> str:
    if isinstance(value, str):
        return value.strip().lower()
    if not isinstance(value, (list, tuple, set, frozenset)):
        return ""
    items = [item.strip().lower() for item in value
             if isinstance(item, str) and item.strip()]
    if isinstance(value, (set, frozenset)):
        items.sort()
    unique_items = list(dict.fromkeys(items))
    if len(unique_items) > 1:
        return _AMBIGUOUS_ACTION_TYPE
    return unique_items[0] if unique_items else ""
def governance_scope(assessment: dict | None) -> bool:
    data = assessment if isinstance(assessment, dict) else {}
    action_type = _normalize_action_type(data.get("action_type"))
    return (
        _bool_field(data.get("governance_scope"), dirty_default=True)
        or action_type in _GOVERNANCE_ACTION_TYPES
        or action_type == _AMBIGUOUS_ACTION_TYPE
        or bool(data.get("governance_method")
                or data.get("governance_proposal"))
        or _present_merge_value(data.get("merge_argument"))
    )
def governance_proposal(assessment: dict | None,
                        proposal: dict | None = None) -> dict:
    if isinstance(proposal, dict):
        return proposal
    data = assessment if isinstance(assessment, dict) else {}
    inner = data.get("governance_proposal")
    if isinstance(inner, dict):
        merged = dict(data)
        merged.update(inner)
        return merged
    return dict(data)
def normalized_governance_action_type(data: dict | None) -> str:
    payload = data if isinstance(data, dict) else {}
    return _normalize_action_type(payload.get("action_type"))
def effective_governance_action_type(data: dict | None) -> str:
    payload = data if isinstance(data, dict) else {}
    declared = _normalize_action_type(payload.get("action_type"))
    if declared:
        return declared
    if _present_merge_value(payload.get("merge_argument")):
        return "merge"
    return "governance" if governance_scope(payload) else ""
GOVERNANCE_PRINCIPLES: tuple[dict[str, str], ...] = (
    {
        "principle_id": "GOV-P1",
        "title": "非拆分治理优先",
        "statement": (
            "复杂度治理优先通过简化逻辑、消除重复、收敛依赖、迁移代码、"
            "提取同模块内私有实现完成；禁止以拆分文件或模块为治理手段。"
        ),
    },
    {
        "principle_id": "GOV-P2",
        "title": "不拆分，合并须论证",
        "statement": (
            "原则上不拆分文件或模块；合并必须论证利大于弊，net_benefit "
            "为 positive 且决策写入留痕后方可执行。"
        ),
    },
    {
        "principle_id": "GOV-P3",
        "title": "模块边界与公共 API",
        "statement": (
            "跨模块调用只能使用目标模块/包对外导出的公共 API（声明 __all__ 时"
            "只认白名单，未声明时认非下划线公开名）；禁止直接导入其他模块的"
            "内部函数、类、常量、类型、状态与配置。"
        ),
    },
    {
        "principle_id": "GOV-P4",
        "title": "统一出入口与最小公共面",
        "statement": (
            "每个包只保留统一出入口（__init__.py 显式白名单导出），公共 "
            "API 最小化；禁止深层路径导入（from pkg.sub.module import ...）。"
        ),
    },
    {
        "principle_id": "GOV-P5",
        "title": "依赖规则机器守护",
        "statement": (
            "循环依赖与非法导入由 lint/依赖规则持续检查，不依赖人工复查；"
            "检测口径与验收口径同源。"
        ),
    },
    {
        "principle_id": "GOV-P6",
        "title": "迁移降耦而非搬移耦合",
        "statement": (
            "代码迁移的目标是降低耦合：迁移必须同时消除反向依赖或重复"
            "实现，原样搬移耦合视为未治理。"
        ),
    },
    {
        "principle_id": "GOV-P7",
        "title": "六项基线验收与回滚",
        "statement": (
            "每轮治理后对比基线：无新增循环依赖、跨模块非法导入为 0、"
            "公共 API 不膨胀、复杂度不劣化、测试全通过、合并决策有记录；"
            "任一不达标定向回滚并记录失败原因。"
        ),
    },
)
GOVERNANCE_CONSTRAINTS: list[dict[str, Any]] = [
    {
        "rule_id": "GOV-01",
        "name": "禁止以拆分文件/模块作为治理手段",
        "severity": "ERROR",
        "priority": 0,
        "description": (
            "复杂度治理不得通过拆分文件或模块完成。检测器输出拆分候选时，"
            "必须改写为简化逻辑/消除重复/收敛依赖/迁移代码/提取同模块内"
            "私有实现之一的治理建议；未改写的拆分提案一律退回。"
        ),
        "suggestion": (
            "先定位复杂度来源：重复实现→消除重复；耦合过多→收敛依赖；"
            "块间无关联→迁移到既有职责模块；函数过长→提取同模块私有实现；"
            "分支嵌套→简化逻辑。"
        ),
    },
    {
        "rule_id": "GOV-02",
        "name": "合并必须附带 pros/cons/net_benefit 论证",
        "severity": "ERROR",
        "priority": 0,
        "description": (
            "合并操作必须附带 pros（收益）、cons（代价与风险）、net_benefit "
            "三项论证，且 net_benefit 必须为 positive 才允许执行；论证与"
            "决策必须写入治理决策留痕（decision_id 可回查）。"
        ),
        "suggestion": (
            "pros/cons 各至少一条，cons 不得留空；net_benefit 取 "
            "positive/negative/neutral，非 positive 一律拒绝执行并销项留痕。"
        ),
    },
    {
        "rule_id": "GOV-03",
        "name": "跨模块仅可使用公共 API",
        "severity": "ERROR",
        "priority": 0,
        "description": (
            "跨模块调用只能使用目标模块/包对外导出的公共 API（声明 __all__ "
            "时只认白名单，未声明时认非下划线公开名）；禁止导入其他模块的"
            "内部函数、类、常量、类型、状态与配置。"
        ),
        "suggestion": (
            "目标符号未导出时，改为调用其公共入口；确需共享则把该符号"
            "提升为目标模块的显式导出并评估 API surface 影响。"
        ),
    },
    {
        "rule_id": "GOV-04",
        "name": "统一出入口与禁止深层路径导入",
        "severity": "ERROR",
        "priority": 0,
        "description": (
            "包内调用统一经包出入口（__init__.py 白名单导出）；禁止深层"
            "路径导入（from pkg.sub.module import internal_func / import "
            "pkg.sub.module）；公共 API 新增或删除导出符号必须显式声明并"
            "评估 API surface 影响。"
        ),
        "suggestion": (
            "把需要跨包使用的符号在最近一级包 __init__.py 的 __all__ 中"
            "登记为统一出入口；调用方只 from pkg.sub import symbol。"
        ),
    },
    {
        "rule_id": "GOV-05",
        "name": "迁移用于降耦而非搬移耦合",
        "severity": "ERROR",
        "priority": 0,
        "description": (
            "代码迁移必须降低耦合：迁移后不得保留原实现的转发桩、不得把"
            "同一组互相依赖的代码整体搬到新位置、不得引入新的反向依赖。"
        ),
        "suggestion": (
            "迁移前先断开反向依赖或消除重复实现，迁移后删除兼容桩并更新"
            "全部引用方导入源（R-10 无残留转发）。"
        ),
    },
    {
        "rule_id": "GOV-06",
        "name": "循环依赖与非法导入由依赖规则守护",
        "severity": "ERROR",
        "priority": 0,
        "description": (
            "循环依赖与非法导入必须由 lint/依赖规则持续检查，禁止仅靠"
            "人工评审；检测器口径与验收口径必须同源（同一扫描器、同一"
            "基线文件）。"
        ),
        "suggestion": (
            "接入 diag_module_topology 的边界扫描与环检测，"
            "由本模块执行六项验收；新增规则先登记 SSOT 再接入门禁，"
            "禁止在消费方复制判定逻辑。"
        ),
    },
    {
        "rule_id": "GOV-07",
        "name": "六项基线验收与定向回滚",
        "severity": "ERROR",
        "priority": 0,
        "description": (
            "每轮治理完成必须逐项确认：循环依赖数不高于基线、跨模块非法"
            "导入为 0、公共 API 不膨胀、复杂度不劣化、测试全部通过、合并"
            "决策有记录；任一不达标即定向回滚并记录失败原因。"
        ),
        "suggestion": (
            "治理前 capture_baseline，治理后 check_acceptance；失败项写入 "
            "governance_acceptance.jsonl 并按 rollback_id 执行定向回滚。"
        ),
    },
]
GOVERNANCE_METHODS: tuple[str, ...] = (
    "simplify_logic",
    "remove_duplication",
    "converge_dependency",
    "migrate_code",
    "extract_private_impl",
    "adjust_layer_boundary",
)
GOVERNANCE_METHOD_LABELS: dict[str, str] = {
    "simplify_logic": "简化逻辑",
    "remove_duplication": "消除重复",
    "converge_dependency": "收敛依赖",
    "migrate_code": "迁移代码",
    "extract_private_impl": "提取同模块内私有实现",
    "adjust_layer_boundary": "分层与边界调整",
}
_GOVERNANCE_METHOD_BY_LABEL = {
    label: method_id for method_id, label in GOVERNANCE_METHOD_LABELS.items()
}
FORBIDDEN_GOVERNANCE_METHODS: tuple[str, ...] = (
    "split_file",
    "split_module",
)
GOVERNANCE_METHOD_KEYWORDS: dict[str, tuple[str, ...]] = {
    "simplify_logic": (
        "简化逻辑", "简化分支", "降低复杂度", "减少嵌套", "扁平化",
        "simplify", "flatten", "reduce complexity", "early return",
    ),
    "remove_duplication": (
        "消除重复", "去重", "合并重复", "复用既有实现", "单一实现",
        "deduplicate", "duplication", "single implementation",
    ),
    "converge_dependency": (
        "收敛依赖", "减少依赖", "降低耦合", "统一入口", "收敛扇出",
        "converge", "decouple", "unify entry",
    ),
    "migrate_code": (
        "迁移代码", "迁到既有", "移动到既有", "归位到", "挪到既有模块",
        "migrate", "relocate", "move to existing",
    ),
    "extract_private_impl": (
        "提取私有", "提取同模块", "私有函数", "私有方法", "内部辅助函数",
        "extract private", "private helper",
    ),
    "adjust_layer_boundary": (
        "分层与边界调整", "分层调整", "边界调整", "调整依赖方向",
        "跨层依赖", "layer boundary", "adjust layer",
    ),
}
_FORBIDDEN_KEYWORDS: tuple[str, ...] = (
    *FORBIDDEN_GOVERNANCE_METHODS,
    "拆分为", "拆分文件", "拆分模块", "拆成", "抽出新文件", "新建模块",
    "新建文件", "独立成模块", "独立成文件", "另起文件", "分文件",
    "split file", "split module", "split into", "new module", "new file",
    "extract module", "extract into new",
)
MERGE_NET_BENEFIT_VALUES: tuple[str, ...] = ("positive", "negative", "neutral")
GOVERNANCE_DECISION_KINDS: tuple[str, ...] = (
    "merge",
    "governance",
    "boundary",
    "exception",
    "acceptance",
)
def governance_review_projection() -> tuple[
    list[dict[str, Any]], dict[str, Any]
]:
    dimensions = [
        {
            "key": "governance_method_compliance",
            "name": "治理手段合规性",
            "values": list(METHOD_COMPLIANCE_VALUES),
            "mandatory_when": (
                "action_type ∈ governance/split/merge/migrate，或 assessment "
                "声明 governance_scope=true / governance_method"),
            "rule_ids": ["GOV-01", "GOV-02", "GOV-05"],
            "hint": (
                "方案是否以拆分文件/模块为手段？是→必须改写为简化逻辑/"
                "消除重复/收敛依赖/迁移代码/提取同模块内私有实现并置 "
                "rewrite_required；合并须附 pros/cons/net_benefit=positive；"
                "迁移须证明降耦而非原样搬移"),
        },
        {
            "key": "boundary_compliance",
            "name": "边界合规性",
            "values": list(BOUNDARY_COMPLIANCE_VALUES),
            "mandatory_when": (
                "治理范围裁决；提供 fixed_source/proposed_imports 时强制"
                "复扫，无证据才可置 not_applicable"),
            "rule_ids": ["GOV-03", "GOV-04"],
            "hint": (
                "方案是否引入深层路径导入（from pkg.sub.module import ...）"
                "或跨模块内部符号导入？是→violation，必须改为包统一出入口"
                "（from pkg.sub import symbol）并显式登记 __all__；"
                "有证据但无法复核→unverified（不得批准）"),
        },
    ]
    governance = {
        "values": {
            "governance_method_compliance": list(METHOD_COMPLIANCE_VALUES),
            "boundary_compliance": list(BOUNDARY_COMPLIANCE_VALUES),
        },
        "scope": ("action_type ∈ governance/split/merge/migrate，或 "
                  "governance_scope=true，或声明 governance_method / "
                  "merge_argument；普通修复仅在提供 fixed_source 时做边界复扫"),
        "policy": (
            "1) 禁止以拆分文件/模块作为治理手段：split 提案必须改写为"
            "简化逻辑/消除重复/收敛依赖/迁移代码/提取同模块内私有实现，"
            "并置 governance_method_compliance=rewrite_required；"
            "2) 合并必须附 pros/cons/net_benefit 且 net_benefit=positive，"
            "否则 rewrite_required；"
            "3) 跨模块只能经包统一出入口，禁止深层路径导入与未导出内部"
            "符号导入，违反即 boundary_compliance=violation；"
            "4) 申报与复核取严：自报 compliant 而复核更差时以复核为准并退回；"
            "5) 批准类裁决要求两维均为 compliant/not_applicable，有证据但"
            "无法复核（unverified）一律阻断批准；"
            "6) 全部治理裁决经 ai_review_governance_review.record_review_verdict 写入 "
            "jinhua/ai_review_verdicts.jsonl，合并/治理/边界决策另写入 "
            "jinhua/governance_decisions.jsonl（decision_id 可回查）。"
        ),
        "ledger": "jinhua/governance_decisions.jsonl",
        "acceptance_ledger": "jinhua/governance_acceptance.jsonl",
        "baseline": "jinhua/governance_baseline.json",
        "acceptance": (
            "六项指标：循环依赖数不高于基线 / 跨模块非法导入为 0 / 公共 "
            "API 不膨胀 / 复杂度不劣化 / 测试全通过 / 合并决策有记录；"
            "任一不达标按 rollback_id 定向回滚并记录失败原因"
        ),
    }
    return dimensions, governance
def governance_constraint_ids() -> tuple[str, ...]:
    return tuple(item["rule_id"] for item in GOVERNANCE_CONSTRAINTS)
def normalize_governance_method(value: Any) -> str:
    if not isinstance(value, str):
        return ""
    token = value.strip()
    if not token:
        return ""
    lowered = token.lower()
    if lowered in GOVERNANCE_METHODS:
        return lowered
    label_hit = _GOVERNANCE_METHOD_BY_LABEL.get(token)
    if label_hit is not None:
        return label_hit
    hits = classify_governance_method(token)
    return hits[0] if hits else ""
def is_governance_method(value: Any) -> bool:
    return bool(normalize_governance_method(value))
def classify_governance_method(text: Any) -> tuple[str, ...]:
    if not isinstance(text, str) or not text.strip():
        return ()
    lowered = text.lower()
    hits = [
        method_id for method_id in GOVERNANCE_METHODS
        if any(_has_affirmative_keyword(lowered, kw.lower())
               for kw in GOVERNANCE_METHOD_KEYWORDS.get(method_id, ()))
    ]
    return tuple(hits)
_NEGATED_ACTION_PREFIX_RE = re.compile(
    r"(?:"
    r"(?:禁止|严禁|不得|不应|不要|不可|避免|无需|无须|"
    r"不能|无法|不会|不需要|没必要|不建议|不推荐|不宜|请勿|切勿|勿|"
    r"拒绝|反对|停止|放弃|"
    r"不(?:允许|准许|许可|许|准)?|未|非)"
    r"(?:\s*(?:以|通过|将|把|采用|使用|进行|再|直接|任意|随意|继续|是|并))*"
    r"\s*"
    r"|"
    r"\b(?:not|never|avoid|no|do\s+not|does\s+not|did\s+not|"
    r"must\s+not|should\s+not|cannot|can't|don't|doesn't|didn't|"
    r"shouldn't|mustn't)"
    r"(?:\s+(?:any|the|a|an|directly|simply|further))*\s*"
    r")$")
_NEGATED_ACTION_SCOPE_RE = re.compile(
    r"(?:禁止|严禁|不得|不应|不要|不可|避免|无需|无须|"
    r"不能|无法|不会|不需要|没必要|不建议|不推荐|不宜|请勿|切勿|勿|"
    r"拒绝|反对|停止|放弃|"
    r"(?:不(?:允许|准许|许可|许|准)?|未)"
    r"(?=\s*(?:以|通过|将|把|采用|使用|进行)))"
    r"(?:(?!改为|改成|建议|推荐|应当|应该|需要|而是|而要|而应|转而).){0,64}$")
_ACTION_CLAUSE_SPLIT_RE = re.compile(
    r"[,，;；。.!！？?\n\r]+|但|然而|\bbut\b|\bhowever\b")
def _has_affirmative_keyword(text: str, keyword: str) -> bool:
    for occurrence in re.finditer(re.escape(keyword), text):
        start = occurrence.start()
        for outer_keyword in _FORBIDDEN_KEYWORDS:
            if len(outer_keyword) <= len(keyword):
                continue
            for outer in re.finditer(re.escape(outer_keyword.lower()), text):
                if outer.start() <= start and occurrence.end() <= outer.end():
                    start = min(start, outer.start())
        prefix = _ACTION_CLAUSE_SPLIT_RE.split(text[:start])[-1]
        if (_NEGATED_ACTION_PREFIX_RE.search(prefix[-64:])
                or _NEGATED_ACTION_SCOPE_RE.search(prefix[-64:])):
            continue
        return True
    return False
_FORBIDDEN_SPLIT_VERB_RE = re.compile(
    r"(?<![a-z])split(?:ting|s)?(?![a-z])", re.IGNORECASE)

def _has_affirmative_split_verb(text: str) -> bool:
    for occurrence in _FORBIDDEN_SPLIT_VERB_RE.finditer(text):
        prefix = _ACTION_CLAUSE_SPLIT_RE.split(text[:occurrence.start()])[-1]
        if (_NEGATED_ACTION_PREFIX_RE.search(prefix[-64:])
                or _NEGATED_ACTION_SCOPE_RE.search(prefix[-64:])):
            continue
        return True
    return False

def detect_forbidden_method(text: Any) -> tuple[str, ...]:
    if not isinstance(text, str) or not text.strip():
        return ()
    lowered = text.lower()
    hits = tuple(
        kw for kw in _FORBIDDEN_KEYWORDS
        if _has_affirmative_keyword(lowered, kw.lower()))
    extra_hits: list[str] = []
    if (not any("split" in hit for hit in hits)
            and _has_affirmative_split_verb(lowered)):
        extra_hits.append("split")
    if (not any("拆分" in hit for hit in hits)
            and _has_affirmative_keyword(lowered, "拆分")):
        extra_hits.append("拆分")
    return (*hits, *extra_hits)
_MIGRATION_COUPLING_SIGNALS: tuple[str, ...] = (
    "原样搬移", "原样搬过去", "整段复制", "整体搬运", "copy as-is",
    "move as-is", "搬移耦合",
)
_MIGRATION_DECOUPLING_SIGNALS: tuple[str, ...] = (
    "断开", "切断", "移除旧依赖", "消除反向依赖", "减少依赖",
    "收敛依赖", "降低耦合", "降耦", "消除重复", "去重",
    "复用既有实现", "单一实现", "显式入参", "依赖注入",
    "decoupl", "remove dependency", "eliminate dependency",
    "dependency injection", "deduplicat", "eliminate duplication",
    "explicit parameter", "single implementation",
)
_MIGRATION_NEGATION_RE = re.compile(
    r"(?:(?:未能|不再|没有|并无|并未|不是|并非|不曾|不能|无法|"
    r"不会|不要|不允许|不得|禁止|未|没|无(?!论)|非(?!常)|"
    r"不(?!仅|只是|同|断|管|论))"
    r"|(?<![a-z])(?:not(?!\s+only\b)|never|without|no)(?![a-z]))"
    r".*$",
    re.IGNORECASE)
_MIGRATION_CLAUSE_BOUNDARY_RE = re.compile(
    r"[\n。！？!?；;，,.]|而是|但是|但|然而|不过|"
    r"(?<![a-z])(?:but|however)(?![a-z])",
    re.IGNORECASE)
_MIGRATION_POST_NEGATION_RE = re.compile(
    r"^(?:[a-z]+)?\s+(?:(?:is|are|was|were|be|been|being|has|have|had|"
    r"actually|really|still|also)\s+){0,6}"
    r"(?:not(?!\s+only\b)|never|no|"
    r"(?:is|are|was|were|has|have|had|do|does|did|can|could|will|would|"
    r"should|must|need)n['’]t|can['’]t|won['’]t)(?![a-z])"
    r"|^(?:(?:[\s的所并亦也都仍]|依然|仍然|实际上|实际|确实))*"
    r"(?:未能|不再|没有|并无|并未|不是|并非|不曾|不能|无法|不会|"
    r"不要|不允许|不得|禁止|未|没|无(?!论)|非(?!常)|"
    r"不(?!仅|只是|同|断|管|论))",
    re.IGNORECASE)
def _has_affirmative_signal(text: str, signals: tuple[str, ...]) -> bool:
    lowered = text.lower()
    for signal in signals:
        for match in re.finditer(re.escape(signal.lower()), lowered):
            prefix = lowered[:match.start()]
            clause = _MIGRATION_CLAUSE_BOUNDARY_RE.split(prefix)[-1]
            suffix = lowered[match.end():]
            following = _MIGRATION_CLAUSE_BOUNDARY_RE.split(suffix)[0]
            if (not _MIGRATION_NEGATION_RE.search(clause)
                    and not _MIGRATION_POST_NEGATION_RE.match(following)):
                return True
    return False
def migration_decoupling_errors(text: str) -> list[str]:
    violations: list[str] = []
    if not _has_affirmative_signal(text, _MIGRATION_DECOUPLING_SIGNALS):
        violations.append(
            "GOV-05：迁移缺少降耦证据；须明确切断/减少的旧依赖，"
            "或说明消除的重复实现，不能只声明变更代码位置")
    if _has_affirmative_signal(text, _MIGRATION_COUPLING_SIGNALS):
        violations.append(
            "GOV-05：迁移被描述为原样搬移/整段复制，未证明降耦")
    return violations
_LINES_PER_EXTRACT_UNIT = 50.0
_CC_PER_NESTING_UNIT = 10.0
def _signal_score(data: dict[str, Any], key: str) -> float:
    value = data.get(key, 0)
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return 0.0
    try:
        score = float(value)
    except (OverflowError, ValueError) as _swallow_e:
        log_swallowed(
            __name__, _swallow_e,
            context=f'_signal_score:{type(_swallow_e).__name__}')
        return 0.0
    return score if is_finite_num(score) else 0.0
def suggest_governance_methods(signals: dict[str, Any] | None = None) -> tuple[str, ...]:
    data = signals if isinstance(signals, dict) else {}
    scored: list[tuple[float, str]] = [
        (_signal_score(data, "duplication"), "remove_duplication"),
        (_signal_score(data, "coupling"), "converge_dependency"),
        (_signal_score(data, "unrelated_blocks"), "migrate_code"),
        (_signal_score(data, "max_function_lines") / _LINES_PER_EXTRACT_UNIT,
         "extract_private_impl"),
        ((_signal_score(data, "nesting_depth")
          + _signal_score(data, "complexity") / _CC_PER_NESTING_UNIT),
         "simplify_logic"),
    ]
    positive = [(score, method) for score, method in scored if score > 0]
    if not positive:
        return GOVERNANCE_METHODS
    positive.sort(key=lambda item: (-item[0], GOVERNANCE_METHODS.index(item[1])))
    return tuple(method for _score, method in positive)
_PLACEHOLDER_VALUES: frozenset[str] = frozenset({"无", "none", "n/a", "-"})
_MERGE_ARGUMENT_FIELDS: tuple[tuple[str, Any], ...] = (
    ("pros", ()),
    ("cons", ()),
    ("net_benefit", ""),
    ("risk", ""),
    ("decision", ""),
)
_MERGE_ARGUMENT_DEFAULTS: dict[str, Any] = dict(_MERGE_ARGUMENT_FIELDS)
_NON_HUMAN_APPROVERS: frozenset[str] = frozenset({
    "", "ai", "assistant", "agent", "auto",
    "system", "bot", "automation", "ci",
}) | _PLACEHOLDER_VALUES | frozenset({"tbd", "待定", "unknown", "null"})
_NON_HUMAN_IDENTITY_MARKERS: tuple[str, ...] = (
    "人工智能", "智能体", "机器人", "助手", "自动",
)
def _as_str_tuple(value: Any) -> tuple[str, ...]:
    if isinstance(value, str):
        text = value.strip()
        return (text,) if text else ()
    if not isinstance(value, (list, tuple, set, frozenset)):
        return ()
    items = [item.strip() for item in value
             if isinstance(item, str) and item.strip()]
    return tuple(sorted(items) if isinstance(value, (set, frozenset)) else items)
class MergeArgument:
    __slots__ = ("cons", "decision", "net_benefit", "pros", "risk")
    def __init__(self, pros: Any = _MERGE_ARGUMENT_DEFAULTS["pros"],
                 cons: Any = _MERGE_ARGUMENT_DEFAULTS["cons"],
                 net_benefit: Any = _MERGE_ARGUMENT_DEFAULTS["net_benefit"],
                 risk: Any = _MERGE_ARGUMENT_DEFAULTS["risk"],
                 decision: Any = _MERGE_ARGUMENT_DEFAULTS["decision"]) -> None:
        self.pros: tuple[str, ...] = _as_str_tuple(pros)
        self.cons: tuple[str, ...] = _as_str_tuple(cons)
        self.net_benefit: str = (
            net_benefit.strip().lower()
            if isinstance(net_benefit, str) else "")
        self.risk: str = risk.strip() if isinstance(risk, str) else ""
        self.decision: str = (
            decision.strip() if isinstance(decision, str) else "")
    def validate(self) -> tuple[bool, list[str]]:
        return validate_merge_argument(
            self.pros, self.cons, self.net_benefit, self.risk)
    def as_dict(self) -> dict[str, Any]:
        data = {
            name: getattr(self, name)
            for name, _default in _MERGE_ARGUMENT_FIELDS
        }
        data["pros"] = list(self.pros)
        data["cons"] = list(self.cons)
        return data
def _present_merge_value(value: Any) -> bool:
    if value is None:
        return False
    if isinstance(value, MergeArgument):
        return any(
            _present_merge_value(getattr(value, name, None))
            for name, _default in _MERGE_ARGUMENT_FIELDS)
    if isinstance(value, str):
        return bool(value.strip())
    if isinstance(value, (list, tuple, set, frozenset, dict)):
        return bool(value)
    return True
def merge_argument_payload(data: Any) -> dict[str, Any]:
    proposal = data if isinstance(data, dict) else {}
    nested = proposal.get("merge_argument")
    if isinstance(nested, dict):
        inner = nested
    elif nested is None:
        inner = {}
    else:
        inner = {name: action_field(nested, name, None)
                 for name, _default in _MERGE_ARGUMENT_FIELDS}
    payload: dict[str, Any] = {}
    for name, default in _MERGE_ARGUMENT_FIELDS:
        outer = proposal.get(name)
        if _present_merge_value(outer):
            payload[name] = outer
            continue
        inner_value = inner.get(name)
        payload[name] = (inner_value if _present_merge_value(inner_value)
                         else default)
    return payload
def _placeholder_only(items: tuple[str, ...]) -> bool:
    return bool(items) and all(
        item.strip().lower() in _PLACEHOLDER_VALUES for item in items)
def _merge_presence_errors(pros: tuple[str, ...],
                           cons: tuple[str, ...]) -> list[str]:
    errors: list[str] = []
    for name, items, tail in (
            ("pros", pros, "至少给出 1 条具体收益"),
            ("cons", cons, "必须列出代价与风险，不得只写收益")):
        if not items:
            errors.append(f"合并论证缺失 {name}：{tail}")
        elif _placeholder_only(items):
            errors.append(f"{name} 不得以「无」占位：{tail}")
    return errors
def _merge_benefit_errors(net_benefit: Any) -> list[str]:
    benefit = (net_benefit.strip().lower()
               if isinstance(net_benefit, str) else "")
    if benefit not in MERGE_NET_BENEFIT_VALUES:
        return [
            ("net_benefit 非法：须为 positive/negative/neutral，实际为 "
             f"{net_benefit!r}"),
        ]
    if benefit != "positive":
        return [
            f"net_benefit={benefit}：合并仅在净收益为正（positive）时允许执行"]
    return []
def _merge_risk_errors(risk: Any) -> list[str]:
    if isinstance(risk, str) and risk.strip().lower() in _PLACEHOLDER_VALUES:
        return ["risk 不得以「无」占位：至少说明一项可观测风险"]
    return []
def validate_merge_argument(
        pros: Any, cons: Any, net_benefit: Any,
        risk: Any = _MERGE_ARGUMENT_DEFAULTS["risk"],
) -> tuple[bool, list[str]]:
    errors = [
        *_merge_presence_errors(_as_str_tuple(pros), _as_str_tuple(cons)),
        *_merge_benefit_errors(net_benefit),
        *_merge_risk_errors(risk),
    ]
    return (not errors, errors)
def _as_str_list(value: Any) -> list[str]:
    return list(_as_str_tuple(value))
def _clean_text(value: Any) -> str:
    if isinstance(value, str):
        return value.strip()
    if isinstance(value, (bytes, os.PathLike)):
        try:
            return os.fsdecode(value).strip()
        except (TypeError, ValueError) as _swallow_e:
            log_swallowed(
                __name__, _swallow_e,
                context=f'_clean_text:{type(_swallow_e).__name__}')
            return ""
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        return str(value)
    return ""
def _normalize_fix_approach(value: Any) -> str:
    return _clean_text(value).lower()
_TRUE_TEXT = frozenset({"true", "1", "yes", "y", "on"})
_FALSE_TEXT = frozenset(FALSE_SIGNAL_TEXT | {"n", "off"})
def _bool_field(
    value: Any, *, default: bool = False,
    dirty_default: bool | None = None,
) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        return value != 0
    if isinstance(value, str):
        token = value.strip().lower()
        if token in _TRUE_TEXT:
            return True
        if token in _FALSE_TEXT:
            return False
    if value is None:
        return default
    return default if dirty_default is None else dirty_default
def _first_present(source: dict, *keys: str) -> str:
    for key in keys:
        text = _clean_text(source.get(key))
        if text:
            return text
    return ""
def _exception_parts(action: Any) -> tuple[str, str, str]:
    exc = action_field(action, "governance_exception", "")
    if isinstance(exc, dict):
        return (
            _clean_text(exc.get("rationale")),
            _clean_text(exc.get("approved_by")).lower(),
            _first_present(exc, "decision_id", "record_id"),
        )
    return (
        _clean_text(exc),
        _clean_text(action_field(action, "exception_approved_by", "")).lower(),
        _clean_text(action_field(action, "governance_decision_id", "")),
    )
_APPROVER_TOKEN_SPLIT = re.compile(r"[^0-9a-z\u4e00-\u9fff]+")
_APPROVER_SCRIPT_BOUNDARY = re.compile(
    r"(?<=[0-9a-z])(?=[\u4e00-\u9fff])|(?<=[\u4e00-\u9fff])(?=[0-9a-z])")
_AUTOMATION_TOKEN_RE = re.compile(
    r"^(?:ai|bot|agent|system|auto|assistant|ci)(?:[-_]?\d+|[-_].*)?$")
def _is_human_approver(approved_by: str) -> bool:
    text = approved_by.strip().lower()
    if (not text or text in _NON_HUMAN_APPROVERS
            or any(marker in text for marker in _NON_HUMAN_IDENTITY_MARKERS)):
        return False
    segmented = _APPROVER_SCRIPT_BOUNDARY.sub(" ", text)
    tokens = [token for token in _APPROVER_TOKEN_SPLIT.split(segmented)
              if token]
    return not any(
        token in _NON_HUMAN_APPROVERS or _AUTOMATION_TOKEN_RE.match(token)
        for token in tokens)
def is_split_exception_valid(action: Any) -> bool:
    rationale, approved_by, decision_id = _exception_parts(action)
    if not rationale or not decision_id:
        return False
    return _is_human_approver(approved_by)
def rewrite_split_to_governance(action: Any) -> dict[str, Any]:
    source_files = _as_str_list(action_field(action, "source_files", []))
    code_elements = _as_str_list(action_field(action, "code_elements", []))
    reason = _clean_text(action_field(action, "reason", ""))
    justification = _clean_text(
        action_field(action, "boundary_justification", ""))
    original_reason = "；".join(part for part in (reason, justification) if part)
    methods = suggest_governance_methods(
        {"unrelated_blocks": len(code_elements)})
    labels = "、".join(GOVERNANCE_METHOD_LABELS[m] for m in methods)
    return {
        "action_type": "governance",
        "rewrite_from": "split",
        "source_files": source_files,
        "target_files": [],
        "code_elements": code_elements,
        "governance_method": list(methods),
        "governance_method_labels": labels,
        # R-15 的 _governance_method_declared 会对 reason/description/
        # boundary_justification 做 affirmative 禁用手段扫描；改写说明本身
        # 若以“拆分候选”开头会被判为 affirmatively 使用拆分手段，导致治理项
        # 永远无法通过 SPLIT_MERGE 前置门禁。原检测文本已完整保留在
        # original_reason（该字段不参与扫描），故 reason 只陈述治理语义。
        "reason": (
            "检测候选按 GOV-01 改写为既有模块内治理："
            f"优先{labels}；原检测结论保留于 original_reason"
        ),
        "boundary_justification": (
            "不新增文件/模块边界，仅在既有模块内降低复杂度；"
            "处置后以六项基线验收复核"
        ),
        "original_reason": original_reason,
        "is_size_based": False,
    }
def build_decision_record(
        kind: str, target: Any, payload: dict[str, Any] | None = None,
        decision: str = "", rationale: str = "",
        approved_by: str = "", skill_dir: str = "") -> dict[str, Any]:
    kind_text = _clean_text(kind)
    if kind_text not in GOVERNANCE_DECISION_KINDS:
        _log.warning("治理决策 kind 不在值域内（按原值写入）: %r", kind)
    at_ts = timestamp_ms()
    body = {
        "kind": kind_text,
        "target": _clean_text(target),
        "decision": _clean_text(decision),
        "rationale": _clean_text(rationale),
        "approved_by": _clean_text(approved_by),
        "payload": payload if isinstance(payload, dict) else {},
        "skill_dir": _clean_text(skill_dir),
    }
    nonce = f"{os.getpid()}:{next(_DECISION_SEQ)}:{time.time_ns()}"
    digest = hashlib.sha256(
        json.dumps(dict(body, at_ts=at_ts, nonce=nonce),
                   ensure_ascii=False, sort_keys=True,
                   default=str).encode("utf-8")).hexdigest()[:16]
    body["decision_id"] = f"GOVD-{digest}"
    body["at"] = now_iso_seconds()
    body["at_ts"] = at_ts
    body["trace_version"] = 1
    return body
def _escapes_root(rel: str) -> bool:
    return rel.split(os.sep, maxsplit=1)[0] == ".."
def _slash_key(path_text: str) -> str:
    normalized = (os.path.normcase(os.path.normpath(path_text))
                  if path_text else "")
    return normalized.replace(os.sep, "/")
def decision_target_key(target: Any, skill_dir: str = "") -> str:
    text = _clean_text(target)
    if not text:
        return ""
    skill_root = _clean_text(skill_dir)
    if skill_root and os.path.isabs(text):
        try:
            rel = os.path.relpath(text, skill_root)
        except ValueError as _swallow_e:
            log_swallowed(__name__, _swallow_e, context='decision_target_key:ValueError')
            return _slash_key(text)
        if not _escapes_root(rel):
            return _slash_key(rel)
    return _slash_key(text)
def action_field(action: Any, name: str, default: Any = None) -> Any:
    if isinstance(action, dict):
        return action.get(name, default)
    return getattr(action, name, default)
def merge_argument_of(action: Any) -> MergeArgument:
    if isinstance(action, dict):
        raw = action
    else:
        raw = {
            name: action_field(action, name, None)
            for name, _default in _MERGE_ARGUMENT_FIELDS
        }
        raw["merge_argument"] = action_field(action, "merge_argument", None)
    payload = merge_argument_payload(raw)
    return MergeArgument(
        pros=payload["pros"],
        cons=payload["cons"],
        net_benefit=payload["net_benefit"],
        risk=payload["risk"],
        decision=payload["decision"] or action_field(action, "reason", ""))
SIX_CONSTRAINTS: dict[str, str] = {
    "version_unified": "所有模块使用同一版本号",
    "zero_lazy_loading": "所有 import 在模块顶部直接完成",
    "zero_degraded": "不保留 _degraded/fallback/try-except ImportError",
    "zero_circular_deps": "严格分层,下层不导入上层",
    "rewrite_not_copy": "逐文件重写,不复制粘贴",
    "no_regression": "公开 API 覆盖度 >= 90%",
}
@dataclass
class DisciplineReport:
    constraints_checked: int = len(SIX_CONSTRAINTS)
    compliant: bool = False
    compliance_score: int = 0
    constraint_results: dict[str, dict[str, Any]] = field(default_factory=dict)
    violations: list[str] = field(default_factory=list)
    recommendations: list[str] = field(default_factory=list)
    verdict: str = "UNKNOWN"
    generated_at: float = 0.0
    def to_dict(self) -> dict[str, Any]:
        return {
            "constraints_checked": self.constraints_checked,
            "compliant": self.compliant,
            "compliance_score": self.compliance_score,
            "constraint_results": self.constraint_results,
            "violations": self.violations,
            "recommendations": self.recommendations,
            "verdict": self.verdict,
            "generated_at": self.generated_at,
        }
def _constraint_row(passed: bool, detail: str, key: str) -> dict[str, Any]:
    return {"desc": SIX_CONSTRAINTS.get(key, key),
            "passed": passed, "detail": detail}
def _gate_fail_precheck(report: DisciplineReport, new_dir: str) -> bool:
    _gate_fail_detail: str | None = None
    if not os.path.isdir(new_dir):
        _gate_fail_detail = f"目标目录不存在: {new_dir!r}"
    else:
        try:
            _has_py = bool(collect_py_source_files(new_dir))
        except Exception as _scan_exc:  # noqa: BLE001
            log_swallowed(
                __name__, _scan_exc,
                context=f'_gate_fail_precheck:{type(_scan_exc).__name__}')
            _gate_fail_detail = f"目标目录扫描失败: {_scan_exc}"
        else:
            if not _has_py:
                _gate_fail_detail = (
                    "目标目录无 .py 文件（迁移未开始或路径错误）: "
                    f"{new_dir!r}")
    if _gate_fail_detail is None:
        return False
    for _key in SIX_CONSTRAINTS:
        report.constraint_results[_key] = _constraint_row(
            False, _gate_fail_detail, _key)
    report.violations.append(f"[gate] {_gate_fail_detail}")
    report.recommendations.append("确认迁移目标目录路径后重跑门禁")
    report.constraints_checked = len(report.constraint_results)
    report.compliance_score = 0
    report.compliant = False
    report.verdict = "VIOLATIONS_FOUND"
    _log.warning(
        "[Discipline] check_refactoring_discipline 门禁前置失败: %s",
        _gate_fail_detail)
    return True
def _same_dir_precheck(report: DisciplineReport, old_dir: str,
                       new_dir: str) -> bool:
    if not old_dir or not new_dir:
        return False
    try:
        same_dir = (os.path.normcase(os.path.realpath(old_dir))
                    == os.path.normcase(os.path.realpath(new_dir)))
    except (OSError, ValueError) as _exc:
        log_swallowed(
            __name__, _exc,
            context=f'_same_dir_precheck:{type(_exc).__name__}')
        return False
    if not same_dir:
        return False
    _same_detail = f"旧目录与新目录相同，自比自不可作为迁移证据: {new_dir!r}"
    for _key in SIX_CONSTRAINTS:
        report.constraint_results[_key] = _constraint_row(
            False, _same_detail, _key)
    report.violations.append(f"[gate] {_same_detail}")
    report.recommendations.append(
        "提供独立的旧版目录与迁移目标目录后重跑门禁")
    report.constraints_checked = len(report.constraint_results)
    report.compliance_score = 0
    report.compliant = False
    report.verdict = "VIOLATIONS_FOUND"
    _log.warning(
        "[Discipline] check_refactoring_discipline 门禁前置失败: %s",
        _same_detail)
    return True

def _constraint_outcome(problems, fail_detail: str, ok_detail: str | None,
                        advice: str) -> tuple[bool, str, str]:
    if problems:
        return False, fail_detail, advice
    return True, fail_detail if ok_detail is None else ok_detail, ""
def _run_c_version_unified(new_dir: str) -> tuple[bool, str, str]:
    raw_entries = check_version_uniformity(new_dir)
    return _constraint_outcome(
        raw_entries,
        f"{len(raw_entries)} 个文件版本号不一致",
        "全部模块版本号一致",
        "统一各模块 __version__ 到同一版本号")
def _run_c_lazy_loading(new_dir: str) -> tuple[bool, str, str]:
    lazy_issues = check_lazy_loading(new_dir)
    return _constraint_outcome(
        lazy_issues,
        f"{len(lazy_issues)} 处惰性加载/降级残留",
        "无惰性加载残留（import 均在模块顶部）",
        "将函数内 import 提升至模块顶部，移除 _lazy_/_degraded/fallback 残留")
def _run_c_zero_degraded(new_dir: str) -> tuple[bool, str, str]:
    _sd_cache = get_warmed_cache(new_dir)
    sd = run_a3_silent_degrade(new_dir, cache=_sd_cache)
    if sd.get("status") == "error":
        return (False,
                str(sd.get("summary") or "静默降级检测引擎异常"),
                "修复静默降级检测引擎后重跑门禁")
    sd_count = int(sd.get("findings_count") or 0)
    return _constraint_outcome(
        sd_count,
        f"{sd_count} 处静默降级候选（吞异常/伪 pass）",
        "无静默降级模式",
        "为宽泛 except 补日志与显式降级标记，或收窄异常类型")
def _run_c_zero_circular(new_dir: str) -> tuple[bool, str, str]:
    cycle_count = count_import_cycles(get_warmed_cache(new_dir))
    return _constraint_outcome(
        cycle_count,
        f"{cycle_count} 个循环依赖环",
        "模块依赖图无环",
        "收敛依赖消环：环内共享部分下沉到既有下层模块或经包入口注入"
        "（GOV-01 禁止新建模块/拆分消环），下层不得导入上层")
_CONSTRAINT_RUNNERS = (
    ("version_unified", _run_c_version_unified,
     "版本统一性检查器异常", "修复检查器异常后重跑门禁"),
    ("zero_lazy_loading", _run_c_lazy_loading,
     "惰性加载检查器异常", "修复惰性加载检查器后重跑门禁"),
    ("zero_degraded", _run_c_zero_degraded,
     "静默降级检测器异常", "修复静默降级检测引擎后重跑门禁"),
    ("zero_circular_deps", _run_c_zero_circular,
     "循环依赖检测器异常", "修复依赖分析引擎后重跑门禁"),
)
def _record_constraint(report: DisciplineReport, key: str, passed: bool,
                       detail: str, recommendation: str = "") -> None:
    report.constraint_results[key] = _constraint_row(passed, detail, key)
    if not passed:
        report.violations.append(
            f"[{key}] {SIX_CONSTRAINTS.get(key, key)}: {detail}")
        if recommendation:
            report.recommendations.append(recommendation)
def _run_old_new_constraints(old_dir: str, new_dir: str,
                             report: DisciplineReport) -> None:
    if old_dir and os.path.isdir(old_dir):
        try:
            progress = assess_honest_progress(old_dir, new_dir)
            copy_suspects = list(progress.copy_suspects)
            code_retention = progress.code_retention
            api_retention = progress.api_retention
            if (not is_finite_num(code_retention)
                    or not is_finite_num(api_retention)):
                raise ValueError(
                    "新旧对比评估器返回非有限留存率: "
                    f"code={code_retention!r}, api={api_retention!r}")
            copy_detail = (f"{len(copy_suspects)} 个文件文本相似度>"
                           f"{COPY_SUSPECT_SIMILARITY:.0%}（复制嫌疑）")
            copy_ok_detail = (
                f"平均文本相似度 {code_retention:.1%}，无复制嫌疑")
            api_failed = api_retention < API_RETENTION_FLOOR
            api_detail = (f"公开 API 覆盖度 {api_retention:.1%}"
                          f"（红线 {API_RETENTION_FLOOR:.0%}）")
        except CacheNotWarmedError:
            raise
        except Exception as exc:  # noqa: BLE001
            _log.warning("[rewrite_not_copy/no_regression] 评估器异常: %s",
                           exc, exc_info=True)
            _hp_detail = f"新旧对比评估器异常: {exc}"
            _record_constraint(report, "rewrite_not_copy", False, _hp_detail,
                               "修复进度评估器后重跑门禁")
            _record_constraint(report, "no_regression", False, _hp_detail,
                               "修复进度评估器后重跑门禁")
        else:
            _record_constraint(
                report, "rewrite_not_copy", *_constraint_outcome(
                    copy_suspects, copy_detail, copy_ok_detail,
                    "对复制嫌疑文件按新版架构逐文件重写而非原样搬运"))
            _record_constraint(
                report, "no_regression", *_constraint_outcome(
                    api_failed, api_detail, None,
                    "回填丢失的公开 API，或经评估确认删除并记录原因"))
    else:
        _missing_old_detail = f"旧目录不可用，缺少新旧对比证据: {old_dir!r}"
        _missing_old_advice = "提供有效旧目录后重跑门禁"
        _record_constraint(report, "rewrite_not_copy", False,
                           _missing_old_detail, _missing_old_advice)
        _record_constraint(report, "no_regression", False,
                           _missing_old_detail, _missing_old_advice)
def _run_constraint_table(report: DisciplineReport, new_dir: str) -> None:
    for _key, _runner, _err_prefix, _err_rec in _CONSTRAINT_RUNNERS:
        try:
            _passed, _detail, _rec = _runner(new_dir)
        except CacheNotWarmedError:
            raise
        except Exception as exc:  # noqa: BLE001
            _log.warning("[%s] 检查器异常: %s", _key, exc, exc_info=True)
            _record_constraint(report, _key, False,
                               f"{_err_prefix}: {exc}", _err_rec)
        else:
            _record_constraint(report, _key, _passed, _detail, _rec)
def _finalize_discipline(
    report: DisciplineReport, old_dir: str, new_dir: str,
) -> None:
    for key in SIX_CONSTRAINTS:
        if key not in report.constraint_results:
            _record_constraint(
                report, key, False, "约束未执行，缺少判定证据",
                "恢复该约束执行后重跑门禁")
    passed_count = sum(1 for r in report.constraint_results.values()
                       if r["passed"])
    report.constraints_checked = len(report.constraint_results)
    report.compliance_score = round(100 * passed_count
                                    / max(report.constraints_checked, 1))
    report.compliant = passed_count == report.constraints_checked
    report.verdict = "COMPLIANT" if report.compliant else "VIOLATIONS_FOUND"
    if report.compliant:
        _log.info("[Discipline] check_refactoring_discipline 合规: new=%s old=%s "
                    "compliance_score=%d 约束通过=%d/%d 违规=0",
                    new_dir, old_dir, report.compliance_score,
                    passed_count, report.constraints_checked)
    else:
        _log.warning("[Discipline] check_refactoring_discipline 检出违规: "
                       "new=%s old=%s compliance_score=%d 约束通过=%d/%d "
                       "违规=%d 建议数=%d",
                       new_dir, old_dir, report.compliance_score,
                       passed_count, report.constraints_checked,
                       len(report.violations), len(report.recommendations))
def check_refactoring_discipline(old_dir: str, new_dir: str) -> DisciplineReport:
    report = DisciplineReport(generated_at=time.time())
    _log.info("check_refactoring_discipline: 开始 old=%s new=%s", old_dir, new_dir)
    if _gate_fail_precheck(report, new_dir):
        return report
    if _same_dir_precheck(report, old_dir, new_dir):
        return report
    _run_constraint_table(report, new_dir)
    _run_old_new_constraints(old_dir, new_dir, report)
    _finalize_discipline(report, old_dir, new_dir)
    return report
_ASSESS_FILE_LIST_LIMIT = 8
def _elided_file_lines(label: str, files: list[str]) -> list[str]:
    if not files:
        return []
    shown = files[:_ASSESS_FILE_LIST_LIMIT]
    suffix = "…" if len(files) > _ASSESS_FILE_LIST_LIMIT else ""
    return [f"  {label}: {', '.join(shown)}{suffix}"]
def format_assessment_report(progress, discipline) -> str:
    lines = [
        "═" * 72,
        "诚实进度评估（骨架 vs 真实完成）",
        "═" * 72,
        str(progress.honest_assessment),
    ]
    lines += _elided_file_lines("骨架文件（过半函数为空桩）",
                                progress.skeleton_files)
    lines += _elided_file_lines("未迁移文件", progress.pending_files)
    lines.append("")
    lines.append("═" * 72)
    lines.append(f"六项重构约束纪律门禁 — {discipline.verdict} "
                 f"({discipline.compliance_score}/100)")
    lines.append("═" * 72)
    for key, res in discipline.constraint_results.items():
        mark = "PASS" if res["passed"] else "FAIL"
        lines.append(f"  [{mark}] {key}: {res['desc']} — {res['detail']}")
    lines.extend(f"  建议: {rec}" for rec in discipline.recommendations)
    return "\n".join(lines)
def _require_dir_pair(args: argparse.Namespace, cli_tag: str) -> tuple[str, str]:
    old_dir = getattr(args, "old", "")
    new_dir = getattr(args, "new", "")
    if (not old_dir or not new_dir
            or not os.path.isdir(old_dir) or not os.path.isdir(new_dir)):
        fail_cli(cli_tag,
                 f"--old/--new 目录必须存在: {old_dir!r} / {new_dir!r}",
                 code=2)
    return old_dir, new_dir
def _load_rename_map_arg(args: argparse.Namespace, cli_tag: str) -> dict:
    path = getattr(args, "rename_map", "")
    if not path:
        return {}
    data = load_json_file(cli_tag, path, "--rename-map 文件不存在",
                          "--rename-map 读取失败", code=2)
    if not isinstance(data, dict):
        fail_cli(cli_tag,
                 "--rename-map 必须是 JSON 对象（旧模块名 -> 新模块名）",
                 code=2)
    return data
@cli_boundary("refactor-guard", "重构守护命令失败")
def cmd_refactor_guard(args: argparse.Namespace) -> None:
    _t0 = time.monotonic()
    old_dir, new_dir = _require_dir_pair(args, "refactor-guard")
    stage = getattr(args, "stage", DEFAULT_GUARD_STAGE)
    rename_map = _load_rename_map_arg(args, "refactor-guard")
    result = run_cli_action(
        "refactor-guard", "重构守护执行异常", run_guard, old_dir, new_dir, stage,
        rename_map=rename_map,
        verbose=getattr(args, "verbose", False), code=2)
    if getattr(args, "json", False):
        print(json_text(result))
    else:
        print(format_guard_report(result))
    guard_passed = result.get("passed") is True
    _violations = result.get("violations", [])
    violations = (len(_violations) if isinstance(_violations, (list, tuple))
                  else 0)
    finish_cli_command(
        "refactor-guard", "cmd_refactor_guard", _t0,
        ok=guard_passed, outcome="passed" if guard_passed else "blocked",
        message=f"守护判定: {'通过' if guard_passed else '阻断'}"
                f"（违规 {violations} 项）",
        run_fields={"violations": violations})
def _assess_migration_pair(old_dir: str, new_dir: str) -> tuple[Any, Any]:
    return (assess_honest_progress(old_dir, new_dir),
            check_refactoring_discipline(old_dir, new_dir))
@cli_boundary("assess-migration", "迁移评估命令失败")
def cmd_assess_migration(args: argparse.Namespace) -> None:
    _t0 = time.monotonic()
    old_dir, new_dir = _require_dir_pair(args, "assess-migration")
    progress, discipline = run_cli_action(
        "assess-migration", "迁移评估执行异常", _assess_migration_pair,
        old_dir, new_dir, code=2)
    output_path = getattr(args, "output", None)
    as_json = bool(getattr(args, "json", False))
    payload: dict | None = None
    if as_json or output_path:
        payload = {"honest_progress": progress.to_dict(),
                   "discipline": discipline.to_dict()}
    if output_path:
        dump_json_report_checked(output_path, payload, "assess-migration")
    elif as_json:
        print(json_text(payload))
    else:
        print(format_assessment_report(progress, discipline))
    finish_cli_command(
        "assess-migration", "cmd_assess_migration", _t0,
        ok=discipline.compliant,
        outcome="compliant" if discipline.compliant else "violation",
        message=(f"纪律门禁: {discipline.verdict}"
                 f"（合规分 {discipline.compliance_score}/100）"),
        run_fields={"compliance_score": discipline.compliance_score})
def register_refactor_discipline(sub) -> None:
    p_rg = sub.add_parser(
        "refactor-guard",
        help="重构防退化守护（六约束检查，退出码 0/1/2）")
    p_rg.add_argument("--old", required=True, help="原始代码目录")
    p_rg.add_argument("--new", required=True, help="重构后代码目录")
    p_rg.add_argument("--stage", default=DEFAULT_GUARD_STAGE,
                      choices=["pre", "mid", "post"],
                      help="守护阶段（默认 post）")
    p_rg.add_argument("--rename-map", default="",
                      help="模块重命名映射 JSON（旧模块名 -> 新模块名，可选）")
    p_rg.add_argument("--json", action="store_true", help="输出 JSON 报告")
    p_rg.add_argument("-v", "--verbose", action="store_true",
                      help="详细输出（异常堆栈）")
    p_am = sub.add_parser(
        "assess-migration",
        help="迁移诚实度评估+六约束纪律门禁"
             "（骨架vs真实完成/API覆盖度/复制嫌疑）")
    p_am.add_argument("--old", required=True, help="旧版（迁移源）代码目录")
    p_am.add_argument("--new", required=True, help="新版（迁移目标）代码目录")
    p_am.add_argument("--json", action="store_true", help="输出 JSON 报告")
    p_am.add_argument("-o", "--output", help="JSON 报告输出路径")
REFACTOR_DISCIPLINE_COMMANDS = {
    "refactor-guard": cmd_refactor_guard,
    "assess-migration": cmd_assess_migration,
}
TEST_EXCLUDE_PATTERNS = frozenset({
    "tests", "test", "__pycache__", ".pytest_cache", ".mypy_cache",
    ".tox", ".coverage", "htmlcov", ".eggs",
    "Temp",
}) | SCAN_IGNORE_DIRS
TEST_EXCLUDE_PREFIXES = ("test_",)
TEST_EXCLUDE_SUFFIXES = ("_test.py",)
TEST_CONFIG_FILES = frozenset({
    "pytest.ini", "pytest.cfg", "setup.cfg", "tox.ini",
    "conftest.py",
})
_TEST_EXCLUDE_PATTERNS_LOWER = frozenset(
    part.lower() for part in TEST_EXCLUDE_PATTERNS)
_TEST_CONFIG_FILES_LOWER = frozenset(
    name.lower() for name in TEST_CONFIG_FILES)
_SYS_TMP_PREFIX = os.path.normcase(os.path.realpath(tempfile.gettempdir()))
def _coerce_scan_path(value: Any) -> Path | None:
    try:
        raw = os.fspath(value)
    except TypeError:
        return None
    if isinstance(raw, bytes):
        try:
            raw = os.fsdecode(raw)
        except (UnicodeDecodeError, ValueError) as _swallow_e:
            log_swallowed(
                __name__, _swallow_e,
                context=f'_coerce_scan_path:{type(_swallow_e).__name__}')
            return None
    try:
        return Path(raw)
    except (TypeError, ValueError):
        return None
def is_excluded_file(filepath: Path | str | os.PathLike) -> bool:
    path = _coerce_scan_path(filepath)
    if path is None:
        _log.warning("[RefactorPolicy] is_excluded_file 入参形状非法(%s)，"
                     "按排除处理", type(filepath).__name__)
        return True
    filepath = path
    parts = filepath.parts
    under_sys_tmp = _under_system_temp(filepath, parts)
    if any(_is_excluded_dir_part(part.lower(), under_sys_tmp)
           for part in parts):
        return True
    return _is_test_filename(filepath.name)
def _under_system_temp(filepath: Path, parts: tuple[str, ...]) -> bool:
    if not any(part.lower() == "temp" for part in parts):
        return False
    if not filepath.is_absolute():
        return False
    real = os.path.normcase(
        os.path.realpath(os.path.abspath(str(filepath))))
    return real.startswith(_SYS_TMP_PREFIX + os.sep)
def _is_excluded_dir_part(part: str, under_sys_tmp: bool) -> bool:
    if part == "temp" and under_sys_tmp:
        return False
    return (part in _TEST_EXCLUDE_PATTERNS_LOWER
            or part.endswith("_tests")
            or part == "fixtures")
def _is_test_filename(name: str) -> bool:
    name_lower = name.lower()
    return (name_lower.startswith(TEST_EXCLUDE_PREFIXES)
            or name_lower.endswith(TEST_EXCLUDE_SUFFIXES)
            or name_lower in _TEST_CONFIG_FILES_LOWER)
@dataclass
class FileAnalysis:
    filepath: str
    relative_path: str
    size_bytes: int
    line_count: int
    classes: list[str] = field(default_factory=list)
    functions: list[str] = field(default_factory=list)
    imports_in: list[str] = field(default_factory=list)
    imports_out: list[str] = field(default_factory=list)
    execution_chain_id: str = ""
    module_responsibility: str = ""
    has_mixed_responsibilities: bool = False
    quality_issues: list[str] = field(default_factory=list)
    logic_issues: list[str] = field(default_factory=list)
    unrelated_code_blocks: list[str] = field(default_factory=list)
    substantial_unrelated_blocks: list[str] = field(default_factory=list)
    call_references: dict[str, float] = field(default_factory=dict)
    coupling_score: float = 0.0
    cohesion_score: float = 10.0
    unused_imports: list[str] = field(default_factory=list)
    reexport_bridges: list[str] = field(default_factory=list)
    dead_constants: list[str] = field(default_factory=list)
    cascade_dead_candidates: list[str] = field(default_factory=list)
    cross_file_duplicates: list[str] = field(default_factory=list)
    from_import_entries: set[str] = field(default_factory=set)
    shared_base_consumers: int = 0
@dataclass
class ModuleBoundary:
    name: str
    member_files: list[str] = field(default_factory=list)
    responsibility: str = ""
    imports_in: set[str] = field(default_factory=set)
    imports_out: set[str] = field(default_factory=set)
    execution_chain_id: str = ""
    total_size_bytes: int = 0
@dataclass
class SplitMergeAction:
    action_type: str
    source_files: list[str] = field(default_factory=list)
    target_files: list[str] = field(default_factory=list)
    reason: str = ""
    boundary_justification: str = ""
    is_size_based: bool = False
    is_systematic: bool = False
    code_elements: list[str] = field(default_factory=list)
    precise_fix_attempted: bool = False
    signature_preservation_confirmed: bool = False
    new_code: str = ""
    fix_approach: str = ""
    governance_method: str | list[str] = ""
    governance_exception: str | dict[str, Any] = ""
    exception_approved_by: str = ""
    governance_decision_id: str = ""
    pros: list[str] = field(
        default_factory=lambda: _as_str_list(_MERGE_ARGUMENT_DEFAULTS["pros"]))
    cons: list[str] = field(
        default_factory=lambda: _as_str_list(_MERGE_ARGUMENT_DEFAULTS["cons"]))
    net_benefit: str = _MERGE_ARGUMENT_DEFAULTS["net_benefit"]
    risk: str = _MERGE_ARGUMENT_DEFAULTS["risk"]
    def __post_init__(self) -> None:
        self.action_type = _normalize_action_type(self.action_type)
        for _name in ("source_files", "target_files", "code_elements",
                      "pros", "cons"):
            setattr(self, _name, _as_str_list(getattr(self, _name, ())))
        self.fix_approach = _normalize_fix_approach(self.fix_approach)
        self.is_size_based = _bool_field(
            self.is_size_based, dirty_default=True)
        self.is_systematic = _bool_field(self.is_systematic)
        self.precise_fix_attempted = _bool_field(
            self.precise_fix_attempted)
        self.signature_preservation_confirmed = _bool_field(
            self.signature_preservation_confirmed)
class RefactoringPhase(Enum):
    DEEP_ANALYSIS = "deep_analysis"
    BACKUP = "backup"
    BOUNDARY_ANALYSIS = "boundary_analysis"
    ROUTE_PLANNING = "route_planning"
    SPLIT_MERGE = "split_merge"
    CODE_MIGRATION = "code_migration"
    QUALITY_REWRITE = "quality_rewrite"
PHASE_ORDER: tuple[RefactoringPhase, ...] = (
    RefactoringPhase.DEEP_ANALYSIS,
    RefactoringPhase.BACKUP,
    RefactoringPhase.BOUNDARY_ANALYSIS,
    RefactoringPhase.ROUTE_PLANNING,
    RefactoringPhase.SPLIT_MERGE,
    RefactoringPhase.CODE_MIGRATION,
    RefactoringPhase.QUALITY_REWRITE,
)
_PHASE_INDEX: dict[str, int] = {
    phase.value: index for index, phase in enumerate(PHASE_ORDER)}
@dataclass
class RefactoringRoute:
    actions: list[SplitMergeAction] = field(default_factory=list)
    phase_sequence: list[str] = field(default_factory=lambda: [p.value for p in PHASE_ORDER])
    risk_level: str = "low"
    estimated_files_affected: int = 0
    backup_required: bool = True
    validation_checkpoints: list[str] = field(default_factory=list)
@dataclass
class BoundaryAnalysisResult:
    boundaries: list[ModuleBoundary] = field(default_factory=list)
    execution_chains: dict[str, list[str]] = field(default_factory=dict)
    split_candidates: list[SplitMergeAction] = field(default_factory=list)
    merge_candidates: list[SplitMergeAction] = field(default_factory=list)
    migrate_candidates: list[SplitMergeAction] = field(default_factory=list)
    rewrite_candidates: list[SplitMergeAction] = field(default_factory=list)
    governance_candidates: list[dict] = field(default_factory=list)
    analysis_complete: bool = False
def _proposal_records(value: Any, label: str) -> list[Any]:
    if value is None:
        return []
    if isinstance(value, (dict, SplitMergeAction)):
        records: list[Any] = [value]
    elif isinstance(value, (list, tuple, set, frozenset)):
        records = list(value)
    else:
        _log.warning(
            "[RefactorPolicy] %s 容器形状非法(%s)，按空清单处理",
            label, type(value).__name__)
        return []
    kept = [item for item in records
            if isinstance(item, (dict, SplitMergeAction))]
    if len(kept) != len(records):
        _log.warning(
            "[RefactorPolicy] %s 含 %d 个非法元素（须为 dict/"
            "SplitMergeAction），已丢弃", label, len(records) - len(kept))
    return kept
def approved_split_actions(raw_splits: Any) -> list[Any]:
    return [action for action in _proposal_records(raw_splits, "split_candidates")
            if is_split_exception_valid(action)]
def _proposal_sources(item: Any) -> tuple[str, ...]:
    if isinstance(item, SplitMergeAction):
        return _as_str_tuple(action_field(item, "source_files", None))
    if isinstance(item, dict):
        return _as_str_tuple(item.get("source_files"))
    return ()
def _proposal_methods(data: dict[str, Any]) -> str | list[str]:
    methods = data.get("governance_method")
    if isinstance(methods, str):
        methods = [methods]
    elif isinstance(methods, (set, frozenset)):
        methods = sorted(methods, key=str)
    elif not isinstance(methods, (list, tuple)):
        methods = []
    cleaned = [str(item).strip() for item in methods
               if isinstance(item, str) and item.strip()]
    if not cleaned:
        return ""
    return cleaned[0] if len(cleaned) == 1 else cleaned
def _fallback_governance_proposals(raw_splits: Any) -> list[Any]:
    return [
        rewrite_split_to_governance(action)
        for action in _proposal_records(raw_splits, "split_candidates")
        if not is_split_exception_valid(action)
    ]
def _proposal_source_key(item: Any) -> frozenset[str]:
    return frozenset(_slash_key(source) for source in _proposal_sources(item))
def reconcile_governance_proposals(
    raw_splits: Any,
    candidates: Any,
) -> list[Any]:
    split_records = _proposal_records(raw_splits, "split_candidates")
    candidate_records = _proposal_records(
        candidates, "governance_candidates")
    approved_sources = {
        key for action in approved_split_actions(split_records)
        if (key := _proposal_source_key(action))
    }
    proposals = [
        item for item in candidate_records
        if (not (key := _proposal_source_key(item))
            or key not in approved_sources)
    ]
    covered_sources = {
        key for item in proposals
        if (key := _proposal_source_key(item))
    }
    for action in _fallback_governance_proposals(split_records):
        key = _proposal_source_key(action)
        if key and key in covered_sources:
            continue
        proposals.append(action)
        if key:
            covered_sources.add(key)
    return proposals
class RefactoringRoutePlanner:
    def __init__(self, boundary_result: BoundaryAnalysisResult) -> None:
        self.boundary_result = boundary_result
    @staticmethod
    def _assess_risk_level(actions: list[SplitMergeAction]) -> str:
        counts = Counter(
            _normalize_action_type(action_field(a, "action_type", ""))
            for a in actions)
        rewrite_count = counts["rewrite"]
        structural_count = sum(
            counts[action_type] for action_type in _GOVERNANCE_ACTION_TYPES)
        if rewrite_count > 3 or structural_count > 5:
            return "high"
        if rewrite_count or structural_count:
            return "medium"
        return "low"
    @staticmethod
    def _proposal_to_action(proposal: Any) -> SplitMergeAction:
        if isinstance(proposal, SplitMergeAction):
            if (proposal.action_type == "split"
                    and not is_split_exception_valid(proposal)):
                proposal = rewrite_split_to_governance(proposal)
            else:
                return proposal
        data = proposal if isinstance(proposal, dict) else {}
        action_type = effective_governance_action_type(data)
        if action_type == "split" and not is_split_exception_valid(data):
            data = rewrite_split_to_governance(data)
            action_type = effective_governance_action_type(data)
        merge_values = merge_argument_payload(data)
        return SplitMergeAction(
            action_type=action_type or "governance",
            source_files=_as_str_list(data.get("source_files")),
            target_files=_as_str_list(data.get("target_files")),
            reason=_clean_text(data.get("reason")),
            boundary_justification=_clean_text(
                data.get("boundary_justification")),
            is_size_based=_bool_field(
                data.get("is_size_based"), dirty_default=True),
            is_systematic=_bool_field(data.get("is_systematic")),
            code_elements=_as_str_list(data.get("code_elements")),
            precise_fix_attempted=_bool_field(
                data.get("precise_fix_attempted")),
            signature_preservation_confirmed=_bool_field(
                data.get("signature_preservation_confirmed")),
            new_code=str(data.get("new_code") or ""),
            fix_approach=_normalize_fix_approach(data.get("fix_approach")),
            governance_method=_proposal_methods(data),
            governance_exception=data.get("governance_exception") or "",
            exception_approved_by=_clean_text(
                data.get("exception_approved_by")),
            governance_decision_id=_clean_text(
                data.get("governance_decision_id")),
            pros=_as_str_list(merge_values["pros"]),
            cons=_as_str_list(merge_values["cons"]),
            net_benefit=str(merge_values["net_benefit"] or ""),
            risk=_clean_text(merge_values["risk"]),
        )
    def _route_actions(self) -> list[SplitMergeAction]:
        raw_splits = _proposal_records(
            self.boundary_result.split_candidates, "split_candidates")
        proposals = reconcile_governance_proposals(
            raw_splits, self.boundary_result.governance_candidates)
        candidates = [
            *approved_split_actions(raw_splits),
            *proposals,
            *_proposal_records(
                self.boundary_result.migrate_candidates, "migrate_candidates"),
            *_proposal_records(
                self.boundary_result.merge_candidates, "merge_candidates"),
            *_proposal_records(
                self.boundary_result.rewrite_candidates, "rewrite_candidates"),
        ]
        return [self._proposal_to_action(item) for item in candidates]
    def plan(self) -> RefactoringRoute:
        route = RefactoringRoute()
        actions = self._route_actions()
        route.actions = actions
        route.estimated_files_affected = len({
            f
            for a in actions
            for f in (*_as_str_tuple(action_field(a, "source_files", None)),
                      *_as_str_tuple(action_field(a, "target_files", None)))
        })
        route.risk_level = self._assess_risk_level(actions)
        route.validation_checkpoints = [
            "治理方案不得新增文件/模块边界，仅允许既有模块内降复杂度",
            "迁移后源文件和目标文件都必须通过语法检查",
            "迁移后必须全局搜索所有引用方并更新导入源，确保无残留转发",
            "合并后的文件必须通过语法检查",
            "重写后的文件必须通过语法检查",
            "重写前必须确认所有公开函数签名不变",
            "重构后所有导入必须可解析",
            "重构后所有公开 API 必须保持不变",
            "每个操作步骤完成后验证 __all__ 导出完整性",
            "每个操作步骤完成后验证拓扑排序无循环依赖",
            "验证失败立即回滚该步骤",
            "所有修复逐文件逐问题处理，禁止批量修复",
            ("所有修复一律根因修复（fix_approach=root_cause）：定位缺陷"
             "成因链并以正确语义消除，禁止吞异常掩盖/特判绕过/"
             "下游兜底拦截等补丁方式修复"),
        ]
        return route
@dataclass
class RefactoringConstraint:
    name: str
    description: str
    check: Callable[[dict], bool]
    error_message: str
    is_blocker: bool = True
    def evaluate(self: Self, context: dict) -> tuple[bool, str]:
        msg = self.error_message
        try:
            passed = self.check(context)
        except Exception as e:  # noqa: BLE001
            _log.warning("[RefactorGuard] 约束 %s 评估异常（按不通过处理）: %s",
                         self.name, e, exc_info=True)
            passed = False
            msg = f"{self.error_message} (评估异常: {e})"
        if not passed and self.is_blocker:
            return False, msg
        return True, ""
def _as_records(value: Any) -> list[Any] | None:
    if value is None:
        return []
    if isinstance(value, dict):
        return [value]
    if isinstance(value, (list, tuple, set, frozenset)):
        return list(value)
    return None
def _dict_records_pass(
    value: Any, predicate: Callable[[dict], bool],
) -> bool:
    records = _as_records(value)
    if records is None:
        return False
    return all(
        isinstance(record, dict) and predicate(record) for record in records
    )
def _route_actions(context: dict) -> list[Any] | None:
    route = context.get("refactoring_route")
    if route is None:
        return None
    actions = action_field(route, "actions", None)
    if not isinstance(actions, (list, tuple)):
        return None
    return list(actions)
def _route_scoped_actions(
    context: dict, action_type: str, *fallback_keys: str,
) -> list[Any] | None:
    if context.get("refactoring_route") is None:
        for key in fallback_keys:
            if key not in context:
                continue
            value = context.get(key)
            if value is None:
                continue
            if isinstance(value, (list, tuple, set, frozenset)) and not value:
                continue
            return _as_records(value)
        return []
    route_actions = _route_actions(context)
    if route_actions is None:
        return None
    return [
        action for action in route_actions
        if _normalize_action_type(action_field(action, "action_type", ""))
        == action_type
    ]
def _mentions(justification: Any, keywords: list[str] | tuple[str, ...]) -> bool:
    if not isinstance(justification, str):
        return False
    just_l = justification.lower()
    return any(kw in just_l for kw in keywords)
def _size_only_reason(justification: str, size_keywords: list[str],
                      boundary_keywords: list[str]) -> bool:
    return (_mentions(justification, size_keywords)
            and not _mentions(justification, boundary_keywords))
def _norm_path_key(value: Any) -> str:
    return os.path.normcase(os.path.normpath(str(value)))
def _resolved_path_key(value: Any, skill_dir: Any) -> str:
    text = os.fsdecode(value) if isinstance(value, (bytes, os.PathLike)) else str(value)
    skill_root = _clean_text(skill_dir)
    if skill_root and not os.path.isabs(text):
        text = os.path.join(skill_root, text)
    return _norm_path_key(text)
def _strict_file_names(value: Any) -> list[str] | None:
    if value is None:
        return []
    if isinstance(value, (str, bytes, os.PathLike)):
        return None
    if not isinstance(value, (list, tuple, set, frozenset)):
        return None
    names: list[str] = []
    for item in value:
        if not isinstance(item, (str, bytes, os.PathLike)):
            return None
        name = os.fsdecode(item)
        if not name.strip():
            return None
        names.append(name)
    return names
def _check_all_py_analyzed(context: dict) -> bool:
    skill_dir = _clean_text(context.get("skill_dir", ""))
    analyzed = _strict_file_names(context.get("analyzed_files"))
    if not skill_dir or analyzed is None:
        return False
    skill_path = Path(os.path.abspath(skill_dir))
    if not skill_path.is_dir():
        return False
    all_py = {_norm_path_key(p) for p in _iter_candidate_py_files(skill_path)}
    analyzed_set = {_resolved_path_key(f, str(skill_path)) for f in analyzed}
    return all_py.issubset(analyzed_set)
def _iter_candidate_py_files(skill_path: Path) -> Iterator[Path]:
    for raw in iter_prod_py_files(str(skill_path)):
        path = Path(raw)
        if not is_excluded_file(path):
            yield path
def _check_backup_exists(context: dict) -> bool:
    backed_up_names = _strict_file_names(context.get("backed_up_files"))
    files_to_modify = _strict_file_names(context.get("files_to_modify"))
    if backed_up_names is None or files_to_modify is None:
        return False
    skill_dir = _clean_text(context.get("skill_dir", ""))
    skill_root = os.path.abspath(skill_dir) if skill_dir else ""
    backed_up = {_resolved_path_key(f, skill_root) for f in backed_up_names}
    return all(_resolved_path_key(fpath, skill_root) in backed_up
               for fpath in files_to_modify)
def _check_plan_before_execute(context: dict) -> bool:
    return _route_actions(context) is not None
def _actions_not_size_driven(actions: list, size_keywords: list[str],
                              boundary_keywords: list[str]) -> bool:
    records = _as_records(actions)
    if records is None:
        return False
    for action in records:
        if _bool_field(
                action_field(action, "is_size_based", False),
                dirty_default=True):
            return False
        justification = action_field(action, "boundary_justification", "")
        if not isinstance(justification, str) or not justification.strip():
            return False
        if _size_only_reason(justification, size_keywords, boundary_keywords):
            return False
    return True
SPLIT_BOUNDARY_KEYWORDS = ["模块边界", "混合职责", "内聚", "无关联", "职责域",
                           "module boundary", "mixed responsibilit", "cohesion",
                           "unrelated", "responsibility"]
MERGE_COHESION_KEYWORDS = ["运行链路", "内聚", "cohesion", "导入链",
                           "execution chain", "import chain"]
_SPLIT_SIZE_KEYWORDS = ["大", "行数多", "too large", "too many lines", "size"]
_MERGE_SIZE_KEYWORDS = ["小", "too small", "size"]
def _check_no_size_only_split(context: dict) -> bool:
    actions = _route_scoped_actions(
        context, "split", "split_detector_candidates", "split_actions")
    if actions is None:
        return False
    return _actions_not_size_driven(actions, _SPLIT_SIZE_KEYWORDS,
                                    SPLIT_BOUNDARY_KEYWORDS)
def _check_no_size_only_merge(context: dict) -> bool:
    actions = _route_scoped_actions(context, "merge", "merge_actions")
    if actions is None:
        return False
    return _actions_not_size_driven(actions, _MERGE_SIZE_KEYWORDS,
                                    MERGE_COHESION_KEYWORDS)
def _check_merge_cohesion_only(context: dict) -> bool:
    merge_actions = _route_scoped_actions(context, "merge", "merge_actions")
    if merge_actions is None:
        return False
    for action in merge_actions:
        justification = action_field(action, "boundary_justification", "") or ""
        if not _mentions(justification, MERGE_COHESION_KEYWORDS):
            return False
    return True
def _phase_value(raw_phase: Any) -> Any:
    return raw_phase.value if isinstance(raw_phase, RefactoringPhase) else raw_phase
def _phase_sort_key(raw_phase: Any) -> tuple[int, str]:
    value = _phase_value(raw_phase)
    text = value if isinstance(value, str) else str(value)
    return (_PHASE_INDEX.get(text, len(_PHASE_INDEX)), text)
def _phase_value_list(raw_phases: Any) -> list | None:
    if raw_phases is None:
        return []
    if isinstance(raw_phases, str):
        return [_phase_value(raw_phases)]
    if isinstance(raw_phases, (set, frozenset)):
        return [_phase_value(p)
                for p in sorted(raw_phases, key=_phase_sort_key)]
    if not isinstance(raw_phases, (list, tuple)):
        return None
    return [_phase_value(p) for p in raw_phases]
def _check_phase_order(context: dict) -> bool:
    completed_phases = _phase_value_list(context.get("completed_phases"))
    if completed_phases is None:
        return False
    if not completed_phases:
        return True
    expected_prefix = [p.value for p in PHASE_ORDER[:len(completed_phases)]]
    return completed_phases == expected_prefix
def _check_next_phase(context: dict) -> bool:
    completed_phases = _phase_value_list(context.get("completed_phases"))
    if completed_phases is None:
        return False
    next_phase = _phase_value(context.get("next_phase", "") or "")
    if not next_phase:
        return True
    expected_index = len(completed_phases)
    if expected_index >= len(PHASE_ORDER):
        return False
    expected_phase = PHASE_ORDER[expected_index].value
    return next_phase == expected_phase
def _migration_forwarding_cleared(result: dict) -> bool:
    if result.get("references_updated") is not True:
        return False
    return result.get("has_residual_forwarding") is False
def _check_migration_no_residual_forwarding(context: dict) -> bool:
    results = _action_evidence_records(
        context, "migration_results", "executed_migrations")
    return (results is not None
            and _dict_records_pass(results, _migration_forwarding_cleared))
_SIGNATURE_CONFIRMATION_MARKERS: tuple[str, ...] = (
    "签名不变", "签名检查通过", "签名已确认", "已确认签名",
    "signature preserved", "signatures preserved",
    "signature unchanged", "signatures unchanged",
    "signature preservation confirmed", "signature preservation is confirmed",
    "signature check passed", "signature checks passed",
)
_SIGNATURE_NEGATED_PREFIX_RE = re.compile(
    r"(?:未确认|尚未确认|没能确认|未能确认|不能确认|无法确认|不确认|"
    r"(?:难以|无法|不能|未能|没能|没有|不|未|没)保证|"
    r"未验证|尚未验证|未检查|尚未检查|未通过|尚未通过|不确定|"
    r"\b(?:not(?!\s+only\b)|unconfirmed|unverified|unchecked|unknown|pending)\b)"
    r".{0,64}$")
_SIGNATURE_NEGATED_SUFFIX_RE = re.compile(
    r"^\s*[,，;；(（\[【]?\s*"
    r"(?:(?:\bbut\b|\bhowever\b|但|然而)\s*)?(?:"
    r"(?:[:=：]\s*)?(?:(?:false|no|unknown|unconfirmed|unverified|unchecked|pending|0)\b|"
    r"否|未知|不确定|未确认|尚未确认|待确认|待复核)"
    r"|(?:尚未|未|待|不能|无法|未能)(?:确认|验证|检查|通过)"
    r"|[?？]|是否|能否|可否"
    r"|并非|不是|存疑|未必|不一定)")
def _signature_text_confirmed(element: str) -> bool:
    lowered = element.lower()
    for marker in _SIGNATURE_CONFIRMATION_MARKERS:
        for occurrence in re.finditer(re.escape(marker), lowered):
            prefix = _ACTION_CLAUSE_SPLIT_RE.split(
                lowered[:occurrence.start()])[-1]
            if _SIGNATURE_NEGATED_PREFIX_RE.search(prefix[-64:]):
                continue
            suffix = lowered[occurrence.end():occurrence.end() + 64]
            if _SIGNATURE_NEGATED_SUFFIX_RE.match(suffix):
                continue
            return True
    return False
def _signature_preservation_confirmed(action: Any) -> bool:
    if _bool_field(
            action_field(action, "signature_preservation_confirmed", False)):
        return True
    code_elements = _as_str_tuple(action_field(action, "code_elements", None))
    return any(_signature_text_confirmed(element) for element in code_elements)
def _rewrite_precondition_error(action: Any) -> str:
    is_systematic = _bool_field(
        action_field(action, "is_systematic", False))
    precise_fix_attempted = _bool_field(
        action_field(action, "precise_fix_attempted", False))
    if not is_systematic and not precise_fix_attempted:
        return ("未尝试精确修复且未声明系统性结构问题，须设置 "
                "precise_fix_attempted=True 或 is_systematic=True")
    if not _signature_preservation_confirmed(action):
        return ("未确认公开函数签名不变，必须设置 "
                "signature_preservation_confirmed=True "
                "或在 code_elements 中包含签名不变/签名检查通过的明确证据")
    return ""
def _check_rewrite_preconditions(context: dict) -> bool:
    rewrite_actions = _route_scoped_actions(
        context, "rewrite", "rewrite_actions")
    if rewrite_actions is None:
        return False
    return all(
        not _rewrite_precondition_error(action) for action in rewrite_actions)
def normalize_executed_action_ids(value: Any) -> list[int]:
    if value is None:
        return []
    if isinstance(value, (list, tuple, set, frozenset)):
        return list(dict.fromkeys(
            i for i in value
            if isinstance(i, int) and not isinstance(i, bool) and i >= 0))
    return []
_EXECUTED_ACTION_KEYS = (
    "executed_split_merges", "executed_migrations", "executed_rewrites")
def _valid_executed_action_ids(value: Any) -> bool:
    if value is None:
        return True
    if not isinstance(value, (list, tuple, set, frozenset)):
        return False
    return all(isinstance(i, int) and not isinstance(i, bool) and i >= 0
               for i in value)
def _action_evidence_records(
    context: dict, evidence_key: str, executed_key: str,
) -> list[Any] | None:
    records = _as_records(context.get(evidence_key))
    raw_executed = context.get(executed_key)
    if records is None or not _valid_executed_action_ids(raw_executed):
        return None
    executed_count = len(normalize_executed_action_ids(raw_executed))
    return records if len(records) >= executed_count else None
def _executed_ledgers_valid(context: dict) -> bool:
    return all(_valid_executed_action_ids(context.get(key))
               for key in _EXECUTED_ACTION_KEYS)
def count_executed_actions(context: dict) -> int:
    return sum(
        len(normalize_executed_action_ids(context.get(key)))
        for key in _EXECUTED_ACTION_KEYS)
def _strict_true(value: Any) -> bool:
    return value is True
def _step_validation_passed(validation: Any) -> bool:
    if not isinstance(validation, dict):
        return False
    export_passed = validation.get("all_export_passed")
    topology_passed = validation.get("topological_sort_passed")
    if not isinstance(export_passed, bool) or not isinstance(topology_passed, bool):
        return False
    validation_failed = validation.get("validation_failed", False)
    if validation_failed is True:
        return _strict_true(validation.get("rolled_back"))
    if validation_failed is not False:
        return False
    return export_passed and topology_passed
def _check_step_validation(context: dict) -> bool:
    if not _executed_ledgers_valid(context):
        return False
    step_validations = _as_records(context.get("step_validations"))
    if step_validations is None:
        return False
    executed_count = count_executed_actions(context)
    if not step_validations:
        return executed_count <= 0
    return (len(step_validations) >= executed_count
            and all(_step_validation_passed(v) for v in step_validations))
def _all_actions_executed(
    context: dict, action_type: str, action_key: str, executed_key: str,
) -> bool:
    actions = _route_scoped_actions(context, action_type, action_key)
    if actions is None:
        return False
    raw_executed = context.get(executed_key)
    if not _valid_executed_action_ids(raw_executed):
        return False
    executed = set(normalize_executed_action_ids(raw_executed))
    return executed == set(range(len(actions)))
def _check_migration_completed(context: dict) -> bool:
    return _all_actions_executed(
        context, "migrate", "migrate_actions", "executed_migrations")
def _as_file_names(group: object) -> list[str]:
    if isinstance(group, (str, os.PathLike)):
        items: list = [group]
    elif isinstance(group, (list, tuple, set, frozenset)):
        items = list(group)
    else:
        return []
    names: list[str] = []
    for item in items:
        if not isinstance(item, (str, os.PathLike)):
            continue
        name = os.fsdecode(item)
        if name:
            names.append(name)
    return names
def collect_modified_files(context: dict[str, Any], action: SplitMergeAction,
                           result: Any, dry_run: bool) -> None:
    if dry_run or action_field(result, "status", "") != "success":
        return
    if action_field(result, "changes_made", None) == 0:
        return
    collected = _normalize_modified_files_slot(context)
    file_groups = (
        action_field(result, "source_files", None),
        action_field(result, "target_files", None),
        action_field(action, "source_files", None),
        action_field(action, "target_files", None),
    )
    merged = list(collected)
    for group in file_groups:
        merged.extend(_as_file_names(group))
    collected[:] = dict.fromkeys(merged)
def _normalize_modified_files_slot(context: dict[str, Any]) -> list[str]:
    raw = context.get("refactor_modified_files")
    if isinstance(raw, list):
        raw[:] = _as_file_names(raw)
        return raw
    if isinstance(raw, tuple):
        fresh = _as_file_names(raw)
        context["refactor_modified_files"] = fresh
        return fresh
    if raw is not None:
        _log.warning("[Executor] refactor_modified_files 形状非法(须为 "
                     "list/tuple),已重置为空清单: %s", type(raw).__name__)
    fresh: list[str] = []
    context["refactor_modified_files"] = fresh
    return fresh
def read_modified_files(context: dict[str, Any]) -> list[str] | None:
    files = context.get("refactor_modified_files")
    if not files:
        return None
    if not isinstance(files, (list, tuple)):
        _log.warning("[Executor] refactor_modified_files 形状非法(须为 "
                     "list/tuple),按无结果处理: %s", type(files).__name__)
        return None
    names = _as_file_names(files)
    return names or None
def require_deep_analysis(deep_analyzed: bool) -> None:
    if deep_analyzed is not True:
        raise ContractViolationError(
            "边界分析前置缺失: deep_analyze() 未执行"
            "（阶段1 深度分析必须先于 analyze_boundaries()）")
def require_route_value(context: dict[str, Any]) -> RefactoringRoute:
    route = context.get("refactoring_route")
    if route is None:
        raise ContractViolationError(
            "拆分/迁移/重写前置缺失: refactoring_route 为 None"
            "（阶段4 路线规划未执行或失败）")
    return route
def require_boundary_value(
        boundary_result: BoundaryAnalysisResult | None,
) -> BoundaryAnalysisResult:
    if boundary_result is None:
        raise ContractViolationError(
            "路线规划前置缺失: _boundary_result 为 None"
            "（阶段3 边界分析未执行或失败）")
    return boundary_result
def _check_rewrite_completed(context: dict) -> bool:
    return _all_actions_executed(
        context, "rewrite", "rewrite_actions", "executed_rewrites")
_MAX_ITEMS_PER_FIX_RECORD = 1
def _has_single_item_budget(values: Any) -> bool:
    return (isinstance(values, (list, tuple, set, frozenset))
            and len(values) == _MAX_ITEMS_PER_FIX_RECORD)
def _single_item_fix_record(record: dict) -> bool:
    return (_has_single_item_budget(record.get("files_modified"))
            and _has_single_item_budget(record.get("issues_fixed")))
def _check_no_batch_fix(context: dict) -> bool:
    records = _action_evidence_records(context, "fix_records", "executed_rewrites")
    return (records is not None
            and _dict_records_pass(records, _single_item_fix_record))
FIX_APPROACH_ROOT_CAUSE = "root_cause"
def _root_cause_fix_record(record: dict) -> bool:
    return (_normalize_fix_approach(record.get("fix_approach"))
            == FIX_APPROACH_ROOT_CAUSE)
def _check_no_patch_fix(context: dict) -> bool:
    records = _action_evidence_records(context, "fix_records", "executed_rewrites")
    return (records is not None
            and _dict_records_pass(records, _root_cause_fix_record))
def _governance_method_declared(action: Any) -> bool:
    method = action_field(action, "governance_method", "")
    declared = (method if isinstance(method, (list, tuple, set, frozenset))
                else [method])
    proposal_text = " ".join(
        text
        for key in ("reason", "description", "boundary_justification",
                    "decision", "rationale")
        if (text := _clean_text(action_field(action, key, "")))
    )
    return (not detect_forbidden_method(proposal_text)
            and bool(declared) and all(
                isinstance(item, str)
                and not detect_forbidden_method(item)
                and normalize_governance_method(item)
                for item in declared))
def _check_no_split_as_governance(context: dict) -> bool:
    split_actions = _route_scoped_actions(
        context, "split", "split_detector_candidates", "split_actions")
    if split_actions is None:
        return False
    if any(not is_split_exception_valid(action) for action in split_actions):
        return False
    governance_actions = _route_scoped_actions(
        context, "governance", "governance_actions")
    if governance_actions is None:
        return False
    return all(_governance_method_declared(a) for a in governance_actions)
def _check_merge_argument(context: dict) -> bool:
    merge_actions = _route_scoped_actions(context, "merge", "merge_actions")
    if merge_actions is None:
        return False
    return all(
        merge_argument_of(action).validate()[0] for action in merge_actions
    )
CONSTRAINT_NO_SPLIT_AS_GOVERNANCE = RefactoringConstraint(
    name="no_split_as_governance",
    description=(
        "禁止以拆分文件/模块作为治理手段；拆分候选必须改写为简化逻辑/"
        "消除重复/收敛依赖/迁移代码/提取同模块内私有实现（GOV-01）"),
    check=_check_no_split_as_governance,
    error_message=(
        "[R-15] 拆分被用作治理手段或治理动作未声明白名单手段，阻断；"
        "须改写为 " + "/".join(GOVERNANCE_METHODS)
        + " 之一（拆分例外须人工批准并留痕 decision_id）"),
)
CONSTRAINT_MERGE_ARGUMENT = RefactoringConstraint(
    name="merge_argument_required",
    description=(
        "合并必须附带 pros/cons/net_benefit 论证且 net_benefit=positive，"
        "论证写入治理决策留痕（GOV-02）"),
    check=_check_merge_argument,
    error_message=(
        "[R-16] 合并缺少合规论证（pros/cons 各至少一条且 net_benefit "
        "必须为 positive），阻断"),
)
CONSTRAINT_ALL_PY_ANALYZED = RefactoringConstraint(
    name="must_analyze_all_py",
    description="必须深度分析目标技能根目录内所有 .py 文件",
    check=_check_all_py_analyzed,
    error_message="[R-01] 未完成所有 .py 文件的深度分析，不允许进入下一阶段",
)
CONSTRAINT_BACKUP_BEFORE_MODIFY = RefactoringConstraint(
    name="must_backup_before_modify",
    description="任何文件修改前必须备份到 get_backup_root() 归口目录中",
    check=_check_backup_exists,
    error_message="[R-02] 存在待修改文件未完成备份，阻断修改操作",
)
CONSTRAINT_PLAN_BEFORE_EXECUTE = RefactoringConstraint(
    name="must_plan_before_execute",
    description="收集完成信息后必须进行执行路线规划",
    check=_check_plan_before_execute,
    error_message="[R-03] 未生成重构执行路线图，不允许执行拆分/合并/迁移/重写",
)
CONSTRAINT_NO_SIZE_ONLY_SPLIT = RefactoringConstraint(
    name="no_size_only_split",
    description="不能因为文件大而拆分，必须基于模块边界",
    check=_check_no_size_only_split,
    error_message="[R-04] 拆分决策基于文件大小而非模块边界，阻断",
)
CONSTRAINT_NO_SIZE_ONLY_MERGE = RefactoringConstraint(
    name="no_size_only_merge",
    description="不能因为文件小而合并，必须基于运行链路内聚性",
    check=_check_no_size_only_merge,
    error_message="[R-05] 合并决策基于文件大小而非模块边界，阻断",
)
CONSTRAINT_MERGE_COHESION_ONLY = RefactoringConstraint(
    name="merge_cohesion_only",
    description="文件大小仅作辅助参考，合并的唯一依据是运行链路内聚性是否足够高",
    check=_check_merge_cohesion_only,
    error_message="[R-06] 合并决策未以内聚性为依据，文件大小不能作为合并的唯一理由",
)
CONSTRAINT_PHASE_ORDER = RefactoringConstraint(
    name="phase_order_enforcement",
    description="已完成阶段序列必须是 PHASE_ORDER 的前缀",
    check=_check_phase_order,
    error_message="[R-07] 阶段顺序违反，必须按 deep_analysis→backup→"
                  "boundary_analysis→route_planning→split_merge→"
                  "code_migration→quality_rewrite 顺序执行",
)
CONSTRAINT_NEXT_PHASE = RefactoringConstraint(
    name="next_phase_correct",
    description="即将执行的阶段必须是已完成阶段的下一个",
    check=_check_next_phase,
    error_message="[R-07b] 阶段跳跃或重复，必须严格按顺序执行",
)
CONSTRAINT_MIGRATION_DONE = RefactoringConstraint(
    name="migration_completed",
    description="同文件内无关联代码必须迁移到有关联的文件",
    check=_check_migration_completed,
    error_message="[R-08] 存在未完成的代码迁移动作",
)
CONSTRAINT_REWRITE_DONE = RefactoringConstraint(
    name="rewrite_completed",
    description="代码质量和逻辑有问题的文件必须重写",
    check=_check_rewrite_completed,
    error_message="[R-09] 存在未完成的质量重写动作",
)
CONSTRAINT_MIGRATION_NO_RESIDUAL = RefactoringConstraint(
    name="migration_no_residual_forwarding",
    description="迁移函数后必须全局搜索所有引用方并更新导入源，确保无残留转发",
    check=_check_migration_no_residual_forwarding,
    error_message="[R-10] 迁移后存在残留导入转发或引用方未更新，阻断",
)
CONSTRAINT_REWRITE_PRECONDITIONS = RefactoringConstraint(
    name="rewrite_preconditions",
    description="优先精确修复，仅系统性结构问题才重写，重写前确认函数签名不变",
    check=_check_rewrite_preconditions,
    error_message="[R-11] 重写前置条件不满足：未尝试精确修复或未确认函数签名不变",
)
CONSTRAINT_STEP_VALIDATION = RefactoringConstraint(
    name="step_validation_required",
    description="每个操作步骤完成后验证 __all__ 导出完整性和拓扑排序无循环依赖，失败立即回滚",
    check=_check_step_validation,
    error_message="[R-12] 操作步骤未通过验证或验证失败未回滚，阻断",
)
CONSTRAINT_NO_BATCH_FIX = RefactoringConstraint(
    name="no_batch_fix",
    description="所有修复逐文件逐问题处理，禁止批量修复",
    check=_check_no_batch_fix,
    error_message="[R-13] 检测到批量修复行为（单次修复涉及多个文件或多个问题），阻断",
)
CONSTRAINT_NO_PATCH_FIX = RefactoringConstraint(
    name="no_patch_fix",
    description="所有修复一律根因修复（fix_approach=root_cause），禁止补丁方式修复",
    check=_check_no_patch_fix,
    error_message="[R-14] 检测到补丁方式修复或未声明根因修复方式"
                  "（fix_approach 须为 root_cause），阻断",
)
ALL_CONSTRAINTS: tuple[RefactoringConstraint, ...] = (
    CONSTRAINT_ALL_PY_ANALYZED,
    CONSTRAINT_BACKUP_BEFORE_MODIFY,
    CONSTRAINT_PLAN_BEFORE_EXECUTE,
    CONSTRAINT_NO_SIZE_ONLY_SPLIT,
    CONSTRAINT_NO_SIZE_ONLY_MERGE,
    CONSTRAINT_MERGE_COHESION_ONLY,
    CONSTRAINT_PHASE_ORDER,
    CONSTRAINT_NEXT_PHASE,
    CONSTRAINT_MIGRATION_DONE,
    CONSTRAINT_REWRITE_DONE,
    CONSTRAINT_MIGRATION_NO_RESIDUAL,
    CONSTRAINT_REWRITE_PRECONDITIONS,
    CONSTRAINT_STEP_VALIDATION,
    CONSTRAINT_NO_BATCH_FIX,
    CONSTRAINT_NO_PATCH_FIX,
    CONSTRAINT_NO_SPLIT_AS_GOVERNANCE,
    CONSTRAINT_MERGE_ARGUMENT,
)
def _validate_split_action(
    action: SplitMergeAction,
) -> tuple[bool, str] | None:
    if not is_split_exception_valid(action):
        return False, (
            "拆分动作违反治理约束: 禁止以拆分文件/模块作为治理手段"
            "（GOV-01/R-15）；必须改写为 "
            + "/".join(GOVERNANCE_METHODS)
            + " 之一；确需拆分须附 governance_exception + "
            "exception_approved_by（非 AI）+ governance_decision_id 人工批准留痕"
        )
    justification = action_field(action, "boundary_justification", "")
    has_boundary_reason = _mentions(justification, SPLIT_BOUNDARY_KEYWORDS)
    if not has_boundary_reason:
        detail = ("仅引用文件大小，必须基于模块边界/混合职责/内聚度"
                  if _mentions(justification, _SPLIT_SIZE_KEYWORDS)
                  else "未引用模块边界/混合职责/内聚度")
        return False, f"拆分动作违反原则: boundary_justification {detail}"
    return None
def _validate_merge_action(
    action: SplitMergeAction,
) -> tuple[bool, str] | None:
    justification = action_field(action, "boundary_justification", "")
    if not _mentions(justification, MERGE_COHESION_KEYWORDS):
        detail = ("仅引用文件大小"
                  if _mentions(justification, _MERGE_SIZE_KEYWORDS)
                  else "未引用运行链路/内聚性")
        return False, (
            f"合并动作违反原则: boundary_justification {detail}，"
            "合并的唯一依据必须是运行链路内聚性"
        )
    ok, errors = merge_argument_of(action).validate()
    if not ok:
        return False, (
            "合并动作违反治理约束（GOV-02/R-16）: "
            + "；".join(errors)
            + "；论证须写入 governance_decisions.jsonl"
        )
    return None
def _validate_migrate_action(
    action: SplitMergeAction,
) -> tuple[bool, str] | None:
    if not _as_str_tuple(action_field(action, "code_elements", None)):
        return False, (
            "迁移动作违反原则: 缺少 code_elements，"
            "必须指定要迁移的代码元素"
        )
    text = " ".join(
        part for key in ("reason", "description", "boundary_justification",
                         "decision", "rationale", "governance_method")
        if (part := _clean_text(action_field(action, key, "")))
    )
    errors = migration_decoupling_errors(text)
    if errors:
        return False, "迁移动作违反治理约束: " + "；".join(errors)
    return None
def _validate_rewrite_action(
    action: SplitMergeAction,
) -> tuple[bool, str] | None:
    fix_approach = _normalize_fix_approach(
        action_field(action, "fix_approach", ""))
    if fix_approach != FIX_APPROACH_ROOT_CAUSE:
        return False, (
            "重写动作违反原则: fix_approach 必须显式声明根因修复"
            f"（当前为 {fix_approach!r}，要求 "
            f"fix_approach={FIX_APPROACH_ROOT_CAUSE!r}），"
            "禁止未声明修复方式或吞异常掩盖/特判绕过/下游兜底拦截"
        )
    precondition_error = _rewrite_precondition_error(action)
    if precondition_error:
        return False, f"重写动作违反原则: {precondition_error}"
    return None
def _validate_governance_action(
    action: SplitMergeAction,
) -> tuple[bool, str] | None:
    if not _governance_method_declared(action):
        return False, (
            "治理动作违反治理约束（GOV-01/R-15）: "
            "governance_method 必须声明 "
            + "/".join(GOVERNANCE_METHODS)
            + " 之一，且提案文本不得夹带拆分文件/模块手段；"
            "禁止 split_file/split_module 或未声明方法"
        )
    return None
def _common_action_precheck(action: Any) -> tuple[bool, str] | None:
    action_type = _normalize_action_type(action_field(action, "action_type", ""))
    if _bool_field(
            action_field(action, "is_size_based", False), dirty_default=True):
        return False, (
            f"动作 {action_type} 违反核心原则: "
            f"is_size_based=True，不能基于文件大小做拆分/合并决策"
        )
    justification = action_field(action, "boundary_justification", "")
    if not (isinstance(justification, str) and justification.strip()):
        return False, (
            f"动作 {action_type} 违反核心原则: "
            f"缺少 boundary_justification，必须说明模块边界依据"
        )
    return None
_ACTION_TYPE_VALIDATORS: dict[
    str, Callable[[SplitMergeAction], tuple[bool, str] | None]] = {
    "split": _validate_split_action,
    "merge": _validate_merge_action,
    "migrate": _validate_migrate_action,
    "rewrite": _validate_rewrite_action,
    "governance": _validate_governance_action,
}
def validate_refactoring_action(action: Any) -> tuple[bool, str]:
    verdict = _common_action_precheck(action)
    if verdict is not None:
        return verdict
    action_type = _normalize_action_type(action_field(action, "action_type", ""))
    type_validator = _ACTION_TYPE_VALIDATORS.get(action_type)
    if type_validator is not None:
        return type_validator(action) or (True, "")
    known = "/".join(_ACTION_TYPE_VALIDATORS)
    return False, (
        f"动作类型 {action_type!r} 未登记，不得派发；"
        f"已登记类型: {known}（新增类型须先登记校验器）")
COHESION_STRONG_SIGNAL = 3.0

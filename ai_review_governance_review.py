from __future__ import annotations

import ast
import logging
import math
import os
from typing import Any, NamedTuple

from jwsgj.ai_review_item_plan import (
    provided_source,
)
from jwsgj.build_refactor_gate import (
    merge_target_key,
    record_decision,
)
from jwsgj.build_refactor_policy import (
    BOUNDARY_COMPLIANCE_VALUES,
    GOVERNANCE_METHODS,
    MERGE_NET_BENEFIT_VALUES,
    METHOD_COMPLIANCE_VALUES,
    MergeArgument,
    classify_governance_method,
    decision_target_key,
    detect_forbidden_method,
    effective_governance_action_type,
    governance_proposal,
    governance_review_projection,
    governance_scope,
    is_split_exception_valid,
    merge_argument_payload,
    migration_decoupling_errors,
    normalize_governance_method,
    normalized_governance_action_type,
    rewrite_split_to_governance,
    suggest_governance_methods,
)
from jwsgj.diag_module_topology import (
    ModuleTopology,
    build_module_topology,
    check_source_boundary,
)
from jwsgj.diag_types_normalize import (
    as_dict,
    strip_bom,
)
from jwsgj.diag_zero_backlog_ledger import (
    write_verdict_trace,
)
from jwsgj.runtime_scope import (
    normalize_text,
)

__all__ = [
    'APPROVAL_VERDICTS',
    'FIXABILITY_LEVELS',
    'FIX_APPROACH_VALUES',
    'FP_OR_REAL_VALUES',
    'REVIEW_FRAMEWORK',
    'SEVERITY_ASSESSMENT_LEVELS',
    'VERDICT_VALUES',
    'approval_flag',
    'as_text',
    'evaluate_governance_review',
    'is_missing_dimension',
    'record_governance_decision',
    'record_review_verdict',
    'resolve_review_decision',
    'validate_governance_assessment',
    'validate_review_assessment',
]
logger = logging.getLogger(__name__)
logger.info("ai_review_governance_review 已加载: %d 项导出", len(__all__))
SEVERITY_ASSESSMENT_LEVELS = ("P0", "P1", "P2", "P3")
FIXABILITY_LEVELS = ("trivial", "moderate", "complex", "risky", "unfixable")
FP_OR_REAL_VALUES = ("true_positive", "false_positive", "uncertain")
VERDICT_VALUES = ("approve_and_fix", "approve", "reject_as_fp", "reject", "defer")
FIX_APPROACH_VALUES = ("root_cause", "patch_deviation")
_GOVERNANCE_DIMENSIONS, _GOVERNANCE_POLICY = governance_review_projection()
REVIEW_FRAMEWORK = {
    "dimensions": [
        {"key": "severity_assessment", "name": "严重性复核",
         "values": list(SEVERITY_ASSESSMENT_LEVELS),
         "hint": "复核原始 severity 是否属实，可升/降级；附 severity_rationale 判定理由"},
        {"key": "fixability", "name": "可修复性",
         "values": list(FIXABILITY_LEVELS),
         "hint": "trivial 机械改写 / moderate 局部重构 / complex 跨模块 / "
                 "risky 修复风险大于收益 / unfixable 暂无可行修复路径；附 fixability_rationale"},
        {"key": "trade_off", "name": "利弊权衡",
         "fields": ["pros", "cons", "net_benefit"],
         "hint": "修复收益(pros) vs 代价与风险(cons)；net_benefit=positive/negative/neutral"},
        {"key": "fp_or_real", "name": "误报判定",
         "values": list(FP_OR_REAL_VALUES),
         "hint": "代码类通道（treatment/security/cleanup 及 feedback 的 "
                 "source_fix 改码方案，均有 code_context 代码现场）基于 "
                 "code_context/fix_plan/fix_guidance 代码级证据与 "
                 "rule_fp_history/treatment_history 历史基线判定；参数/规则类通道"
                 "（enhancement/adjustment 及 feedback 的非改码方案，无代码现场）"
                 "基于 diagnosis_context（方法审计统计）与 "
                 "treatment_context（fp_confirmed/net_improvement 全局治疗实证、"
                 "target_treatment_evidence 目标级下钻）及 "
                 "retrospective_context（issues_found 复盘根因）与 adjustment_history "
                 "历史裁决判定；false_positive 须附 fp_evidence（反哺通道可为"
                 "统计证据归因）"},
        *_GOVERNANCE_DIMENSIONS,
    ],
    "governance": _GOVERNANCE_POLICY,
    "fix_approach": {
        "values": list(FIX_APPROACH_VALUES),
        "requirement": "approve_and_fix 必填执行方式声明：root_cause 根因修复"
                       "（改变设计/契约/源头实现）/ patch_deviation 补丁方式"
                       "（故障点外包 try-except 吞错、调用点类型强转绕过、表面规避不改根因）",
        "policy": "禁止补丁方式修复（P0 强制）：patch_deviation 与"
                  "approve/approve_and_fix 组合一律退回；根因修复方可写盘",
    },
    "fix_scope": {
        "code": "修复逻辑代码：fixed_source 为修复后源码全文（非 diff），"
                "须根因修复（fix_approach=root_cause，禁止补丁方式：故障点"
                "外包 try-except 吞错/调用点类型强转/表面规避不改根因一律"
                "退回），经 fix_safety_verify 分层阶梯 + diag_guard_injection_enforce "
                "内联验证写盘",
        "comments": "同步更新受影响的注释与 docstring（写盘门禁强制）：修复改变行为/语义/契约时，相关注释、docstring、"
                    "示例说明必须一并修正，禁止留下与新实现矛盾的旧注释；机检 SSOT="
                    "diag_split_gate.comment_docstring_sync_error（底层复用 diag_shared_source_core.check_comment_docstring_sync），"
                    "治疗链（FixSafetyVerifier L0 契约第 4 项）与反哺 source_fix"
                    "写盘门同口径拦截：实现体修改后原 docstring 被删未重写 / 签名收缩后参数文档段仍引用已删参数 / 模块 docstring"
                    "被删，三形态命中即拒绝写盘并要求同步修订后重提（治疗与反哺写码通道同口径）",
        "regression": "写盘成功后只跑被修改文件对应的定向回归测试（run_targeted_regression："
                      "bridge 覆盖→文件名匹配→模糊匹配三级定位），绝不跑全量回归；"
                      "failed 自动回滚，error 交 AI 决策",
        "no_patch_fix": "禁止补丁方式修复：一律定位根因并以根因消除方式修复"
                        "（SSOT 归口/契约对齐/结构校正），禁止吞异常遮蔽、"
                        "特判绕过、硬编码短路、只治症状不除根因；"
                        "fixed_source 须与根因分析可对应，补丁式修复"
                        "在审核环节直接打回（reject 并附 verdict_rationale 要求根因重修）",
    },
    "verdicts": {
        "approve_and_fix": "真实问题且可修复：AI 生成 fixed_source 提交写盘（经三层验证，含受影响注释/docstring 同步更新）",
        "approve": "真实问题但由编排器代执行（enhancement/adjustment 等非源码通道）",
        "reject_as_fp": "判定误报：治疗项置 fp_confirmed 并即时固化误报规则反哺诊断过滤",
        "reject": "真实问题但利弊权衡后不修复：授权留痕（建议附 verdict_rationale）；治疗/cv_uncertain 通道不是终态，条目保持 pending 并阻塞交付",
        "defer": "暂缓处理（fixability=risky/unfixable 等）：授权留痕；治疗/cv_uncertain 通道不是终态，条目保持 pending 并阻塞交付",
    },
    "submit": ("run_next_ai_review(skill_dir, review_id=..., assessment={...}, "
               "fixed_source=...) — assessment.verdict 为必填裁决字段；"
               "provider 回调返回值亦可携带 assessment 键。维度按裁决分级必填："
               "approve_and_fix 须全四维(severity_assessment/fixability/net_benefit/"
               "fp_or_real)+执行方式声明 fix_approach=root_cause（禁止补丁方式"
               "修复，patch_deviation 一律退回）；approve 须"
               "severity_assessment+fp_or_real；reject_as_fp 须附 fp_evidence"
               "代码级证据；reject/defer 建议附 verdict_rationale。缺失维度提交"
               "会被退回(resubmit_with_valid_assessment)；执行内容口径见"
               "fix_scope：改代码+同步注释/docstring+定向回归")
}
_COMPLIANT_STATUSES: tuple[str, ...] = ("compliant", "not_applicable")
_STATUS_SEVERITY: dict[str, int] = {
    "compliant": 0,
    "not_applicable": 0,
    "unverified": 1,
    "rewrite_required": 2,
    "violation": 2,
}
_VERDICT_REQUIRED_FIELDS: dict[str, tuple[str, ...]] = {
    "approve_and_fix": ("severity_assessment", "fixability",
                        "net_benefit", "fp_or_real", "fix_approach"),
    "approve": ("severity_assessment", "fp_or_real"),
    "reject_as_fp": ("fp_evidence",),
}
APPROVAL_VERDICTS: tuple[str, ...] = ("approve", "approve_and_fix")
_FALSE_APPROVAL_TOKENS = frozenset((
    "false", "0", "no", "n", "off", "reject", "rejected", "deny",
    "denied", "disable", "disabled", "", "none", "null", "nil", "nope",
    "否", "不", "无", "拒绝", "驳回", "不批准", "不通过", "不采纳",
    "不同意", "失败"))
_TRUE_APPROVAL_TOKENS = frozenset((
    "true", "1", "yes", "y", "on", "ok", "approve", "approved",
    "accept", "accepted", "pass", "passed", "是", "同意", "批准",
    "通过", "采纳", "确认"))
def approval_flag(value) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        return value != 0
    if isinstance(value, float):
        return math.isfinite(value) and value != 0
    if isinstance(value, str):
        text = value.strip().lower()
        if not text or text in _FALSE_APPROVAL_TOKENS:
            return False
        if text in _TRUE_APPROVAL_TOKENS:
            return True
        try:
            number = float(text)
        except ValueError:
            logger.warning(
                "[AIReview] 无法识别的 approved 值 %r，按未批准处理", value)
            return False
        return math.isfinite(number) and number != 0
    if value is None:
        return True
    logger.warning(
        "[AIReview] approved 类型 %s 不受支持，按未批准处理",
        type(value).__name__)
    return False
def _resolve_provider_output(output, fixed_source):
    approved = True
    assessment = None
    if isinstance(output, dict):
        if not provided_source(fixed_source):
            fixed_source = provided_source(output.get("fixed_source"))
        approved = approval_flag(output.get("approved"))
        if isinstance(output.get("assessment"), dict):
            assessment = output["assessment"]
    elif not provided_source(fixed_source):
        fixed_source = provided_source(output)
    return fixed_source, approved, assessment
def resolve_review_decision(review: dict, fixed_source, provider, assessment):
    fs = provided_source(fixed_source)
    approved = True
    asm: dict | None = assessment
    if provider is not None:
        fs, approved, provider_asm = _resolve_provider_output(
            provider(review), fs)
        if asm is None:
            asm = provider_asm
    if isinstance(asm, dict):
        verdict = as_text(asm.get("verdict"))
        if verdict:
            approved = approved and verdict in APPROVAL_VERDICTS
    return fs, approved, asm
_ENUM_VALIDATION_SPECS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("severity_assessment", SEVERITY_ASSESSMENT_LEVELS),
    ("fixability", FIXABILITY_LEVELS),
    ("fp_or_real", FP_OR_REAL_VALUES),
    ("fix_approach", FIX_APPROACH_VALUES),
    ("net_benefit", MERGE_NET_BENEFIT_VALUES),
)
def _verdict_contradictions(normalized: dict, verdict: str,
                            approving: bool) -> list[str]:
    errors: list[str] = []
    if verdict == "reject_as_fp" and normalized.get("fp_or_real") is None:
        normalized["fp_or_real"] = "false_positive"
    fp_or_real = normalized.get("fp_or_real")
    if (verdict == "reject_as_fp" and fp_or_real is not None
            and fp_or_real != "false_positive"):
        errors.append(
            f"verdict=reject_as_fp 与 fp_or_real={fp_or_real} 矛盾"
            "（误报判定必须确认为 false_positive；证据不足应改用 defer）")
    if approving and fp_or_real == "false_positive":
        errors.append(f"verdict={verdict} 与 fp_or_real=false_positive 矛盾"
                      "（判定误报不可批准修复，应改用 reject_as_fp）")
    if (not approving and verdict != "reject_as_fp"
            and fp_or_real == "false_positive"):
        errors.append(
            f"verdict={verdict} 与 fp_or_real=false_positive 矛盾"
            "（判定误报须改用 reject_as_fp 并附 fp_evidence 完成固化；"
            "reject/defer 仅用于真实问题或证据不足）")
    if approving and fp_or_real == "uncertain":
        errors.append(f"verdict={verdict} 与 fp_or_real=uncertain 矛盾"
                      "（误报判定不确定须按保守口径阻塞，应改用 defer 并说明"
                      "缺失证据）")
    if approving and normalized.get("fixability") in ("risky", "unfixable"):
        errors.append(
            f"verdict={verdict} 与 fixability={normalized['fixability']} 矛盾"
            "（修复风险大于收益或暂无可行修复路径时不得批准执行，"
            "应改用 defer 并说明原因）")
    if approving and normalized.get("net_benefit") in ("negative", "neutral"):
        errors.append(
            f"verdict={verdict} 与 net_benefit={normalized['net_benefit']} 矛盾"
            "（仅净收益为 positive 才允许执行，否则应 reject 或 defer）")
    if approving and normalized.get("fix_approach") == "patch_deviation":
        errors.append(f"verdict={verdict} 禁止补丁方式修复"
                      "（fix_approach=patch_deviation）："
                      "须根因修复（fix_approach=root_cause）后重新提交")
    return errors
_MAX_EVIDENCE_DEPTH = 20
def _substantive_container_value(value, depth: int = 0) -> bool:
    if depth > _MAX_EVIDENCE_DEPTH:
        return False
    if value is None:
        return False
    if isinstance(value, str):
        return bool(value.strip())
    if isinstance(value, (bool, int, float)):
        return False
    if isinstance(value, dict):
        return any(_substantive_container_value(item, depth + 1)
                   for item in value.values())
    if isinstance(value, (list, tuple, set, frozenset)):
        return any(_substantive_container_value(item, depth + 1)
                   for item in value)
    return False
def is_missing_dimension(value) -> bool:
    if isinstance(value, (bool, int, float)):
        return True
    if value is None:
        return True
    if isinstance(value, str):
        return not value.strip()
    if isinstance(value, (dict, list, tuple, set, frozenset)):
        return not _substantive_container_value(value)
    return True
def _required_field_errors(normalized: dict, verdict: str) -> list[str]:
    errs: list[str] = []
    for field in _VERDICT_REQUIRED_FIELDS.get(verdict, ()):
        if is_missing_dimension(normalized.get(field)):
            errs.append(
                f"verdict={verdict} 须附审核维度 {field!r}（缺失则退回修正）")
    return errs
def _collect_enum_errors(normalized: dict) -> list[str]:
    return [
        f"{field} 须为 {'/'.join(allowed)} 之一，当前: {normalized.get(field)!r}"
        for field, allowed in _ENUM_VALIDATION_SPECS
        if normalized.get(field) is not None
        and normalized.get(field) not in allowed
    ]
def as_text(value: Any) -> str:
    return normalize_text(value).strip()
def _proposal_text(data: dict) -> str:
    keys = ("reason", "description", "boundary_justification", "decision",
            "rationale", "governance_method")
    return " ".join(as_text(data.get(key)) for key in keys if data.get(key))
def _method_result(status: str, violations: list[str], suggested: list[str],
                   **extra: Any) -> dict[str, Any]:
    result: dict[str, Any] = {
        "status": status,
        "violations": violations,
        "suggested_methods": suggested,
    }
    result.update(extra)
    return result
def _forbidden_violation(hits: tuple[str, ...], tail: str = "") -> str:
    text = "提案文本含拆分措辞：" + "、".join(hits)
    return f"{text}；{tail}" if tail else text
def _check_merge(data: dict, suggested: list[str],
                 forbidden_hits: tuple[str, ...]) -> dict[str, Any]:
    argument = MergeArgument(**merge_argument_payload(data))
    valid, errors = argument.validate()
    evidence = {"merge_argument": argument.as_dict()}
    if not valid:
        return _method_result("rewrite_required", errors, suggested, **evidence)
    if forbidden_hits:
        return _method_result(
            "rewrite_required",
            [_forbidden_violation(forbidden_hits, "合并方案不得夹带拆分手段")],
            suggested, **evidence)
    return _method_result("compliant", [], suggested, **evidence)
def _check_split(data: dict, suggested: list[str]) -> dict[str, Any]:
    if is_split_exception_valid(data):
        return _method_result("compliant", [], suggested,
                              note="拆分例外：已附人工批准与决策留痕")
    return _method_result(
        "rewrite_required",
        ["GOV-01：以拆分文件/模块作为治理手段；必须改写为 "
         + "/".join(GOVERNANCE_METHODS)],
        suggested,
        rewritten_proposal=rewrite_split_to_governance(data))
def _check_migrate(text: str, suggested: list[str],
                   forbidden_hits: tuple[str, ...]) -> dict[str, Any]:
    violations = migration_decoupling_errors(text)
    if forbidden_hits:
        violations.append(
            _forbidden_violation(forbidden_hits, "迁移方案不得夹带拆分手段"))
    if violations:
        return _method_result(
            "rewrite_required", violations,
            ["converge_dependency", "remove_duplication"])
    return _method_result("compliant", [], suggested)
def _declared_methods(data: dict) -> tuple[list[str], list[Any], bool]:
    declared = data.get("governance_method")
    if isinstance(declared, (set, frozenset)):
        declared_list = sorted(declared, key=str)
    elif isinstance(declared, (list, tuple)):
        declared_list = list(declared)
    else:
        declared_list = [declared]
    normalized: list[str] = []
    unknown: list[Any] = []
    for item in declared_list:
        if not as_text(item):
            continue
        norm = normalize_governance_method(item)
        if norm:
            normalized.append(norm)
        else:
            unknown.append(item)
    declared_any = any(as_text(item) for item in declared_list)
    return normalized, unknown, declared_any
def _unknown_method_message(unknown: list[Any]) -> str:
    return ("治理手段不在白名单："
            + "、".join(as_text(item) for item in unknown)
            + f"；合法集合={'/'.join(GOVERNANCE_METHODS)}")
def _governance_violations(action_type: str, unknown: list[Any],
                           declared_any: bool,
                           forbidden_hits: tuple[str, ...]) -> list[str]:
    domain = "/".join(GOVERNANCE_METHODS)
    candidates = (
        (bool(unknown), _unknown_method_message(unknown)),
        (action_type == "governance" and not declared_any,
         f"GOV-01：治理方案未声明治理手段，须显式选择 {domain}"),
        (bool(forbidden_hits),
         _forbidden_violation(forbidden_hits, "须改为非拆分治理方案")),
    )
    return [message for hit, message in candidates if hit]
def _check_governance(action_type: str, data: dict, suggested: list[str],
                      forbidden_hits: tuple[str, ...]) -> dict[str, Any]:
    declared, unknown, declared_any = _declared_methods(data)
    violations = _governance_violations(
        action_type, unknown, declared_any, forbidden_hits)
    result = _method_result(
        "rewrite_required" if violations else "compliant",
        violations,
        declared or suggested)
    if forbidden_hits or (action_type == "governance" and not declared):
        result["rewritten_proposal"] = rewrite_split_to_governance(data)
    return result
def _check_other(action_type: str, data: dict, text: str,
                 suggested: list[str],
                 forbidden_hits: tuple[str, ...]) -> dict[str, Any]:
    if forbidden_hits:
        return _method_result(
            "rewrite_required", [_forbidden_violation(forbidden_hits)],
            suggested, rewritten_proposal=rewrite_split_to_governance(data))
    if action_type in ("rewrite", "fix"):
        return _method_result(
            "compliant", [],
            list(classify_governance_method(text)) or suggested)
    if action_type:
        return _method_result(
            "rewrite_required",
            [(f"动作类型 {action_type!r} 未登记，无法复核治理手段；"
              "须改用已登记动作类型后重提")],
            suggested)
    return _method_result("not_applicable", [], [])
def _container_len(value: Any) -> int:
    return len(value) if isinstance(value, (list, tuple, set, frozenset)) else 0
def _apply_declared_method_gate(result: dict[str, Any],
                                unknown: list[Any]) -> dict[str, Any]:
    if not unknown:
        return result
    violations = [_unknown_method_message(unknown),
                  *result.get("violations", [])]
    status = result.get("status")
    if status in ("compliant", "not_applicable"):
        status = "rewrite_required"
    return {**result, "status": status, "violations": violations}
def _check_method(data: dict) -> dict[str, Any]:
    action_type = effective_governance_action_type(data)
    text = _proposal_text(data)
    suggested = list(suggest_governance_methods({
        "unrelated_blocks": _container_len(data.get("code_elements")),
    }))
    forbidden_hits = detect_forbidden_method(text)
    _declared, unknown, _declared_any = _declared_methods(data)
    if action_type == "merge":
        return _apply_declared_method_gate(
            _check_merge(data, suggested, forbidden_hits), unknown)
    if action_type == "split":
        return _apply_declared_method_gate(
            _check_split(data, suggested), unknown)
    if action_type == "migrate":
        return _apply_declared_method_gate(
            _check_migrate(text, suggested, forbidden_hits), unknown)
    if action_type == "governance":
        return _check_governance(action_type, data, suggested, forbidden_hits)
    return _apply_declared_method_gate(
        _check_other(action_type, data, text, suggested, forbidden_hits),
        unknown)
class _BoundaryEvidence(NamedTuple):
    fixed_source: str
    file_path: str
    has_imports: bool
    proposed_source: str
    invalid_reason: str
def _evidence_shape_error(field: str, value: Any,
                          expectation: str = "源码字符串或导入清单（list/tuple）") -> str:
    return (f"{field} 须为 {expectation}，"
            f"当前为 {type(value).__name__}，"
            "形态非法不可作为边界证据（fail-safe 阻断批准）")
def _boundary_path_error(raw_path: Any) -> str:
    if raw_path is None:
        return ""
    if not isinstance(raw_path, str):
        return _evidence_shape_error("file_path", raw_path, "路径字符串")
    text = raw_path.strip()
    if not text:
        return ""
    if any(ord(ch) < 32 or ord(ch) == 127 for ch in text):
        return (f"file_path 含控制字符，无法安全定位模块身份复核: "
                f"{raw_path!r}（fail-safe 阻断批准）")
    if not text.lower().endswith(".py"):
        return (f"file_path 须指向 Python 源文件（.py），当前: {raw_path!r}；"
                "无法定位模块身份复核（fail-safe 阻断批准）")
    return ""
def _declared_imports(raw: Any) -> tuple[list, bool]:
    proposed = [raw] if isinstance(raw, str) else raw
    if proposed is None:
        return [], True
    if not isinstance(proposed, (list, tuple)):
        return [], False
    if any(not isinstance(item, str) for item in proposed):
        return [], False
    return [item for item in proposed if item.strip()], True
def _boundary_evidence(data: dict) -> _BoundaryEvidence:
    raw_source = data.get("fixed_source")
    fixed_source = strip_bom(raw_source) \
        if isinstance(raw_source, str) else ""
    raw_path = data.get("file_path")
    declared, imports_ok = _declared_imports(data.get("proposed_imports"))
    invalid_reason = ""
    if raw_source is not None and not isinstance(raw_source, str):
        invalid_reason = _evidence_shape_error(
            "fixed_source", raw_source, "源码字符串")
    elif not imports_ok:
        invalid_reason = _evidence_shape_error(
            "proposed_imports", data.get("proposed_imports"))
    elif _has_boundary_evidence(fixed_source, bool(declared)):
        invalid_reason = _boundary_path_error(raw_path)
    if invalid_reason:
        return _BoundaryEvidence("", as_text(raw_path),
                                 False, "", invalid_reason)
    return _BoundaryEvidence(
        fixed_source=fixed_source,
        file_path=as_text(raw_path),
        has_imports=bool(declared),
        proposed_source="\n".join(as_text(item) for item in declared),
        invalid_reason="")
def _has_boundary_evidence(fixed_source: str, has_imports: bool) -> bool:
    return bool(fixed_source.strip() or has_imports)
def _anchor_boundary_path(file_path: str,
                          topology: ModuleTopology) -> tuple[str, bool]:
    anchor = topology.skill_root or topology.root_dir
    # 拓扑锚点已是 realpath；证据里的文件路径可能经符号链接访问（如
    # target_skills/<skill> → user_skills/<skill>），两端统一解析后才能正确判定归属。
    root = os.path.normcase(os.path.realpath(os.path.abspath(anchor)))
    target = file_path if os.path.isabs(file_path) \
        else os.path.join(anchor, file_path)
    target = os.path.realpath(os.path.abspath(target))
    try:
        rel = os.path.relpath(os.path.normcase(target), root)
    except ValueError as e:
        logger.debug("_anchor_boundary_path 跨盘符降级为绝对判定: %s", e)
        return target, False
    inside = not (rel == os.pardir or rel.startswith(os.pardir + os.sep))
    return target, inside
_BOUNDARY_PARSE_ERRORS = (SyntaxError, ValueError, RecursionError)
def _is_parseable_source(source: str) -> bool:
    try:
        # 仅做语法可解析性检查：``ast.parse`` 与 ``compile(..., 'exec')``
        # 抛同样的 ``SyntaxError``，但不生成可执行代码对象（避免动态编译面）。
        ast.parse(source, "<boundary>")
    except _BOUNDARY_PARSE_ERRORS as exc:
        logger.debug("边界证据源码不可解析（fail-safe unverified）: %s", exc)
        return False
    return True
def _check_boundary(data: dict,
                    topology: ModuleTopology | None) -> dict[str, Any]:
    evidence = _boundary_evidence(data)
    fixed_source = evidence.fixed_source
    file_path = evidence.file_path
    has_imports = evidence.has_imports
    proposed_source = evidence.proposed_source
    if evidence.invalid_reason:
        return {
            "status": "unverified",
            "violations": [],
            "checked": False,
            "reason": evidence.invalid_reason,
        }
    if not _has_boundary_evidence(fixed_source, has_imports):
        return {"status": "not_applicable", "violations": [], "checked": False}
    if topology is None:
        return {
            "status": "unverified",
            "violations": [],
            "checked": False,
            "reason": "缺少目标技能拓扑，无法复核导入边界（fail-safe 阻断批准）",
        }
    if not file_path:
        return {
            "status": "unverified",
            "violations": [],
            "checked": False,
            "reason": ("导入证据缺目标文件路径，无法定位模块身份复核"
                       "（fail-safe 阻断批准）"),
        }
    target, inside = _anchor_boundary_path(file_path, topology)
    if not inside:
        return {
            "status": "unverified",
            "violations": [],
            "checked": False,
            "reason": ("目标文件不在技能拓扑内，无法定位模块身份复核"
                       "（fail-safe 阻断批准）"),
        }
    source = "\n".join(
        part for part in (fixed_source, proposed_source) if part)
    if ((fixed_source.strip() and not _is_parseable_source(fixed_source))
            or not _is_parseable_source(source)):
        return {
            "status": "unverified",
            "violations": [],
            "checked": False,
            "reason": ("源码证据不可解析（语法错误/超深嵌套），无法复核导入"
                       "边界（fail-safe 阻断批准）"),
        }
    try:
        violations = check_source_boundary(source, target, topology)
    except Exception as exc:
        logger.warning(
            "边界复核异常（降级 unverified，阻断批准）: %s", exc,
            exc_info=True)
        return {
            "status": "unverified",
            "violations": [],
            "checked": False,
            "reason": f"边界复核异常（fail-safe 阻断批准）: {exc}",
        }
    if not violations:
        return {"status": "compliant", "violations": [], "checked": True}
    return {
        "status": "violation",
        "checked": True,
        "violations": [item.as_dict() for item in violations],
    }
def _strictest(review_status: str, declared_status: str = "") -> str:
    if not declared_status:
        return review_status
    if (_STATUS_SEVERITY.get(declared_status, 0)
            > _STATUS_SEVERITY.get(review_status, 0)):
        return declared_status
    return review_status
def _not_scoped_result(data: dict) -> dict[str, Any]:
    return {
        "scope": False,
        "action_type": normalized_governance_action_type(data),
        "method": {"status": "not_applicable", "violations": [],
                   "suggested_methods": []},
        "boundary": {"status": "not_applicable", "violations": [],
                     "checked": False},
        "effective_method_status": "not_applicable",
        "effective_boundary_status": "not_applicable",
        "blocked": False,
        "errors": [],
    }
def _resolve_topology(topology: ModuleTopology | None,
                      skill_dir: str) -> ModuleTopology | None:
    if topology is not None or not skill_dir:
        return topology
    try:
        return build_module_topology(skill_dir)
    except Exception as exc:
        logger.warning(
            "治理审核拓扑构建失败（边界维降级 unverified）: %s", exc,
            exc_info=True)
        return None
def _details(items: Any) -> str:
    if isinstance(items, str):
        return as_text(items)
    if isinstance(items, dict):
        items = [items]
    if not isinstance(items, (list, tuple, set, frozenset)):
        return as_text(items)
    parts = (
        as_text(item.get("message")) if isinstance(item, dict) else as_text(item)
        for item in items
    )
    return "；".join(part for part in parts if part)
def _declared_status(declared: str, allowed: tuple[str, ...]) -> str:
    if not declared:
        return ""
    if declared in allowed:
        return declared
    logger.warning(
        "[AIReview] 未知合规申报值 %r（合法值=%s），按 unverified 取严",
        declared, list(allowed))
    return "unverified"
def _declaration_errors(declared_method: str, declared_boundary: str,
                        method: dict[str, Any],
                        boundary: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if _review_worse_than_declared(declared_method, method["status"]):
        errors.append(
            f"治理手段申报 {declared_method} 但复核为 "
            f"{method['status']}：" + _details(method["violations"]))
    if declared_boundary == "compliant" and boundary["status"] != "compliant":
        detail = (_details(boundary["violations"])
                  or as_text(boundary.get("reason"))
                  or "未提供 fixed_source/file_path 证据，"
                     "无证据不得申报 compliant")
        errors.append(
            f"边界申报 compliant 但复核为 {boundary['status']}：{detail}")
    if (declared_boundary == "not_applicable"
            and boundary["status"] != "not_applicable"):
        errors.append(
            f"边界申报 not_applicable 但复核为 {boundary['status']}："
            "存在 fixed_source/proposed_imports 边界证据时必须复扫，"
            "无证据才可申报 not_applicable")
    return errors
def _review_worse_than_declared(declared: str, review_status: str) -> bool:
    if not declared:
        return False
    return (_STATUS_SEVERITY.get(review_status, 0)
            > _STATUS_SEVERITY.get(declared, 0))
def evaluate_governance_review(
        assessment: dict | None,
        topology: ModuleTopology | None = None,
        skill_dir: str = "",
        proposal: dict | None = None) -> dict[str, Any]:
    data = governance_proposal(assessment, proposal)
    if not governance_scope(data):
        scoped = _boundary_scoped_review(data, topology, skill_dir)
        return scoped if scoped is not None else _not_scoped_result(data)
    method = _check_method(data)
    topo = (_resolve_topology(topology, skill_dir)
            if _boundary_evidence_present(data) else None)
    boundary = _check_boundary(data, topo)
    declared_method = _declared_status(
        as_text(data.get("governance_method_compliance")),
        METHOD_COMPLIANCE_VALUES)
    declared_boundary = _declared_status(
        as_text(data.get("boundary_compliance")),
        BOUNDARY_COMPLIANCE_VALUES)
    effective_method = _strictest(method["status"], declared_method)
    effective_boundary = _strictest(boundary["status"], declared_boundary)
    errors = _declaration_errors(
        declared_method, declared_boundary, method, boundary)
    return {
        "scope": True,
        "action_type": normalized_governance_action_type(data),
        "method": method,
        "boundary": boundary,
        "effective_method_status": effective_method,
        "effective_boundary_status": effective_boundary,
        "blocked": bool(
            errors
            or effective_method not in _COMPLIANT_STATUSES
            or effective_boundary not in _COMPLIANT_STATUSES),
        "errors": errors,
    }
def _enum_declaration_errors(field: str, declared: str,
                             allowed: tuple[str, ...], *,
                             required: bool) -> list[str]:
    if not declared:
        if not required:
            return []
        return [f"治理范围裁决缺 {field}（{'/'.join(allowed)}）"]
    if declared not in allowed:
        return [f"{field} 非法值 {declared!r}，值域={list(allowed)}"]
    return []
def _declared_value_errors(declared_method: str,
                           declared_boundary: str) -> list[str]:
    return [
        *_enum_declaration_errors(
            "governance_method_compliance", declared_method,
            METHOD_COMPLIANCE_VALUES, required=True),
        *_enum_declaration_errors(
            "boundary_compliance", declared_boundary,
            BOUNDARY_COMPLIANCE_VALUES, required=True),
    ]
def _merge_verification(data: dict, verification: dict | None) -> dict:
    proposal = governance_proposal(data)
    proposal.pop("governance_proposal", None)
    if isinstance(verification, dict):
        for key, value in verification.items():
            if value is not None:
                proposal[key] = value
    if "verdict" in data:
        proposal["verdict"] = data["verdict"]
    return proposal
def _approval_errors(review: dict[str, Any], verdict: str) -> list[str]:
    if verdict not in APPROVAL_VERDICTS:
        return []
    errors: list[str] = []
    for label, status_key, block_key in (
            ("治理手段", "effective_method_status", "method"),
            ("边界", "effective_boundary_status", "boundary")):
        status = review[status_key]
        if status in _COMPLIANT_STATUSES:
            continue
        detail = (_details(review[block_key]["violations"])
                  or as_text(review[block_key].get("reason")))
        errors.append(
            f"批准类裁决要求{label}合规：当前为 {status}；" + detail)
    return errors
def _boundary_evidence_present(data: dict) -> bool:
    evidence = _boundary_evidence(data)
    return bool(evidence.invalid_reason
                or _has_boundary_evidence(evidence.fixed_source,
                                          evidence.has_imports))
def _boundary_only_review(data: dict, topology: ModuleTopology | None,
                          declared_boundary: str = "") -> dict[str, Any]:
    boundary = _check_boundary(data, topology)
    effective_boundary = _strictest(boundary["status"], declared_boundary)
    return {
        "scope": False,
        "boundary_only": True,
        "action_type": normalized_governance_action_type(data),
        "method": {"status": "not_applicable", "violations": [],
                   "suggested_methods": []},
        "boundary": boundary,
        "effective_method_status": "not_applicable",
        "effective_boundary_status": effective_boundary,
        "blocked": effective_boundary not in _COMPLIANT_STATUSES,
        "errors": [],
    }
def _boundary_scoped_review(data: dict, topology: ModuleTopology | None,
                            skill_dir: str) -> dict[str, Any] | None:
    raw_boundary = as_text(data.get("boundary_compliance"))
    has_evidence = _boundary_evidence_present(data)
    if not has_evidence and not raw_boundary:
        return None
    declared_boundary = _declared_status(
        raw_boundary, BOUNDARY_COMPLIANCE_VALUES)
    review = _boundary_only_review(
        data, _resolve_topology(topology, skill_dir) if has_evidence else None,
        declared_boundary)
    errors = _enum_declaration_errors(
        "boundary_compliance", raw_boundary, BOUNDARY_COMPLIANCE_VALUES,
        required=False)
    errors.extend(_declaration_errors(
        "", declared_boundary, review["method"], review["boundary"]))
    errors.extend(_approval_errors(review, as_text(data.get("verdict"))))
    review["errors"] = errors
    review["blocked"] = bool(review["blocked"] or errors)
    return review
def validate_governance_assessment(
        assessment: dict | None,
        topology: ModuleTopology | None = None,
        skill_dir: str = "",
        verification: dict | None = None) -> tuple[bool, list[str], dict]:
    if assessment is not None and not isinstance(assessment, dict):
        return False, [
            (f"治理评估 assessment 须为 dict 或 None，当前: "
             f"{type(assessment).__name__}")
        ], {}
    data = assessment if isinstance(assessment, dict) else {}
    merged = _merge_verification(data, verification)
    if not governance_scope(merged):
        review = _boundary_scoped_review(merged, topology, skill_dir)
        if review is None:
            return True, [], {}
        errors = list(review.get("errors") or [])
        return (not errors), errors, review
    review = evaluate_governance_review(
        merged, topology=topology, skill_dir=skill_dir)
    errors = _declared_value_errors(
        as_text(merged.get("governance_method_compliance")),
        as_text(merged.get("boundary_compliance")))
    errors.extend(review["errors"])
    errors.extend(_approval_errors(review, as_text(merged.get("verdict"))))
    return (not errors), errors, review
_CONTAINER_LIST_TYPES = (tuple, set, frozenset)
def _normalize_list_fields(data: dict, keys: tuple[str, ...]) -> None:
    for key in keys:
        value = data.get(key)
        if value is None or isinstance(value, list):
            continue
        if isinstance(value, _CONTAINER_LIST_TYPES):
            items = [str(item) for item in value]
            data[key] = sorted(items) if isinstance(value, (set, frozenset)) \
                else items
            continue
        data[key] = [str(value)]
def validate_review_assessment(
        assessment, topology=None, skill_dir: str = "",
        verification: dict | None = None) -> tuple[bool, list[str], dict]:
    errors: list[str] = []
    if not isinstance(assessment, dict):
        return False, ["assessment 须为 dict（四维审核信息框架）"], {}
    normalized = dict(assessment)
    verdict = as_text(normalized.get("verdict"))
    if verdict:
        normalized["verdict"] = verdict
    if verdict not in VERDICT_VALUES:
        errors.append(f"verdict 必填且须为 {'/'.join(VERDICT_VALUES)} 之一，当前: {verdict!r}")
    else:
        errors.extend(_verdict_contradictions(
            normalized, verdict, verdict in APPROVAL_VERDICTS))
        errors.extend(_required_field_errors(normalized, verdict))
    errors.extend(_collect_enum_errors(normalized))
    _normalize_list_fields(normalized, ("pros", "cons"))
    _gok, _gerrors, _greview = validate_governance_assessment(
        normalized, topology=topology, skill_dir=skill_dir,
        verification=verification)
    if _gerrors:
        errors.extend(_gerrors)
    if _greview:
        normalized["governance_review"] = _greview
    return (not errors), errors, normalized
def _governance_decision_kind(assessment: dict) -> str:
    if effective_governance_action_type(governance_proposal(assessment)) == "merge":
        return "merge"
    review = assessment.get("governance_review")
    if not isinstance(review, dict):
        return "governance"
    if review.get("boundary_only") is True:
        return "boundary"
    boundary = review.get("boundary")
    if isinstance(boundary, dict) and boundary.get("status") == "violation":
        return "boundary"
    return "governance"
def _is_governance_assessment(assessment: dict) -> bool:
    review = assessment.get("governance_review")
    if isinstance(review, dict) and (
            review.get("scope") is True or review.get("boundary_only") is True):
        return True
    return governance_scope(assessment)
def _governance_merge_target(proposal: dict, review: dict,
                            skill_dir: str) -> str:
    action = dict(proposal)
    if not (action.get("source_files") or action.get("merge_sources")
            or action.get("source") or action.get("target")):
        action["target"] = review.get("target")
    return merge_target_key(action, skill_dir)
def _governance_decision_payload(assessment: dict, review: dict, kind: str,
                                 skill_dir: str) -> tuple[str, dict]:
    proposal = governance_proposal(assessment)
    if kind == "merge":
        return (_governance_merge_target(proposal, review, skill_dir),
                merge_argument_payload(proposal))
    target = decision_target_key(
        proposal.get("target") or review.get("target")
        or review.get("review_id"), skill_dir)
    return target, {
        "governance_review": assessment.get("governance_review") or {},
        "governance_method": (proposal.get("governance_method")
                              or assessment.get("governance_method") or []),
    }
def record_governance_decision(review: dict, assessment: dict | None,
                                result: dict, skill_dir: str | None) -> None:
    if not skill_dir or not isinstance(assessment, dict):
        return
    if not _is_governance_assessment(assessment):
        return
    try:
        kind = _governance_decision_kind(assessment)
        target, payload = _governance_decision_payload(
            assessment, review, kind, skill_dir)
        record_decision(
            skill_dir, kind=kind, target=target, payload=payload,
            decision=as_text(assessment.get("verdict")
                             or as_dict(result).get("status")),
            rationale=str(assessment.get("verdict_rationale")
                          or assessment.get("rationale") or ""),
            approved_by="ai")
    except Exception as exc:  # noqa: BLE001
        logger.warning("[AIReview] 治理决策留痕失败（不影响执行）: %s", exc)
def record_review_verdict(review: dict, assessment: dict | None,
                           result: dict, skill_dir: str | None = None,
                           fixed_source_sha256: str = "") -> None:
    try:
        write_verdict_trace(review, assessment, result, skill_dir,
                            fixed_source_sha256)
    except Exception as exc:
        logger.warning(
            "[AIReview] verdict trace 留痕失败（继续治理决策留痕）: %s",
            exc, exc_info=True)
    record_governance_decision(review, assessment, result, skill_dir)

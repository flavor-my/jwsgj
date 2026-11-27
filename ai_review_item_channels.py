from __future__ import annotations

import hashlib
import json
import logging
import math

from jwsgj.ai_review_item_plan import (
    _PLAN_COLLECT_MAX_ITEMS,
    _enhancement_action_type,
    _load_plan_queue,
    _queue_skill_dir,
    feedback_plan_path,
    identity_pair,
    is_pending_plan,
    run_code_level_feedback,
    security_plan_path,
)
from jwsgj.diag_guard_state import max_review_seq
from jwsgj.diag_types_normalize import (
    as_list,
    normalize_file_ref,
    normalize_line_no,
    str_or,
)
from jwsgj.diag_types_vocab import FIELD_EXPECTED_IMPACT, FIELD_SUGGESTED_VALUE
from jwsgj.fix_guide_rule_identity import get_fix_guidance, resolve_rule_alias
from jwsgj.retrospective_ledger import (
    get_pending_enhancements,
    get_retrospective_history,
)
from jwsgj.runtime_paths import adjustment_plan_path, cv_uncertain_path
from jwsgj.runtime_scope import normalize_text
from jwsgj.treatment_evidence import extract_code_context_in_project
from jwsgj.treatment_experience import get_ai_fix_candidates

__all__ = [
    'CHANNELS',
    'CHANNEL_ITEM_KIND',
    'CHANNEL_REVIEW_INPUT_CONTRACT',
    'CHANNEL_TARGET_KIND',
    'PROVENANCE_KEYS',
    'collect_adjustment_reviews',
    'collect_cv_uncertain_reviews',
    'collect_enhancement_reviews',
    'collect_feedback_reviews',
    'collect_security_reviews',
    'collect_treatment_reviews',
    'describe_review_item_keys',
    'normalize_cleanup_reviews',
    'normalize_review_item',
    'resolve_entry_severity',
]
logger = logging.getLogger(__name__)
logger.info("ai_review_item_channels 已加载: %d 项导出", len(__all__))
_CHANNEL_EXPECTED_EVIDENCE_KEYS: dict[str, tuple] = {
    "treatment": (
        "code_context", "function_summary", "diagnosis_evidence",
        "cv_context", "fix_plan", "fix_guidance", "fixer_risk",
        "fix_precheck", "fix_experience", "treatment_history",
        "rule_fp_history",
    ),
    "feedback": (
        "plan", "description", FIELD_SUGGESTED_VALUE,
        FIELD_EXPECTED_IMPACT, "fix_guidance", "level", "confidence",
        "feedback_history", "rule_fp_history",
    ),
    "enhancement": (
        "entry", "description", FIELD_SUGGESTED_VALUE,
        FIELD_EXPECTED_IMPACT, "fix_guidance", "confidence",
        "enhancement_history", "rule_fp_history",
    ),
    "security": (
        "plan", "code_context", FIELD_SUGGESTED_VALUE, "fix_guidance",
        "rule_fp_history",
    ),
    "cleanup": ("plan", "code_context"),
    "adjustment": (
        "proposal", FIELD_SUGGESTED_VALUE, "kind", "adjustment_history",
        "rule_fp_history",
    ),
    "cv_uncertain": ("cv_evidence", "entry", "code_context"),
}
_CHANNEL_LEGITIMATE_ABSENT_KEYS: dict[str, tuple] = {
    "treatment": (
        "cv_context", "fix_experience", "fixer_risk",
        "treatment_history", "rule_fp_history",
    ),
    "feedback": ("rule_fp_history", "feedback_history"),
    "enhancement": ("enhancement_history", "rule_fp_history"),
    "security": ("rule_fp_history",),
    "cleanup": ("code_context",),
    "adjustment": ("adjustment_history", "rule_fp_history"),
    "cv_uncertain": ("code_context",),
}
def _is_dynamic_legitimate_absent(channel: str, item: dict, key: str) -> bool:
    if channel != "treatment" or key != "function_summary":
        return False
    file_path = str(item.get("file_path") or "").strip()
    return bool(file_path) and not file_path.lower().endswith(".py")
def _effective_legitimate_absent_keys(channel: str, item: dict) -> set:
    keys = set(_CHANNEL_LEGITIMATE_ABSENT_KEYS.get(channel, ()))
    for key in _CHANNEL_EXPECTED_EVIDENCE_KEYS.get(channel, ()):
        if _is_dynamic_legitimate_absent(channel, item, key):
            keys.add(key)
    return keys
def _build_evidence_completeness(item: dict) -> dict:
    _ch = str(item.get("channel") or "")
    _expected = _CHANNEL_EXPECTED_EVIDENCE_KEYS.get(_ch)
    if not _expected:
        return {"present": [], "legitimate_absent": [], "missing": [],
                "verdict": "unknown"}
    _legit = _effective_legitimate_absent_keys(_ch, item)
    _present: list = []
    _legit_absent: list = []
    _missing: list = []
    for _k in _expected:
        _v = item.get(_k)
        if _is_substantive(_v):
            _present.append(_k)
        elif _k in _legit:
            _legit_absent.append(_k)
        else:
            _missing.append(_k)
    return {
        "present": _present,
        "legitimate_absent": _legit_absent,
        "missing": _missing,
        "verdict": "incomplete" if _missing else "complete",
    }
def _is_substantive(value) -> bool:
    if isinstance(value, str):
        return bool(value.strip())
    if isinstance(value, (list, tuple, set, frozenset, dict)):
        return bool(value)
    return value is not None
def _has_substance(value) -> bool:
    return (isinstance(value, dict)
            and any(_is_substantive(v) for v in value.values()))
def _is_nonempty_str(value) -> bool:
    return isinstance(value, str) and bool(value.strip())
def _is_real_number(value) -> bool:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return False
    if isinstance(value, int):
        return True
    return math.isfinite(value)
def _is_nonneg_int(value) -> bool:
    return _is_real_number(value) and isinstance(value, int) and value >= 0
def _normalized_confidence(value):
    if not _is_real_number(value):
        return None
    if value < 0:
        return 0.0
    if value > 1:
        return 1.0
    return value
def _normalized_review_text(value) -> str:
    return normalize_text(value) if value else ""
def _norm_basic_review_fields(item: dict) -> None:
    if "channel" in item:
        item["channel"] = str_or(item.get("channel"))
    item["strategy"] = _normalized_review_text(item.get("strategy"))
    if not item["strategy"].strip():
        item["strategy"] = "ai_review"
    item["confidence"] = _normalized_confidence(item.get("confidence"))
    item["severity"] = _normalized_review_text(item.get("severity"))
    item["rule_id"] = _normalized_review_text(item.get("rule_id"))
    item["description"] = _normalized_review_text(item.get("description"))
def _carrier_of(item: dict) -> dict | None:
    _plan = item.get("plan")
    if isinstance(_plan, dict):
        _entry = _plan.get("entry")
        return _entry if isinstance(_entry, dict) else _plan
    for _key in ("entry", "proposal"):
        _carrier = item.get(_key)
        if isinstance(_carrier, dict):
            return _carrier
    return None
def _derive_carrier_provenance(item: dict) -> None:
    _carrier = _carrier_of(item)
    if _carrier is None:
        return
    _prov = {k: _carrier.get(k) for k in PROVENANCE_KEYS
             if _is_substantive(_carrier.get(k))}
    if _prov:
        item["provenance"] = _prov
def _diagnosis_context_view(item: dict) -> dict | None:
    diagnosis = item.get("diagnosis_evidence")
    if not _has_substance(diagnosis):
        return None
    view = dict(diagnosis)
    cv_context = item.get("cv_context")
    if _has_substance(cv_context):
        view["cv_context"] = cv_context
    return view
def _treatment_context_view(item: dict) -> dict | None:
    view: dict = {}
    fix_plan = item.get("fix_plan")
    if _has_substance(fix_plan):
        view["fix_plan"] = fix_plan
    fix_guidance = item.get("fix_guidance")
    if _is_nonempty_str(fix_guidance):
        view["fix_guidance"] = fix_guidance
    treatment_history = item.get("treatment_history")
    if (isinstance(treatment_history, list)
            and any(_has_substance(rec) if isinstance(rec, dict)
                    else _is_substantive(rec) for rec in treatment_history)):
        view["treatment_history"] = treatment_history
    return view or None
def _derive_treatment_provenance(item: dict) -> dict:
    _derived: dict = {}
    _dc = _diagnosis_context_view(item)
    if _dc:
        _derived["diagnosis_context"] = _dc
    _tc = _treatment_context_view(item)
    if _tc:
        _derived["treatment_context"] = _tc
    if _derived:
        _derived["phase"] = "treatment_review"
        _derived["source"] = "ai_fix_candidates"
    return _derived
_EVOLUTION_PHASE_BY_CHANNEL = {
    "feedback": "fupan_review",
    "enhancement": "evolution_review",
}
_EVOLUTION_PROVENANCE_LAYERS = (
    "diagnosis_context", "treatment_context", "retrospective_context")
def _annotate_evolution_phase_source(item: dict) -> None:
    _ch = item.get("channel")
    if _ch not in _EVOLUTION_PHASE_BY_CHANNEL:
        return
    _pv_evo = item.get("provenance")
    if not isinstance(_pv_evo, dict):
        return
    if not all(_is_substantive(_pv_evo.get(_k))
               for _k in _EVOLUTION_PROVENANCE_LAYERS):
        return
    if not _is_nonempty_str(_pv_evo.get("phase")):
        _pv_evo["phase"] = _EVOLUTION_PHASE_BY_CHANNEL[_ch]
    if not _is_nonempty_str(_pv_evo.get("source")):
        _pv_evo["source"] = "ai_review_governance"
def _ensure_provenance_strata(item: dict) -> None:
    _pv = item.get("provenance")
    item["provenance_strata"] = (
        sum(1 for k in PROVENANCE_KEYS if _is_substantive(_pv.get(k)))
        if isinstance(_pv, dict) else 0)
def _annotate_item_semantics(item: dict) -> None:
    _ch = item.get("channel")
    if isinstance(_ch, str) and _ch:
        _kind = item.get("item_kind")
        if not _is_nonempty_str(_kind):
            item["item_kind"] = CHANNEL_ITEM_KIND.get(_ch, _ch)
        _tkind = item.get("target_kind")
        if not _is_nonempty_str(_tkind):
            item["target_kind"] = CHANNEL_TARGET_KIND.get(_ch, "")
    _ensure_rule_guidance_view(item)
_CHANNEL_RULE_GUIDANCE = frozenset(
    ("treatment", "feedback", "enhancement", "security"))
def _ensure_rule_guidance_view(item: dict) -> None:
    if item.get("channel") not in _CHANNEL_RULE_GUIDANCE:
        return
    _rid = normalize_text(item.get("rule_id"))
    if not _is_nonempty_str(item.get("fix_guidance")):
        _guidance = get_fix_guidance(_rid, normalize_text(item.get("description")))
        if _guidance:
            item["fix_guidance"] = _guidance
    if not _is_nonempty_str(item.get("rule_id_canonical")):
        item["rule_id_canonical"] = resolve_rule_alias(_rid)
def _unify_cv_evidence_aliases(item: dict) -> None:
    _cve = item.get("cv_evidence")
    if not isinstance(_cve, dict) or not _cve:
        return
    if not _is_nonempty_str(_cve.get("cv_conclusion")):
        _cve["cv_conclusion"] = normalize_text(_cve.get("conclusion"))
    _cv_confidence = _normalized_confidence(_cve.get("cv_confidence"))
    if _cv_confidence is None:
        _cv_confidence = _normalized_confidence(
            _cve.get("adjusted_confidence"))
    _cve["cv_confidence"] = (
        0.0 if _cv_confidence is None else _cv_confidence)
    if not _is_nonneg_int(_cve.get("cv_source_count")):
        _srcs = _cve.get("sources")
        _cve["cv_source_count"] = len(_srcs) if isinstance(_srcs, list) else 0
    if not _is_nonempty_str(_cve.get("cv_locator")):
        _cve["cv_locator"] = normalize_text(item.get("target"))
def _ensure_provenance_view(item: dict) -> None:
    if _has_substance(item.get("provenance")):
        return
    _derive_carrier_provenance(item)
    if _has_substance(item.get("provenance")):
        return
    if item.get("channel") == "treatment":
        _derived = _derive_treatment_provenance(item)
        if _derived:
            item["provenance"] = _derived
            return
    if "provenance" in item:
        item.pop("provenance", None)
def normalize_review_item(item: dict) -> dict:
    if not isinstance(item, dict):
        return item
    _norm_basic_review_fields(item)
    _annotate_item_semantics(item)
    _ensure_provenance_view(item)
    _annotate_evolution_phase_source(item)
    _ensure_provenance_strata(item)
    item["evidence_completeness"] = _build_evidence_completeness(item)
    _unify_cv_evidence_aliases(item)
    return item
PROVENANCE_KEYS = ("phase", "source", "diagnosis_context",
                    "treatment_context", "retrospective_context")
CHANNEL_ITEM_KIND = {
    "treatment": "code_fix",
    "security": "code_fix",
    "cleanup": "code_clean",
    "feedback": "code_feedback",
    "enhancement": "enhancement",
    "adjustment": "param_adjust",
    "cv_uncertain": "semantic_review",
}
CHANNEL_TARGET_KIND = {
    "treatment": "rule_id",
    "security": "rule_id",
    "cleanup": "target",
    "feedback": "target",
    "enhancement": "target",
    "adjustment": "adjustment_key",
    "cv_uncertain": "locator",
}
CHANNELS = ("treatment", "feedback", "enhancement", "adjustment", "cleanup", "cv_uncertain", "security")
_REVIEW_TRACE_SUFFIX = (
    "信息完整度：provenance_strata（<3 须在 assessment 附注证据缺口）")
CHANNEL_REVIEW_INPUT_CONTRACT: dict[str, str] = {
    "treatment": (
        "治疗阶段审核输入（完整诊断信息+治疗建议）——"
        "完整诊断信息：code_context 代码现场（自适应窗口："
        "P0±20/P1±16/P2±12/P3±8，目标行所在函数 ≤60 行时全覆盖完整函数体，"
        "上限 ±40）+ function_summary 函数摘要 + "
        "diagnosis_evidence 诊断证据链（message/code_snippet/sources/"
        "evidence_strength/adjusted_confidence/evidence_type/conclusion/"
        "rule_applied/locator/finding_id/notes/domain + "
        "raw_finding_digest 白名单摘要：pattern/ast_node_type/行列区间等 "
        "≤12 键体积可控，缺省=诊断侧无白名单键非断链）+ cv_context CV 结论上下文；"
        "完整治疗建议：fix_plan 治疗方案（strategy/risk_level/regression_plan"
        "〔恒在：恒 targeted_tests=True+full_regression=False，"
        "preview_tests/preview_mode 为定向回归测试清单只读预览〕）+ "
        "fix_guidance 规则指引 + fixer_risk 风险分级 + fix_precheck 写前预检 + "
        "fix_experience 历史修复经验；"
        "历史基线：treatment_history 治疗尝试史 + rule_fp_history 规则误报率；"
        "信息完整度：provenance 派生视图 + provenance_strata（<3 须在 "
        "assessment 附注证据缺口，不得脑补缺失证据）"),
    "feedback": (
        "反哺进化阶段审核输入（完整诊断+治疗+复盘+进化建议）——"
        "三层溯源：plan.entry 源建议全文 / provenance 视图 "
        "（diagnosis_context 诊断实证 + treatment_context 治疗实证 + "
        "retrospective_context 复盘根因 issues_found）；"
        "进化建议本体：description + suggested_value + expected_impact + "
        "fix_guidance + level（L1 阈值/L2 逻辑/L3 CV规则/L4 FP抑制）+ "
        "confidence；"
        "历史基线：feedback_history 同类 target 历史裁决统计（applied/"
        "rejected/deferred 计数+last_reject_reason，与 enhancement 通道 "
        "enhancement_history 同口径同源——feedback 裁决经销项联动回流 "
        "enhancement_log）+ rule_fp_history 规则误报率 + plan.entry 内"
        "全局统计；"
        + _REVIEW_TRACE_SUFFIX),
    "enhancement": (
        "反哺进化阶段审核输入（完整诊断+治疗+复盘+进化建议）——"
        "三层溯源：entry 源建议全文 / provenance 视图 "
        "（diagnosis_context 诊断实证 + treatment_context 治疗实证 + "
        "retrospective_context 复盘根因 issues_found）；"
        "进化建议本体：description + suggested_value + expected_impact + "
        "fix_guidance + strategy(action_type) + confidence；"
        "历史基线：enhancement_history 同类建议裁决轨迹+last_reject_reason + "
        "rule_fp_history；"
        + _REVIEW_TRACE_SUFFIX),
    "security": (
        "安全修复审核输入（CRITICAL/HIGH 安全建议，requires_fixed_source="
        "True）——完整证据面：plan 安全修复方案全文（漏洞类型/污点路径/"
        "边界校验要求）+ code_context 代码现场 + suggested_value 建议修复值"
        "（参数化查询/凭证外部化等）+ fix_guidance 修复指引；"
        "历史基线：rule_fp_history 规则误报率；"
        "审核维重点：严重性复核（CRITICAL/HIGH 是否成立）+ 误报判定"
        "（污点是否可达/是否有既有防线）+ fix_approach（P0 口径必填"
        "root_cause，缺失或 patch_deviation 由结构校验退回）；"
        + _REVIEW_TRACE_SUFFIX),
    "cleanup": (
        "清理方案审核输入（requires_fixed_source 写码通道或 plan 自带"
        "源码回退）——完整证据面：plan 清理方案全文（plan_id/category/"
        "影响面/fixed_source 预览）+ code_context 目标现场；"
        "审核维重点：影响面复核（引用链/动态注册/tests 消费豁免是否已核）"
        "+ 可逆性（safe_delete 回收站通道）+ fix_approach（P0 口径必填"
        "root_cause）；" + _REVIEW_TRACE_SUFFIX),
    "adjustment": (
        "参数调整审核输入（诊断/CV/修复器参数，写入生效文件可经 "
        "FeedbackRollbackManager 回滚）——完整证据面：proposal 参数调整提案"
        "全文（diagnosis_context/treatment_context/retrospective_context "
        "三维背景 + kind 调整类别 + suggested_value 目标值）+ "
        "adjustment_history 同类调整历史裁决统计（approved/rejected 数"
        "+last_reject_reason，利弊权衡基线）+ rule_fp_history；"
        "审核维重点：利弊权衡（P0/P1 永不抑制阈值下限）+ 与历史裁决"
        "振荡检测（同类调整反复翻转即 defer）；"
        + _REVIEW_TRACE_SUFFIX),
    "cv_uncertain": (
        "CV 语义复核审核输入（CV 结论不确定/矛盾且 P0/P1 + 被抑制项复核"
        "）——完整证据面：cv_evidence CV 多源证据聚合（conclusion/sources/"
        "evidence_strength/adjusted_confidence/counter_evidence(+reasons)/"
        "suppressed_review/suppression_rule/suppression_evidence/"
        "evidence_detail/conclusion_params/investigated_review/"
        "review_flagged/single_source_confirmed/forced_security，别名键族"
        "cv_conclusion/cv_confidence/cv_source_count/cv_locator 恒在）+ "
        "entry 队列条目原文（含三段抑制依据与复核标记全貌）；"
        "审核维重点：误报判定（抑制是否成立，不得臆断补全缺失证据）+ "
        "证据强度（独立源数，单源结论降权）；"
        + _REVIEW_TRACE_SUFFIX),
}
_COMMON_KEY_SEMANTICS: dict[str, str] = {
        "channel": "通道标识（treatment/feedback/enhancement/adjustment/"
                   "cleanup/cv_uncertain/security 七值之一）",
        "review_id": "裁决入口唯一定位键（销项/裁决回填凭此定位单条，"
                     "缺失=永远无法销项已拦截不入队）",
        "target": "审核对象定位（locator 或复合键；与 target_kind 配对阅读）",
        "rule_id": "命中规则 ID（规则历史误报率/修复经验关联键）",
        "finding_id": "finding 身份锚（诊断→治疗→审核→裁决全链 join 主键；"
                     "treatment 通道由收集层从 diagnosis_evidence 提取置顶，"
                     "凭本键直接回查诊断 finding 与归零台账事件；无 finding "
                     "级定位的通道（enhancement/adjustment 等）为空串）",
        "file_path": "目标文件路径（空串=条目无文件对象，如 adjustment 参数类）",
        "line": "目标行号（0=无行级定位）",
        "severity": "严重度（P0/P1/P2/P3 词系；严重性复核维的判定对象）",
        "strategy": "修复策略标识（恒 str，空白归一 ai_review）",
        "description": "问题描述（含通道前缀标记裁决语义，如 suppressed 复核的"
                       "「裁决抑制是否成立」）",
        "confidence": "生产端置信度（None=未评估语义；脏值已归一）",
        "code_context": "代码现场（队列携带或按 file+line 现提；空=无现场，"
                       "代码类通道缺失时应以 plan／队列原文为据）；"
                       "treatment 通道另有自适应窗口（口径见通道输入契约）"
                       "——高危项与小函数审核可见完整控制流",
        "fix_guidance": "修复指引（根因方向建议；无指引时 AI 需自定根因路线）",
        "requires_fixed_source": "是否需 AI 提交修复源码全文执写盘",
        "apply_hint": "执行入口提示（该通道的落地函数签名）",
        "provenance": "四层溯源视图（phase/source 两标注 + diagnosis/"
                     "treatment/retrospective 三层证据，键面 SSOT="
                     "PROVENANCE_KEYS 五键；省缺=载体无溯源信息）。"
                     "treatment 治疗通道无"
                     "plan/entry/proposal 载体，由收集层从顶层证据键派生"
                     "视图（diagnosis_evidence+cv_context→diagnosis_context；"
                     "fix_plan+fix_guidance+treatment_history→"
                     "treatment_context；phase=treatment_review、source="
                     "ai_fix_candidates 通道语义标注）——仅确有实质诊断/"
                     "治疗证据时建视图（不造空层），派生后 strata 如实"
                     "反映治疗候选的信息完整度且常态=4",
        "provenance_strata": "溯源命中层数视图键（0-5，恒在）：四层溯源航迹"
                            "命中计数，<3 即审核依据存在断链需在 assessment"
                            "附注证据缺口；0=载体无溯源且无实质顶层证据"
                            "（历史/脏条目常态），不等于可盲裁；treatment "
                            "通道经派生视图正常形态=4（诊断+治疗两层+"
                            "phase/source 标注），retrospective_context 层"
                            "如实缺省（治疗阶段尚无复盘产物）",
        "evidence_completeness": "证据完整度三态机读视图（恒注"
                      "入）：present/legitimate_absent/missing 三键清单 + "
                      "verdict（complete|incomplete|unknown）。missing 非空"
                      "（verdict=incomplete）即审核依据断链嫌疑，须在 "
                      "assessment 附注证据缺口后裁，不得脑补；"
                      "legitimate_absent 为「无历史数据/无产物」合法缺省"
                      "（cv_context 无 CV 产物/fix_experience 无经验命中/"
                      "fixer_risk 规则不在风险表/各类 *_history 首次无历史），"
                      "免附注防噪音；另有动态规则——treatment 非 .py 目标的 "
                      "function_summary 豁免（非代码对象无函数可摘要，"
                      "口径见 _build_evidence_completeness docstring）；"
                      "键面 SSOT=_CHANNEL_EXPECTED_EVIDENCE_KEYS"
                      "与 _CHANNEL_LEGITIMATE_ABSENT_KEYS（收集层）+动态规则",
        "item_kind": "动作类型统一视图（"
                    + "/".join(dict.fromkeys(CHANNEL_ITEM_KIND.values()))
                    + "；词表 SSOT=CHANNEL_ITEM_KIND）",
        "target_kind": "target 语义标注（"
                    + "/".join(dict.fromkeys(CHANNEL_TARGET_KIND.values()))
                    + "；词表 SSOT=CHANNEL_TARGET_KIND）",
}
_CHANNEL_EVIDENCE_KEY_SEMANTICS: dict[str, dict[str, str]] = {
        "treatment": {
            "fix_plan": "治疗方案（strategy/risk 分级/regression_plan 恒"
                       " targeted_tests=True+full_regression=False；"
                       "regression_plan 恒在且 preview_tests/"
                       "preview_mode 为定向回归测试清单只读预览，"
                       "缺省=无对应测试或定位失败非断链）",
            "treatment_history": "最近 5 次治疗尝试历史（成败+原因；校准"
                                "可修复性、防重复提交已失败修法）",
            "cv_context": "CV 上下文（结论/独立源数/调整后置信度/溯源）",
            "diagnosis_evidence": "诊断原始证据（检测器明细/引擎相位；"
                                  "含 raw_finding_digest 白名单"
                                  "摘要——pattern/ast_node_type/行列区间等"
                                  "≤12 键体积可控，缺省=诊断侧无白名单键"
                                  "非断链）",
            "fix_experience": "修复经验库命中记录（同类问题历史修法与结果）",
            "fix_precheck": "写前预检结果（幻觉 API 差集等）",
            "fixer_risk": "修复器风险分级证据面",
            "function_summary": "目标函数摘要（签名/职责概述）",
            "orig_status": "治疗项入队前原始状态",
            "index": "治疗候选序号（apply_ai_fix 传入参）",
            "rule_id_canonical": "规则 ID 规范化形态（跨轮匹配稳定键）",
        },
        "cv_uncertain": {
            "cv_evidence": "CV 多源证据聚合｛conclusion/sources/"
                          "evidence_strength/adjusted_confidence/"
                          "counter_evidence(+reasons)/suppressed_review/"
                          "suppression_rule/suppression_evidence/"
                          "evidence_detail/conclusion_params/"
                          "investigated_review/review_flagged/"
                          "single_source_confirmed/forced_security｝—"
                          "缺键即复核依据断链，不得臆断补全",
            "entry": "队列条目原文（含三段抑制依据与复核标记全貌）",
        },
        "feedback": {
            "plan": "反哺方案全文（plan.entry 源建议+期望影响+修复指引"
                   "+四层溯源；source_fix 类需 AI 产出 fixed_source）",
            "level": "反哺级别（L1 阈值/L2 逻辑/L3 CV规则/L4 FP抑制）",
            "feedback_history": "同类 target 历史裁决统计（applied/"
                               "rejected/deferred 计数+last_reject_reason；"
                               "与 enhancement_history 同口径同源，防重复"
                               "提交已拒建议）",
            "rule_id_canonical": "规则 ID 规范化形态（跨轮稳定键）",
        },
        "enhancement": {
            "entry": "复盘增强建议全文（issues_found 复盘根因+expected_impact"
                    "+fix_guidance+provenance 四层溯源+enhancement_history"
                    "同类历史裁决）",
        },
        "adjustment": {
            "proposal": "参数调整提案全文（diagnosis_context/treatment_context"
                       "/retrospective_context 三维背景+kind+suggested_value）",
            "suggested_value": "调整目标值",
            "adjustment_history": "同类调整历史裁决统计（approved/rejected 数"
                                 "+last_reject_reason；利弊权衡基线）",
            "kind": "调整类别（cv_threshold/diag_param/fixer_param 等）",
        },
        "cleanup": {
            "plan": "清理方案全文（plan_id+category+影响面+fixed_source 预览）",
        },
        "security": {
            "plan": "安全修复方案全文（漏洞类型/污点路径/边界校验要求）",
            "suggested_value": "建议修复值（参数化查询/凭证外部化等）",
        },
}
def _describe_provenance_keys() -> dict:
    return {
        _k: _sem for _k, _sem in (
            ("phase", ("审核相位标注（treatment_review/fupan_review/"
                       "evolution_review）")),
            ("source", "条目来源标注（生产端模块名/候选导出来源）"),
            ("diagnosis_context", ("诊断层证据（诊断原始证据链，含并入的 "
                                   "CV 复核上下文）")),
            ("treatment_context", ("治疗层证据（fix_plan/fix_guidance/"
                                   "treatment_history 治疗建议与尝试史）")),
            ("retrospective_context", ("复盘层证据（复盘根因与历史裁决轨迹；"
                                       "治疗阶段尚无复盘产物时合法缺省）")),
        ) if _k in PROVENANCE_KEYS
    }
def describe_review_item_keys() -> dict:
    return {
        "common_keys": dict(_COMMON_KEY_SEMANTICS),
        "per_channel_evidence_keys": {
            channel: dict(keys)
            for channel, keys in _CHANNEL_EVIDENCE_KEY_SEMANTICS.items()},
        "provenance_keys": _describe_provenance_keys(),
        "missing_key_semantics": {
            "三态机读判定": "日常审核优先读 evidence_completeness 视图而非逐键"
                       "推断：missing 清单即须附注键集（verdict=incomplete）；"
                       "legitimate_absent 清单即免附注键集（合法缺省）",
            "通用口径": "键缺失=生产端无此证据或证据面断链；任何缺失不得由"
                     " AI 臆造补全——参数/规则类通道无 code_context 属常态"
                     "（非代码对象），代码类通道缺 code_context 则以队列原文/"
                     "plan 为审核依据并在 assessment 附注证据缺口",
            "confidence=None": "生产端未评估置信度，不等于 0（误报判定须看"
                             "证据键）",
            "provenance 省缺": "载体（plan/entry/proposal）无四层溯源信息；"
                          "存在性检查通过但为空时语义同上",
        },
    }
def resolve_entry_severity(entry) -> str:
    if not isinstance(entry, dict):
        return ""
    for _src in (entry, entry.get("diagnosis_context")):
        if isinstance(_src, dict):
            _sev = _src.get("severity")
            if isinstance(_sev, str) and _sev.strip():
                return _sev
    return ""
_DECIDED_VERDICT_STATUSES = frozenset(("applied", "rejected", "deferred"))
_REJECTED_VERDICT_STATUSES = frozenset(("rejected", "deferred"))
_ADJUSTMENT_DECIDED_STATUSES = frozenset(
    ("approved", "rejected", "deferred"))
def _has_pending_id(item: dict, id_key: str, channel: str, label_key: str) -> bool:
    _rid = item.get(id_key, "")
    if isinstance(_rid, str) and _rid.strip():
        return True
    logger.warning("[AIReview] %s 条目缺 %s 或非 str 脏形态(脏数据)，跳过: %r",
                   channel, id_key, item.get(label_key, ""))
    return False
def _iter_pending_entries(entries, id_key: str, channel: str,
                          label_key: str):
    for entry in as_list(entries):
        if not isinstance(entry, dict):
            continue
        if not is_pending_plan(entry):
            continue
        if not _has_pending_id(entry, id_key, channel, label_key):
            continue
        yield entry
def _iter_decided_verdict_entries(entries):
    if isinstance(entries, dict):
        entries = entries.get("entries")
    if not isinstance(entries, list):
        return
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        status = str(entry.get("status", "") or "")
        if status not in _DECIDED_VERDICT_STATUSES:
            continue
        yield entry, status
def _accumulate_decided_bucket(stats: dict, key, status: str,
                              reject_reason: str) -> None:
    bucket = stats.setdefault(key, {})
    bucket[status] = bucket.get(status, 0) + 1
    if status in _REJECTED_VERDICT_STATUSES:
        bucket["last_reject_reason"] = reject_reason[:200]
def _same_target_verdict_stats(entries) -> dict:
    _stats: dict[str, dict] = {}
    for _entry, _status in _iter_decided_verdict_entries(entries):
        _accumulate_decided_bucket(
            _stats, str(_entry.get("target", "") or ""), _status,
            normalize_text(_entry.get("ai_review_rationale")))
    return _stats
def _load_verdict_stats_or_empty(skill_dir: str, label: str) -> dict:
    try:
        return _same_target_verdict_stats(
            get_retrospective_history(skill_dir))
    except Exception:
        logger.debug("[AIReview] %s历史统计加载降级", label, exc_info=True)
        return {}
def _attach_target_history(item: dict, key: str, stats: dict,
                          target) -> None:
    _target = str(target or "")
    if not _target:
        return
    history = stats.get(_target)
    if history:
        item[key] = history
def _adj_key(entry: dict) -> tuple[str, str]:
    return (str(entry.get("kind", "") or ""),
            str(entry.get("target", "") or ""))
def _group_adjustment_stats(proposals: list) -> dict:
    adj_stats: dict[tuple[str, str], dict] = {}
    for _q in proposals:
        if not isinstance(_q, dict):
            continue
        _qs = str(_q.get("status", ""))
        if _qs not in _ADJUSTMENT_DECIDED_STATUSES:
            continue
        _accumulate_decided_bucket(
            adj_stats, _adj_key(_q), _qs,
            normalize_text(_q.get("reject_reason"))
            or normalize_text(_q.get("reason")))
    return adj_stats
def _treatment_candidate_index(cand: dict) -> int | None:
    _idx = cand.get("index", -1)
    if isinstance(_idx, bool) or not isinstance(_idx, int) or _idx < 0:
        logger.warning("[AIReview] 治疗候选 index 非法(%r)，跳过: %s",
                       cand.get("index"), cand.get("rule_id", ""))
        return None
    return _idx
def _treatment_diagnosis_evidence(cand: dict) -> dict:
    _evidence = cand.get("diagnosis_evidence")
    if isinstance(_evidence, dict):
        return _evidence
    if _evidence:
        logger.warning(
            "[AIReview] 治疗候选 diagnosis_evidence 非 dict 脏形态(%s)，"
            "按空证据链处理: index=%r",
            type(_evidence).__name__, cand.get("index"))
    return {}
def _treatment_review_item(cand: dict, idx: int) -> dict:
    _evidence = _treatment_diagnosis_evidence(cand)
    return normalize_review_item({
        "channel": "treatment",
        "review_id": f"TREAT-{idx:03d}",
        "target": cand.get("rule_id", ""),
        "rule_id": cand.get("rule_id", ""),
        "finding_id": normalize_text(_evidence.get("finding_id")),
        "file_path": normalize_file_ref(cand.get("file_path", "")),
        "line": normalize_line_no(cand.get("line", 0)),
        "severity": cand.get("severity", ""),
        "strategy": cand.get("strategy", ""),
        "description": cand.get("message", ""),
        "confidence": None,
        FIELD_SUGGESTED_VALUE: "",
        "code_context": cand.get("code_context", ""),
        "orig_status": cand.get("orig_status", ""),
        "cv_context": cand.get("cv_context"),
        "diagnosis_evidence": _evidence,
        "function_summary": cand.get("function_summary"),
        "fixer_risk": cand.get("fixer_risk") or {},
        "fix_precheck": cand.get("fix_precheck") or {},
        "fix_experience": cand.get("fix_experience") or [],
        "rule_id_canonical": cand.get("rule_id_canonical", ""),
        "fix_plan": cand.get("fix_plan"),
        "treatment_history": cand.get("treatment_history") or [],
        "fix_guidance": cand.get("fix_guidance", ""),
        "requires_fixed_source": True,
        "apply_hint": ("四维审核（严重性/可修复性/利弊/误报）后提交裁决："
                       "修复用 run_next_ai_review(skill_dir, review_id=..., "
                       "fixed_source=..., assessment={verdict:'approve_and_fix',...})，"
                       "fixed_source 须含代码修复与受影响注释/docstring 的同步更新；"
                       "判定误报用 assessment={verdict:'reject_as_fp', "
                       "fp_evidence:...}（自动固化误报规则）；"
                       "不修复/暂缓用 verdict='reject'/'defer'"
                       "（保持 pending 并阻塞交付）；"
                       "写盘后自动跑对应修改的定向回归（不跑全量回归）"),
        "index": idx,
    })
def collect_treatment_reviews(skill_dir: str) -> list[dict]:
    skill_dir = _queue_skill_dir(skill_dir)
    res = get_ai_fix_candidates(skill_dir)
    if not isinstance(res, dict):
        raise TypeError(
            f"治疗候选导出返回非 dict: {type(res).__name__}")
    if res.get("state_integrity") == "torn":
        reason = normalize_text(res.get("state_integrity_reason")) or "治疗状态撕裂"
        raise RuntimeError(f"治疗候选导出受阻: {reason}")
    candidates = as_list(res.get("candidates"))
    items = []
    for cand in candidates:
        if not isinstance(cand, dict):
            continue
        _idx = _treatment_candidate_index(cand)
        if _idx is None:
            continue
        items.append(_treatment_review_item(cand, _idx))
    return items
_FEEDBACK_IDENTITY_KEYS = ("target", "description")
def _feedback_plan_identity(plan: dict) -> tuple[str, str]:
    entry = plan.get("entry") if isinstance(plan.get("entry"), dict) else {}
    return (
        normalize_text(plan.get("target")) or normalize_text(entry.get("target")),
        normalize_text(plan.get("description")) or normalize_text(
            entry.get("description")),
    )
def _ensure_feedback_plan_identity(plan: dict) -> None:
    for key, value in zip(
            _FEEDBACK_IDENTITY_KEYS, _feedback_plan_identity(plan)):
        if normalize_text(plan.get(key)):
            continue
        if value:
            plan[key] = value
def _pending_feedback_plan_keys(skill_dir: str) -> set:
    _, plans = _load_plan_queue(feedback_plan_path(skill_dir), "plans")
    plan_keys: set[tuple[str, str]] = set()
    for p in plans:
        if not is_pending_plan(p):
            continue
        _e = p.get("entry") if isinstance(p.get("entry"), dict) else {}
        for _src in (p, _e):
            _key = identity_pair(_src)
            if any(_key):
                plan_keys.add(_key)
        _merged_key = _feedback_plan_identity(p)
        if any(_merged_key):
            plan_keys.add(_merged_key)
    return plan_keys
def _is_reviewable_feedback_plan(plan: dict) -> bool:
    if not is_pending_plan(plan):
        return False
    plan_id = plan.get("plan_id")
    if isinstance(plan_id, str) and plan_id.strip():
        return True
    return any(_feedback_plan_identity(plan))
def _load_feedback_plans(skill_dir: str) -> list:
    _, plans = _load_plan_queue(feedback_plan_path(skill_dir), "plans")
    if any(_is_reviewable_feedback_plan(p) for p in plans):
        return plans
    generated = run_code_level_feedback(
        skill_dir, max_items=_PLAN_COLLECT_MAX_ITEMS)
    if not isinstance(generated, dict):
        raise TypeError(
            f"反哺方案生成返回非 dict: {type(generated).__name__}")
    if generated.get("status") == "error":
        message = normalize_text(generated.get("message")) or "反哺方案生成失败"
        raise RuntimeError(message)
    return as_list(generated.get("plans", []))
def _feedback_review_item(skill_dir: str, plan: dict, pid: str) -> dict:
    _entry = plan.get("entry") if isinstance(plan.get("entry"), dict) else {}
    _fp = normalize_file_ref(plan.get("file", "") or _entry.get("file_path", ""))
    _ln = normalize_line_no(_entry.get("line", 0))
    _rid = _entry.get("rule_id", "")
    _desc = normalize_text(plan.get("description")) or normalize_text(
        plan.get("summary"))
    return normalize_review_item({
        "channel": "feedback",
        "review_id": pid,
        "target": plan.get("target", ""),
        "rule_id": _rid,
        "file_path": _fp,
        "line": _ln,
        "severity": resolve_entry_severity(_entry),
        "code_context": extract_code_context_in_project(skill_dir, _fp, _ln),
        "strategy": plan.get("action_type", ""),
        "description": _desc,
        "confidence": plan.get("confidence", 0),
        FIELD_SUGGESTED_VALUE: plan.get(FIELD_SUGGESTED_VALUE, ""),
        FIELD_EXPECTED_IMPACT: str(
            plan.get(FIELD_EXPECTED_IMPACT, "")
            or _entry.get(FIELD_EXPECTED_IMPACT, "") or ""),
        "level": plan.get("level", ""),
        "requires_fixed_source": plan.get("action_type", "") == "source_fix",
        "apply_hint": ("四维审核（严重性/可修复性/利弊/误报，依据 "
                       "plan.entry 四层溯源+suggested_value/"
                       "expected_impact）后：run_next_ai_review("
                       "skill_dir, review_id=..., assessment={verdict:"
                       "'approve' 或 'approve_and_fix'+fixed_source...})；"
                       "写码方案写盘后只跑对应修改的定向回归"),
        "plan": plan,
    })
def collect_feedback_reviews(skill_dir: str) -> list[dict]:
    skill_dir = _queue_skill_dir(skill_dir)
    plans = _load_feedback_plans(skill_dir)
    items = []
    _fdb_stats = _load_verdict_stats_or_empty(skill_dir, "反哺")
    _fdb_seq = max_review_seq(plans, "FDB", id_key="plan_id")
    for plan in plans:
        if not isinstance(plan, dict):
            continue
        if not is_pending_plan(plan):
            continue
        _ensure_feedback_plan_identity(plan)
        _raw_pid = plan.get("plan_id")
        _pid = _raw_pid if isinstance(_raw_pid, str) and _raw_pid.strip() else ""
        if not _pid and not any(identity_pair(plan)):
            logger.warning(
                "[AIReview] feedback 条目缺 plan_id 且无身份键(target/"
                "description 双空，脏数据)，无法销项定位，跳过: %r",
                plan.get("action_type", ""))
            continue
        if not _pid:
            _fdb_seq += 1
            _pid = f"FDB-{_fdb_seq:03d}"
        item = _feedback_review_item(skill_dir, plan, _pid)
        _attach_target_history(item, "feedback_history", _fdb_stats,
                               plan.get("target"))
        items.append(item)
    return items
def _enhancement_stable_id(entry: dict, desc: str) -> str:
    _basis = json.dumps(
        (normalize_text(entry.get("target")), normalize_text(desc)),
        ensure_ascii=False, separators=(",", ":"))
    return "ENH-" + hashlib.sha1(
        _basis.encode("utf-8"), usedforsecurity=False).hexdigest()[:8].upper()
def _enhancement_review_item(skill_dir: str, e: dict) -> dict:
    _fp = normalize_file_ref(e.get("file_path", "") or e.get("file", ""))
    _ln = normalize_line_no(e.get("line", 0))
    _enh_atype = _enhancement_action_type(e)
    _enh_rid = normalize_text(e.get("rule_id"))
    _enh_desc = normalize_text(e.get("description"))
    return normalize_review_item({
        "channel": "enhancement",
        "review_id": _enhancement_stable_id(e, _enh_desc),
        "target": e.get("target", ""),
        "rule_id": _enh_rid,
        "file_path": _fp,
        "line": _ln,
        "severity": resolve_entry_severity(e),
        "code_context": extract_code_context_in_project(skill_dir, _fp, _ln),
        "strategy": _enh_atype,
        "description": _enh_desc,
        "confidence": e.get("confidence", 0),
        FIELD_SUGGESTED_VALUE: e.get(FIELD_SUGGESTED_VALUE, ""),
        FIELD_EXPECTED_IMPACT: str(e.get(FIELD_EXPECTED_IMPACT, "") or ""),
        "requires_fixed_source": False,
        "apply_hint": "mark_enhancement_applied(skill_dir, target, description)；随后按返回的 memory_operation 执行记忆同步",
        "entry": e,
    })
def collect_enhancement_reviews(skill_dir: str) -> list[dict]:
    skill_dir = _queue_skill_dir(skill_dir)
    try:
        entries = get_pending_enhancements(skill_dir)
    except Exception as e:
        logger.warning("[AIReview] 增强建议收集失败: %s", e, exc_info=True)
        raise
    _enh_stats = _load_verdict_stats_or_empty(skill_dir, "增强")
    try:
        _plan_keys = _pending_feedback_plan_keys(skill_dir)
    except Exception as e:
        logger.warning(
            "[AIReview] 反馈计划匹配键读取失败，中止增强收集以防重复裁决: %s",
            e, exc_info=True)
        raise
    items = []
    for e in entries:
        if not isinstance(e, dict):
            continue
        identity = identity_pair(e)
        if not any(identity):
            logger.warning(
                "[AIReview] enhancement 条目 target/description 双空，"
                "无法可靠定位销项，跳过")
            continue
        if identity in _plan_keys:
            continue
        item = _enhancement_review_item(skill_dir, e)
        _attach_target_history(item, "enhancement_history", _enh_stats,
                               e.get("target"))
        items.append(item)
    return items
def _adjustment_review_item(p: dict, history: dict | None) -> dict:
    _adj_dc = p.get("diagnosis_context") if isinstance(p.get("diagnosis_context"), dict) else {}
    _adj_rid = str(_adj_dc.get("rule_id", "") or "").strip()
    item = {
        "channel": "adjustment",
        "review_id": p.get("review_id", ""),
        "target": p.get("target", ""),
        "rule_id": _adj_rid or p.get("target", ""),
        "file_path": "",
        "line": 0,
        "severity": resolve_entry_severity(p),
        "strategy": p.get("kind", ""),
        "description": p.get("reason", ""),
        "confidence": p.get("confidence", 0),
        FIELD_SUGGESTED_VALUE: p.get(FIELD_SUGGESTED_VALUE, ""),
        "kind": p.get("kind", ""),
        "requires_fixed_source": False,
        "apply_hint": ("apply_approved_adjustment(skill_dir, review_id, "
                       "assessment={...})"),
        "proposal": p,
    }
    if history:
        item["adjustment_history"] = history
    return normalize_review_item(item)
def collect_adjustment_reviews(skill_dir: str) -> list[dict]:
    _, proposals = _load_plan_queue(
        adjustment_plan_path(_queue_skill_dir(skill_dir)), "proposals")
    items = []
    _adj_stats = _group_adjustment_stats(proposals)
    for p in _iter_pending_entries(proposals, "review_id", "adjustment", "target"):
        items.append(_adjustment_review_item(p, _adj_stats.get(_adj_key(p))))
    return items
def _cv_review_prefix(entry: dict) -> str:
    if entry.get("conclusion") == "fp_prefilter":
        return "[FP预过滤复核][疑似误报-须AI裁决抑制是否成立] "
    if entry.get("single_source_confirmed"):
        return "[CV uncertain复核][单源自我背书-须AI二次仲裁] "
    if entry.get("suppressed_review"):
        return "[CV suppressed复核][被抑制项-须AI裁决抑制是否成立] "
    if entry.get("investigated_review"):
        return "[CV investigated复核][降级项-须AI裁决降级是否成立] "
    if entry.get("review_flagged"):
        return "[CV uncertain复核][已标记待复核] "
    return "[CV uncertain复核] "
def _build_cv_evidence(entry: dict) -> dict:
    evidence = {
        "conclusion": entry.get("conclusion", ""),
        "sources": entry.get("sources", []) or [],
        "evidence_strength": entry.get("evidence_strength", 0.0),
        "adjusted_confidence": entry.get("adjusted_confidence", 0.0),
        "notes": entry.get("notes", ""),
        "counter_evidence": entry.get("counter_evidence", False),
        "counter_evidence_reasons": entry.get("counter_evidence_reasons", []) or [],
        "single_source_confirmed": entry.get("single_source_confirmed", False),
        "forced_security": entry.get("forced_security", False),
        "suppressed_review": entry.get("suppressed_review", False),
        "suppression_rule": entry.get("suppression_rule", ""),
        "review_flagged": entry.get("review_flagged", False),
        "investigated_review": entry.get("investigated_review", False),
        "suppression_evidence": entry.get("suppression_evidence", []) or [],
        "evidence_detail": entry.get("evidence_detail", []) or [],
        "conclusion_params": entry.get("conclusion_params", {}) or {},
        "aggregate_review": entry.get("aggregate_review", False),
        "suppressed_count": entry.get("suppressed_count", 0),
        "suppressed_details": entry.get("suppressed_details", []) or [],
    }
    if not any(entry.get(key) for key in evidence):
        return {}
    return evidence
def _cv_uncertain_review_item(e: dict, skill_dir: str, prefix: str) -> dict:
    _fp = normalize_file_ref(e.get("file_path", ""))
    _msg = normalize_text(e.get("message"))
    _loc = normalize_text(e.get("locator"))
    _cc = e.get("code_context")
    return normalize_review_item({
        "channel": "cv_uncertain",
        "review_id": e.get("review_id", ""),
        "target": _loc,
        "rule_id": e.get("rule_id", ""),
        "file_path": _fp,
        "line": normalize_line_no(e.get("line", 0)),
        "severity": e.get("severity", ""),
        "strategy": "ai_semantic_review",
        "description": f"{prefix}{_msg} (locator={_loc})",
        "confidence": e.get("confidence", 0),
        "code_context": (
            _cc if _is_nonempty_str(_cc)
            else extract_code_context_in_project(skill_dir, _fp, e.get("line", 0))
        ),
        "cv_evidence": _build_cv_evidence(e),
        "requires_fixed_source": False,
        "apply_hint": ("apply_cv_uncertain_verdict(skill_dir, review_id, "
                       "approved=None, verdict='', fp_evidence='') — 无裁决信号"
                       "拒绝执行；确认则提升观察、reject_as_fp/approved=False "
                       "须附 fp_evidence 才记FP；reject/defer 均保持待审并阻塞交付"),
        "entry": e,
    })
def collect_cv_uncertain_reviews(skill_dir: str) -> list[dict]:
    skill_dir = _queue_skill_dir(skill_dir)
    _, entries = _load_plan_queue(cv_uncertain_path(skill_dir), "entries")
    items = []
    for e in _iter_pending_entries(entries, "review_id",
                                   "cv_uncertain", "locator"):
        items.append(_cv_uncertain_review_item(e, skill_dir, _cv_review_prefix(e)))
    return items
def _security_review_item(p: dict, skill_dir: str) -> dict:
    _fp = normalize_file_ref(p.get("file", ""))
    return normalize_review_item({
        "channel": "security",
        "review_id": p.get("plan_id", ""),
        "target": p.get("rule_id", ""),
        "rule_id": p.get("rule_id", ""),
        "file_path": _fp,
        "line": normalize_line_no(p.get("line", 0)),
        "severity": p.get("severity", ""),
        "description": p.get("message", ""),
        "strategy": "security_fix",
        FIELD_SUGGESTED_VALUE: p.get("suggestion", ""),
        "code_context": extract_code_context_in_project(skill_dir, _fp, p.get("line", 0)),
        "fix_guidance": p.get("suggestion", ""),
        "requires_fixed_source": True,
        "apply_hint": ("审核通过后由 AI 生成修复后源码全文并再次调用 "
                       "run_next_ai_review(skill_dir, fixed_source=..., "
                       f"review_id='{p.get('plan_id', '')}') 提交写盘"),
        "plan": p,
    })
def collect_security_reviews(skill_dir: str) -> list[dict]:
    skill_dir = _queue_skill_dir(skill_dir)
    _, plans = _load_plan_queue(security_plan_path(skill_dir), "plans")
    items = []
    for p in _iter_pending_entries(plans, "plan_id", "security", "rule_id"):
        items.append(_security_review_item(p, skill_dir))
    return items
def normalize_cleanup_reviews(items, skill_dir: str) -> list[dict]:
    out: list[dict] = []
    for item in as_list(items):
        if not isinstance(item, dict):
            continue
        if not _has_pending_id(item, "review_id", "cleanup", "target"):
            continue
        if item.get("channel") != "cleanup":
            if "channel" in item:
                logger.warning("[AIReview] cleanup 条目 channel 为脏值 %r，"
                               "已归一为 cleanup: %s",
                               item["channel"], item.get("review_id", ""))
            item["channel"] = "cleanup"
        item["file_path"] = normalize_file_ref(item.get("file_path", ""))
        item["line"] = normalize_line_no(item.get("line", 0))
        if not _is_nonempty_str(item.get("code_context")):
            item["code_context"] = extract_code_context_in_project(
                skill_dir, item["file_path"], item.get("line", 0))
        out.append(normalize_review_item(item))
    return out

from __future__ import annotations

import hashlib
import json
import logging
import math
import os
import time
from typing import Any, NamedTuple

from jwsgj.diag_types_normalize import (
    as_dict,
    as_list,
    extract_finding_line,
    int_or,
    now_iso,
    parse_locator_file,
    str_or,
)
from jwsgj.diag_types_vocab import MEMORY_WRITE_ACTIONS
from jwsgj.diag_zero_backlog_ledger import (
    _DEFAULT_ROUND_START_TS,
    FUZZY_VERDICT_CHANNELS,
    P0_SEVERITIES,
    PRECISE_VERDICT_CHANNELS,
    _finding_keys,
    _round_anchor,
    _verdict_hit_for_context,
    build_round_scope,
    classify_terminal,
    finding_identity,
    ledger_resolution,
    p0_has_fixed_proof,
    terminal_verb,
)
from jwsgj.html_report_stage_doc import (
    normalize_skill_key,
    read_stage_meta,
    stage_of_file,
    stage_pair_status,
)
from jwsgj.log_config import locked_artifact, log_swallowed
from jwsgj.memory_bridge_ops import memory_operation_issue
from jwsgj.pipeline_round_trace import load_pipeline_state
from jwsgj.runtime_paths import (
    evolution_events_path,
    get_html_report_base,
    json_root_dir,
    read_evolution_section,
)
from jwsgj.runtime_scope import normalize_skill_dir

logger = logging.getLogger(__name__)
__all__ = [
    "MEMORY_INJECTION_RECEIPT_FILENAME",
    "MIN_FUPAN_QUALITY",
    "PRECISE_VERDICT_CHANNELS",
    "check_diagnosis_ledger_coverage",
    "check_false_negative_probe",
    "check_memory_injection_quality",
    "check_precision_evidence",
    "check_precision_trend",
    "check_stage_pair_integrity",
    "load_memory_injection_receipts",
    "record_memory_injection",
]
MEMORY_INJECTION_RECEIPT_FILENAME = "memory_injection_receipt.jsonl"
MIN_FUPAN_QUALITY = 60
_FUPAN_LATE_PHASES = frozenset({
    "review_done", "fupan_done", "feedback_done", "code_feedback_done",
    "evolution_pending", "all_completed",
})
_PRECISION_PREVIEW = 40
class _PrecisionEvidence(NamedTuple):
    precise: bool
    channel: str
    verdicts: frozenset
    verb: str
def _precise_channel(finding: dict, ctx,
                     source: str) -> _PrecisionEvidence:
    verb = terminal_verb(finding, ctx)
    if source.startswith("ledger:"):
        return _PrecisionEvidence(True, "ledger_finding", frozenset(), verb)
    if source == "treatment_state":
        return _PrecisionEvidence(True, "treatment_precise", frozenset(),
                                  verb)
    keys = _finding_keys(finding)
    verdicts = _verdict_hit_for_context(keys, ctx)[1]
    return _PrecisionEvidence(source in PRECISE_VERDICT_CHANNELS,
                              source or "unknown", verdicts, verb)
def _precision_report(round_ts: str, findings: list, terminal_count: int,
                     masked: list[dict], p0_semantic: list[dict],
                     ledger_errors: list, actions: list[str]) -> dict:
    blocking = bool(masked or p0_semantic or ledger_errors)
    if ledger_errors:
        reason = "precision_ledger_unreadable"
    elif blocking:
        reason = "precision_masked"
    elif not findings:
        reason = "no_round_findings"
    else:
        reason = ""
    return {
        "gate_id": "GATE-PRECISION-EVIDENCE",
        "gate_name": "精确证据门禁",
        "passed": not blocking,
        "skipped": not findings and not ledger_errors,
        "reason": reason,
        "round_start_ts": round_ts,
        "total_findings": len(findings),
        "terminal_count": terminal_count,
        "masked_count": len(masked),
        "p0_semantic_count": len(p0_semantic),
        "masked_items": masked[:_PRECISION_PREVIEW],
        "masked_truncated": max(0, len(masked) - _PRECISION_PREVIEW),
        "p0_semantic_items": p0_semantic[:_PRECISION_PREVIEW],
        "p0_semantic_truncated": max(
            0, len(p0_semantic) - _PRECISION_PREVIEW),
        "ledger_errors": list(ledger_errors),
        "actions_required": actions,
    }
def check_precision_evidence(skill_dir: str) -> dict:
    sd = normalize_skill_dir(skill_dir)
    scope = build_round_scope(sd)
    findings, ctx, round_ts = (scope.findings, scope.ctx,
                               scope.round_start_ts)
    masked: list[dict] = []
    p0_semantic: list[dict] = []
    terminal_count = 0
    for finding in findings:
        source = classify_terminal(finding, ctx)
        if not source:
            continue
        terminal_count += 1
        evidence = _precise_channel(finding, ctx, source)
        severity = str_or(finding.get("severity")).strip().upper() or "unknown"
        resolution = ledger_resolution(finding, ctx.resolved)
        item = {
            "finding_id": finding_identity(finding),
            "rule_id": str_or(finding.get("rule_id")),
            "severity": severity,
            "domain": str_or(finding.get("domain")) or "unknown",
            "file": str_or(finding.get("file")),
            "line": int_or(finding.get("line"), 0),
            "terminal_source": source,
            "channel": evidence.channel,
            "channel_status": evidence.verb,
            "resolution": resolution,
            "verdicts": sorted(evidence.verdicts),
        }
        if (severity in P0_SEVERITIES
                and not p0_has_fixed_proof(finding, ctx)):
            item["reason"] = (
                "P0 只接受真实修复终态（fixed/ai_fixed/succeeded），"
                f"当前销项={evidence.verb or source} 属语义销项——"
                "真实问题被掩盖，必须撤回并转真实修复")
            p0_semantic.append(item)
            continue
        if not evidence.precise:
            item["reason"] = (
                "株连式模糊裁决（rule_id/basename）缺逐项精确定位——"
                "同规则其他真实问题会被一起掩盖；"
                "须补 locator/file+line+rule 精确证据或逐项复核"
                if evidence.channel in FUZZY_VERDICT_CHANNELS else
                f"终态通道 {evidence.channel} 缺逐项精确证据——"
                "须补 locator/file+line+rule 精确证据或逐项复核")
            masked.append(item)
    ledger_errors = list(scope.ledger_errors)
    actions: list[str] = []
    if ledger_errors:
        actions.append(
            f"precision_ledger_unreadable: 台账 {len(ledger_errors)} 条读取/"
            "解析错误——损坏台账不得退化成「零终态放行」，"
            "修复或恢复 zero_backlog_ledger.jsonl 后重跑交付门禁")
    if p0_semantic:
        sample = "、".join(item["finding_id"] for item in p0_semantic[:5])
        actions.append(
            f"p0_semantic_sweep: {len(p0_semantic)} 项 P0 以非修复语义销项"
            f"（{sample}）——P0 无销项豁免，必须撤回处置并转真实修复")
    if masked:
        sample = "、".join(item["finding_id"] for item in masked[:5])
        actions.append(
            f"precision_masked: {len(masked)} 项 finding 以株连/模糊证据"
            f"销项（{sample}）——补逐项精确证据（resolve_backlog_item 带 "
            "locator 处置）或撤回并转真实修复/误报固化")
    report = _precision_report(round_ts, findings, terminal_count, masked,
                              p0_semantic, ledger_errors, actions)
    if report["passed"]:
        logger.info("[PrecisionEvidence] 门禁通过: %d 项终态全部有逐项精确证据",
                    terminal_count)
    else:
        logger.warning(
            "[PrecisionEvidence] 门禁阻塞: 模糊销项=%d, P0语义销项=%d, "
            "台账错误=%d, 终态=%d/%d（轮次 %s）",
            len(masked), len(p0_semantic), len(ledger_errors), terminal_count,
            len(findings), round_ts or "-")
    return report
_COVERAGE_PREVIEW = 40
_DIAG_STAGE_PREFIX = "诊断"


def _iter_nested_dicts(obj: Any):
    """深度优先枚举嵌套结构中的全部 dict（防自引用循环）。"""
    stack = [obj]
    seen: set[int] = set()
    while stack:
        current = stack.pop()
        if isinstance(current, dict):
            if id(current) in seen:
                continue
            seen.add(id(current))
            yield current
            stack.extend(current.values())
        elif isinstance(current, (list, tuple)):
            stack.extend(current)


def _coverage_entry_key(entry: dict, skill_dir: str = "") -> tuple | None:
    """提取覆盖键；有项目锚时使用规范路径，避免同名文件互相顶替。"""
    rule_id = str_or(entry.get("rule_id") or entry.get("check_id")).strip()
    if not rule_id:
        return None
    file_path = str_or(
        entry.get("file") or entry.get("file_path") or entry.get("filepath"))
    if not file_path:
        file_path = parse_locator_file(entry.get("locator"))
    if not file_path:
        return None
    normalized = file_path.replace("\\", "/").strip()
    if not normalized:
        return None
    if skill_dir:
        if not os.path.isabs(normalized):
            normalized = os.path.join(skill_dir, normalized)
        normalized = os.path.normcase(os.path.normpath(normalized))
    else:
        # 保留无私有项目锚调用方的历史键形态。
        normalized = os.path.basename(normalized)
    return (rule_id.upper(), normalized, extract_finding_line(entry))


def _diagnosis_report_paths(sd: str, round_ts: str) -> list[str]:
    """列出本技能、本轮次的诊断阶段配套 JSON。"""
    try:
        html_dir = get_html_report_base()
    except (RuntimeError, ValueError):
        return []
    if not html_dir or not os.path.isdir(html_dir):
        return []
    target = normalize_skill_key(sd)
    paths: list[str] = []
    for name in sorted(os.listdir(html_dir)):
        if not name.lower().endswith(".html"):
            continue
        if not name.startswith(_DIAG_STAGE_PREFIX):
            continue
        path = os.path.join(html_dir, name)
        if not os.path.isfile(path):
            continue
        if round_ts and round_ts not in name:
            continue
        owner = normalize_skill_key(
            str_or(read_stage_meta(path).get("skill")))
        if owner and target and owner != target:
            continue
        json_path = str_or(stage_pair_status(path, sd).get("json_path"))
        if json_path:
            paths.append(json_path)
    return paths


def check_diagnosis_ledger_coverage(skill_dir: str) -> dict:
    """诊断→台账全量入账门禁：防「诊断出来但没入账」的真问题被掩盖。

    其余门禁都以台账 finding 为全集——只要某个 finding 在聚合/交叉验证阶段
    被静默丢弃、从未写入 ``finding_seen``，它就不会出现在任何残留统计里，
    门禁反而因为「看不见」而放行。本门禁反向枚举本轮诊断阶段报告里的
    全部 finding，要求每一条都在台账中有对应登记；缺失即判定为「真实问题
    被掩盖」，无论严重度（P0–P3）一律阻断交付。
    """
    sd = normalize_skill_dir(skill_dir)
    scope = build_round_scope(sd)
    round_ts = _round_anchor(scope.round_start_ts) or ""
    base = {
        "gate_id": "GATE-DIAGNOSIS-COVERAGE",
        "gate_name": "诊断全量入账门禁",
        "passed": True,
        "skipped": False,
        "reason": "",
        "round_start_ts": round_ts,
        "diagnosis_findings": 0,
        "ledger_findings": len(scope.findings),
        "masked_count": 0,
        "masked_items": [],
        "actions_required": [],
    }
    if scope.ledger_errors:
        base.update({
            "passed": False,
            "reason": "coverage_ledger_unreadable",
            "actions_required": [
                ("台账读取/解析失败，覆盖性无法核验——修复 "
                 "zero_backlog_ledger.jsonl 后重跑交付门禁")],
        })
        return base
    reports = _diagnosis_report_paths(sd, round_ts)
    if not reports:
        base.update({"skipped": True, "reason": "no_diagnosis_report"})
        return base
    ledger_keys: set[tuple] = set()
    for finding in scope.findings:
        if not isinstance(finding, dict):
            continue
        key = _coverage_entry_key(finding, sd)
        if key is None:
            continue
        ledger_keys.add(key)
    diagnosis: dict[tuple, dict] = {}
    for json_path in reports:
        try:
            with open(json_path, encoding="utf-8-sig") as handle:
                payload = json.load(handle)
        except (OSError, ValueError, RecursionError) as exc:
            base.update({
                "passed": False,
                "reason": "diagnosis_report_unreadable",
                "actions_required": [
                    (f"诊断阶段报告不可读（{os.path.basename(json_path)}）: "
                     f"{type(exc).__name__}——修复/重跑诊断后重试")],
            })
            return base
        for entry in _iter_nested_dicts(payload):
            key = _coverage_entry_key(entry, sd)
            if key is None:
                continue
            # 同键并存时真实 finding 必须压过降级记录：否则降级项先被枚举到
            # 就会把同键真实漏登记项一起当成「降级跳过」放行。
            if (key in diagnosis
                    and str_or(diagnosis[key].get("degrade_reason"))
                    and not str_or(entry.get("degrade_reason"))):
                diagnosis[key] = entry
            else:
                diagnosis.setdefault(key, entry)
    masked: list[dict] = []
    degraded_n = 0
    for key, entry in diagnosis.items():
        if key in ledger_keys:
            continue
        # 降级跳过（degrade_reason 非空）不是诊断发现：入口在沙箱里根本没跑
        # 起来（内存守卫 / 缺依赖 / 超时），不存在可修复的代码。把它们算进
        # 「未入账」，门禁会永远无法通过，反过来掩盖真正漏登记的 finding。
        if str_or(entry.get("degrade_reason")):
            degraded_n += 1
            continue
        masked.append({
            "rule_id": key[0],
            "file": os.path.basename(key[1]),
            "line": key[2],
            "severity": str_or(entry.get("severity")) or "unknown",
            "message": str_or(entry.get("message"))[:200],
        })
    base.update({
        "diagnosis_findings": len(diagnosis) - degraded_n,
        "degraded_skipped": degraded_n,
        "masked_count": len(masked),
        "masked_items": masked[:_COVERAGE_PREVIEW],
    })
    if masked:
        sample = "、".join(
            f"{item['rule_id']}@{item['file']}:{item['line']}"
            for item in masked[:5])
        base.update({
            "passed": False,
            "reason": "diagnosis_findings_masked",
            "actions_required": [
                (f"diagnosis_unledgered: {len(masked)} 条诊断 finding "
                 f"未入台账（{sample}）——补 register_cv_findings_snapshot "
                 "登记并逐项处置（真实修复或误报固化），"
                 "禁止以「没入账」方式掩盖")],
        })
        logger.warning(
            "[DiagnosisCoverage] 门禁阻塞: 诊断 %d 条中 %d 条未入台账——%s",
            len(diagnosis), len(masked), sample)
    else:
        logger.info(
            "[DiagnosisCoverage] 门禁通过: 诊断 %d 条全部入账（台账 %d 条）",
            len(diagnosis), len(scope.findings))
    return base
_FN_PROBE_HISTORY_SECTION = "fn_probe_history"
_FN_PROBE_FN_RATE_LIMIT = 0.2
_FN_PROBE_BACKLOG_ACTIONS = {
    "missing_checker": "补 AST checker 并挂入 AST_CHECKERS",
    "missing_rule_spec": "在 RULES 补规则声明（rule_id/name/priority）",
    "checker_logic_gap": "修 checker 判定逻辑，使它识别该缺陷形态",
    "wiring_regression": "重新接线到 DetectorRegistry（检查是否被注销）",
    "precision_violation": "修 checker 精确度，无缺陷样本上必须零 finding",
    "unclassified": "人工归因后补入模板库或修复检测器",
}
def check_false_negative_probe(skill_dir: str) -> dict:
    """漏报探针门禁：已知缺陷必须被检出。

    与精确证据门禁互为补角：精确门禁防“假阳性被当终态放行”（掩盖
    真实问题），本门禁防“真实缺陷根本没 finding 可放行”（静默漏报）。
    后者更隐蔽——findings 为空时下游所有门禁都会“通过”。

    首轮基线豁免：仓库首次接入探针必然暴露存量漏报，直接阻断会让
    交付永远无法完成。首轮只记基线，第二轮起按阈值判定。
    """
    sd = normalize_skill_dir(skill_dir)
    base = {
        "gate_id": "GATE-FALSE-NEGATIVE",
        "gate_name": "漏报探针门禁",
        "passed": True,
        "skipped": False,
        "reason": "",
        "rounds": 0,
        "templates": 0,
        "killed": 0,
        "survived_count": 0,
        "fn_rate": 0.0,
        "pending": [],
        "actions_required": [],
    }
    # 默认值：异常分支会提前 return，但静态分析无法证明这一点，
    # 预置默认值同时消除 UnboundLocalError 风险。
    killed_value = 0
    try:
        history = read_evolution_section(sd, _FN_PROBE_HISTORY_SECTION)
        rounds = (history.get("rounds")
                  if isinstance(history, dict) else None)
        if isinstance(rounds, list) and rounds:
            latest = rounds[-1]
            if not isinstance(latest, dict):
                raise ValueError("latest probe round must be an object")
            for key in ("survived", "pending"):
                value = latest.get(key)
                if value is not None and not isinstance(value, (list, tuple)):
                    raise ValueError(f"latest probe round {key} must be a list")
            killed_value, killed_valid = _memory_operation_count(
                latest.get("killed"))
            if not killed_valid or killed_value < 0:
                raise ValueError(
                    "latest probe round killed must be a non-negative integer")
    except (OSError, ValueError, TypeError) as exc:
        logger.warning(
            "[FalseNegative] 探针历史读取失败: %s", type(exc).__name__)
        base.update({
            "passed": False,
            "skipped": False,
            "reason": "probe_history_unreadable",
            "actions_required": [
                "修复或恢复 fn_probe_history 后重跑漏报探针与交付门禁"],
        })
        return base
    if not isinstance(rounds, list) or not rounds:
        base["skipped"] = True
        base["reason"] = "no_probe_round"
        return base
    latest = rounds[-1] if isinstance(rounds[-1], dict) else {}
    survived = latest.get("survived") or []
    killed = killed_value
    pending = latest.get("pending") or []
    evaluated = killed + len(survived)
    fn_rate = (len(survived) / evaluated) if evaluated else 0.0
    base.update({
        "rounds": len(rounds),
        "templates": int_or(latest.get("templates"), 0),
        "killed": killed,
        "survived_count": len(survived),
        "fn_rate": round(fn_rate, 4),
        "pending": pending[:_PRECISION_PREVIEW],
        "round_ts": str_or(latest.get("ts")),
    })
    if len(rounds) <= 1:
        base["skipped"] = True
        base["reason"] = "first_round_baseline"
        base["actions_required"].append(
            f"first_round_baseline: 首次接入探针记录基线"
            f"（钉住 {killed} 项、漏报 {len(survived)} 项），"
            "从第二轮起按阈值阻断")
        return base
    reasons: list[str] = []
    actions: list[str] = []
    if fn_rate > _FN_PROBE_FN_RATE_LIMIT:
        reasons.append("false_negative_leak")
        sample = "、".join(str(rid) for rid in survived[:5])
        actions.append(
            f"false_negative_leak: 漏报率 {fn_rate:.1%} 超过阈值 "
            f"{_FN_PROBE_FN_RATE_LIMIT:.0%}（{len(survived)}/{evaluated}，"
            f"样本 {sample}）——已知缺陷未被检出，严重度高于误报")
    precision_violations = [
        item for item in pending
        if isinstance(item, dict)
        and item.get("reason") == "precision_violation"]
    if precision_violations:
        reasons.append("probe_precision_violation")
        sample = "、".join(
            str(item.get("rule_id")) for item in precision_violations[:5])
        actions.append(
            f"probe_precision_violation: {len(precision_violations)} 条规则"
            f"在无缺陷样本上误报（{sample}）——拒绝激活，先修精确度")
    for item in pending:
        if not isinstance(item, dict):
            continue
        reason = str_or(item.get("reason"))
        action = _FN_PROBE_BACKLOG_ACTIONS.get(reason)
        if action:
            actions.append(
                f"{item.get('rule_id')}({reason}): {action}")
    base["reason"] = reasons[0] if reasons else ""
    base["passed"] = not reasons
    base["actions_required"] = actions
    if base["passed"]:
        logger.info(
            "[FalseNegative] 门禁通过: 漏报率 %.1f%%（%d/%d）",
            fn_rate * 100, len(survived), evaluated)
    else:
        logger.warning(
            "[FalseNegative] 门禁阻塞: %s（漏报率 %.1f%%，%d/%d）",
            ", ".join(reasons), fn_rate * 100, len(survived), evaluated)
    return base
_TREND_WINDOW = 3
_TREND_WORSENING_DELTA = 0.05
def _fn_rate_series(history: Any) -> list[float]:
    rounds = history.get("rounds") if isinstance(history, dict) else None
    if not isinstance(rounds, list):
        return []
    series: list[float] = []
    for item in rounds[-_TREND_WINDOW:]:
        if not isinstance(item, dict):
            continue
        survived = item.get("survived")
        if not isinstance(survived, (list, tuple)):
            continue
        evaluated = int_or(item.get("killed"), 0) + len(survived)
        if evaluated <= 0:
            continue
        series.append(len(survived) / evaluated)
    return series
def _fp_rate_series(history: Any) -> list[float]:
    sessions = history.get("sessions") if isinstance(history, dict) else None
    if not isinstance(sessions, list):
        return []
    series: list[float] = []
    for session in sessions[-_TREND_WINDOW:]:
        if not isinstance(session, dict):
            continue
        summary = session.get("outcome_summary")
        if not isinstance(summary, dict):
            continue
        rate = _quality_value(summary.get("fp_rate"))
        if rate is None:
            continue
        series.append(
            min(1.0, max(0.0, rate if rate <= 1.0 else rate / 100.0)))
    return series
def _worsening_delta(series: list[float]) -> float:
    if len(series) < 2:
        return 0.0
    for index in range(1, len(series)):
        if series[index] <= series[index - 1]:
            return 0.0
    delta = series[-1] - series[0]
    return delta if delta >= _TREND_WORSENING_DELTA else 0.0
def check_precision_trend(skill_dir: str) -> dict:
    """精度趋势门禁：精度不得连续退步。

    前序门禁看的是“当前快照”（误报率、漏报率各一道），本门禁看的是
    “方向”——单轮快照可以通过补充证据解释掉，但连续上升意味着反哺在
    反向生效（越治越差），必须停下来定位根因，否则阈值/权重会沿着错误
    方向持续漂移。
    """
    sd = normalize_skill_dir(skill_dir)
    base = {
        "gate_id": "GATE-PRECISION-TREND",
        "gate_name": "精度趋势门禁",
        "passed": True,
        "skipped": False,
        "reason": "",
        "fn_series": [],
        "fp_series": [],
        "worst_metric": "",
        "delta": 0.0,
        "retired_rules": [],
        "actions_required": [],
    }
    try:
        fn_history = read_evolution_section(sd, _FN_PROBE_HISTORY_SECTION)
        fp_history = read_evolution_section(sd, "feedback_history")
    except (OSError, ValueError, TypeError) as exc:
        logger.warning(
            "[PrecisionTrend] 趋势历史读取失败: %s", type(exc).__name__)
        base.update({
            "passed": False,
            "skipped": False,
            "reason": "trend_history_unreadable",
            "actions_required": [
                "修复或恢复 fn_probe_history / feedback_history 后重跑趋势门禁"],
        })
        return base
    try:
        from jwsgj.xv_threshold_learning import retired_rule_ids

        base["retired_rules"] = retired_rule_ids()
    except Exception as _swallow_e:  # noqa: BLE001 — 可见性字段不得阻断门禁
        log_swallowed(__name__, _swallow_e,
                      context='build_trend_payload:retired_rules')
        base["retired_rules"] = []
    fn_series = _fn_rate_series(fn_history)
    fp_series = _fp_rate_series(fp_history)
    base["fn_series"] = [round(value, 4) for value in fn_series]
    base["fp_series"] = [round(value, 4) for value in fp_series]
    if len(fn_series) < 2 and len(fp_series) < 2:
        base["skipped"] = True
        base["reason"] = "insufficient_rounds"
        return base
    reasons: list[str] = []
    actions: list[str] = []
    worst_metric = ""
    worst_delta = 0.0
    fn_delta = _worsening_delta(fn_series)
    fp_delta = _worsening_delta(fp_series)
    if fn_delta > 0:
        reasons.append("recall_trend_worsening")
        worst_metric, worst_delta = "fn_rate", fn_delta
        actions.append(
            f"recall_trend_worsening: 漏报率连续 {len(fn_series)} 轮上升"
            f"（{fn_series[0]:.1%} → {fn_series[-1]:.1%}）——"
            "先修 checker 判定逻辑或接线回退，再继续反哺")
    if fp_delta > 0:
        reasons.append("precision_trend_worsening")
        actions.append(
            f"precision_trend_worsening: 误报率连续 {len(fp_series)} 轮上升"
            f"（{fp_series[0]:.1%} → {fp_series[-1]:.1%}）——"
            "先收敛高频误报规则并复核抑制证据，再继续反哺")
        if fp_delta > worst_delta:
            worst_metric, worst_delta = "fp_rate", fp_delta
    if base["retired_rules"]:
        _retired_sample = "、".join(base["retired_rules"][:5])
        actions.append(
            f"retired_rules_visible: {len(base['retired_rules'])} 条规则处于"
            f"退休态（{_retired_sample}）——confirmed 已降级为 suggestion，"
            "需重写规则或补精确证据后解除")
    base["worst_metric"] = worst_metric
    base["delta"] = round(worst_delta, 4)
    base["reason"] = reasons[0] if reasons else ""
    base["passed"] = not reasons
    base["actions_required"] = actions
    if base["passed"]:
        logger.info(
            "[PrecisionTrend] 门禁通过: fn_series=%s, fp_series=%s",
            base["fn_series"], base["fp_series"])
    else:
        logger.warning(
            "[PrecisionTrend] 门禁阻塞: %s（%s +%.1f%%）",
            ", ".join(reasons), worst_metric, worst_delta * 100)
    return base
def _quality_value(value: Any) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    try:
        number = float(value)
    except OverflowError:
        return None
    return number if math.isfinite(number) else None
def _memory_operation_count(value: Any) -> tuple[int, bool]:
    if isinstance(value, bool) or value is None:
        return 0, False
    if isinstance(value, int):
        return value, True
    if isinstance(value, float):
        if math.isfinite(value) and value.is_integer():
            return int(value), True
        return 0, False
    if isinstance(value, str):
        try:
            return int(value), True
        except (TypeError, ValueError, OverflowError):
            return 0, False
    return 0, False
def _operation_content_sha(op: dict) -> str:
    payload = json.dumps(
        {
            "action": str_or(op.get("action")),
            "path": str_or(op.get("path")),
            "content": str_or(op.get("content")),
            "old_text": str_or(op.get("old_text")),
        },
        ensure_ascii=False, sort_keys=True, default=str)
    return hashlib.sha256(payload.encode("utf-8", errors="replace")).hexdigest()
def _normalized_operation(op: Any) -> dict | None:
    if not isinstance(op, dict):
        return None
    action = str_or(op.get("action") or op.get("operation")).strip().lower()
    path = str_or(op.get("path")).strip()
    content = str_or(op.get("content"))
    if action not in MEMORY_WRITE_ACTIONS or not path or not content:
        return None
    normalized = {
        "action": action,
        "path": path,
        "content": content,
        "old_text": str_or(op.get("old_text")),
        "category": str_or(op.get("category")),
        "rule_id": str_or(op.get("rule_id")),
        "quality_score": _quality_value(op.get("quality_score")) or 0.0,
    }
    if memory_operation_issue(normalized, 0) is not None:
        return None
    return normalized
def _peek_pipeline_round_anchor(skill_dir: str) -> str:
    """轮次锚兜底：调用方未传时从管线状态读取。

    回执按 ``round_start_ts`` 精确匹配（``_round_receipts``）；无轮次回执
    永远匹配不到任何轮，写进去只是死重（实测 881 条中 144 条如此，占
    16%）。读取失败按缺失处理，不抛穿。
    """
    try:
        state = as_dict(load_pipeline_state(skill_dir))
    except Exception as exc:  # noqa: BLE001 — 读取失败按缺失降级
        log_swallowed(__name__, exc,
                      context='_peek_pipeline_round_anchor:load')
        return ""
    return _round_anchor(state.get("round_start_ts"))
def record_memory_injection(
        skill_dir: str, operations: Any, *,
        round_start_ts: str = _DEFAULT_ROUND_START_TS,
        source: str = "stage6a_fupan",
        quality_score: float = 0.0) -> dict:
    sd = normalize_skill_dir(skill_dir)
    ops = [_normalized_operation(op) for op in as_list(operations)]
    valid = [op for op in ops if op is not None]
    invalid = len(ops) - len(valid)
    if not valid:
        logger.warning("[MemoryInjection] 无合法记忆操作可注入（source=%s）",
                       source)
        return {"recorded": 0, "skipped_dup": 0, "invalid": len(ops),
                "receipt_path": "", "passed": False}
    anchor = _round_anchor(round_start_ts) or _peek_pipeline_round_anchor(sd)
    if not anchor:
        logger.warning(
            "[MemoryInjection] 轮次锚缺失（round_start_ts 未登记），回执无法"
            "被任何轮次消费，拒绝写入死重（source=%s，操作 %d 条）",
            source, len(valid))
        return {"recorded": 0, "skipped_dup": 0, "invalid": invalid,
                "failed": len(valid), "receipt_path": "", "passed": False,
                "error": "轮次锚缺失（round_start_ts 未登记）"}
    try:
        path = evolution_events_path(sd)
    except (OSError, RuntimeError, ValueError) as exc:
        logger.warning("[MemoryInjection] 回执落点解析失败: %s", exc)
        return {"recorded": 0, "skipped_dup": 0, "invalid": invalid,
                "failed": len(valid), "receipt_path": "", "passed": False,
                "error": f"回执落点解析失败: {exc}"}
    try:
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    except (OSError, ValueError, TypeError) as exc:
        logger.warning("[MemoryInjection] 回执目录创建失败: %s", exc)
        return {"recorded": 0, "skipped_dup": 0, "invalid": invalid,
                "failed": len(valid), "receipt_path": path, "passed": False,
                "error": f"回执目录创建失败: {exc}"}
    fallback_quality = _quality_value(quality_score) or 0.0
    recorded = 0
    skipped = 0
    failed = 0
    with locked_artifact(path) as locked:
        if not locked:
            logger.warning("[MemoryInjection] 回执写锁不可用，拒绝无锁追加: %s",
                           path)
            return {
                "recorded": 0, "skipped_dup": 0, "invalid": invalid,
                "failed": len(valid), "receipt_path": path, "passed": False,
                "error": "回执写锁不可用，拒绝无锁追加",
            }
        try:
            existing = _read_memory_injection_receipts(path)
        except OSError as exc:
            logger.warning("[MemoryInjection] 回执读取失败，拒绝追加: %s", exc)
            return {
                "recorded": 0, "skipped_dup": 0, "invalid": invalid,
                "failed": len(valid), "receipt_path": path, "passed": False,
                "error": f"回执读取失败: {exc}",
            }
        remaining: dict[tuple[str, str], int] = {}
        for item in existing:
            if not _receipt_has_injection_proof(item):
                continue
            sha = str_or(item.get("content_sha256")).strip().lower()
            key = (_round_anchor(item.get("round_start_ts")), sha)
            remaining[key] = remaining.get(key, 0) + 1
        for op in valid:
            sha = _operation_content_sha(op)
            key = (anchor, sha)
            if remaining.get(key, 0) > 0:
                remaining[key] -= 1
                skipped += 1
                continue
            entry = {
                "event": "memory_injected",
                "schema": "jwsgj/memory-injection-receipt/1",
                "round_start_ts": anchor,
                "source": str_or(source),
                "action": op["action"],
                "path": op["path"],
                "category": op["category"],
                "rule_id": op["rule_id"],
                "content_sha256": sha,
                "quality_score": round(
                    op["quality_score"] or fallback_quality, 3),
                "at": now_iso(),
                "ts": time.time(),
            }
            line = json.dumps(entry, ensure_ascii=False, default=str)
            if _append_receipt_line_locked(path, line):
                recorded += 1
            else:
                failed += 1
    passed = failed == 0 and invalid == 0
    if recorded:
        logger.info("[MemoryInjection] 注入回执: 新增 %d 条（重复 %d，失败 %d）",
                    recorded, skipped, failed)
    if invalid:
        logger.warning("[MemoryInjection] 批次含 %d 条非法操作，整批不得标记通过",
                       invalid)
    return {
        "recorded": recorded,
        "skipped_dup": skipped,
        "invalid": invalid,
        "failed": failed,
        "receipt_path": path,
        "passed": passed,
    }
def _parse_receipt_line(line: str) -> dict | None:
    text = line.strip()
    if not text:
        return None
    try:
        payload = json.loads(text)
    except (ValueError, RecursionError):
        payload = None
    if isinstance(payload, dict):
        event = str_or(payload.get("event")).strip()
        if event == "memory_injected":
            return payload
        if event:
            return None
        return {"event": "memory_injected", "_receipt_parse_error": True}
    return {"event": "memory_injected", "_receipt_parse_error": True}
def _append_receipt_line_locked(path: str, line: str) -> bool:
    try:
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
                  errors="backslashreplace") as fh:
            payload = line if line.endswith("\n") else line + "\n"
            fh.write(separator + payload)
            fh.flush()
        return True
    except (OSError, ValueError, TypeError, UnicodeError) as exc:
        logger.warning("[MemoryInjection] 回执追加失败: %s", exc)
        return False
def _read_memory_injection_receipts(path: str) -> list[dict]:
    if not os.path.isfile(path):
        return []
    receipts: list[dict] = []
    with open(path, encoding="utf-8-sig", errors="replace") as fh:
        for line in fh:
            entry = _parse_receipt_line(line)
            if entry is None:
                continue
            if str_or(entry.get("event")) != "memory_injected":
                continue
            receipts.append(entry)
    return receipts
def load_memory_injection_receipts(skill_dir: str) -> list[dict]:
    sd = normalize_skill_dir(skill_dir)
    try:
        path = evolution_events_path(sd)
    except (OSError, RuntimeError, ValueError) as exc:
        logger.warning("[MemoryInjection] 回执路径解析失败: %s", exc)
        return []
    if not os.path.isfile(path):
        return []
    with locked_artifact(path):
        try:
            return _read_memory_injection_receipts(path)
        except OSError as exc:
            logger.warning("[MemoryInjection] 回执读取失败: %s", exc)
            return []
def _receipt_has_injection_proof(item: dict) -> bool:
    action = str_or(item.get("action")).strip().lower()
    path = str_or(item.get("path")).strip()
    sha = str_or(item.get("content_sha256")).strip().lower()
    return (action in MEMORY_WRITE_ACTIONS and bool(path) and len(sha) == 64
            and all(char in "0123456789abcdef" for char in sha))
def _round_receipts(receipts: list[dict], round_ts: str) -> list[dict]:
    anchor = _round_anchor(round_ts)
    return [item for item in receipts
            if (_round_anchor(item.get("round_start_ts")) == anchor
                or item.get("_receipt_parse_error") is True)]
def _precision_sample_state(skill_dir: str) -> str:
    """精度样本状态：``ok``（可算误报率或漏报率）/ ``absent`` / ``unreadable``。"""
    try:
        fn_history = read_evolution_section(skill_dir, "fn_probe_history")
        fp_history = read_evolution_section(skill_dir, "feedback_history")
    except (OSError, ValueError, TypeError):
        return "unreadable"
    fn_rounds = (fn_history.get("rounds")
                 if isinstance(fn_history, dict) else None)
    fp_sessions = (fp_history.get("sessions")
                   if isinstance(fp_history, dict) else None)
    if isinstance(fn_rounds, list) and fn_rounds:
        return "ok"
    if isinstance(fp_sessions, list) and fp_sessions:
        return "ok"
    return "absent"


def _ensure_precision_sample(skill_dir: str) -> str:
    """确保精度样本可用；缺失时惰性跑一次漏报探针。

    ``fn_probe_history`` 为空意味着探针尚未落基线（6d 未跑或失败）。此时
    下游门禁会“无样本即放行”，而漏报最隐蔽——findings 为空时所有门禁都
    通过。这里惰性补跑探针，把“无样本”变成“有样本”，探针异常则显式暴露
    为 ``unreadable``（保守阻塞）。探针结果按技能指纹缓存，重跑不重复计费。
    """
    state = _precision_sample_state(skill_dir)
    if state != "absent":
        return state
    try:
        from jwsgj.diag_testing_mutation import (
            run_cached_false_negative_probe,
        )

        run_cached_false_negative_probe(skill_dir)
    except Exception as exc:  # noqa: BLE001 — 探针失败保守阻塞
        logger.warning(
            "[MemoryInjection] 惰性漏报探针失败，精度无法验证: %s", exc)
        return "unreadable"
    return _precision_sample_state(skill_dir)


def check_memory_injection_quality(skill_dir: str) -> dict:
    sd = normalize_skill_dir(skill_dir)
    state = as_dict(load_pipeline_state(sd))
    phase = str_or(state.get("phase"))
    base: dict = {
        "gate_id": "GATE-MEMORY-INJECTION",
        "gate_name": "复盘记忆注入质量门禁",
        "passed": True,
        "skipped": True,
        "reason": "",
        "phase": phase,
        "round_start_ts": str_or(state.get("round_start_ts")),
        "fupan_quality_score": None,
        "memory_ops_count": 0,
        "receipt_count": 0,
        "receipt_covered": 0,
        "receipt_invalid_count": 0,
        "precision_sample_state": "",
        "failure_reasons": [],
        "actions_required": [],
    }
    state_load_error = str_or(state.get("_state_load_error")).strip()
    if state_load_error:
        base.update({
            "passed": False,
            "skipped": False,
            "reason": "pipeline_state_unverified",
            "failure_reasons": [
                "现有管线状态无法验证，不得按初始状态跳过复盘记忆门禁: "
                + state_load_error[:200],
            ],
            "actions_required": [
                "修复或重新生成可验证的 pipeline state 后重跑交付门禁",
            ],
        })
        return base
    if phase not in _FUPAN_LATE_PHASES:
        base["reason"] = "no_fupan_round"
        return base
    quality = _quality_value(state.get("fupan_quality_score"))
    ops_count, ops_count_valid = _memory_operation_count(
        state.get("fupan_memory_ops"))
    round_ts = str_or(state.get("round_start_ts")).strip()
    round_receipts = _round_receipts(
        load_memory_injection_receipts(sd), round_ts)
    receipts = [item for item in round_receipts
                if _receipt_has_injection_proof(item)]
    invalid_receipts = len(round_receipts) - len(receipts)
    reasons: list[str] = []
    actions: list[str] = []
    precision_state = _ensure_precision_sample(sd)
    base["precision_sample_state"] = precision_state
    if precision_state == "unreadable":
        reasons.append(
            "精度样本不可读（fn_probe_history / feedback_history 解析失败）"
            "——误报率与漏报率都无法计算，复盘质量分不足以证明诊断收敛")
        actions.append(
            "修复 jinhua/evolution_state.json 的 fn_probe_history / "
            "feedback_history 节后重跑阶段6a")
    elif precision_state != "ok":
        # 惰性探针跑完仍是 absent：探针零证据或落盘失败，精度同样无法计算，
        # 不得按「有样本」放行（否则重现「无样本即放行」的漏报盲区）。
        reasons.append(
            "精度样本缺失（惰性漏报探针未产出可评估证据或未落盘）"
            "——误报率与漏报率都无法计算，复盘质量分不足以证明诊断收敛")
        actions.append(
            "排查漏报探针零证据/落盘失败原因（模板、检测器注册、"
            "evolution_state 写入）后重跑阶段6d 与 6a")
    if not round_ts:
        reasons.append(
            "管线轮次锚缺失（round_start_ts 未登记）——无法按轮核对"
            "注入回执，历史轮回执不得替代本轮证据")
        actions.append(
            "补登记 pipeline state 的 round_start_ts 后重跑阶段6a 复盘")
    if quality is None:
        reasons.append("复盘质量分缺失（fupan_quality_score 未登记）")
        actions.append(
            "复跑阶段6a run_fupan_step，产出质量分与记忆操作后再交付")
    elif quality < MIN_FUPAN_QUALITY:
        reasons.append(
            f"复盘质量分 {quality:.1f} 低于门槛 {MIN_FUPAN_QUALITY}"
            "（复盘内容质量未达标不得注入）")
        actions.append(
            "补齐复盘证据（风险/改进/代码现场）提升质量分后重跑阶段6a")
    if not ops_count_valid:
        reasons.append(
            "复盘记忆操作计数非法（必须是整数，不得截断小数或非有限值）")
        actions.append(
            "重跑阶段6a 以重建 fupan_memory_ops 整数计数后再交付")
    elif ops_count <= 0:
        reasons.append("复盘记忆操作为空（复盘内容未产出可注入记忆）")
        actions.append(
            "补齐复盘记忆候选并重跑阶段6a，确保 memory_operations 非空")
    if invalid_receipts:
        reasons.append(
            f"存在 {invalid_receipts} 条无效回执（损坏或缺操作、路径、合法内容指纹）"
            "——损坏证据不得与有效回执混计后放行")
        actions.append(
            "核对并修复 memory_injection_receipt.jsonl 的无效记录，"
            "重跑阶段6a 使本轮操作与有效回执一一对应")
    receipt_total = len(receipts)
    covered = receipt_total
    if ops_count_valid and ops_count > 0 and covered < ops_count:
        reasons.append(
            f"注入回执覆盖不足：{covered}/{ops_count} 条记忆操作未落回执"
            "（复盘内容未真正注入灵犀记忆系统）")
        actions.append(
            "record_memory_injection 补记回执（阶段6a 失败重跑），"
            "确保每条记忆操作有 path+content 指纹留痕")
    if ops_count_valid and receipt_total > ops_count:
        reasons.append(
            f"注入回执覆盖超量：本轮 {ops_count} 条记忆操作却有 {receipt_total} 条"
            "有效回执——重复重试、跨批残留或状态计数失真均会破坏一一对应")
        actions.append(
            "核对本轮 memory_operations 与回执的轮次锚、path+content 指纹，"
            "重跑阶段6a 并确保每条操作恰好对应一条有效回执")
    if reasons:
        logger.warning(
            "[MemoryInjection] 门禁阻塞: %s（phase=%s, quality=%s, "
            "ops=%d, receipts=%d）",
            "；".join(reasons), phase, quality, ops_count, covered)
    else:
        logger.info(
            "[MemoryInjection] 门禁通过: quality=%.1f, ops=%d, receipts=%d",
            quality, ops_count, covered)
    base.update({
        "passed": not reasons,
        "skipped": False,
        "reason": "" if not reasons else "memory_injection_blocked",
        "round_start_ts": round_ts,
        "fupan_quality_score": quality,
        "memory_ops_count": ops_count,
        "receipt_count": receipt_total,
        "receipt_covered": covered,
        "receipt_invalid_count": invalid_receipts,
        "precision_sample_state": precision_state,
        "failure_reasons": reasons,
        "actions_required": actions,
    })
    return base
_STAGE_PAIR_PREVIEW = 20
_STAGE_PAIR_BLOCK_STATUSES = frozenset({"missing", "mismatch", "invalid"})
_STAGE_JSON_OWNER_UNKNOWN = "\x00owner-unknown"
def _stage_pair_base() -> dict:
    return {
        "gate_id": "GATE-STAGE-PAIR",
        "gate_name": "阶段报告配对门禁",
        "passed": True,
        "skipped": True,
        "reason": "",
        "checked_count": 0,
        "paired_count": 0,
        "missing_count": 0,
        "mismatch_count": 0,
        "invalid_count": 0,
        "orphan_json_count": 0,
        "unowned_html_count": 0,
        "unowned_json_count": 0,
        "pair_violation_count": 0,
        "violations": [],
        "failure_reasons": [],
        "actions_required": [],
    }
def _stage_pair_error(message: str) -> dict:
    base = _stage_pair_base()
    base.update({
        "passed": False,
        "skipped": False,
        "reason": "stage_pair_gate_error",
        "pair_violation_count": -1,
        "failure_reasons": [message],
        "actions_required": [
            "修复 htm/zhenduan 落点解析或目录权限后重跑交付门禁"],
    })
    return base
def _stage_pair_abort(base: dict, reasons: list[str], error: dict) -> dict:
    collected = [str_or(text).strip()
                 for text in (error.get("failure_reasons") or [])]
    base.update({
        "passed": False,
        "skipped": False,
        "reason": str_or(error.get("reason")) or "stage_pair_gate_error",
        "pair_violation_count": -1,
        "failure_reasons": list(reasons) + [text for text in collected if text],
        "actions_required": list(error.get("actions_required") or []),
    })
    return base
def _landing_listing(path: str, label: str) -> tuple[list | None, dict | None]:
    if not path:
        return None, None
    if not os.path.exists(path):
        return None, None
    if not os.path.isdir(path):
        return None, _stage_pair_error(f"{label} 落点不是目录: {path}")
    try:
        return sorted(os.listdir(path)), None
    except OSError as exc:
        return None, _stage_pair_error(f"{label} 目录读取失败: {exc}")
def _stage_html_read_error(path: str) -> dict | None:
    try:
        with open(path, "rb") as handle:
            handle.read(1)
    except OSError as exc:
        return _stage_pair_error(f"阶段 HTML 读取失败: {exc}")
    return None

def _stage_json_owner(path: str) -> tuple[str, dict | None]:
    try:
        with open(path, encoding="utf-8-sig") as handle:
            doc = json.load(handle)
    except OSError as exc:
        return "", _stage_pair_error(f"阶段 JSON 读取失败: {exc}")
    except (ValueError, RecursionError):
        return _STAGE_JSON_OWNER_UNKNOWN, None
    if not isinstance(doc, dict):
        return _STAGE_JSON_OWNER_UNKNOWN, None
    return str_or(doc.get("skill_dir")), None
def _stage_filename_key(name: str) -> str:
    return os.path.normcase(os.path.normpath(name))
def _stage_pair_reason(name: str, status: str, pair: dict) -> str:
    html_items = pair.get("html_items")
    json_items = pair.get("json_items")
    if status == "missing":
        return f"{name} 缺配套 JSON（HTML {html_items} 条 ↔ 0 条）"
    if status == "invalid":
        if pair.get("owner_mismatch"):
            return f"{name} 配套 JSON 归属其他技能，拒绝跨技能错配"
        return f"{name} 配套 JSON 结构非法或缺少 item_count"
    return (f"{name} 条目数不一致"
            f"（HTML {html_items} ↔ JSON {json_items}）")
def check_stage_pair_integrity(skill_dir: str) -> dict:
    raw = (os.fspath(skill_dir) if isinstance(skill_dir, os.PathLike)
           else skill_dir)
    if not isinstance(raw, str) or not raw.strip():
        return _stage_pair_error("缺少技能归属锚（skill_dir 为空）")
    sd = normalize_skill_dir(raw.strip())
    if not sd:
        return _stage_pair_error("缺少技能归属锚（skill_dir 解析为空）")
    try:
        html_dir = get_html_report_base()
        json_dir = json_root_dir(sd)
    except (RuntimeError, ValueError) as exc:
        return _stage_pair_error(f"阶段报告落点解析失败: {exc}")
    target = normalize_skill_key(sd)
    base = _stage_pair_base()
    reasons: list[str] = []
    actions: list[str] = []
    violations: list[dict] = base["violations"]
    html_names: set[str] = set()
    html_listing, html_error = _landing_listing(html_dir, "htm")
    if html_error is not None:
        return _stage_pair_abort(base, reasons, html_error)
    if html_listing is not None:
        for name in html_listing:
            if not name.lower().endswith(".html"):
                continue
            path = os.path.join(html_dir, name)
            if not os.path.isfile(path):
                continue
            if not stage_of_file(name):
                continue
            read_error = _stage_html_read_error(path)
            if read_error is not None:
                return _stage_pair_abort(base, reasons, read_error)
            owner = normalize_skill_key(
                str_or(read_stage_meta(path).get("skill")))
            pair = None
            if not owner:
                base["unowned_html_count"] += 1
                candidate = stage_pair_status(path, sd)
                candidate_json_path = str_or(candidate.get("json_path"))
                candidate_owner, owner_error = (
                    _stage_json_owner(candidate_json_path)
                    if candidate_json_path else ("", None))
                if owner_error is not None:
                    return _stage_pair_abort(base, reasons, owner_error)
                if (candidate_owner
                        and candidate_owner != _STAGE_JSON_OWNER_UNKNOWN
                        and normalize_skill_key(candidate_owner) == target):
                    owner = target
                    pair = candidate
                else:
                    continue
            if owner != target:
                continue
            html_names.add(_stage_filename_key(name))
            base["checked_count"] += 1
            if pair is None:
                pair = stage_pair_status(path, sd)
            status = str_or(pair.get("status")) or "missing"
            json_path = str_or(pair.get("json_path"))
            json_owner, owner_error = (
                _stage_json_owner(json_path) if json_path else ("", None))
            if owner_error is not None:
                return _stage_pair_abort(base, reasons, owner_error)
            if (json_owner and json_owner != _STAGE_JSON_OWNER_UNKNOWN
                    and normalize_skill_key(json_owner) != target):
                status = "invalid"
                pair = dict(pair, owner_mismatch=True)
            if status == "paired":
                base["paired_count"] += 1
                continue
            if status not in _STAGE_PAIR_BLOCK_STATUSES:
                status = "mismatch"
            base[f"{status}_count"] += 1
            if len(violations) < _STAGE_PAIR_PREVIEW:
                violations.append({
                    "file": name,
                    "status": status,
                    "html_items": pair.get("html_items"),
                    "json_items": pair.get("json_items"),
                    "json_path": str_or(pair.get("json_path")),
                })
            reasons.append(_stage_pair_reason(name, status, pair))
    json_listing, json_error = _landing_listing(json_dir, "zhenduan")
    if json_error is not None:
        return _stage_pair_abort(base, reasons, json_error)
    if json_listing is not None:
        for name in json_listing:
            if not name.lower().endswith(".json"):
                continue
            path = os.path.join(json_dir, name)
            if not os.path.isfile(path):
                continue
            stem = os.path.splitext(name)[0]
            if _stage_filename_key(f"{stem}.html") in html_names:
                continue
            if not stage_of_file(stem + ".html"):
                continue
            owner, owner_error = _stage_json_owner(path)
            if owner_error is not None:
                return _stage_pair_abort(base, reasons, owner_error)
            if not owner or owner == _STAGE_JSON_OWNER_UNKNOWN:
                base["unowned_json_count"] += 1
                continue
            if normalize_skill_key(owner) != target:
                continue
            base["orphan_json_count"] += 1
            if len(violations) < _STAGE_PAIR_PREVIEW:
                violations.append({
                    "file": name,
                    "status": "orphan_json",
                    "html_items": 0,
                    "json_items": None,
                    "json_path": path,
                })
            reasons.append(f"{name} 为孤儿阶段快照（无同名 HTML）")
    blocking = (base["missing_count"] + base["mismatch_count"]
                + base["invalid_count"] + base["orphan_json_count"])
    base["pair_violation_count"] = blocking
    if blocking:
        actions.append(
            "修复阶段报告配对：缺失或结构非法用 stage_pair_status 复核后"
            "重发对应阶段报告，条目不一致按 HTML 快照回填，孤儿快照用 "
            "migrate_legacy_report_artifacts 预演后迁移")
    if base["unowned_html_count"] or base["unowned_json_count"]:
        actions.append(
            "存在无归属阶段文件，运行 "
            "migrate_legacy_report_artifacts(skill_dir, dry_run=True) "
            "预演后迁移（只移动不删除）")
    base.update({
        "passed": not blocking,
        "skipped": (not blocking and base["checked_count"] == 0
                    and base["unowned_html_count"] == 0
                    and base["unowned_json_count"] == 0),
        "reason": "" if not blocking else "stage_pair_blocked",
        "failure_reasons": reasons,
        "actions_required": actions,
    })
    if blocking:
        logger.warning(
            "[StagePair] 门禁阻塞: 检查=%d, 缺JSON=%d, 不一致=%d, "
            "结构非法=%d, 孤儿快照=%d",
            base["checked_count"], base["missing_count"],
            base["mismatch_count"], base["invalid_count"],
            base["orphan_json_count"])
    else:
        logger.info(
            "[StagePair] 门禁通过: 检查=%d, 配对=%d, 无归属 html/json=%d/%d",
            base["checked_count"], base["paired_count"],
            base["unowned_html_count"], base["unowned_json_count"])
    return base

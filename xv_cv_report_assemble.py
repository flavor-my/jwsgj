from __future__ import annotations

import logging
import os
from datetime import datetime
from typing import Any

from jwsgj.diag_blindspot_report import ensure_call_graph
from jwsgj.diag_types_normalize import (
    as_number,
    coerce_line,
    coerce_text_list,
    conf_chain,
    degrade_factor_of,
    get_max_severity,
    integral_count,
    is_real_number,
    iter_payload_finding_items,
    list_field,
    method_status_detail,
    norm_dict,
    normalize_list_field,
    parse_locator_file,
    parse_locator_line,
    safe_float,
    safe_int,
    safe_isfinite,
    signal_bool,
    timestamp_ms,
)
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    CONFIRMED_DISPLAY_LIMIT,
    CV_RULES,
    FIELD_ADJUSTED_CONFIDENCE,
    FIELD_BASE_CONFIDENCE,
    FIELD_EVIDENCE_FAMILIES,
    FIELD_EVIDENCE_STRENGTH,
    FIELD_INTERMEDIATE_REPORTS,
    FIELD_METHOD_CONFIDENCE_MULTIPLIERS,
    FIELD_RULES_TRIGGERED,
    FIELD_TOTAL_INPUT_FINDINGS,
    MESSAGE_TRUNCATE_LEN,
    SIGNAL_DEGRADE_FACTOR,
)
from jwsgj.log_config import log_swallowed
from jwsgj.xv_context_derivation import (
    METHOD_REGISTRY,
    normalize_method_status,
    sub_engine_payload,
)
from jwsgj.xv_evidence_strength import (
    PHASE_CRITICALITY_LEVELS,
    PHASE_MODULE_CRITICALITY,
)
from jwsgj.xv_intermediate_store import (
    atomic_save_json,
    get_round_start_ts,
    load_all_intermediates,
    load_intermediate_fused,
    locate_sub_results,
)

logger = logging.getLogger(__name__)
def _phase_error_module_of(err: Any) -> str | None:
    if isinstance(err, dict):
        module = err.get("module")
        if isinstance(module, str):
            return module
    return None
def _declared_criticality(err: Any) -> str:
    if not isinstance(err, dict):
        return ""
    value = err.get("criticality")
    return (value if isinstance(value, str)
            and value in PHASE_CRITICALITY_LEVELS else "")
def _criticality_policy(criticality: Any) -> dict:
    if not isinstance(criticality, dict):
        return dict(PHASE_MODULE_CRITICALITY)
    return {module: level for module, level in criticality.items()
            if isinstance(module, str) and module
            and isinstance(level, str)
            and level in PHASE_CRITICALITY_LEVELS}
def _error_criticality(err: Any, policy: dict) -> str:
    declared = _declared_criticality(err)
    if declared:
        return declared
    module = _phase_error_module_of(err)
    return policy.get(module, "") if module else ""
def _normalized_errors(phase_errors: Any) -> list:
    if not phase_errors:
        return []
    if isinstance(phase_errors, (list, tuple, set, frozenset)):
        return list(phase_errors)
    if isinstance(phase_errors, (str, bytes, bytearray, dict)):
        return [phase_errors]
    if not hasattr(phase_errors, "__iter__"):
        return [phase_errors]
    try:
        return list(phase_errors)
    except TypeError:
        return [phase_errors]
def _health_report(status: str, critical: list, degraded: list,
                   all_errors: list, summary: str) -> dict:
    return {
        "overall_status": status,
        "critical_errors": critical,
        "degraded_errors": degraded,
        "all_errors": all_errors,
        "summary": summary,
    }
def _phase_health_status(phase_health: Any) -> str:
    if not isinstance(phase_health, dict):
        return ""
    raw = phase_health.get("overall_status")
    return raw.strip().lower() if isinstance(raw, str) else ""
def _classify_phase_errors(phase_errors: list,
                           policy: dict | None = None
                           ) -> tuple[list, list]:
    effective = _criticality_policy(policy)
    critical = []
    degraded = []
    for err in phase_errors:
        level = _error_criticality(err, effective)
        if level == "critical":
            critical.append(err)
        elif level == "degraded":
            degraded.append(err)
    return critical, degraded
def _modules_csv(errors: list) -> str:
    return ', '.join(
        str(e.get('module') or '?') if isinstance(e, dict) else str(e)
        for e in errors)
def summarize_phase_health(phase_errors: list[dict], *,
                           criticality: dict | None = None) -> dict:
    normalized_errors: list = []
    try:
        normalized_errors = _normalized_errors(phase_errors)
        if not normalized_errors:
            return _health_report(
                "healthy", [], [], [], "Phase 1/2 全部正常运行")
        critical, degraded = _classify_phase_errors(
            normalized_errors, criticality)
        if critical:
            return _health_report(
                "critical", critical, degraded, normalized_errors,
                f"Phase 1/2 关键模块失败: {_modules_csv(critical)}")
        if degraded:
            return _health_report(
                "degraded", critical, degraded, normalized_errors,
                f"Phase 1/2 部分降级: {_modules_csv(degraded)}")
        return _health_report(
            "warning", critical, degraded, normalized_errors,
            f"Phase 1/2 有 {len(normalized_errors)} 个警告")
    except Exception as e:
        logger.exception("[summarize_phase_health] 异常降级")
        _payload = _health_report(
            "degraded", [], [], normalized_errors,
            f"Phase 1/2 健康汇总异常降级: {e}")
        _payload["_error"] = True
        _payload["_partial"] = True
        return _payload
__all__ = [
    'ReportAggregator',
    'attach_cv_report_summary',
    'build_executive_summary',
    'build_f1_report',
    'extract_cv_stats',
    'extract_degraded_findings',
    'generate_cv_report',
    'log_cv_extract_summary',
    'summarize_phase_health',
]
logger.info("xv_cv_report_assemble 已加载: %d 项导出", len(__all__))
_RULE_EXEC_DIAG_METRICS: tuple[tuple[str, str], ...] = (
    ("总 locator 数", "total_locators"),
    ("规则匹配", "rule_matched"),
    ("规则未匹配", "rule_not_matched"),
    ("降级匹配", "degraded_matched"),
    ("通用回退", "generic_fallback"),
)
_LIKELY_DISPLAY_LIMIT = 10
_P0P1_DISPLAY_LIMIT = 5
_FUNCTION_SUMMARY_LIMIT = 10
_CRITICAL_CONFIRMED_THRESHOLD = 5
_REPORT_CONFIDENCE_FIELDS = (
    FIELD_ADJUSTED_CONFIDENCE, FIELD_BASE_CONFIDENCE, "confidence")
def _log_degraded(label: str, error: Exception) -> None:
    logger.warning("[%s] 异常降级: %s", label, error)
def _layer2_details_ref(mid: str, ts: str, round_ref: str) -> str:
    if round_ref:
        return f"_intermediate/{round_ref}"
    if ts:
        return f"_intermediate/{mid}_{ts}.json"
    return f"_intermediate/{mid}.json"
def _cfg_attr(cfg, name: str, default: str) -> str:
    return getattr(cfg, name, default) if cfg else default
def _abs_dir(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, os.PathLike):
        try:
            text = os.fsdecode(value)
        except (TypeError, ValueError):
            return ""
    elif isinstance(value, str):
        text = value.strip()
    else:
        return ""
    return os.path.abspath(text) if text else ""
def _layer2_identity_fields(mid: str, data: dict, cfg) -> dict:
    return {
        "method_id": mid,
        "method_name": _text(data.get("method_name") or _cfg_attr(cfg, "name", mid)),
        "domain": _text(data.get("domain") or _cfg_attr(cfg, "domain", "")),
        "status": _text(data.get("status") or "unknown"),
    }
def _layer2_metric_fields(data: dict) -> dict:
    return {
        "elapsed_s": as_number(data.get("elapsed_s")),
        "findings_count": safe_int(data.get("findings_count")),
        "score": safe_float(data.get("score"), 0.0),
    }
def _layer2_text_fields(data: dict) -> dict:
    return {
        "summary": _text(data.get("summary")),
        "error": _text(data.get("error")),
    }
def _layer2_entry(mid: str, data: dict, cfg, ts: str) -> dict:
    entry = _layer2_identity_fields(mid, data, cfg)
    entry.update(_layer2_metric_fields(data))
    entry.update(_layer2_text_fields(data))
    entry["_details_ref"] = _layer2_details_ref(
        mid, ts, str(data.get("_round_ref") or ""))
    return entry
def _corrupted_intermediate(mid: str, value: Any) -> dict:
    return {
        "method_id": mid,
        "status": "corrupted",
        "error": f"中间结果必须是 dict，实际为 {type(value).__name__}",
        "payload": {},
    }
def _valid_results(results: dict) -> dict:
    if not isinstance(results, dict):
        raise TypeError(
            f"load_all_intermediates 返回非 dict({type(results).__name__})")
    if results.get("_error"):
        raise RuntimeError("中间结果加载失败（load_all_intermediates 降级哨兵）")
    valid = {}
    for mid, data in results.items():
        if (not isinstance(mid, str) or mid.startswith("_")
                or mid not in METHOD_REGISTRY):
            continue
        valid[mid] = (data if isinstance(data, dict)
                      else _corrupted_intermediate(mid, data))
    return valid
def _dict_list(value) -> list[dict]:
    return [x for x in normalize_list_field(value) if isinstance(x, dict)]
_CV_MISSING_STATUS = "insufficient_coverage"
def _cv_degraded_payload(reason: str) -> dict:
    return {
        "status": _CV_MISSING_STATUS,
        "health": "critical",
        "health_description": "覆盖不足，CV 结论不完整（不代表代码库健康）",
        "_degraded": True,
        "_degraded_reason": reason,
    }
_CV_FAILURE_STATUSES = frozenset({
    "error", "fail", "failed", "blocked", "timeout", "skip", "skipped",
    "corrupted",
})
def _normalize_cv_failure(result: dict) -> dict:
    if isinstance(result, dict) and not result:
        reason = "CV 返回空映射，缺少验证结论"
        logger.warning("[Aggregator] %s，按覆盖不足降级", reason)
        return _cv_degraded_payload(reason)
    raw_status = result.get("status")
    status = raw_status.strip().lower() if isinstance(raw_status, str) else ""
    if not signal_bool(result.get("_error")) and status not in _CV_FAILURE_STATUSES:
        return result
    detail = result.get("error") or result.get("message") or status or "_error 哨兵"
    reason = f"CV 返回失败结果({status or '_error'}): {str(detail)[:160]}"
    logger.warning("[Aggregator] %s，按覆盖不足降级", reason)
    return _cv_degraded_payload(reason)
class ReportAggregator:
    def __init__(self, intermediate_dir: str, output_dir: str,
                 skill_dir: str | None = None, cv_runner=None):
        self.intermediate_dir = _abs_dir(intermediate_dir)
        self.output_dir = _abs_dir(output_dir)
        self.skill_dir = _abs_dir(skill_dir)
        self.cv_runner = cv_runner
        self.results: dict[str, dict] = {}
        self.xv_result: dict = {}
    def build(self, xv_result: dict | None = None) -> dict:
        if not self.intermediate_dir:
            logger.error(
                "[Aggregator] intermediate_dir 为空，拒绝按 cwd 猜测中间结果根")
            return {"_error": True, "_partial": True}
        try:
            cutoff = get_round_start_ts(self.skill_dir) if self.skill_dir else ""
            self.results = _valid_results(load_all_intermediates(
                self.intermediate_dir, freshness_cutoff=cutoff))
            self.xv_result = self._resolve_xv_result(xv_result)
            return self._assemble()
        except Exception as e:  # noqa: BLE001 -- 异常降级留痕
            log_swallowed(__name__, e, context='ReportAggregator.build:Exc')
            _log_degraded("build", e)
            return {"_error": True, "_partial": True}
    def _resolve_xv_result(self, xv_result: dict | None) -> dict:
        if xv_result is None:
            if not callable(self.cv_runner):
                logger.warning(
                    "[Aggregator] 未提供 xv_result 且无 cv_runner，"
                    "CV 章节按覆盖不足降级")
                return _cv_degraded_payload("未提供 CV 结果且无 cv_runner")
            try:
                resolved = self.cv_runner()
            except Exception as e:  # noqa: BLE001 -- CV 单章节降级
                logger.warning(
                    "[Aggregator] cv_runner 执行失败(%s)，CV 章节按覆盖不足降级", e)
                return _cv_degraded_payload(
                    f"cv_runner 执行失败: {type(e).__name__}: {e}"[:200])
            if isinstance(resolved, dict):
                return _normalize_cv_failure(resolved)
            return _cv_degraded_payload(
                "cv_runner 返回非映射: " + type(resolved).__name__)
        if isinstance(xv_result, dict):
            return _normalize_cv_failure(xv_result)
        logger.warning(
            "[Aggregator] build 入参 xv_result 非 dict(%s)，CV 章节按覆盖不足降级",
            type(xv_result).__name__)
        return _cv_degraded_payload(
            "build 入参 xv_result 非映射: " + type(xv_result).__name__)
    def _assemble(self) -> dict:
        stats = self._compute_stats()
        layer_1 = self._build_layer_1()
        layer_2, intermediate_timestamps = self._build_layer_2()
        layer_3 = self._build_layer_3()
        report_chain = {
            FIELD_INTERMEDIATE_REPORTS: intermediate_timestamps,
            "note": ("每个中间报告文件名格式为 {mid}_{YYYYMMDDHHMMSSfff}.json"
                     "（毫秒级），可通过年月日时分秒毫秒准确识别完整分析链和每次运行"),
            "intermediate_dir": self.intermediate_dir,
            "output_dir": self.output_dir,
            "skill_dir": self.skill_dir,
        }
        _ts_str = timestamp_ms()
        lift_src, lift_payload = self._lift_source()
        dead_code_phases, exception_metrics = self._lift_c_group_metrics(
            lift_src, lift_payload)
        runtime_metrics = self._lift_runtime_metrics(lift_src, lift_payload)
        return {
            "report_version": "2.0",
            "timestamp": _ts_str,
            "summary": stats,
            "report_chain": report_chain,
            "dead_code_phases": dead_code_phases,
            "exception_metrics": exception_metrics,
            "runtime_metrics": runtime_metrics,
            "conclusion_layers": {
                "layer_1_rapid": layer_1,
                "layer_2_detailed": layer_2,
                "layer_3_evidence": layer_3,
            },
            CAT_CROSS_VALIDATION: self.xv_result,
        }
    def _lift_source(self) -> tuple[dict, dict]:
        c_result = norm_dict(self.results.get("C"))
        c_payload = norm_dict(c_result.get("payload"))
        sub_results = locate_sub_results(c_payload)
        c1_result = norm_dict(sub_results.get("C1")).get("result")
        lift_src = (c1_result if isinstance(c1_result, dict) and c1_result
                    else c_result)
        return lift_src, c_payload
    def _lift_c_group_metrics(self, lift_src: dict,
                              c_payload: dict) -> tuple[dict, dict]:
        return (lift_src.get("dead_code_phases") or c_payload.get("dead_code_phases") or {},
                lift_src.get("exception_metrics") or c_payload.get("exception_metrics") or {})
    def _lift_runtime_metrics(self, lift_src: dict, c_payload: dict) -> dict:
        sandbox = (norm_dict(norm_dict(lift_src.get("payload")).get("sandbox"))
                   or norm_dict(c_payload.get("sandbox")))
        runtime = {
            "simulation": norm_dict(sandbox.get("simulation")
                                    or lift_src.get("simulation")),
            "blindspot_metrics": norm_dict(
                sandbox.get("blindspot_metrics")
                or lift_src.get("blindspot_metrics")),
        }
        return {key: value for key, value in runtime.items() if value}
    def _compute_stats(self) -> dict:
        statuses = self._count_statuses()
        verdicts = self._count_verdicts()
        cv_degraded = bool(signal_bool(self.xv_result.get("_degraded"))
                           or _cv_degraded_reason(self.xv_result))
        phase_status = _phase_health_status(
            self.xv_result.get("phase_health"))
        if (verdicts["fail"] or statuses["error"] or statuses["timeout"]
                or phase_status == "critical"):
            overall_status = "blocked"
        elif (cv_degraded or phase_status in ("degraded", "warning")
              or len(self.results) < len(METHOD_REGISTRY)
              or statuses["pass"] == 0 or statuses["skip"]
              or statuses["warn"] or statuses["corrupted"]):
            overall_status = "warn"
        else:
            overall_status = "pass"
        return {
            "total_independent_methods": len(METHOD_REGISTRY),
            "executed": len(self.results),
            "passed": statuses["pass"],
            "warned": statuses["warn"],
            "timeout": statuses["timeout"],
            "failed": statuses["fail"],
            "error": statuses["error"],
            "skipped": statuses["skip"],
            "corrupted": statuses["corrupted"],
            "verdict_failed": verdicts["fail"],
            "overall_score": self._avg_score(),
            "findings_total": self._findings_total(),
            "overall_status": overall_status,
        }
    def _count_verdicts(self) -> dict[str, int]:
        """按诊断结论（verdict）计数；历史记录无 verdict 时回退 status=fail。"""
        verdicts = {"pass": 0, "warn": 0, "fail": 0}
        for data in self.results.values():
            if not isinstance(data, dict):
                continue
            _verdict = str(data.get("verdict") or "").strip().lower()
            if _verdict in verdicts:
                verdicts[_verdict] += 1
            elif method_status_detail(data.get("status")) == "fail":
                verdicts["fail"] += 1
        return verdicts
    def _count_statuses(self) -> dict[str, int]:
        statuses = {"pass": 0, "warn": 0, "fail": 0,
                    "timeout": 0, "skip": 0, "error": 0, "corrupted": 0}
        for data in self.results.values():
            statuses[method_status_detail(data.get("status"))] += 1
        return statuses
    def _avg_score(self) -> float:
        scores = []
        for data in self.results.values():
            if not is_real_number(data.get("score")):
                continue
            number = safe_float(data.get("score"), None)
            if number is not None:
                scores.append(number)
        if not scores:
            return 0.0
        total = sum(scores)
        if not safe_isfinite(total):
            return 0.0
        return round(total / len(scores), 1)
    def _findings_total(self) -> int:
        total = 0
        for data in self.results.values():
            declared = integral_count(data.get("findings_count"))
            explicit = declared if declared is not None and declared > 0 else 0
            actual = sum(1 for _ in iter_payload_finding_items(
                data.get("payload", {})))
            total += max(explicit, actual)
        return total
    def _build_layer_1(self) -> dict:
        xv = self.xv_result
        enumerated = _reconciled_conclusion_counts(xv)
        layer_1 = {
            "source": CAT_CROSS_VALIDATION,
            "confirmed_count": max(
                _stat_count(xv.get("confirmed")), enumerated["confirmed"]),
            "suppressed_count": max(
                _stat_count(xv.get("suppressed")), enumerated["suppressed"]),
            "investigated_count": _stat_count(xv.get("investigated")),
            "review_count": _stat_count(xv.get("review")),
            "rules_applied": _rules_applied_count(xv),
            FIELD_TOTAL_INPUT_FINDINGS: _input_total_with_lower_bound(
                _stat_count(xv.get(FIELD_TOTAL_INPUT_FINDINGS)), enumerated),
        }
        layer_1.update(_participation_fields(
            norm_dict(xv.get("participation"))))
        return layer_1
    def _build_layer_2(self) -> tuple:
        layer_2 = {}
        intermediate_timestamps = {}
        for mid, data in sorted(self.results.items()):
            cfg = METHOD_REGISTRY.get(mid)
            ts = str(data.get("_report_timestamp") or "")
            if ts:
                intermediate_timestamps[mid] = ts
            layer_2[mid] = _layer2_entry(mid, data, cfg, ts)
        return layer_2, intermediate_timestamps
    def _build_layer_3(self) -> dict:
        xv = self.xv_result
        findings = _dict_list(xv.get("findings_index"))
        return {
            "cross_validation_rules": _dict_list(xv.get("rules_detail")),
            "findings_by_evidence_family": _group_evidence_by_family(findings),
            "top_findings": findings,
            "top_findings_total": len(findings),
            "top_findings_truncated": False,
        }
    def write(self, report: dict | None = None) -> str:
        try:
            if report is None:
                report = self.build()
            if not isinstance(report, dict):
                raise TypeError(
                    f"report 必须是 dict({type(report).__name__})")
            if report.get("_error"):
                logger.error("[Aggregator] 聚合构建失败（_error 哨兵），拒绝落盘")
                return ""
            if not self.output_dir:
                logger.error("[Aggregator] output_dir 为空，拒绝写入 cwd")
                return ""
            timestamp = timestamp_ms()
            path = os.path.join(self.output_dir, f"report_{timestamp}.json")
            report_chain = report.get("report_chain")
            if not isinstance(report_chain, dict):
                if report_chain is not None:
                    logger.warning(
                        "[Aggregator] report_chain 非 dict(%s)，归一为空链",
                        type(report_chain).__name__)
                report_chain = {}
                report["report_chain"] = report_chain
            report_chain["final_report_timestamp"] = timestamp
            os.makedirs(self.output_dir, exist_ok=True)
            atomic_save_json(path, report)
            logger.info("[Aggregator] 报告已写入: %s", path)
            return path
        except Exception as e:  # noqa: BLE001 -- 写盘降级返回空串
            log_swallowed(__name__, e, context='ReportAggregator.write:Exc')
            _log_degraded("write", e)
            return ""
def _stat_value(value) -> int | None:
    number = safe_float(value, None)
    if (number is None or not safe_isfinite(number) or number < 0
            or not number.is_integer()):
        return None
    return int(number)
def _stat_count(value) -> int:
    count = _stat_value(value)
    return 0 if count is None else count
_INPUT_CONCLUSION_BUCKETS = ("confirmed", "likely", "uncertain", "suppressed")
def _input_total_with_lower_bound(declared: int, enumerated: dict) -> int:
    indexed_inputs = sum(
        enumerated.get(bucket, 0) for bucket in _INPUT_CONCLUSION_BUCKETS)
    return max(declared, indexed_inputs)
def _rules_applied_count(cv_result: dict) -> int:
    declared = _stat_count(cv_result.get("rules_applied_count"))
    enumerated = sum(
        1 for rule in _dict_list(cv_result.get("rules_detail"))
        if signal_bool(rule.get("triggered")))
    return max(declared, enumerated)
def _degrade_status_of(finding: dict) -> str | None:
    status = finding.get("_degrade_status")
    if status in ("partial_degraded", "degraded"):
        return status
    if signal_bool(finding.get("_partial_degrade")):
        return "partial_degraded"
    if signal_bool(finding.get("_is_degraded")):
        return "degraded"
    return None
def _iter_degraded(cv_result: dict):
    for entry in _dict_list(cv_result.get("findings_index")):
        entry_status = _degrade_status_of(entry)
        if entry_status is not None:
            yield entry, entry, entry_status
        for finding in _dict_list(entry.get("findings")):
            status = _degrade_status_of(finding)
            if status is not None:
                yield entry, finding, status
def _pick_stat(primary: dict, key: str, fallback: dict,
               fallback_key: str) -> int:
    primary_value = _stat_value(primary.get(key))
    if primary_value is not None:
        return primary_value
    return _stat_count(fallback.get(fallback_key))
def _participation_fields(participation: dict) -> dict:
    _missing = coerce_text_list(
        participation["missing"] if "missing" in participation
        else participation.get("missing_methods"))
    _full = participation.get("all_participated")
    if not isinstance(_full, (bool, str)):
        _full = participation.get("full_participation")
    if isinstance(_full, str):
        _full = signal_bool(_full)
    elif not isinstance(_full, bool):
        _full = False
    return {
        "participation_rate": as_number(
            participation.get("participation_rate"), 0),
        "full_participation": _full,
        "missing_methods": [m for m in _missing if m],
    }
def _evidence_entry(f: dict) -> dict:
    return {
        "locator": str(f.get("locator") or ""),
        "conclusion": str(f.get("conclusion") or ""),
        "confidence": conf_chain(f, *_REPORT_CONFIDENCE_FIELDS),
        "sources": coerce_text_list(f.get("sources")),
    }
def _group_evidence_by_family(findings: list[dict]) -> dict:
    by_family: dict[str, list[dict]] = {}
    for f in findings:
        families = tuple(coerce_text_list(
            f.get(FIELD_EVIDENCE_FAMILIES))) or ("unknown",)
        by_family.setdefault(" \u00d7 ".join(families), []).append(
            _evidence_entry(f))
    return by_family
def extract_cv_stats(report: dict) -> dict:
    try:
        report = norm_dict(report)
        cv_result = norm_dict(report.get(CAT_CROSS_VALIDATION))
        summary = norm_dict(report.get("summary"))
        enumerated = _reconciled_conclusion_counts(cv_result)
        for bucket in _INPUT_CONCLUSION_BUCKETS:
            enumerated[bucket] = max(
                enumerated[bucket],
                _pick_stat(cv_result, bucket, summary, f"cv_{bucket}"))
        confirmed = enumerated["confirmed"]
        suppressed = enumerated["suppressed"]
        investigated = _pick_stat(cv_result, "investigated", summary, "cv_investigated")
        total_input = _pick_stat(cv_result, FIELD_TOTAL_INPUT_FINDINGS,
                                 summary, FIELD_TOTAL_INPUT_FINDINGS)
        total_input = _input_total_with_lower_bound(total_input, enumerated)
        degraded_counts = {"degraded": 0, "partial_degraded": 0}
        for _e, _f, status in _iter_degraded(cv_result):
            degraded_counts[status] += 1
        return {
            "confirmed": confirmed,
            "suppressed": suppressed,
            "investigated": investigated,
            "degraded": degraded_counts["degraded"],
            "partial_degraded": degraded_counts["partial_degraded"],
            FIELD_TOTAL_INPUT_FINDINGS: total_input,
        }
    except Exception as e:  # noqa: BLE001 -- 统计提取降级
        _log_degraded("extract_cv_stats", e)
        return {"_error": True, "_partial": True}
def extract_degraded_findings(report: dict) -> list:
    try:
        report = norm_dict(report)
        cv_result = norm_dict(report.get(CAT_CROSS_VALIDATION))
        return [_degraded_entry(entry, f, status)
                for entry, f, status in _iter_degraded(cv_result)]
    except Exception as e:  # noqa: BLE001 -- 提取降级返回空列表
        _log_degraded("extract_degraded_findings", e)
        return []
def log_cv_extract_summary(report: dict) -> None:
    cv_stats = extract_cv_stats(report)
    if cv_stats.get("_error"):
        logger.warning("[Aggregator-v5] CV统计不可读（提取已降级），"
                       "跳过统计汇总")
        return
    degraded_findings = extract_degraded_findings(report)
    if degraded_findings:
        logger.info("[Aggregator-v5] 降级findings: %d 条（详情见治疗方案的降级来源项）",
                    len(degraded_findings))
    logger.info("[Aggregator-v5] CV统计: confirmed=%d, suppressed=%d, degraded=%d, "
                 "partial_degraded=%d, total_input=%d",
                 cv_stats.get("confirmed", 0),
                 cv_stats.get("suppressed", 0),
                 cv_stats.get("degraded", 0),
                 cv_stats.get("partial_degraded", 0),
                 cv_stats.get(FIELD_TOTAL_INPUT_FINDINGS, 0))
def _text(value) -> str:
    return str(value or "")
def _degraded_entry(entry: dict, f: dict, status: str) -> dict:
    raw_factor = f.get(SIGNAL_DEGRADE_FACTOR)
    factor = degrade_factor_of(f) if raw_factor is not None else None
    return {
        "locator": _text(entry.get("locator")),
        "rule_family": _text(f.get("rule_family") or f.get("rule_id")),
        "severity": _text(f.get("severity")),
        "degrade_status": status,
        "adj_confidence": conf_chain(f, *_REPORT_CONFIDENCE_FIELDS),
        "degrade_factor": factor,
        "source_method": _text(f.get("_source_method")),
        "degrade_reason": _text(
            f.get("_partial_reason") or f.get("_degraded_reason")
            or f.get("_degrade_reason")),
    }
def generate_cv_report(cv_result: dict) -> dict:
    try:
        report = _build_report_structure(_normalize_cv_failure(cv_result))
        report_md = _MarkdownRenderer(report).render()
        logger.info("[CV-Report] 结构化报告已生成（纯内存，report_md=%d 字符）",
                    len(report_md))
        return {
            "status": "ok",
            "data": {
                "report_md": report_md,
                "summary": report["executive_summary"],
            },
            "message": "结构化报告已生成（纯内存传递，无.md落盘）",
        }
    except Exception as e:
        log_swallowed(__name__, e, context='generate_cv_report:Exc')
        logger.exception("[CV-Report] 报告生成失败")
        return {"status": "error", "data": None, "message": str(e)}
def _assemble_executive_summary(cv_result: dict) -> dict:
    enumerated = _reconciled_conclusion_counts(cv_result)
    total = _input_total_with_lower_bound(
        _stat_count(cv_result.get(FIELD_TOTAL_INPUT_FINDINGS)), enumerated)
    confirmed = max(
        _stat_count(cv_result.get("confirmed")), enumerated["confirmed"])
    likely = max(_stat_count(cv_result.get("likely")), enumerated["likely"])
    uncertain = max(
        _stat_count(cv_result.get("uncertain")), enumerated["uncertain"])
    suppressed = max(
        _stat_count(cv_result.get("suppressed")), enumerated["suppressed"])
    contradictions = max(
        _stat_count(cv_result.get("contradictions")),
        enumerated["contradictions"])
    rules_triggered = _rules_applied_count(cv_result)
    participation = norm_dict(cv_result.get("participation"))
    participation_rate = as_number(participation.get("participation_rate"), 0)
    has_other_findings = (any((uncertain, suppressed, contradictions))
                          or any(enumerated.values()))
    health, health_desc = _summary_health(
        total, confirmed, likely, _cv_degraded_reason(cv_result), uncertain,
        has_other_findings=has_other_findings)
    health, health_desc = _apply_phase_health(
        health, health_desc, cv_result.get("phase_health"))
    return {
        "total_findings": total,
        "confirmed": confirmed,
        "likely": likely,
        "uncertain": uncertain,
        "suppressed": suppressed,
        "contradictions": contradictions,
        FIELD_RULES_TRIGGERED: rules_triggered,
        "participation_rate": participation_rate,
        "health": health,
        "health_description": health_desc,
        "generated_at": datetime.now().isoformat(),
    }
_DEGRADED_HEALTH: dict[str, tuple[str, str]] = {
    "insufficient_coverage": (
        "critical", "覆盖不足，CV 结论不完整（不代表代码库健康）"),
    "empty_degradation": (
        "degraded", "全部方法无 findings，空降级报告（不代表代码库健康）"),
}
_DEGRADED_HEALTH_FALLBACK = ("degraded", "CV 降级报告（不代表代码库健康）")
_NO_DEGRADED_REASON = ""
def _cv_degraded_reason(cv_result: dict) -> str:
    status = cv_result.get("status")
    normalized = status.strip().lower() if isinstance(status, str) else ""
    if normalized in _DEGRADED_HEALTH:
        return normalized
    if normalized == "degraded" or signal_bool(cv_result.get("_degraded")):
        return "degraded"
    return ""
def _health_tier(total: int, confirmed: int, likely: int,
                 degraded_reason: str = _NO_DEGRADED_REASON, *,
                 has_other_findings: bool) -> str:
    if degraded_reason:
        return _DEGRADED_HEALTH.get(
            degraded_reason, _DEGRADED_HEALTH_FALLBACK)[0]
    if confirmed > _CRITICAL_CONFIRMED_THRESHOLD:
        return "critical"
    if confirmed > 0:
        return "warning"
    if likely > 0:
        return "info"
    if total == 0 and not has_other_findings:
        return "clean"
    return "healthy"
def _summary_health(total: int, confirmed: int, likely: int,
                    degraded_reason: str = _NO_DEGRADED_REASON,
                    uncertain: int = 0, *,
                    has_other_findings: bool) -> tuple[str, str]:
    health = _health_tier(
        total, confirmed, likely, degraded_reason,
        has_other_findings=has_other_findings)
    return health, _executive_health_desc(
        health, confirmed, likely, uncertain, degraded_reason)
_PHASE_HEALTH_DESCRIPTIONS = {
    "critical": "Phase 1/2 关键模块失败，CV 结论不完整",
    "degraded": "Phase 1/2 部分降级，CV 结论可能不完整",
    "warning": "Phase 1/2 存在警告",
}
def _apply_phase_health(health: str, description: str,
                        phase_health: Any) -> tuple[str, str]:
    status = _phase_health_status(phase_health)
    if status not in _PHASE_HEALTH_DESCRIPTIONS:
        return health, description
    if status == "degraded" and health == "critical":
        return health, description
    if status == "warning" and health not in ("clean", "healthy", "info"):
        return health, description
    raw_summary = phase_health.get("summary")
    summary = raw_summary.strip() if isinstance(raw_summary, str) else ""
    return status, summary or _PHASE_HEALTH_DESCRIPTIONS[status]
_CONCLUSION_FALLBACK = "uncertain"
_EFFECTIVE_V2_CONCLUSIONS = frozenset({
    "confirmed", "likely", "uncertain", "suppressed",
})
def _raw_conclusion(f: dict) -> str:
    raw = f.get("conclusion")
    return raw if isinstance(raw, str) and raw else _CONCLUSION_FALLBACK
def _conclusion_bucket(f: dict, conclusion: str) -> str:
    if str(f.get("locator", "")).startswith("CONTRADICTION:"):
        return "contradiction"
    conclusion_v2 = f.get("conclusion_v2")
    if (isinstance(conclusion_v2, str)
            and conclusion_v2 in _EFFECTIVE_V2_CONCLUSIONS):
        conclusion = conclusion_v2
    if conclusion in ("confirmed", "suppressed"):
        return conclusion
    if conclusion == "likely":
        return "likely"
    return _CONCLUSION_FALLBACK
def _enumerated_conclusion_counts(cv_result: dict) -> dict[str, int]:
    counts = {"confirmed": 0, "likely": 0, "uncertain": 0,
              "suppressed": 0, "contradictions": 0}
    for finding in list_field(cv_result, "findings_index"):
        if not isinstance(finding, dict):
            continue
        bucket = _conclusion_bucket(finding, _raw_conclusion(finding))
        key = "contradictions" if bucket == "contradiction" else bucket
        counts[key] += 1
    return counts
def _reconciled_conclusion_counts(cv_result: dict) -> dict[str, int]:
    counts = _enumerated_conclusion_counts(cv_result)
    for bucket in _INPUT_CONCLUSION_BUCKETS:
        counts[bucket] = max(
            _stat_count(cv_result.get(bucket)), counts[bucket])
    counts["contradictions"] = max(
        _stat_count(cv_result.get("contradictions")),
        counts["contradictions"])
    return counts
def _assemble_findings_buckets(findings_index: list) -> dict:
    buckets: dict[str, list] = {
        "confirmed": [], "likely": [], "uncertain": [],
        "suppressed": [], "contradiction": [],
    }
    for f in findings_index:
        bucket = _conclusion_bucket(f, _raw_conclusion(f))
        buckets[bucket].append(_finding_entry(f, bucket))
    return buckets
def _finding_entry(f: dict, conclusion: str) -> dict:
    sources = coerce_text_list(f.get("sources"))
    return {
        "locator": str(f.get("locator") or ""),
        "rule": str(f.get("rule_applied") or ""),
        "conclusion": conclusion,
        "severity": _get_max_severity(f),
        "confidence": conf_chain(f, *_REPORT_CONFIDENCE_FIELDS),
        FIELD_EVIDENCE_STRENGTH: as_number(f.get(FIELD_EVIDENCE_STRENGTH), 0),
        "sources": sources,
        "source_count": max(_stat_count(f.get("source_count")), len(sources)),
        FIELD_EVIDENCE_FAMILIES: coerce_text_list(
            f.get(FIELD_EVIDENCE_FAMILIES)),
        "sample_message": _get_sample_message(f),
        "file": _extract_file(f),
        "line": _extract_line(f),
        "is_degraded": (_degrade_status_of(f) is not None or any(
            _degrade_status_of(inner) is not None
            for inner in _dict_list(f.get("findings")))),
        "annotation_adjustments": coerce_text_list(
            f.get("_annotation_adjustments")),
    }
def _assemble_arbitration_traces(findings_index: list) -> list:
    arbitration_traces = []
    for f in findings_index:
        adj = coerce_text_list(f.get("_annotation_adjustments"))
        if adj:
            arbitration_traces.append({
                "locator": str(f.get("locator") or ""),
                "rule": str(f.get("rule_applied") or ""),
                "conclusion": _conclusion_bucket(f, _raw_conclusion(f)),
                FIELD_BASE_CONFIDENCE: conf_chain(f, FIELD_BASE_CONFIDENCE),
                FIELD_ADJUSTED_CONFIDENCE: conf_chain(f, FIELD_ADJUSTED_CONFIDENCE),
                "adjustments": adj,
            })
    return arbitration_traces
def _build_report_structure(cv_result: dict) -> dict:
    exec_summary = _assemble_executive_summary(cv_result)
    findings_index = [f for f in list_field(cv_result, "findings_index")
                      if isinstance(f, dict)]
    buckets = _assemble_findings_buckets(findings_index)
    rules_detail = _dict_list(cv_result.get("rules_detail"))
    rule_analysis = _assemble_rule_analysis(rules_detail)
    rule_coverage = cv_result.get("rule_coverage") or {}
    coverage_analysis = _analyze_coverage_gaps(rule_coverage, rules_detail)
    phase_health = norm_dict(cv_result.get("phase_health", {}))
    phase_errors = _dict_list(cv_result.get("phase_errors", []))
    degradation = norm_dict(cv_result.get("degradation_impact", {}))
    fp_filter_log = _dict_list(cv_result.get("fp_filter_log", []))
    feedback = norm_dict(cv_result.get("feedback_adjustments", {}))
    p0p1_log = _dict_list(cv_result.get("p0p1_protection_log", []))
    function_summary = _dict_list(cv_result.get("function_level_summary", []))
    context_summary = norm_dict(cv_result.get("context_summary", {}))
    rule_execution_log = dict(norm_dict(
        cv_result.get("rule_execution_log", {})))
    if "rule_check_failures" in rule_execution_log:
        rule_execution_log["rule_check_failures"] = _dict_list(
            rule_execution_log["rule_check_failures"])
    return {
        "executive_summary": exec_summary,
        "confirmed_findings": buckets["confirmed"],
        "likely_findings": buckets["likely"],
        "uncertain_findings": buckets["uncertain"],
        "suppressed_findings": buckets["suppressed"],
        "contradiction_findings": buckets["contradiction"],
        "rule_analysis": rule_analysis,
        "coverage_analysis": coverage_analysis,
        "phase_health": phase_health,
        "phase_errors": phase_errors,
        "degradation_impact": degradation,
        "fp_filter_log": fp_filter_log,
        "feedback_adjustments": feedback,
        "p0p1_protection_log": p0p1_log,
        "function_level_summary": function_summary,
        "context_summary": context_summary,
        "rule_execution_log": rule_execution_log,
        "arbitration_traces": _assemble_arbitration_traces(findings_index)[:CONFIRMED_DISPLAY_LIMIT],
        "rule_execution_diagnostics": _assemble_rule_execution_diagnostics(
            rule_execution_log, cv_result),
    }
def _assemble_rule_analysis(rules_detail: list) -> dict:
    triggered = [r for r in rules_detail if signal_bool(r.get("triggered"))]
    return {
        "total_rules": len(rules_detail),
        "triggered": triggered,
        "never_triggered": [
            r for r in rules_detail if not signal_bool(r.get("triggered"))],
        "most_active": sorted(
            triggered,
            key=lambda r: safe_int(r.get("findings_count")),
            reverse=True,
        )[:5],
    }
def _assemble_rule_execution_diagnostics(rule_execution_log: dict,
                                         cv_result: dict) -> dict:
    return {
        "rule_check_failures": _dict_list(
            rule_execution_log.get("rule_check_failures")),
        "refinements_applied": safe_int(
            rule_execution_log.get("refinements_applied") or 0),
        "refinement_paths": coerce_text_list(
            rule_execution_log.get("refinement_paths")),
        "fp_tracker_calibration": norm_dict(
            cv_result.get("fp_tracker_calibration")),
    }
class _MarkdownRenderer:
    __slots__ = ("lines", "report")
    def __init__(self, report: dict):
        self.report = report
        self.lines: list[str] = []
    def executive_summary(self, es: dict) -> None:
        self.lines.append("## 执行摘要")
        self.lines.append("")
        self.lines.append("| 指标 | 值 |")
        self.lines.append("|------|-----|")
        self.lines.append(f"| 输入发现总数 | {es['total_findings']} |")
        self.lines.append(f"| 已确认 (confirmed) | **{es['confirmed']}** |")
        self.lines.append(f"| 较可信 (likely) | {es['likely']} |")
        self.lines.append(f"| 不确定 (uncertain) | {es['uncertain']} |")
        self.lines.append(f"| 已抑制 (suppressed) | {es['suppressed']} |")
        self.lines.append(f"| 矛盾 (contradictions) | {es['contradictions']} |")
        self.lines.append(f"| 触发规则数 | {es[FIELD_RULES_TRIGGERED]} |")
        self.lines.append(f"| 方法参与率 | {es['participation_rate']}% |")
        self.lines.append("")
    def confirmed_section(self, confirmed: list) -> None:
        if not confirmed:
            return
        self.lines.append("## 已确认问题 (confirmed)")
        self.lines.append("")
        for f in confirmed[:CONFIRMED_DISPLAY_LIMIT]:
            self.confirmed_item(f)
        if len(confirmed) > CONFIRMED_DISPLAY_LIMIT:
            self.lines.append(f"... 还有 {len(confirmed) - CONFIRMED_DISPLAY_LIMIT} 条确认问题未显示")
            self.lines.append("")
    def confirmed_item(self, f: dict) -> None:
        self.lines.append(f"### {f['file']}:{f['line']} — {f['severity']}")
        self.lines.append(f"- **规则**: {f['rule']}")
        self.lines.append(f"- **置信度**: {as_number(f['confidence']):.2f} | **证据强度**: {as_number(f[FIELD_EVIDENCE_STRENGTH]):.2f}")
        self.lines.append(f"- **来源**: {self.join_csv(f.get('sources'))} ({f.get('source_count', 0)}源)")
        if f.get(FIELD_EVIDENCE_FAMILIES):
            self.lines.append(f"- **证据家族**: {self.join_csv(f.get(FIELD_EVIDENCE_FAMILIES))}")
        if f['sample_message']:
            self.lines.append(f"- **描述**: {f['sample_message']}")
        if f['is_degraded']:
            self.lines.append("- **注意**: 此发现来自降级方法")
        if f.get('annotation_adjustments'):
            self.lines.append(f"- **注解调整**: {self.join_csv(f.get('annotation_adjustments'))}")
        self.lines.append("")
    @staticmethod
    def join_csv(values) -> str:
        if isinstance(values, str):
            return values
        return ", ".join(str(x) for x in (values or []))
    def rule_analysis_section(self, ra: dict, ca: dict) -> None:
        self.lines.append("## 规则执行分析")
        self.lines.append("")
        self.lines.append(f"- 总规则数: {ra.get('total_rules', 0)}")
        self.lines.append(f"- 已触发: {len(ra.get('triggered', []))}")
        self.lines.append(f"- 未触发: {len(ra.get('never_triggered', []))}")
        self.lines.append("")
        if ra.get("most_active"):
            self.lines.append("### 最活跃规则")
            self.lines.append("")
            self.lines.append("| 规则 | 描述 | 发现数 | 确认 | 抑制 |")
            self.lines.append("|------|------|--------|------|------|")
            for r in ra["most_active"]:
                self.lines.append(f"| {r.get('rule_id', '')} | {str(r.get('description', ''))[:40]} | {safe_int(r.get('findings_count') or 0)} | {safe_int(r.get('confirmed') or 0)} | {safe_int(r.get('suppressed') or 0)} |")
            self.lines.append("")
        if ca.get("gaps"):
            self.lines.append("## 覆盖度分析")
            self.lines.append("")
            self.lines.append(f"触发率: {as_number(ca.get('trigger_rate')):.1%}")
            self.lines.append("")
            self.lines.append("### 未触发规则及可能原因")
            self.lines.append("")
            for gap in ca["gaps"]:
                self.lines.append(f"- **{gap['rule_id']}**: {gap['reason']}")
            self.lines.append("")
    def rule_diag_section(self, report: dict) -> None:
        rule_log = report.get("rule_execution_log", {})
        self.rule_exec_diag_table(rule_log)
        arb_traces = report.get("arbitration_traces", [])
        self.arbitration_trace_block(arb_traces)
        diag = report.get("rule_execution_diagnostics", {})
        fp_cal = norm_dict(diag.get("fp_tracker_calibration"))
        self.fp_calibration_block(fp_cal)
    @staticmethod
    def rule_log_count(rule_log: dict, key: str) -> int:
        return safe_int(rule_log.get(key))
    def rule_exec_diag_table(self, rule_log: dict) -> None:
        if not rule_log:
            return
        self.lines.append("## 规则执行诊断")
        self.lines.append("")
        self.lines.append("| 指标 | 值 |")
        self.lines.append("|------|-----|")
        for label, key in _RULE_EXEC_DIAG_METRICS:
            self.lines.append(f"| {label} | {self.rule_log_count(rule_log, key)} |")
        refinements = self.rule_log_count(rule_log, 'refinements_applied')
        if refinements:
            self.lines.append(f"| 精炼应用 | {refinements} |")
        failures = rule_log.get('rule_check_failures') or []
        if isinstance(failures, list) and failures:
            self.lines.append(f"| 规则检查异常 | {len(failures)} |")
        self.lines.append("")
    def arbitration_trace_block(self, arb_traces: list) -> None:
        if not arb_traces:
            return
        self.lines.append(
            f"## 仲裁追踪 (Top {CONFIRMED_DISPLAY_LIMIT})")
        self.lines.append("")
        for trace in arb_traces[:CONFIRMED_DISPLAY_LIMIT]:
            self.lines.append(f"### {trace['locator']}")
            self.lines.append(f"- **规则**: {trace['rule']} | **结论**: {trace['conclusion']}")
            self.lines.append(f"- **置信度**: {as_number(trace[FIELD_BASE_CONFIDENCE]):.2f} -> {as_number(trace[FIELD_ADJUSTED_CONFIDENCE]):.2f}")
            if trace.get('adjustments'):
                for adj in trace['adjustments']:
                    self.lines.append(f"  - {adj}")
            self.lines.append("")
    def fp_calibration_block(self, fp_cal: dict) -> None:
        if not fp_cal:
            return
        self.lines.append("## FP 追踪器校准")
        self.lines.append("")
        self.lines.append(f"- 更新规则族数: {safe_int(fp_cal.get('updated_families') or 0)}")
        self.lines.append(f"- 总更新次数: {safe_int(fp_cal.get('total_updates') or 0)}")
        self.lines.append("")
    def compact_findings_section(self, title: str, label: str,
                                 findings: list) -> None:
        if not findings:
            return
        self.lines.append(f"## {title}")
        self.lines.append("")
        for f in findings[:_LIKELY_DISPLAY_LIMIT]:
            self.lines.append(f"- `{f['file']}:{f['line']}` [{f['severity']}] {f['sample_message'] or f['rule']} (conf={as_number(f['confidence']):.2f})")
        if len(findings) > _LIKELY_DISPLAY_LIMIT:
            self.lines.append(
                f"... 还有 {len(findings) - _LIKELY_DISPLAY_LIMIT} 条{label}")
        self.lines.append("")
    def contradiction_section(self, contradictions: list) -> None:
        if not contradictions:
            return
        self.lines.append("## 矛盾分析")
        self.lines.append("")
        for c in contradictions:
            self.lines.append(f"- **{c['locator']}** — {c['sample_message'] or '矛盾'}")
            self.lines.append(f"  - 结论: {c['conclusion']} | 置信度: {as_number(c['confidence']):.2f}")
            self.lines.append(f"  - 证据家族: {self.join_csv(c.get(FIELD_EVIDENCE_FAMILIES))}")
        self.lines.append("")
    def context_summary_section(self, ctx_sum: dict) -> None:
        if not ctx_sum:
            return
        self.lines.append("## 上下文覆盖摘要 (D1)")
        self.lines.append("")
        call_graph_available = signal_bool(
            ctx_sum.get("call_graph_available"))
        self.lines.append(
            f"- 调用图可用: {'是' if call_graph_available else '否'}")
        self.lines.append(f"- 孤儿函数数: {safe_int(ctx_sum.get('orphan_count') or 0)}")
        self.lines.append(f"- 盲点数: {safe_int(ctx_sum.get('blindspot_count') or 0)}")
        self.lines.append(f"- 未覆盖文件数: {safe_int(ctx_sum.get('uncovered_file_count') or 0)}")
        self.lines.append(f"- 高复杂度函数数: {safe_int(ctx_sum.get('high_complexity_count') or 0)}")
        self.lines.append("")
    def phase_health_section(self, report: dict) -> None:
        ph = report["phase_health"]
        if not ph:
            return
        self.lines.append("## Phase 1/2 健康状态")
        self.lines.append("")
        self.lines.append(f"- 整体状态: **{ph.get('overall_status') or 'unknown'!s}**")
        self.lines.append(f"- 摘要: {ph.get('summary') or ''!s}")
        if report["phase_errors"]:
            self.lines.append(f"- 错误数: {len(report['phase_errors'])}")
        self.lines.append("")
    def fp_filter_section(self, fp_log: list) -> None:
        if not fp_log:
            return
        self.lines.append("## 误报过滤日志")
        self.lines.append("")
        self.lines.append(f"共过滤 {len(fp_log)} 条发现:")
        self.lines.append("")
        reason_counts = {}
        for entry in fp_log:
            reason = str(entry.get("reason") or "unknown")
            reason_counts[reason] = reason_counts.get(reason, 0) + 1
        self.lines.append("| 过滤原因 | 数量 |")
        self.lines.append("|----------|------|")
        for reason, count in sorted(reason_counts.items(), key=lambda x: -x[1]):
            self.lines.append(f"| {reason} | {count} |")
        self.lines.append("")
    def p0p1_protection_section(self, p0p1: list) -> None:
        if not p0p1:
            return
        self.lines.append("## P0/P1 误报保护")
        self.lines.append("")
        self.lines.append(f"共 {len(p0p1)} 条 P0/P1 发现被标记保护:")
        for entry in p0p1[:_P0P1_DISPLAY_LIMIT]:
            self.lines.append(f"- `{entry.get('locator') or ''!s}` [{entry.get('severity') or ''!s}] — {', '.join(coerce_text_list(entry.get('reasons')))}")
        if len(p0p1) > _P0P1_DISPLAY_LIMIT:
            self.lines.append(f"... 还有 {len(p0p1) - _P0P1_DISPLAY_LIMIT} 条")
        self.lines.append("")
    @staticmethod
    def threshold_display(value) -> str:
        return "N/A" if value is None or value == "" else str(value)
    def feedback_section(self, feedback: dict) -> None:
        if not feedback:
            return
        self.lines.append("## 自适应学习状态")
        self.lines.append("")
        et = norm_dict(feedback.get("effective_thresholds"))
        self.lines.append(f"- 确认阈值: {self.threshold_display(et.get('auto_confirm'))}")
        self.lines.append(f"- 强度阈值: {self.threshold_display(et.get('auto_strength'))}")
        self.lines.append(f"- 最小调整: {self.threshold_display(et.get('auto_min_adjusted'))}")
        mc = norm_dict(feedback.get(FIELD_METHOD_CONFIDENCE_MULTIPLIERS))
        if mc:
            self.lines.append(f"- 方法置信度乘数: {len(mc)} 个已加载")
        self.lines.append("")
    def degradation_section(self, deg: dict) -> None:
        if not deg:
            return
        self.lines.append("## 降级影响分析")
        self.lines.append("")
        for k, v in deg.items():
            if isinstance(v, (int, float, str)):
                self.lines.append(f"- {k}: {v}")
        self.lines.append("")
    def function_summary_section(self, func_summary: list) -> None:
        if not func_summary:
            return
        self.lines.append(f"## 文件级聚合摘要 (Top {_FUNCTION_SUMMARY_LIMIT})")
        self.lines.append("")
        self.lines.append("| 文件 | 发现数 | 最高严重度 | 主导结论 | 平均置信度 |")
        self.lines.append("|------|--------|-----------|---------|-----------|")
        for fs in func_summary[:_FUNCTION_SUMMARY_LIMIT]:
            self.lines.append(f"| {fs.get('file') or ''!s} | {safe_int(fs.get('total_findings') or 0)} | {fs.get('max_severity') or ''!s} | {fs.get('dominant_conclusion') or ''!s} | {as_number(fs.get('avg_confidence')):.2f} |")
        self.lines.append("")
    def render(self) -> str:
        report = self.report
        es = report["executive_summary"]
        self.lines.append("# 交叉验证报告")
        self.lines.append("")
        self.lines.append(f"**生成时间**: {es['generated_at']}")
        self.lines.append(f"**健康状态**: {es['health'].upper()} — {es['health_description']}")
        self.lines.append("")
        self.executive_summary(es)
        self.confirmed_section(report.get("confirmed_findings"))
        self.compact_findings_section(
            "可能问题 (likely)", "可能问题", report["likely_findings"])
        self.compact_findings_section(
            "不确定问题 (uncertain)", "不确定问题",
            report["uncertain_findings"])
        self.compact_findings_section(
            "已抑制问题 (suppressed)", "已抑制问题",
            report["suppressed_findings"])
        self.contradiction_section(report["contradiction_findings"])
        self.rule_analysis_section(report.get("rule_analysis", {}), report.get("coverage_analysis", {}))
        self.context_summary_section(report.get("context_summary") or {})
        self.phase_health_section(report)
        self.fp_filter_section(report["fp_filter_log"])
        self.p0p1_protection_section(report["p0p1_protection_log"])
        self.feedback_section(report["feedback_adjustments"])
        self.degradation_section(report["degradation_impact"])
        self.function_summary_section(report["function_level_summary"])
        self.rule_diag_section(report)
        self.lines.append("---")
        self.lines.append("*本报告由交叉验证引擎自动生成*")
        return "\n".join(self.lines)
def _analyze_coverage_gaps(rule_coverage: dict, rules_detail: list) -> dict:
    if not isinstance(rule_coverage, dict):
        rule_coverage = {}
    gaps = []
    never_triggered = [
        rid for rid in list_field(rule_coverage, "rules_never_triggered")
        if isinstance(rid, str) and rid
    ]
    rules_map = {r.get("rule_id"): r for r in rules_detail
                 if isinstance(r, dict) and isinstance(r.get("rule_id"), str)}
    for rid in never_triggered:
        gaps.append(_coverage_gap_entry(rid, rules_map))
    total_rules = safe_int(rule_coverage.get("total_rules_defined") or 0)
    triggered_count = len(list_field(rule_coverage, FIELD_RULES_TRIGGERED))
    if (not isinstance(rule_coverage.get(FIELD_RULES_TRIGGERED), list)
            and total_rules):
        triggered_count = max(0, total_rules - len(never_triggered))
    trigger_rate = safe_float(rule_coverage.get("trigger_rate"), None)
    if trigger_rate is None:
        trigger_rate = triggered_count / total_rules if total_rules else 0.0
    return {
        "trigger_rate": trigger_rate,
        "total_rules": total_rules,
        "triggered_count": triggered_count,
        "never_triggered_count": len(never_triggered),
        "gaps": gaps,
    }
def _coverage_gap_entry(rid: str, rules_map: dict) -> dict:
    rule = rules_map.get(rid) or {}
    _desc_obj = CV_RULES.get(rid)
    source_methods = list(getattr(_desc_obj, "source_methods", ()) or ())
    return {
        "rule_id": rid,
        "description": str(rule.get("description") or "")[:60],
        "reason": _coverage_gap_reason(source_methods),
    }
_COVERAGE_GAP_REASON_SPECS = (
    (("E", "T"), "依赖测试方法 {methods}，测试可能未执行或无失败"),
    (("D",), "依赖诊断方法 {methods}，方法可能未产出相关发现"),
    (("A",), "依赖分析方法 {methods}，分析可能未检测到相关问题"),
)
def _coverage_gap_reason(source_methods: list) -> str:
    methods = [m for m in source_methods if isinstance(m, str) and m]
    if not methods:
        return "无关联诊断方法，规则可能依赖动态发现（如测试失败）"
    for prefixes, template in _COVERAGE_GAP_REASON_SPECS:
        if any(method.startswith(prefixes) for method in methods):
            return template.format(methods=methods)
    return f"关联方法 {methods} 未产出匹配发现"
def _get_max_severity(finding: dict) -> str:
    sev = finding.get("severity", "")
    if isinstance(sev, str) and sev:
        return sev
    inner = list_field(finding, "findings")
    if inner:
        return get_max_severity(inner)
    return "P3"
def _get_sample_message(finding: dict) -> str:
    carriers = [finding.get("sample_finding"), finding]
    carriers.extend(_dict_list(finding.get("findings")))
    for carrier in carriers:
        if not isinstance(carrier, dict):
            continue
        msg = carrier.get("message") or carrier.get("sample_message") or ""
        if msg:
            return str(msg)[:MESSAGE_TRUNCATE_LEN]
    return ""
def _locator_candidate(locator: str) -> str:
    if locator.startswith("CONTRADICTION:"):
        return ""
    return parse_locator_file(locator) or ""
def _first_text(value) -> str:
    if isinstance(value, (list, tuple)):
        value = value[0] if value else ""
    return value if isinstance(value, str) else ""
def _sample_file_candidate(finding: dict) -> str:
    sample = finding.get("sample_finding", {})
    sample_file = sample.get("file") if isinstance(sample, dict) else None
    return _first_text(sample_file)
def _file_candidates(finding: dict) -> list[str]:
    candidates = [
        _first_text(finding.get("file", "")),
        _locator_candidate(str(finding.get("locator") or "")),
        _sample_file_candidate(finding),
    ]
    return [candidate for candidate in candidates if candidate]
def _extract_file(finding: dict) -> str:
    for candidate in _file_candidates(finding):
        label = os.path.basename(candidate.replace("\\", "/"))
        if label:
            return label
    return "unknown"
def _extract_line(finding: dict) -> int:
    sample = finding.get("sample_finding", {})
    sample_line = sample.get("line") if isinstance(sample, dict) else None
    locator = str(finding.get("locator") or "")
    locator_line = (
        0 if locator.startswith("CONTRADICTION:")
        else parse_locator_line(locator))
    for candidate in (finding.get("line"), locator_line, sample_line):
        if candidate is None or candidate == "":
            continue
        line = coerce_line(candidate)
        if line > 0:
            return line
    return 0
def _executive_health_desc(health: str, confirmed: int, likely: int,
                           uncertain: int, degraded_reason: str) -> str:
    if degraded_reason:
        return _DEGRADED_HEALTH.get(
            degraded_reason, _DEGRADED_HEALTH_FALLBACK)[1]
    if health == "critical":
        return f"{confirmed} 个确认问题需优先处理"
    if health == "warning":
        return f"{confirmed} 个确认问题需处理，{likely} 个可能问题待调查"
    if health == "info":
        return f"{likely} 个可能问题待调查"
    if health == "clean":
        return "无发现，代码库状态良好"
    return f"无确认问题，{uncertain} 条待调查"
def build_executive_summary(total: int, confirmed: int, likely: int,
                            uncertain: int, suppressed: int,
                            contradictions: int, findings_count: int,
                            *, degraded_reason: str = _NO_DEGRADED_REASON,
                            phase_health: dict | None = None) -> dict:
    total = _stat_count(total)
    confirmed = _stat_count(confirmed)
    likely = _stat_count(likely)
    uncertain = _stat_count(uncertain)
    suppressed = _stat_count(suppressed)
    contradictions = _stat_count(contradictions)
    findings_count = _stat_count(findings_count)
    total = _input_total_with_lower_bound(total, {
        "confirmed": confirmed, "likely": likely, "uncertain": uncertain,
        "suppressed": suppressed,
    })
    health, desc = _summary_health(
        total, confirmed, likely, degraded_reason, uncertain,
        has_other_findings=any(
            (uncertain, suppressed, contradictions, findings_count)))
    health, desc = _apply_phase_health(health, desc, phase_health)
    return {
        "health": health,
        "description": desc,
        "total_findings": total,
        "confirmed": confirmed,
        "likely": likely,
        "uncertain": uncertain,
        "suppressed": suppressed,
        "contradictions": contradictions,
        "findings_validated": findings_count,
    }
def _callgraph_summary_from_cache(cache, skill_dir: str) -> dict | None:
    try:
        health = cache.slots.get_call_graph_health()
        if health != cache.slots.CALL_GRAPH_MISSING:
            summary = cache.slots.get_call_graph_summary()
        else:
            summary = ensure_call_graph(skill_dir, cache)
            health = cache.slots.get_call_graph_health()
        if (isinstance(summary, dict) and summary
                and health != cache.slots.CALL_GRAPH_MISSING):
            return summary
        logger.warning(
            "[F1] SharedCache 调用图不可用(health=%s)，回退中间文件", health)
    except Exception as e:  # noqa: BLE001
        logger.warning("[F1] SharedCache 调用图读取失败，回退中间文件: %s", e)
    return None
def _f1_report_from_callgraph(cg: dict) -> dict:
    return {
        "call_chain": {
            "orphans": safe_int(cg.get("orphans") or 0),
            "break_points": safe_int(cg.get("break_points") or 0),
            "syntax_errors": safe_int(cg.get("syntax_errors") or 0),
        },
        "blindspots": {"total": safe_int(cg.get("blindspots") or 0)},
    }
def build_f1_report(intermediate_dir: str, skill_dir: str, cache=None) -> dict:
    if cache is not None and hasattr(cache, "slots"):
        cg = _callgraph_summary_from_cache(cache, skill_dir)
        if isinstance(cg, dict):
            return _f1_report_from_callgraph(cg)
    return _f1_report_from_intermediate(intermediate_dir, skill_dir)
def _f1_report_from_intermediate(intermediate_dir: str, skill_dir: str) -> dict:
    try:
        _round_ts = get_round_start_ts(skill_dir)
        d1 = load_intermediate_fused(intermediate_dir, "D1",
                                     strict_provenance=False,
                                     freshness_cutoff=_round_ts)
        if (not isinstance(d1, dict)
                or normalize_method_status(d1.get("status")) == "corrupted"):
            return {}
        payload = sub_engine_payload(d1, "D1")
        cg = payload.get("callgraph") if isinstance(payload, dict) else None
        if not isinstance(cg, dict):
            return {}
        return _f1_report_from_callgraph(cg)
    except Exception as e:  # noqa: BLE001
        logger.warning("[F1] report 组装失败（不影响执行）: %s", e)
        return {}
def attach_cv_report_summary(cv_report: dict, result: dict) -> None:
    try:
        report_result = generate_cv_report(cv_report)
        if report_result.get("status") == "ok":
            result["report_summary"] = report_result["data"]["summary"]
            logger.info("[Stage2b] 结构化报告已生成（纯内存，无.md落盘）")
    except Exception as e:  # noqa: BLE001 -- 结构化报告生成失败跳过
        logger.warning("[Stage2b] 结构化报告生成跳过: %s", e)

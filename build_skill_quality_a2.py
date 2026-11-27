from __future__ import annotations

import logging
import math
import os
import re
import time
from collections import Counter
from collections.abc import Callable
from itertools import pairwise
from pathlib import Path
from typing import Any, NamedTuple

from jwsgj.build_pipeline_checks import diag_skill_security
from jwsgj.build_skill_discovery import (
    analyze_skill_discoverability,
    resolve_analyze_input,
    run_c2_doc_quality_engine,
)
from jwsgj.build_skill_health import (
    DESC_CRITICAL,
    DESC_WARN,
    UNUSED_DAYS_THRESHOLD,
    _newest_skill_mtime,
    diag_todos,
    find_token_budget,
    matching_duplicate_groups,
    matching_unused_skill,
    normalize_skill_path,
    resolve_skill_attribution,
    run_five_dimension_health,
    skill_md_desc_line,
)
from jwsgj.build_skill_lifecycle import (
    ZOMBIE_THRESHOLDS,
    detect_zombie_status,
    quick_health_check,
)
from jwsgj.build_skill_lifecycle import (
    skill_md_path as _skill_md_path,
)
from jwsgj.diag_detector_findings import (
    _locator_str,
    _sub_locator,
    consolidate_findings,
    detector_entry,
    group_envelope,
    is_retired_rule,
    verdict_from_severity_counts,
    worst_sub_status,
)
from jwsgj.diag_health_scoring import structural_health_component
from jwsgj.diag_types_defs import make_a2_finding
from jwsgj.diag_types_normalize import (
    as_sequence,
    dict_or_empty,
    int_or,
)
from jwsgj.diag_types_vocab import LINE_LIMIT, SEVERITY_RANK
from jwsgj.engine_a1_defects import (
    A1_METHOD_ID,
    FileAnalyzerScanner,
    collect_py_files,
    enhance_defects,
    enhance_single_file_defects,
)
from jwsgj.engine_a1_structure import (
    DomainCategory,
    FileDefect,
    FileOverallProfile,
    FileVerdict,
    VerdictLevel,
    a1_to_dict,
    behavioral_classes,
    ensure_domains,
    module_stem,
)
from jwsgj.engine_a3_silent_degrade import run_a3_silent_degrade
from jwsgj.runtime_scope import is_test_file_path, normalize_skill_dir
from jwsgj.shared_cache import (
    as_diag_ctx,
    ensure_entry_warmed,
    fingerprint_freeze_window,
    require_warmed,
)
from jwsgj.skill_audit_rules import (
    DOC_ROLE_NONE,
    DOC_ROLE_SKILL,
    TARGET_KIND_PROJECT,
    TARGET_KIND_SKILL,
    resolve_target_document,
)

__all__ = [
    'DEFAULT_THRESHOLDS',
    'VerdictEngine',
    'normalize_defect_severity',
    'render_verdict',
    'render_verdicts_batch',
    'run_a1_file_analyzer',
    'run_a2_health_assessment',
    'run_engine_a',
]
_log = logging.getLogger(__name__)
_DISCOVER_REC_SCORE_FLOOR = 60.0
def _discoverability_score(value: Any) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return 0.0
    try:
        if not math.isfinite(value):
            return 0.0
    except OverflowError:  # jwsgj:silent-ok
        return 0.0
    return round(min(100.0, max(0.0, float(value))), 1)
def a2_discoverability_component(skill_dir: str, findings: list,
                                 payload_parts: dict) -> None:
    resolved_dir, name, description, keywords = resolve_analyze_input(
        skill_dir, "", [])
    disc_result = analyze_skill_discoverability(
        name, description, keywords,
        skill_dir=resolved_dir, record_activation=False)
    if not isinstance(disc_result, dict):
        payload_parts["discoverability"] = {
            "error": f"可发现性分析返回非 dict: {type(disc_result).__name__}"}
        return
    disc_score = _discoverability_score(disc_result.get("overall_score", 0))
    disc_recommendations = as_sequence(disc_result.get("recommendations"))
    if disc_score < _DISCOVER_REC_SCORE_FLOOR:
        findings.append(make_a2_finding(
            "DISCOVER-LOW-SCORE", "P2", str(skill_dir), 0,
            f"可发现性触发评分偏低: {disc_score:.1f}/100"))
    _recs = [str(r) for r in disc_recommendations[:5]]
    if _recs and disc_score < _DISCOVER_REC_SCORE_FLOOR:
        findings.append(make_a2_finding(
            "DISCOVER-REC", "P3", str(skill_dir), 0,
            f"可发现性改进建议({len(_recs)}条): " + "; ".join(_recs),
            detail={"recommendations": _recs}))
    payload_parts["discoverability"] = {
        "overall_score": disc_score,
        "trigger_score": disc_result.get("trigger_score", 0),
        "keyword_count": disc_result.get("keyword_count", 0),
        "recommendations_count": len(disc_recommendations),
        "recommendations": _recs,
    }
def _token_over_message(b, is_critical: bool) -> str:
    over = (f"{DESC_CRITICAL} 双倍硬上限（DESC_WARN={DESC_WARN}）"
            if is_critical else f"{DESC_WARN} 硬上限")
    return (f"Token超预算: description {b.description_chars} 字符超 " + over
            + f"（全 SKILL.md 估计 {b.estimated_tokens} tokens）")
def _emit_token_over(skill_dir: str, findings: list, over_budget: list) -> int:
    if not over_budget:
        return 0
    _desc_line = skill_md_desc_line(skill_dir)
    emitted = 0
    for b in over_budget:
        _is_critical = b.status == "critical"
        findings.append(make_a2_finding(
            "TOKEN-OVER", "P1" if _is_critical else "P2",
            str(_skill_md_path(skill_dir)), _desc_line,
            _token_over_message(b, _is_critical)))
        emitted += 1
    return emitted
def _duplicate_group_descriptor(group: Any) -> dict[str, Any]:
    skills = [str(name) for name in as_sequence(getattr(group, "skills", ()))]
    return {
        "skills": skills,
        "similarity": round(float(getattr(group, "similarity", 0.0) or 0.0), 3),
        "reason": str(getattr(group, "reason", "")),
    }
def _emit_dup_groups(skill_dir: str, findings: list, dup_groups: list) -> None:
    if not dup_groups:
        return
    groups = [_duplicate_group_descriptor(g) for g in dup_groups]
    findings.append(make_a2_finding(
        "SKILL-DUP", "P1", str(skill_dir), 0,
        f"重复技能({len(groups)}组): " + "; ".join(
            f"{'|'.join(g['skills'])} 相似度 {g['similarity']:.2f}"
            f"（{g['reason']}）"
            for g in groups),
        detail={"groups": groups}))
def _emit_unused_skills(skill_dir: str, findings: list, unused: list) -> None:
    if not unused:
        return
    names = "，".join(dict.fromkeys(str(n) for n in unused))
    findings.append(make_a2_finding(
        "SKILL-UNUSED", "P2", str(_skill_md_path(skill_dir)), 0,
        f"技能疑似闲置: SKILL.md 超{UNUSED_DAYS_THRESHOLD:g}天未更新（{names}），"
        "建议确认维护状态（判定基于文件 mtime，非调用统计）"))
def _over_budget_for_target(skill_dir: str, skills_root: str) -> list:
    budget = find_token_budget(skills_root, skill_dir)
    return [budget] if budget is not None and budget.status != "ok" else []
def a2_quality_component(skill_dir: str, findings: list,
                         payload_parts: dict) -> None:
    skills_root = _skill_collection_root(skill_dir)
    if skills_root is None:
        payload_parts["quality"] = {
            "error": "技能目录为空，无法派生集合根（Token 预算/重复/闲置不可判定）"}
        return
    doc = resolve_target_document(skill_dir)
    if doc.kind != TARGET_KIND_SKILL:
        payload_parts["quality"] = {
            "not_applicable": "技能集合级扫描（Token 表/技能去重/技能闲置）仅适用于技能目录",
            "target_kind": doc.kind,
            "doc_role": doc.doc_role,
        }
        return
    over_budget = _over_budget_for_target(skill_dir, skills_root)
    _emit_token_over(skill_dir, findings, over_budget)
    attribution = resolve_skill_attribution(skills_root, skill_dir)
    dup_groups: list = []
    unused: list[str] = []
    if attribution.attributable:
        dup_groups = matching_duplicate_groups(skills_root, skill_dir)
        _emit_dup_groups(skill_dir, findings, dup_groups)
        _unused_name = matching_unused_skill(skills_root, skill_dir)
        unused = [_unused_name] if _unused_name is not None else []
        _emit_unused_skills(skill_dir, findings, unused)
    quality_payload: dict[str, Any] = {
        "over_budget": len(over_budget),
        "duplicate_groups": len(dup_groups),
        "unused_skills": unused,
    }
    if not attribution.attributable:
        quality_payload["skipped_reason"] = attribution.reason
    payload_parts["quality"] = quality_payload
def _skill_collection_root(skill_dir: Any) -> str | None:
    text = str(skill_dir or "").strip()
    if not text:
        return None
    return str(Path(text).resolve().parent)
def _lifecycle_findings(life_result: dict) -> list[dict]:
    raw = as_sequence(life_result.get("findings"))
    kept = [f for f in raw if isinstance(f, dict)]
    if len(kept) != len(raw):
        _log.warning("[A2] 生命周期发现条目非 dict 已丢弃: %d 条",
                     len(raw) - len(kept))
    return kept
def _lifecycle_missing_finding(skill_md_path: Path | None) -> dict | None:
    if skill_md_path is None:
        return None
    return make_a2_finding(
        "SKILL-MD-MISSING", "P1", str(skill_md_path), 0,
        "SKILL.md 缺失: 技能无法被上传注册或被 Agent 发现"
        "（可发现性/质量/僵尸检测均无有效输入），建议补建")
def _lifecycle_zombie_finding(skill_md_path: Path, zombie: str,
                              label: str = "SKILL.md",
                              rule_prefix: str = "SKILL") -> dict | None:
    if zombie == "dormant":
        return make_a2_finding(
            f"{rule_prefix}-DORMANT", "P3", str(skill_md_path), 0,
            f"目标休眠: {label} 超过"
            f"{ZOMBIE_THRESHOLDS['dormant_days']}天未更新"
            f"（状态={zombie}），建议确认是否仍在维护")
    if zombie not in ("zombie", "sunset"):
        return None
    threshold = (ZOMBIE_THRESHOLDS["sunset_days"]
                 if zombie == "sunset" else ZOMBIE_THRESHOLDS["zombie_days"])
    return make_a2_finding(
        f"{rule_prefix}-ZOMBIE", "P2", str(skill_md_path), 0,
        f"目标严重闲置: {label} 超过{threshold}天未更新"
        f"（状态={zombie}），建议评估归档或淘汰")
def a2_lifecycle_component(skill_dir: str, findings: list,
                           payload_parts: dict) -> None:
    life_result = quick_health_check(skill_dir)
    lifecycle_payload: dict = {}
    if isinstance(life_result, dict):
        life_findings = _lifecycle_findings(life_result)
        findings.extend(life_findings)
        lifecycle_payload["findings_count"] = len(life_findings)
    else:
        lifecycle_payload["error"] = (
            f"生命周期检查返回非 dict: {type(life_result).__name__}")
    doc = resolve_target_document(skill_dir) if skill_dir else None
    skill_md_path = _skill_md_path(skill_dir) if skill_dir else None
    if doc is None or doc.doc_role == DOC_ROLE_NONE:
        zombie = "no_document" if (doc is not None and doc.kind == TARGET_KIND_PROJECT
                                   ) else "no_skill_md"
        if doc is not None and doc.kind == TARGET_KIND_PROJECT:
            _finding = make_a2_finding(
                "TARGET-DOC-MISSING", "P3", str(skill_dir), 0,
                "目标缺少 SKILL.md/README/pyproject 等描述载体："
                "无法判定用途与维护状态，建议补建 README 或项目清单")
        else:
            _finding = _lifecycle_missing_finding(skill_md_path)
    else:
        evidence = doc.path if doc.path is not None else skill_md_path
        activity_mtime, activity_source = _newest_skill_mtime(
            Path(skill_dir), evidence)
        lifecycle_payload["activity_evidence"] = activity_source
        if activity_mtime is None:
            zombie = "unknown"
            rule_prefix = "SKILL" if doc.doc_role == DOC_ROLE_SKILL else "TARGET"
            _finding = make_a2_finding(
                f"{rule_prefix}-MTIME-DEGRADED", "P3",
                str(evidence or skill_dir), 0,
                "目标维护状态证据不可用：项目文档与源码修改时间均不可读，"
                "不按 sunset 处置，建议恢复时间证据后复跑")
        else:
            zombie = detect_zombie_status(
                {"last_modified": activity_mtime.timestamp()}, evidence)
            if doc.doc_role == DOC_ROLE_SKILL:
                _finding = _lifecycle_zombie_finding(evidence, zombie)
            else:
                _finding = _lifecycle_zombie_finding(
                    evidence, zombie, label=evidence.name,
                    rule_prefix="TARGET")
    if _finding is not None:
        findings.append(_finding)
    lifecycle_payload["zombie_status"] = zombie
    payload_parts["lifecycle"] = lifecycle_payload
_RULE_ID_TAIL_RE = re.compile(
    r"([A-Z]{1,6}-[A-Z0-9]{1,6}(?:-[A-Z0-9]{1,6})*|[A-Z]{1,2}\d{1,4}"
    r"|[a-z][a-z0-9]*_(?=[a-z0-9])(?:[a-z0-9]|_(?=[a-z0-9]))*)$")
_DEFAULT_SECURITY_RULE_ID = "SKILL-SECURITY"
def _std_rule_id_from_category(category: object) -> str:
    text = "" if category is None else str(category).strip()
    if not text:
        return _DEFAULT_SECURITY_RULE_ID
    m = _RULE_ID_TAIL_RE.search(text)
    return m.group(1) if m else text
def _norm_severity_p(iss) -> str:
    _sev_raw = getattr(iss, "severity", None)
    sev_name = str(getattr(_sev_raw, "name", _sev_raw) or "LOW").upper()
    return normalize_defect_severity(sev_name)
def _parse_loc(loc: object) -> tuple[str, int]:
    text = loc if isinstance(loc, str) else ""
    _head, _sep, _tail = text.rpartition(":")
    if _sep and _tail.isdecimal():
        return _head, int(_tail)
    return text, 0
def _sec_issue_finding(iss) -> dict:
    _category_raw = getattr(iss, "category", _DEFAULT_SECURITY_RULE_ID)
    _file, _line = _parse_loc(getattr(iss, "location", ""))
    return make_a2_finding(
        _std_rule_id_from_category(_category_raw), _norm_severity_p(iss),
        _file, _line, getattr(iss, "description", ""),
        security_category=(str(_category_raw)
                           if _category_raw is not None else None))
_SEC_REPORT_REQUIRED_FIELDS = ("issues", "risk_level", "passed")
def _sec_report_missing_fields(sec_report: object) -> list[str]:
    return [name for name in _SEC_REPORT_REQUIRED_FIELDS
            if not hasattr(sec_report, name)]
def a2_security_component(skill_dir: str, findings: list, payload_parts: dict,
                          cache=None) -> None:
    sec_report = diag_skill_security(skill_dir, cache=cache)
    _missing = _sec_report_missing_fields(sec_report)
    if _missing:
        payload_parts["security"] = {
            "error": (
                "安全审计返回不可用结果: "
                f"{type(sec_report).__name__} 缺少契约字段 {_missing}"
                "（按审计失败处置，不视为零发现）")}
        return
    sec_issues = getattr(sec_report, "issues", [])
    if not isinstance(sec_issues, (list, tuple)):
        payload_parts["security"] = {
            "error": ("安全审计 issues 非序列: "
                      f"{type(sec_issues).__name__}（按审计失败处置）")}
        return
    for iss in sec_issues:
        findings.append(_sec_issue_finding(iss))
    passed = getattr(sec_report, "passed", None)
    invalid_passed = not isinstance(passed, bool)
    if invalid_passed or (not sec_issues and passed is False):
        detail = (
            f"安全审计 passed 非布尔（实际为 {passed!r}），结果不可信"
            if invalid_passed else
            "安全审计未通过且未返回具体 issue "
            f"(risk_level={getattr(sec_report, 'risk_level', 'unknown')})"
        )
        findings.append(make_a2_finding(
            "SEC-FAILED", "P1", str(skill_dir), 0,
            detail + "；保留失败信号，不按零发现放行"))
    _degraded = dict_or_empty(getattr(sec_report, "degraded_layers", {}))
    if _degraded:
        findings.append(make_a2_finding(
            "SEC-DEGRADED", "P3", str(skill_dir), 0,
            "安全审计部分通道降级: "
            + ", ".join(f"{k}×{v}" for k, v in _degraded.items())
            + "（该段发现可能缺失，建议复跑确认）"))
    security_payload = {
        "findings_count": len(sec_issues),
        "risk_level": getattr(sec_report, "risk_level", "low"),
        "passed": passed,
        "degraded_layers": _degraded,
    }
    if invalid_passed:
        security_payload["error"] = (
            "安全审计 passed 须为 bool，实际为 "
            f"{type(passed).__name__}（按审计失败处置）")
    payload_parts["security"] = security_payload
def a2_todo_debt_component(skill_dir: str, findings: list, payload_parts: dict,
                           cache=None) -> None:
    todo_report = diag_todos(skill_dir, cache=cache)
    for item in todo_report.items:
        if not item.is_valid:
            findings.append(make_a2_finding(
                "TODO-RISK", "P2", item.file, item.line,
                f"TODO危险信号({item.marker}): {item.description} {item.validation_note}"))
        elif item.is_stale:
            findings.append(make_a2_finding(
                "TODO-STALE", "P3", item.file, item.line,
                f"TODO遗留{item.age_days}天({item.marker}): {item.description}"))
    if todo_report.partial:
        findings.append(make_a2_finding(
            "TODO-DEGRADED", "P3", str(skill_dir), 0,
            "TODO 台账不完整（目录枚举、源码读取、词法分析或修改时间证据不可用），"
            "标记与陈旧统计可能缺失，建议复跑确认"))
    payload_parts["todo_debt"] = {
        "total": len(todo_report.items),
        "invalid": sum(1 for i in todo_report.items if not i.is_valid),
        "stale": todo_report.stale_count,
        "threshold_days": todo_report.stale_threshold_days,
        "partial": todo_report.partial,
    }
def a2_five_dim_component(skill_dir: str, findings: list, payload_parts: dict,
                          ctx=None) -> None:
    skills_root = _skill_collection_root(skill_dir)
    five_dim = run_five_dimension_health(
        skill_dir, skills_root=skills_root, ctx=ctx)
    payload_parts["five_dim"] = {
        "overall_score": five_dim.overall_score,
        "health_status": five_dim.health_status,
        "dimension_scores": {
            "code_quality": five_dim.code_quality_score,
            "test_quality": five_dim.test_quality_score,
            "architecture": five_dim.architecture_score,
            "security": five_dim.security_score,
            "documentation": five_dim.documentation_score,
        },
        "recommendations": list((five_dim.recommendations or [])[:5]),
    }
    if five_dim.health_status in {"warning", "critical"}:
        critical = five_dim.health_status == "critical"
        findings.append(make_a2_finding(
            "FIVE-DIM-CRITICAL" if critical else "FIVE-DIM-WARNING",
            "P2" if critical else "P3", str(skill_dir), 0,
            f"五维体检综合评分 {five_dim.overall_score:.1f}/100，"
            f"状态={five_dim.health_status}"
            f"（代码{five_dim.code_quality_score:.0f}/测试{five_dim.test_quality_score:.0f}"
            f"/架构{five_dim.architecture_score:.0f}/安全{five_dim.security_score:.0f}"
            f"/文档{five_dim.documentation_score:.0f}），建议专项治理"))
class _A2Component(NamedTuple):
    name: str
    key: str
    runner: Callable[..., None]
    arg_form: str | None = None
_A2_COMPONENTS: tuple[_A2Component, ...] = (
    _A2Component("可发现性分析", "discoverability", a2_discoverability_component),
    _A2Component("安全诊断", "security", a2_security_component, "cache"),
    _A2Component("质量评估", "quality", a2_quality_component),
    _A2Component("生命周期检查", "lifecycle", a2_lifecycle_component),
    _A2Component("TODO债务诊断", "todo_debt", a2_todo_debt_component, "cache"),
    _A2Component("结构健康分析", "structural", structural_health_component, "ctx"),
    _A2Component("五维体检", "five_dim", a2_five_dim_component, "ctx"),
)
def _norm_finding_file(value: object, base_dir: str | None = None) -> str:
    text = value if isinstance(value, str) else ""
    if not text:
        return ""
    if base_dir and not os.path.isabs(text):
        text = os.path.join(base_dir, text)
    return normalize_skill_path(text)
def _credential_pair_key(finding: dict, base_dir: str | None = None) -> tuple | None:
    rid = str(finding.get("rule_id", ""))
    if rid != "SS-03" and "hardcoded_secret" not in str(
            finding.get("security_category", "")):
        return None
    file_key = _norm_finding_file(finding.get("file"), base_dir)
    if not file_key:
        return None
    line_no = int_or(finding.get("line", 0), 0)
    if line_no <= 0:
        return None
    return file_key, line_no
def _has_both_credential_channels(findings: list, idxs: list[int]) -> bool:
    has_ss03 = any(str(findings[i].get("rule_id")) == "SS-03" for i in idxs)
    has_exec = any(
        str(findings[i].get("rule_id")) != "SS-03"
        and "hardcoded_secret" in str(findings[i].get("security_category", ""))
        for i in idxs)
    return has_ss03 and has_exec
def _dedup_credential_pairs(findings: list, removed: set,
                            base_dir: str | None = None) -> int:
    cred_dedup = 0
    groups: dict[tuple, list[int]] = {}
    for idx, f in enumerate(findings):
        key = _credential_pair_key(f, base_dir)
        if key is not None:
            groups.setdefault(key, []).append(idx)
    for idxs in groups.values():
        if len(idxs) < 2 or not _has_both_credential_channels(findings, idxs):
            continue
        keep = min(
            idxs, key=lambda i: _severity_sort_key(findings[i].get("severity")))
        removed.update(i for i in idxs if i != keep)
        cred_dedup += len(idxs) - 1
    return cred_dedup
_IDLE_LIFECYCLE_RULES = frozenset({"SKILL-ZOMBIE", "SKILL-DORMANT"})
_IDLE_RULES = _IDLE_LIFECYCLE_RULES | {"SKILL-UNUSED"}
def _dedup_idle_same_root_cause(findings: list, removed: set) -> int:
    idxs = [idx for idx, finding in enumerate(findings)
            if str(finding.get("rule_id")) in _IDLE_RULES
            and idx not in removed]
    if (not any(str(findings[idx].get("rule_id")) == "SKILL-UNUSED"
                for idx in idxs)
            or not any(str(findings[idx].get("rule_id")) in _IDLE_LIFECYCLE_RULES
                       for idx in idxs)):
        return 0
    keep = min(
        idxs,
        key=lambda idx: (
            _severity_sort_key(findings[idx].get("severity")),
            1 if str(findings[idx].get("rule_id")) == "SKILL-UNUSED" else 0,
            idx,
        ),
    )
    dropped = [idx for idx in idxs if idx != keep]
    removed.update(dropped)
    return len(dropped)
def _prune_related_findings(findings: list) -> None:
    valid_locators = {
        _locator_str(_sub_locator(finding))
        for finding in findings if isinstance(finding, dict)
    }
    for finding in findings:
        if not isinstance(finding, dict):
            continue
        related = finding.get("related")
        if not isinstance(related, list):
            continue
        retained = [key for key in related if key in valid_locators]
        if retained:
            finding["related"] = retained
        else:
            finding.pop("related", None)
def _dedup_same_root_cause(findings: list, payload_parts: dict,
                           base_dir: str | None = None) -> None:
    removed: set[int] = set()
    cred_dedup = _dedup_credential_pairs(findings, removed, base_dir)
    idle_dedup = _dedup_idle_same_root_cause(findings, removed)
    if removed:
        for i in sorted(removed, reverse=True):
            del findings[i]
        _prune_related_findings(findings)
        payload_parts["dedup"] = {
            "credential_same_position": cred_dedup,
            "idle_same_root_cause": idle_dedup,
        }
def _invoke_component(entry: _A2Component, skill_dir: str, findings: list,
                      payload_parts: dict, cache) -> None:
    if entry.arg_form == "cache":
        entry.runner(skill_dir, findings, payload_parts, cache=cache)
    elif entry.arg_form == "ctx":
        _ctx = as_diag_ctx(cache) if cache is not None else None
        entry.runner(skill_dir, findings, payload_parts, ctx=_ctx)
    else:
        entry.runner(skill_dir, findings, payload_parts)
_BLOCKING_SEVERITY_RANK = SEVERITY_RANK["P0"]
def _is_blocking_severity(severity: object) -> bool:
    if not isinstance(severity, str):
        return False
    rank = _severity_rank(severity)
    return rank is not None and rank <= _BLOCKING_SEVERITY_RANK
def _a2_final_status(findings: list, component_failed: bool) -> str:
    if not findings and not component_failed:
        return "pass"
    if any(_is_blocking_severity(f.get("severity"))
           for f in findings if isinstance(f, dict)):
        return "fail"
    return "warn"
def _run_a2_components(skill_dir: str, cache) -> tuple[list, dict, bool]:
    findings: list = []
    payload_parts: dict = {}
    component_failed = False
    for entry in _A2_COMPONENTS:
        try:
            _invoke_component(entry, skill_dir, findings, payload_parts, cache)
        except Exception as e:  # noqa: BLE001
            _log.warning("[A2] %s失败: %s", entry.name, e)
            payload_parts[entry.key] = {"error": str(e)[:200]}
            component_failed = True
    return findings, payload_parts, component_failed
def _failed_component_keys(payload_parts: dict) -> list[str]:
    return [
        key for key, value in payload_parts.items()
        if isinstance(value, dict) and "error" in value
    ]
def _normalize_analysis_root(skill_dir: str) -> str:
    raw = os.fspath(skill_dir) if isinstance(skill_dir, os.PathLike) else skill_dir
    if isinstance(raw, (str, bytes)) and not raw.strip():
        raise ValueError("分析根目录不能为空")
    return normalize_skill_dir(skill_dir)
def run_a2_health_assessment(skill_dir: str, cache=None) -> dict:
    skill_dir = _normalize_analysis_root(skill_dir)
    require_warmed(cache, "A2 技能健康评估")
    findings, payload_parts, component_failed = _run_a2_components(
        skill_dir, cache)
    _dedup_same_root_cause(findings, payload_parts, skill_dir)
    _failed = _failed_component_keys(payload_parts)
    if _failed:
        component_failed = True
    n = len(findings)
    all_components_failed = bool(_A2_COMPONENTS) and len(
        _failed) == len(_A2_COMPONENTS)
    status = ("error" if all_components_failed
              else _a2_final_status(findings, component_failed))
    if component_failed:
        payload_parts["component_failed"] = True
        payload_parts["failed_components"] = _failed
    _component_names = "+".join(entry.name for entry in _A2_COMPONENTS)
    return {
        "status": status,
        "findings_count": n,
        "summary": f"技能健康评估: {_component_names}, 共{n}个发现" + (f" [{len(_failed)}个子组件失败]" if _failed else ""),
        "findings": findings,
        "payload": payload_parts,
    }
DEFAULT_THRESHOLDS = {
    "line_limit": LINE_LIMIT,
    "large_file": 1500,
    "p0_penalty": 0.25,
    "p1_penalty": 0.10,
    "p2_penalty": 0.04,
    "p3_penalty": 0.01,
    "critical_threshold": 0.20,
    "serious_threshold": 0.40,
    "moderate_threshold": 0.60,
    "minor_threshold": 0.80,
    "function_limit": 20,
    "function_over_20_penalty": 0.05,
    "behavioral_class_limit": 10,
    "class_over_10_penalty": 0.05,
    "missing_all_penalty": 0.10,
}
def _severity_rank(severity: Any) -> int | None:
    if not isinstance(severity, str):
        return None
    rank = SEVERITY_RANK.get(severity.upper().strip())
    if rank is None:
        return None
    return min(rank, len(_DEFECT_SEVERITIES) - 1)
def normalize_defect_severity(severity: Any) -> str:
    rank = _severity_rank(severity)
    return "P3" if rank is None else _DEFECT_SEVERITIES[rank]
def _severity_sort_key(severity: Any) -> int:
    rank = _severity_rank(severity)
    return 99 if rank is None else rank
class _VerdictStats(NamedTuple):
    level_counts: Counter
    needs_split: int
    needs_refactor: int
    health_sum: float
    total_defects: int
    total_p0: int
    total_p1: int
_LINE_OVER_LIMIT_PENALTY = 0.15
_LARGE_FILE_PENALTY = 0.05
_FUNCTION_PENALTY_CAP = 0.2
_CLASS_PENALTY_CAP = 0.15
_L0_MODULE_MAX_LINES = 500
_L0_MODULE_OVER_PENALTY = 0.05
_P0_CRITICAL_MIN = 2
_P1_SERIOUS_MIN = 5
_NEEDS_REFACTOR_P1_MIN = 2
_NEEDS_REFACTOR_SCORE = 0.5
_DEFECT_SEVERITIES = ("P0", "P1", "P2", "P3")
_LEVEL_LADDER = (
    ("critical_threshold", VerdictLevel.CRITICAL),
    ("serious_threshold", VerdictLevel.SERIOUS),
    ("moderate_threshold", VerdictLevel.MODERATE),
    ("minor_threshold", VerdictLevel.MINOR),
)
def _is_finite_threshold(value) -> bool:
    if not isinstance(value, (int, float)) or isinstance(value, bool):
        return False
    try:
        return math.isfinite(value)
    except OverflowError:  # jwsgj:silent-ok
        return False
_PENALTY_THRESHOLD_KEYS = frozenset({
    "p0_penalty", "p1_penalty", "p2_penalty", "p3_penalty",
    "function_over_20_penalty", "class_over_10_penalty", "missing_all_penalty",
})
_COUNT_LIMIT_THRESHOLD_KEYS = frozenset({
    "line_limit", "large_file", "function_limit", "behavioral_class_limit",
})
_LEVEL_THRESHOLD_KEYS = frozenset({
    "critical_threshold", "serious_threshold",
    "moderate_threshold", "minor_threshold",
})
def _is_valid_threshold(key: str, value) -> bool:
    if not _is_finite_threshold(value):
        return False
    if key in _PENALTY_THRESHOLD_KEYS:
        return value >= 0
    if key in _COUNT_LIMIT_THRESHOLD_KEYS:
        return value > 0
    if key in _LEVEL_THRESHOLD_KEYS:
        return 0 < value <= 1
    return True
class VerdictEngine:
    def __init__(self, thresholds: dict | None = None):
        overrides = thresholds if isinstance(thresholds, dict) else {}
        merged = {**DEFAULT_THRESHOLDS, **overrides}
        self.thresholds = {
            k: v if _is_valid_threshold(k, v) else DEFAULT_THRESHOLDS[k]
            for k, v in merged.items() if k in DEFAULT_THRESHOLDS
        }
        self._restore_invalid_threshold_groups()
    def _restore_invalid_threshold_groups(self) -> None:
        if self.thresholds["large_file"] >= self.thresholds["line_limit"]:
            _log.warning(
                "文件规模阈值顺序非法（large_file 须小于 line_limit），该组回退默认")
            for key in ("large_file", "line_limit"):
                self.thresholds[key] = DEFAULT_THRESHOLDS[key]
        level_values = [self.thresholds[key] for key, _level in _LEVEL_LADDER]
        if any(current >= following
               for current, following in pairwise(level_values)):
            _log.warning(
                "健康等级阈值顺序非法（critical/serious/moderate/minor 须递增），该组回退默认")
            for key, _level in _LEVEL_LADDER:
                self.thresholds[key] = DEFAULT_THRESHOLDS[key]
    def evaluate(self, profile: FileOverallProfile) -> FileVerdict:
        basic = profile.basic_info
        entities = profile.key_entities
        domain = profile.functional_domain
        defects = profile.defects
        health_score = 1.0
        suggestions: list[str] = []
        (health_score, p0_count, p1_count, p2_count, p3_count,
         top_defects) = self._apply_defect_penalties(defects, health_score)
        health_score, needs_split = self._apply_scale_penalties(
            basic, health_score, suggestions)
        health_score = self._apply_missing_all_penalty(
            basic, entities, profile.filepath, health_score, suggestions)
        health_score = self._apply_domain_rules(
            domain, basic, health_score, suggestions)
        needs_refactor = (p0_count > 0
                          or p1_count >= _NEEDS_REFACTOR_P1_MIN
                          or health_score < _NEEDS_REFACTOR_SCORE)
        health_score = max(0.0, min(1.0, health_score))
        level = self._determine_level(health_score, p0_count, p1_count)
        top_defects.sort(key=lambda d: _severity_sort_key(d.severity))
        if level in (VerdictLevel.CRITICAL, VerdictLevel.SERIOUS):
            _log.warning(
                "裁决: %s -> %s (健康分 %.2f, P0=%d, P1=%d)",
                profile.filepath, level, health_score, p0_count, p1_count,
            )
        return FileVerdict(
            filepath=profile.filepath,
            level=level,
            health_score=round(health_score, 2),
            defect_count=p0_count + p1_count + p2_count + p3_count,
            p0_count=p0_count,
            p1_count=p1_count,
            p2_count=p2_count,
            p3_count=p3_count,
            top_defects=top_defects[:10],
            suggestions=suggestions[:5],
            needs_split=needs_split,
            needs_refactor=needs_refactor,
        )
    def _apply_missing_all_penalty(self, basic, entities, filepath: str,
                                    health_score: float,
                                    suggestions: list[str]) -> float:
        fp = str(filepath or "")
        if not (basic and entities) or basic.has_all or not entities.public_api:
            return health_score
        if (module_stem(fp).lower() in {"__init__", "__main__"}
                or is_test_file_path(fp)):
            return health_score
        health_score -= self.thresholds["missing_all_penalty"]
        suggestions.append(
            f"文件有 {len(entities.public_api)} 个公开符号但缺少 __all__")
        return health_score
    def _apply_domain_rules(self, domain, basic,
                            health_score: float,
                            suggestions: list[str]) -> float:
        if (domain and domain.domain == DomainCategory.L0_BASE
                and basic and basic.total_lines > _L0_MODULE_MAX_LINES):
            health_score -= _L0_MODULE_OVER_PENALTY
            suggestions.append("L0 底座模块不应过大，考虑提取共享定义")
        return health_score
    def _apply_defect_penalties(self, defects: list[FileDefect],
                                health_score: float
                                ) -> tuple[float, int, int, int, int, list[FileDefect]]:
        counts = [0] * len(_DEFECT_SEVERITIES)
        top_defects: list[FileDefect] = []
        for defect in defects:
            if is_retired_rule(defect.defect_type):
                continue
            severity = normalize_defect_severity(defect.severity)
            counts[_DEFECT_SEVERITIES.index(severity)] += 1
            health_score -= self.thresholds[f"{severity.lower()}_penalty"]
            if severity in ("P0", "P1"):
                top_defects.append(defect)
        return health_score, *counts, top_defects
    def _apply_scale_penalties(self, basic, health_score: float,
                               suggestions: list[str]) -> tuple[float, bool]:
        if not basic:
            return health_score, False
        needs_split = False
        if basic.total_lines > self.thresholds["line_limit"]:
            health_score -= _LINE_OVER_LIMIT_PENALTY
            needs_split = True
            suggestions.append(
                f"文件 {basic.total_lines} 行超过限制 "
                f"{self.thresholds['line_limit']}：治理候选（优先简化逻辑/"
                "消除重复/迁移无关块/提取同模块私有实现，禁止直接拆分）"
            )
        elif basic.total_lines > self.thresholds["large_file"]:
            health_score -= _LARGE_FILE_PENALTY
            suggestions.append(
                f"文件较大 ({basic.total_lines} 行)：可评估非拆分治理"
                "（简化/去重/提取同模块私有实现）"
            )
        if basic.function_count > self.thresholds["function_limit"]:
            over = basic.function_count - self.thresholds["function_limit"]
            penalty = min(
                over * self.thresholds["function_over_20_penalty"],
                _FUNCTION_PENALTY_CAP)
            health_score -= penalty
            suggestions.append(
                f"文件包含 {basic.function_count} 个函数：按职责收敛依赖"
                "或迁移无关代码块，不新增文件边界"
            )
        behavioral_count = len(behavioral_classes(basic.classes))
        if behavioral_count > self.thresholds["behavioral_class_limit"]:
            over = behavioral_count - self.thresholds["behavioral_class_limit"]
            penalty = min(
                over * self.thresholds["class_over_10_penalty"],
                _CLASS_PENALTY_CAP)
            health_score -= penalty
            suggestions.append(
                f"文件包含 {behavioral_count} 个行为类：合并重复职责"
                "或提取同模块私有实现，不拆分模块"
            )
        return health_score, needs_split
    def _determine_level(self, health_score: float,
                         p0_count: int, p1_count: int) -> str:
        level = VerdictLevel.HEALTHY
        for threshold_key, candidate in _LEVEL_LADDER:
            if health_score < self.thresholds[threshold_key]:
                level = candidate
                break
        if p0_count >= _P0_CRITICAL_MIN:
            return VerdictLevel.CRITICAL
        if ((p0_count == 1 or p1_count >= _P1_SERIOUS_MIN)
                and level != VerdictLevel.CRITICAL):
            return VerdictLevel.SERIOUS
        return level
    def generate_summary(self, profiles: list[FileOverallProfile],
                         verdicts: list[FileVerdict] | None = None) -> dict:
        if verdicts is None:
            verdicts = [self.evaluate(profile) for profile in profiles]
        stats = self._aggregate_verdicts(verdicts)
        total = len(verdicts)
        avg_health = stats.health_sum / max(total, 1)
        self._log_summary(total, avg_health, stats)
        return {
            "total_files": total,
            "avg_health_score": round(avg_health, 2),
            "level_distribution": self._level_distribution(stats.level_counts),
            "needs_split": stats.needs_split,
            "needs_refactor": stats.needs_refactor,
            "worst_files": self._worst_files_report(verdicts),
            "total_defects": stats.total_defects,
            "total_p0": stats.total_p0,
            "total_p1": stats.total_p1,
        }
    @staticmethod
    def _aggregate_verdicts(verdicts: list[FileVerdict]) -> _VerdictStats:
        level_counts: Counter = Counter()
        needs_split = needs_refactor = total_defects = 0
        total_p0 = total_p1 = 0
        health_sum = 0.0
        for verdict in verdicts:
            level_counts[verdict.level] += 1
            needs_split += int(verdict.needs_split)
            needs_refactor += int(verdict.needs_refactor)
            health_sum += verdict.health_score
            total_defects += verdict.defect_count
            total_p0 += verdict.p0_count
            total_p1 += verdict.p1_count
        return _VerdictStats(level_counts, needs_split, needs_refactor,
                             health_sum, total_defects, total_p0, total_p1)
    @staticmethod
    def _log_summary(total: int, avg_health: float, stats: _VerdictStats) -> None:
        _log.info(
            "裁决汇总: %d 文件, 平均健康分 %.2f, 等级分布 healthy=%d "
            "minor=%d moderate=%d serious=%d critical=%d, 需拆分 %d, "
            "需重构 %d, 缺陷总量 %d (P0=%d, P1=%d)",
            total, avg_health,
            stats.level_counts.get(VerdictLevel.HEALTHY, 0),
            stats.level_counts.get(VerdictLevel.MINOR, 0),
            stats.level_counts.get(VerdictLevel.MODERATE, 0),
            stats.level_counts.get(VerdictLevel.SERIOUS, 0),
            stats.level_counts.get(VerdictLevel.CRITICAL, 0),
            stats.needs_split, stats.needs_refactor,
            stats.total_defects, stats.total_p0, stats.total_p1,
        )
    def _worst_files_report(self, verdicts: list[FileVerdict]) -> list[dict]:
        _floor = self.thresholds["minor_threshold"]
        sorted_verdicts = sorted(verdicts, key=lambda v: v.health_score)
        return [
            {
                "filepath": v.filepath,
                "health_score": v.health_score,
                "level": v.level,
                "defect_count": v.defect_count,
                "p0_count": v.p0_count,
                "p1_count": v.p1_count,
            }
            for v in sorted_verdicts
            if v.health_score < _floor
        ][:10]
    @staticmethod
    def _level_distribution(level_counts: Counter) -> dict:
        return {
            "healthy": level_counts.get(VerdictLevel.HEALTHY, 0),
            "minor": level_counts.get(VerdictLevel.MINOR, 0),
            "moderate": level_counts.get(VerdictLevel.MODERATE, 0),
            "serious": level_counts.get(VerdictLevel.SERIOUS, 0),
            "critical": level_counts.get(VerdictLevel.CRITICAL, 0),
        }
def render_verdict(profile: FileOverallProfile,
                   thresholds: dict | None = None) -> FileVerdict:
    ensure_domains([profile])
    enhanced = enhance_single_file_defects(profile)
    profile.defects.extend(enhanced)
    return VerdictEngine(thresholds=thresholds).evaluate(profile)
def render_verdicts_batch(profiles: list[FileOverallProfile],
                          thresholds: dict | None = None) -> list[FileVerdict]:
    ensure_domains(profiles)
    enhance_defects(profiles)
    engine = VerdictEngine(thresholds=thresholds)
    return [engine.evaluate(profile) for profile in profiles]
def _a1_flatten_findings(profiles: list[FileOverallProfile]) -> tuple[list[dict], int]:
    all_findings = []
    retired = 0
    for profile in profiles:
        for defect in profile.defects:
            if is_retired_rule(defect.defect_type):
                retired += 1
                continue
            all_findings.append({
                "rule_id": A1_METHOD_ID + "-" + defect.defect_type,
                "severity": normalize_defect_severity(defect.severity),
                "confidence": defect.confidence,
                "message": defect.message, "file": defect.filepath, "line": defect.lineno,
                "end_line": defect.end_lineno,
                "source": "A1", "family": "structure", "category": defect.defect_type,
                "suggestion": defect.suggestion,
            })
    if retired:
        _log.info("[A1] 退役规则缺陷不计入 findings/健康罚分: %d 项（SSOT: RETIRED_RULE_IDS）",
                    retired)
    return all_findings, len(all_findings)
def _empty_payload() -> dict:
    return {"file_count": 0, "profile_count": 0,
            "total_defects": 0, "profiles": []}
def _error_result(summary: str) -> dict:
    return {"status": "error", "findings_count": 0, "summary": summary,
            "findings": [], "payload": _empty_payload()}
def _a1_zero_profile_result(skill_dir: str) -> dict:
    try:
        has_py = bool(collect_py_files(skill_dir))
        has_content = bool(os.listdir(skill_dir))
    except (OSError, ValueError) as e:
        _log.warning("[A1] 扫描面探查失败，按塌缩处置: %s", e)
        return _error_result(
            "A1 five-dim analysis error: 扫描范围不可判定，"
            "0 个文件画像（目录不可读或已消失）")
    if has_py:
        return _error_result(
            "A1 five-dim analysis error: 扫描范围塌缩，"
            "0 个文件画像（存在 .py 文件但全部扫描失败，"
            "检查 skill_dir 与排除目录）")
    if not has_content:
        return _error_result(
            "A1 five-dim analysis error: 扫描范围塌缩，"
            "0 个文件画像（目录为空，无 SKILL.md、无源码面）")
    return {
        "status": "pass",
        "findings_count": 0,
        "summary": ("A1 five-dim analysis: 0 个 Python 文件"
                    "（非 Python 技能形态，无文件级发现）"),
        "findings": [],
        "payload": {**_empty_payload(),
                    "skipped_reason": "no_python_files"},
    }
def run_a1_file_analyzer(skill_dir: str, cache=None) -> dict:
    skill_dir = _normalize_analysis_root(skill_dir)
    require_warmed(cache, "A1 五维文件分析")
    start = time.perf_counter()
    try:
        profiles = FileAnalyzerScanner(
            skill_dir, cache=cache,
        ).scan_directory()
    except (NotADirectoryError, FileNotFoundError) as e:
        _log.warning("[A1] 扫描根不可用: %s", e)
        return _error_result(
            "A1 five-dim analysis error: 扫描范围塌缩，0 个文件画像（扫描根不可用: "
            + str(e)[:150] + "）")
    except Exception as e:  # noqa: BLE001
        _log.exception("[A1] five-dimension analysis failed")
        return _error_result("A1 analysis failed: " + str(e))
    try:
        if not profiles:
            return _a1_zero_profile_result(skill_dir)
        ensure_domains(profiles, skill_dir)
        enhance_defects(profiles)
        engine = VerdictEngine()
        verdicts = [engine.evaluate(profile) for profile in profiles]
        for p, v in zip(profiles, verdicts, strict=True):
            p.verdict = v
        verdict_summary = engine.generate_summary(profiles, verdicts=verdicts)
        all_findings, total_defects = _a1_flatten_findings(profiles)
        verdict_stats = verdict_summary["level_distribution"]
        split_total = verdict_summary["needs_split"]
        refactor_total = verdict_summary["needs_refactor"]
        avg_health = verdict_summary["avg_health_score"]
        elapsed = round((time.perf_counter() - start) * 1000, 1)
        severity_counts = Counter(d.get("severity") for d in all_findings)
        p0_count = severity_counts["P0"]
        p1_count = severity_counts["P1"]
        p2_count = severity_counts["P2"]
        critical_files = verdict_stats.get("critical", 0)
        serious_files = verdict_stats.get("serious", 0)
        # 执行健康只反映扫描完整性；P0/P1 属于诊断结论（verdict），
        # 不得写成 status=fail，否则下游会把「发现 P0」误读为「方法执行失败」。
        status = "pass"
        verdict, verdict_reason = verdict_from_severity_counts(
            dict(severity_counts))
        if verdict == "pass" and (critical_files > 0 or serious_files > 0):
            verdict = "warn"
            verdict_reason = f"{critical_files + serious_files} 个文件健康度严重"
        return {
            "status": status,
            "verdict": verdict,
            "verdict_reason": verdict_reason,
            "findings_count": len(all_findings),
            "summary": (
                f"A1 five-dim analysis: {len(profiles)} files, "
                f"{total_defects} defects, "
                f"P0={p0_count} P1={p1_count} P2={p2_count} | "
                f"healthy={verdict_stats.get('healthy', 0)} "
                f"minor={verdict_stats.get('minor', 0)} "
                f"moderate={verdict_stats.get('moderate', 0)} "
                f"serious={verdict_stats.get('serious', 0)} "
                f"critical={verdict_stats.get('critical', 0)} | "
                f"avg_health={avg_health} "
                f"needs_split={split_total} "
                f"needs_refactor={refactor_total} | "
                f"{elapsed}ms"),
            "findings": all_findings,
            "payload": {"file_count": len(profiles), "profile_count": len(profiles),
                         "total_defects": total_defects, "verdict_stats": verdict_stats,
                         "avg_health_score": avg_health, "needs_split": split_total,
                         "needs_refactor": refactor_total,
                         "verdict_summary": verdict_summary,
                         "profiles": [a1_to_dict(p) for p in profiles]},
        }
    except Exception as e:  # noqa: BLE001
        _log.exception("[A1] analysis pipeline failed")
        return _error_result("A1 analysis failed: " + str(e))
def _a_detector_table() -> dict[str, Callable[..., dict]]:
    return {
        "A1": run_a1_file_analyzer,
        "A2": run_a2_health_assessment,
        "A3": run_a3_silent_degrade,
        "A4": run_c2_doc_quality_engine,
    }
_A_DETECTOR_IDS = tuple(_a_detector_table())
def _run_a_detectors(skill_dir: str, cache) -> list:
    det_results: list = []
    _table = _a_detector_table()
    with fingerprint_freeze_window(cache, "A组"):
        for _eid in _A_DETECTOR_IDS:
            det_results.append(detector_entry(
                _eid, _table[_eid], skill_dir, cache,
                logger=_log, engine_tag="engine_a"))
    return det_results
_TOKEN_OVER_RULE_ID = "TOKEN-OVER"
_SC05_RULE_SUFFIX = "SC-05"
def _dedup_token_over_by_sc05(merged: list, base_dir: str | None = None) -> int:
    sc05_files = {
        _norm_finding_file(f.get("file"), base_dir)
        for f in merged
        if isinstance(f, dict)
        and str(f.get("rule_id", "")).endswith(_SC05_RULE_SUFFIX)
        and str(f.get("severity", "")) == "P2"
    }
    sc05_files.discard("")
    if not sc05_files:
        return 0
    critical_token_files = {
        _norm_finding_file(f.get("file"), base_dir)
        for f in merged
        if isinstance(f, dict)
        and str(f.get("rule_id", "")) == _TOKEN_OVER_RULE_ID
        and str(f.get("severity", "")) == "P1"
        and _norm_finding_file(f.get("file"), base_dir) in sc05_files
    }
    kept: list = []
    dropped = 0
    for finding in merged:
        if not isinstance(finding, dict):
            kept.append(finding)
            continue
        rule_id = str(finding.get("rule_id", ""))
        severity = str(finding.get("severity", ""))
        file_key = _norm_finding_file(finding.get("file"), base_dir)
        drop_sc05 = (rule_id.endswith(_SC05_RULE_SUFFIX) and severity == "P2"
                     and file_key in critical_token_files)
        drop_token = (rule_id == _TOKEN_OVER_RULE_ID and severity == "P2"
                      and file_key in sc05_files
                      and file_key not in critical_token_files)
        if drop_sc05 or drop_token:
            dropped += 1
            continue
        kept.append(finding)
    if dropped:
        merged[:] = kept
        _prune_related_findings(merged)
    return dropped
def _a_group_summary(det_results: list, stats: dict) -> str:
    return (
        f"主引擎A: A1五维扫描+A2健康评估+A3静默降级+A4文档质量, "
        f"检测器{len(det_results)}个, 原始发现{stats.get('raw_findings', 0)}, "
        f"预合并后{stats.get('merged_findings', 0)}, "
        f"冲突{stats.get('conflicts', 0)}"
    )
def run_engine_a(skill_dir: str, cache=None) -> dict:
    skill_dir = _normalize_analysis_root(skill_dir)
    cache = ensure_entry_warmed(skill_dir, cache, "主引擎 A 组")
    t0 = time.perf_counter()
    det_results = _run_a_detectors(skill_dir, cache)
    try:
        merged, conflicts, stats = consolidate_findings(
            det_results, source_method="A", merged_from="engine_a")
    except (AttributeError, IndexError, KeyError, RuntimeError,
            TypeError, ValueError) as e:
        _log.exception("[A组] 组内预合并失败")
        err = f"{type(e).__name__}: {e}"
        return group_envelope(
            "A", _A_DETECTOR_IDS, "error", [], {}, det_results, t0,
            summary=f"主引擎A: 组内预合并异常 {err[:150]}", error=err)
    _token_deduped = _dedup_token_over_by_sc05(merged, skill_dir)
    if _token_deduped:
        stats["merged_findings"] = len(merged)
        stats["token_over_deduped"] = _token_deduped
    worst = worst_sub_status(det_results, merged)
    return group_envelope(
        "A", _A_DETECTOR_IDS, worst, merged, stats, det_results, t0,
        summary=_a_group_summary(det_results, stats), conflicts=conflicts)

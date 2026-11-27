from __future__ import annotations

import argparse
import logging
import os
import sys
from collections.abc import Callable
from pathlib import Path
from typing import Any, NoReturn

from jwsgj.build_contract import (
    JSON_REPORT_ERRORS,
    cli_boundary,
    emit_json_report,
    fail_cli,
    field_of,
    json_text,
    load_json_file,
    logged_cli_command,
    norm_display,
    norm_warnings,
    num_of,
    require_dict,
    require_dir,
    resolve_report_path,
    run_cli_action,
    split_csv,
    to_mapping,
    write_json_payload,
)
from jwsgj.build_preflight import (
    build_preflight,
    init_skill,
    quick_optimize,
)
from jwsgj.build_preflight_guard import validate_skill
from jwsgj.build_safe_write import (
    BACKUP_RETENTION_DAYS,
    prune_all_backup_roots,
)
from jwsgj.build_skill_discovery import (
    DiscoverabilityDiagnoser,
    evaluate_skill_hotness_for_dir,
    quick_diag_skill_dir,
)
from jwsgj.build_skill_lifecycle import (
    SkillDiagnoser,
    diag_skills_directory,
)
from jwsgj.build_skill_md_optimize import attach_best_practices
from jwsgj.build_skill_md_quality import (
    enforce_workflow_doc,
    validate_workflow_doc,
)
from jwsgj.build_skill_merge import (
    bump_version,
    get_version_history,
    package_skill,
    partition_package_validation_errors,
    read_skill_version_entry,
)
from jwsgj.diag_log_coverage import (
    audit_log_coverage,
)
from jwsgj.diag_self_check import (
    check_missing,
    ensure_dependencies,
    has_missing,
    quick_self_check,
)
from jwsgj.memory_bridge import prepare_diagnostic_context
from jwsgj.memory_bridge_ops import enhance_pipeline_with_memory
from jwsgj.pipeline_trigger_route import (
    mine_trigger_events,
    record_trigger_event,
    render_miner_report,
    run_pipeline_from_trigger,
)
from jwsgj.runtime_paths import (
    normalize_skill_name,
)
from jwsgj.runtime_scope import (
    PACKAGE_NAME,
    SKIP_DEPS_ENV_VAR,
    normalize_skill_dir,
)

_PACKAGE_NAME = PACKAGE_NAME
logger = logging.getLogger(f"{_PACKAGE_NAME}.__main__")
__all__ = [
    'MAINTENANCE_COMMANDS',
    'SKILL_COMMANDS',
    'cmd_bump_version',
    'cmd_deps',
    'cmd_diag',
    'cmd_init',
    'cmd_log_coverage',
    'cmd_memory_enhance',
    'cmd_optimize',
    'cmd_package',
    'cmd_prune_backups',
    'cmd_self_check',
    'cmd_trigger',
    'cmd_trigger_mine',
    'cmd_validate',
    'deps_gate',
    'deps_gate_needed',
    'quick_diag',
    'register_cli_maintenance',
    'register_cli_skill',
]
def _as_entries(value: Any) -> list:
    if value is None:
        return []
    if isinstance(value, (list, tuple, set, frozenset)):
        return list(value)
    return [value]
def _nonblank(value: Any) -> str:
    if not isinstance(value, str):
        return ""
    return value.strip()
def _resolve_workflow_doc(report: dict) -> tuple[str | None, str]:
    skill_dir = _nonblank(report.get("skill_dir"))
    if not skill_dir:
        return None, "自检报告未提供可定位的 SKILL.md：未提供 skill_dir"
    candidate = os.path.join(skill_dir, "SKILL.md")
    if not os.path.isfile(candidate):
        return None, f"自检报告未提供可定位的 SKILL.md：{candidate} 不存在"
    return candidate, ""
def _verify_workflow_doc(report: dict, fix: bool) -> None:
    skill_md_path, missing_reason = _resolve_workflow_doc(report)
    if skill_md_path is None:
        report["workflow_doc"] = {
            "valid": None, "checked_rules": 0, "passed": 0,
            "violations": [], "error": missing_reason,
        }
        print(f"  [WARN] SKILL.md 工作流规范未判定: {missing_reason}")
        logger.warning("[cli:self-check] 工作流规范判定: 未判定（%s）",
                       missing_reason)
        if fix:
            _apply_workflow_fix(report)
        return
    try:
        wf = validate_workflow_doc(skill_md_path)
        workflow_doc = {
            "valid": wf.get("valid"),
            "checked_rules": wf.get("checked_rules", 0),
            "passed": wf.get("passed", 0),
            "violations": _normalize_violations(wf.get("violations")),
        }
        if wf.get("error"):
            workflow_doc["error"] = wf["error"]
        report["workflow_doc"] = workflow_doc
        state = wf.get("valid")
        if state is True:
            _print_workflow_valid(wf)
            return
        if state is False:
            entries = _as_entries(wf.get("violations"))
            _print_workflow_violations(entries)
            if not entries:
                reason = _workflow_error_text(wf)
                print(f"  [WARN] SKILL.md 工作流规范校验不可用: {reason}")
                logger.warning("[cli:self-check] 工作流规范判定: 不可用（%s）",
                               reason)
            else:
                logger.warning("[cli:self-check] 工作流规范判定: 违规（%d 条未通过）",
                               len(entries))
        else:
            print("  [WARN] SKILL.md 工作流规范未判定（诊断引擎降级）")
            logger.warning("[cli:self-check] 工作流规范判定: 未判定（诊断引擎降级）")
        if fix:
            _apply_workflow_fix(report)
    except Exception as e:
        logger.warning("[cli:self-check] 工作流规范检查降级: %s", e)
        partial = report.get("workflow_doc")
        if isinstance(partial, dict):
            partial["valid"] = None
            partial["error"] = str(e)
        else:
            report["workflow_doc"] = {"valid": None, "error": str(e)}
def _print_workflow_valid(wf: dict) -> None:
    print(f"  [OK ] SKILL.md 工作流规范 {wf.get('passed', 0)}/{wf.get('checked_rules', 0)} 条通过")
    logger.info("[cli:self-check] 工作流规范判定: 通过（%d/%d 条）",
                wf.get('passed', 0), wf.get('checked_rules', 0))
def _workflow_error_text(workflow: dict) -> str:
    error = workflow.get("error")
    if isinstance(error, str) and error.strip():
        return error.strip()
    return "未产出违规明细"
def _normalize_violations(value: Any) -> list[dict]:
    normalized: list[dict] = []
    for raw in _as_entries(value):
        mapped = to_mapping(raw)
        normalized.append(mapped if mapped else {"detail": norm_display(raw)})
    return normalized
def _print_workflow_violations(violations: Any) -> None:
    for raw in _as_entries(violations):
        v = to_mapping(raw)
        if not v:
            print(f"  [FAIL] 工作流规则违规（未结构化）: {norm_display(raw)}")
            logger.warning("[cli:self-check] 工作流违规（未结构化）: %s",
                           norm_display(raw))
            continue
        line = (f"工作流规则 {v.get('rule_id')} {v.get('name')}: "
                f"{v.get('fix_hint', '')}")
        print(f"  [FAIL] {line}")
        logger.warning("[cli:self-check] 工作流违规: %s", line)
def _apply_workflow_fix(report: dict) -> None:
    workflow_doc = report["workflow_doc"]
    skill_md_path, missing_reason = _resolve_workflow_doc(report)
    if skill_md_path is None:
        message = f"自动修复未执行：{missing_reason}"
        workflow_doc["enforced"] = {
            "fixed": [], "valid_after": False, "error": message,
        }
        workflow_doc["error"] = message
        print(f"  [WARN] {message}")
        logger.warning("[cli:self-check] %s（skill_dir=%s）",
                       message, report.get("skill_dir"))
        return
    ef = enforce_workflow_doc(skill_md_path, auto_fix=True)
    fixed = ef.get("fixed") or []
    if not isinstance(fixed, list):
        fixed = []
    valid_after = bool(ef.get("valid_after"))
    enforced = {"fixed": fixed, "valid_after": valid_after}
    error = ef.get("error")
    if error:
        enforced["error"] = error
        workflow_doc["error"] = error
    else:
        workflow_doc.pop("error", None)
    workflow_doc["enforced"] = enforced
    if "violations_after" in ef:
        violations = _normalize_violations(ef.get("violations_after"))
        workflow_doc["violations"] = violations
        checked_rules = workflow_doc.get("checked_rules")
        if isinstance(checked_rules, int) and not isinstance(checked_rules, bool):
            workflow_doc["passed"] = max(0, checked_rules - len(violations))
    workflow_doc["valid"] = valid_after
    if fixed:
        print(f"  [FIX] 已自动修复规则: {', '.join(map(str, fixed))}")
        logger.info("[cli:self-check] 自动修复规则: %s",
                    ', '.join(map(str, fixed)))
    if valid_after:
        print("  [OK ] 修复后复验通过")
        logger.info("[cli:self-check] 修复后复验: 通过")
    else:
        print("  [WARN] 自动修复后仍有违规，需人工处理")
        logger.warning("[cli:self-check] 修复后复验: 仍有违规需人工处理")
def _print_facade_lines(facades: Any) -> None:
    for name, info in to_mapping(facades).items():
        info_map = to_mapping(info)
        mark = "OK " if info_map.get("ok") else "FAIL"
        extra = "" if info_map.get("ok") else f"  {str(info_map.get('error', ''))[:120]}"
        print(f"  [{mark}] {name}{extra}")
def _print_dependency_lines(dependencies: Any) -> None:
    for pkg, ok in to_mapping(dependencies).items():
        print(f"  [{'OK ' if ok else 'MISS'}] 依赖 {pkg}")
def _print_shadow_lines(shadow_packages: Any) -> None:
    for shadow in _as_entries(shadow_packages)[:5]:
        shadow_map = to_mapping(shadow)
        name = shadow_map.get("name")
        if not name:
            continue
        print(f"  [WARN] 影子包 {name}: "
              f"{shadow_map.get('loaded_from') or '?'} "
              f"≠ {shadow_map.get('also_exists_at') or '?'}")
def _print_self_check_report(report: dict) -> None:
    print(f"技能包: {report.get('skill') or '-'}  检查时间: {report.get('checked_at') or ''}")
    print(f"Python: {report.get('python_version') or '?'}"
          f" (要求 {report.get('python_required') or '?'})"
          f"  {'OK' if report.get('python_ok') else 'FAIL'}")
    _print_facade_lines(report.get("facades"))
    _print_dependency_lines(report.get("dependencies"))
    _print_shadow_lines(report.get("shadow_packages"))
def _self_check_failed(report: dict) -> bool:
    workflow = report.get("workflow_doc")
    return (not report.get("ok")
            or to_mapping(workflow).get("valid") is not True)
def _self_check_conclusion(report: dict) -> str:
    summary = str(report.get("summary", "") or "")
    workflow = report.get("workflow_doc")
    if not isinstance(workflow, dict):
        return summary
    state = workflow.get("valid")
    if state is True:
        verdict = "SKILL.md 工作流规范=ok"
    elif state is False:
        count = len(_as_entries(workflow.get("violations")))
        if count:
            verdict = f"SKILL.md 工作流规范=FAIL（{count} 条未通过）"
        else:
            verdict = (f"SKILL.md 工作流规范=FAIL"
                       f"（校验不可用: {_workflow_error_text(workflow)}）")
    else:
        verdict = "SKILL.md 工作流规范=未判定"
    return f"{summary}；{verdict}" if summary else verdict
@cli_boundary("self-check", "自健康检查命令失败")
def cmd_self_check(args: argparse.Namespace) -> None:
    try:
        report = to_mapping(quick_self_check())
    except Exception as e:
        fail_cli("self-check", f"自健康检查执行失败: {e}")
    if not report:
        fail_cli("self-check", "自健康检查返回空产物（契约违约）")
    _print_self_check_report(report)
    _verify_workflow_doc(report, fix=getattr(args, "fix", False))
    conclusion = _self_check_conclusion(report)
    report["conclusion"] = conclusion
    print(f"\n结论: {conclusion}")
    if getattr(args, "json", False):
        emit_json_report(
            report, resolve_report_path(args, "self_check_report.json"))
    if _self_check_failed(report):
        sys.exit(1)
def _require_skill_dir(args: argparse.Namespace, tag: str) -> None:
    raw = _nonblank(getattr(args, "skill_dir", ""))
    if not raw:
        fail_cli(tag, "技能目录不能为空（空白路径不得回退到当前目录）")
    args.skill_dir = normalize_skill_dir(raw)
    require_dir(Path(args.skill_dir), tag)
def _resolve_init_name(args: argparse.Namespace) -> str:
    raw = args.skill_name
    skill_name = normalize_skill_name(raw)
    if not skill_name:
        fail_cli("init", "技能名称必须至少包含一个字母或数字。",
                  detail=f"非法技能名: {raw!r}")
    if len(skill_name.replace("-", "")) < 2:
        fail_cli("init", "技能名称过短（最小2个有效字符）",
                  detail=f"归一后技能名: {skill_name!r}")
    if skill_name != raw:
        print(f"提示：技能名已从 '{raw}' 规范化为 '{skill_name}'。")
    return skill_name
def _print_init_plan(skill_name: str, skill_dir: str, description: str,
                     resources: list[str]) -> None:
    print(f"正在初始化技能：{skill_name}")
    print(f"   位置：{skill_dir}")
    if description:
        print(f"   描述：{description}")
    resource_text = (", ".join(resources) if resources
                     else "无（自动创建 scripts/references/tests）")
    print(f"   资源：{resource_text}")
def cmd_init(args: argparse.Namespace) -> None:
    skill_name = _resolve_init_name(args)
    resources = split_csv(getattr(args, "resources", ""))
    output_dir = (_nonblank(getattr(args, "path", ""))
                  or _nonblank(os.environ.get("WORKSPACE_DIR", ""))
                  or ".")
    output_dir = str(Path(
        normalize_skill_dir(os.fspath(output_dir))).resolve())
    skill_dir = str(Path(output_dir) / skill_name)
    description = getattr(args, "description", "") or ""
    _print_init_plan(skill_name, skill_dir, description, resources)
    result = require_dict(
        run_cli_action(
            "init", "初始化异常", init_skill, skill_name,
            target_dir=skill_dir, description=description,
            resources=resources or None),
        "init", "初始化产物")
    if result.get("status") == "ok":
        print(f"初始化成功：{result.get('target_dir', skill_dir)}")
        sys.exit(0)
    fail_cli("init", f"初始化失败：{result}", detail=f"初始化返回: {result}")
def _report_package_blockers(skill_dir: str, blocking: list[str]) -> NoReturn:
    logger.error("[cli:package] 打包前置校验失败: %s（%d 项问题）",
                 skill_dir, len(blocking))
    print("[ERROR] 打包失败（技能未通过校验）：", file=sys.stderr)
    for err in blocking:
        print(f"  - {err}", file=sys.stderr)
    sys.exit(1)
def cmd_package(args: argparse.Namespace) -> None:
    _require_skill_dir(args, "package")
    _valid, errors = _normalize_validation_result(
        run_cli_action("package", "校验异常", validate_skill, args.skill_dir),
        "package")
    blocking_errors, crlf_errors, residue_errors = (
        partition_package_validation_errors(errors))
    if blocking_errors or (not _valid and not errors):
        if not blocking_errors:
            logger.error("[cli:package] 校验未通过且未返回错误明细: %s",
                         args.skill_dir)
            fail_cli(
                "package",
                "打包失败（校验未通过且未返回错误明细，拒绝交付未验证归档）",
                detail=f"validate_skill 返回 valid={_valid!r}, errors={errors!r}")
        _report_package_blockers(args.skill_dir, blocking_errors)
    if crlf_errors:
        print("[WARN] SKILL.md 为 CRLF，打包时自动转换为 LF（源文件不变）",
              file=sys.stderr)
    for residue in residue_errors:
        print(f"[WARN] {residue}（打包时自动排除，不随包分发）",
              file=sys.stderr)
    result = run_cli_action(
        "package", "打包失败", package_skill, args.skill_dir,
        getattr(args, "output", "") or None)
    if not result:
        fail_cli("package", "打包失败（未生成 .skill 文件）")
    print(f"打包成功：{result}")
def _print_preflight_warnings(pre_result) -> None:
    if not isinstance(pre_result, dict):
        return
    pre_warnings = [
        field_of(w, "detail", str(w)) if isinstance(w, dict) else str(w)
        for w in norm_warnings(field_of(pre_result, "warnings", []))
    ]
    if not pre_warnings:
        return
    logger.warning("[cli] 六维预检发现问题: %s", "; ".join(pre_warnings))
    print("[WARNING] 六维预检发现问题：")
    for warn in pre_warnings:
        print(f"  - {warn}")
def _report_preflight(skill_dir: str) -> None:
    try:
        pre_result = build_preflight(skill_dir)
        _print_preflight_warnings(pre_result)
    except Exception as e:
        logger.warning("[cli:validate] 六维预检执行异常（预检未执行）: %s", e)
        print(f"[WARNING] 六维预检执行异常，预检未执行：{e}")
def cmd_validate(args: argparse.Namespace) -> None:
    _require_skill_dir(args, "validate")
    valid, errors = _normalize_validation_result(
        run_cli_action("validate", "校验异常", validate_skill, args.skill_dir),
        "validate")
    if not valid:
        logger.error("[cli:validate] 校验失败: %s（%d 项问题）",
                     args.skill_dir, len(errors or []))
        print("[ERROR] 校验失败：", file=sys.stderr)
        for err in (errors or []):
            print(f"  - {err}", file=sys.stderr)
        sys.exit(1)
    _report_preflight(args.skill_dir)
    print(f"校验通过：{args.skill_dir}")
def _print_scalar_result(result, label: str) -> bool:
    if isinstance(result, dict):
        return False
    print(f"{label}：{result}")
    return True
def _issue_text(issue: Any) -> str:
    if not isinstance(issue, dict):
        return str(issue)
    severity = norm_display(issue.get('severity'))
    rule_id = norm_display(issue.get('rule_id'))
    message = norm_display(issue.get('message') or issue.get('desc'))
    return f"[{severity}] {rule_id}: {message}"
def _skill_issue_scope(skill: dict) -> str:
    return str(skill.get('name') or skill.get('skill_name') or '?')
def _iter_skill_issues(payload: dict, *, include_optimizations: bool = False):
    for skill in _as_entries(payload.get('skills')):
        skill_map = to_mapping(skill)
        label = _skill_issue_scope(skill_map)
        for issue in _as_entries(skill_map.get('issues')):
            yield label, issue
        if include_optimizations:
            for optimization in _as_entries(skill_map.get('optimizations')):
                yield label, optimization
def _iter_discoverability_issues(payload: dict):
    report = to_mapping(payload.get('discoverability'))
    label = _skill_issue_scope(report)
    if label == '?':
        label = '可发现性'
    for issue in _as_entries(report.get('issues')):
        yield label, issue
    for optimization in _as_entries(report.get('optimizations')):
        yield label, optimization
    yield from _iter_skill_issues(report, include_optimizations=True)
    for failed in _as_entries(report.get('failed_skills')):
        failed_map = to_mapping(failed)
        error = failed_map.get('error')
        if not error:
            continue
        failed_scope = str(
            failed_map.get('skill_dir') or _skill_issue_scope(failed_map))
        yield failed_scope, {
            "severity": "P2", "rule_id": "DIAG-COMPONENT",
            "message": f"可发现性体检不可用: {norm_display(error)}",
        }
def _iter_diag_issues(payload: dict):
    top = _as_entries(payload.get('issues')) + _as_entries(payload.get('findings'))
    for issue in top:
        yield '', issue
    yield from _iter_skill_issues(payload)
    yield from _iter_discoverability_issues(payload)
    best = to_mapping(payload.get('best_practices'))
    for item in _as_entries(best.get('irreparable')):
        yield '合规', item
    for key, label in (("discoverability", "可发现性"),
                       ("best_practices", "最佳实践"), ("hotness", "热度画像")):
        error = to_mapping(payload.get(key)).get("error")
        if error:
            yield label, {
                "severity": "P2", "rule_id": "DIAG-COMPONENT",
                "message": f"{label}体检不可用: {norm_display(error)}",
            }
def _safe_check(label: str, fn: Callable, error_factory: Callable[[Exception], Any]) -> Any:
    try:
        return fn()
    except Exception as exc:
        logger.warning("quick_diag: %s失败: %s", label, exc)
        return error_factory(exc)
def _quick_diag_batch(skills_root: str) -> dict:
    result = {
        "ok": True,
        "result": diag_skills_directory(skills_root),
        "mode": "batch",
    }
    result["discoverability"] = _safe_check(
        "批量可发现性体检",
        lambda: DiscoverabilityDiagnoser(skills_root).diag(),
        lambda exc: {"error": str(exc)[:200]},
    )
    return result
def _quick_diag_single(skill_dir: str) -> dict:
    result = {
        "ok": True,
        "result": SkillDiagnoser(skill_dir).run_full_diag(),
        "mode": "single",
    }
    attach_best_practices(result, skill_dir)
    result["hotness"] = _safe_check(
        "热度画像评估",
        lambda: evaluate_skill_hotness_for_dir(skill_dir),
        lambda exc: {"error": str(exc)[:200]})
    def _read_discoverability() -> dict:
        dh = quick_diag_skill_dir(skill_dir)
        if dh is None:
            return {
                "rule_id": "DIAG-COMPONENT",
                "error": f"可发现性体检未生成报告（非技能目录或入口文档不可用）: {skill_dir}",
            }
        return dh.to_dict()
    result["discoverability"] = _safe_check(
        "可发现性体检", _read_discoverability,
        lambda exc: {"error": str(exc)[:200]},
    )
    return result
def _existing_quick_diag_dir(raw: str, label: str) -> str:
    normalized = normalize_skill_dir(raw)
    if not os.path.isdir(normalized):
        raise ValueError(f"{label} 不存在或不是目录: {normalized}")
    return normalized
def quick_diag(skill_dir: str | None = None, skills_root: str | None = None,
               batch: bool = False) -> dict:
    if batch:
        root = _nonblank(
            os.fspath(skills_root) if skills_root is not None else "")
        if not root:
            raise ValueError("batch=True requires a non-empty skills_root")
        return _quick_diag_batch(
            _existing_quick_diag_dir(root, "batch=True skills_root"))
    target = _nonblank(
        os.fspath(skill_dir) if skill_dir is not None else "")
    if not target:
        raise ValueError("skill_dir 不能为空（空白路径不得回退到当前目录）")
    return _quick_diag_single(_existing_quick_diag_dir(target, "skill_dir"))
def _print_diag_result(result) -> None:
    if result is None:
        fail_cli("diag", "诊断引擎返回空产物（契约违约）")
    if _print_scalar_result(result, "诊断结果"):
        return
    print(f"诊断状态：ok={norm_display(result.get('ok'))}")
    payload = dict(to_mapping(result.get("result")))
    for _key in ('best_practices', 'discoverability', 'hotness'):
        _val = result.get(_key)
        if _val is not None:
            payload.setdefault(_key, _val)
    issues = list(_iter_diag_issues(payload))
    if issues:
        print(f"\n发现 {len(issues)} 个问题：")
        for i, (scope, issue) in enumerate(issues, 1):
            prefix = f"[{scope}] " if scope else ""
            print(f"  {i}. {prefix}{_issue_text(issue)}")
    else:
        print("未发现问题。")
def cmd_diag(args: argparse.Namespace) -> None:
    _require_skill_dir(args, "diag")
    print(f"正在诊断技能：{args.skill_dir}")
    _print_diag_result(run_cli_action(
        "diag", "诊断失败", quick_diag, args.skill_dir))
def _print_optimize_result(result) -> None:
    if result is None:
        fail_cli("optimize", "可发现性优化引擎返回空产物（契约违约）")
    if _print_scalar_result(result, "优化结果"):
        return
    print(f"优化状态：ok={norm_display(result.get('ok'))}, "
          f"fix={norm_display(result.get('apply_fixes_requested'))}")
    r = to_mapping(result.get("result"))
    if r.get("optimized_description"):
        print(f"优化后描述：{r['optimized_description']}")
    if r.get("optimized_keywords"):
        print(f"优化后关键词：{r['optimized_keywords']}")
    if r.get("issues"):
        print(f"问题：{r['issues']}")
    if r.get("warnings"):
        print(f"警告：{r['warnings']}")
def cmd_optimize(args: argparse.Namespace) -> None:
    _require_skill_dir(args, "optimize")
    print(f"正在优化技能可发现性：{args.skill_dir}")
    result = run_cli_action(
        "optimize", "优化失败", quick_optimize, args.skill_dir,
        fix=getattr(args, "fix", False))
    _print_optimize_result(result)
    if isinstance(result, dict) and not result.get("ok", True):
        message = field_of(result, "error", "") or field_of(
            result, "message", "可发现性优化失败")
        fail_cli("optimize", str(message))
def _print_version_history(skill_dir: str) -> None:
    def _render_history() -> None:
        for entry in get_version_history(skill_dir):
            if not isinstance(entry, dict):
                raise TypeError(f"历史条目异常结构: {entry!r}")
            print(f"  {norm_display(entry.get('timestamp'))}  "
                  f"{norm_display(entry.get('old_version'))} -> "
                  f"{norm_display(entry.get('new_version'))}  "
                  f"{norm_display(entry.get('description'))}")
    run_cli_action("bump-version", "版本历史读取失败", _render_history)
def _execute_bump_and_report(skill_dir: str, args: argparse.Namespace) -> None:
    entry = to_mapping(run_cli_action(
        "bump-version", "版本信息读取失败", read_skill_version_entry, skill_dir))
    print(f"当前版本: {field_of(entry, 'current', '') or '(未找到)'}")
    previous = field_of(entry, "previous", "")
    if previous:
        print(f"上一版本: {previous}")
    new_version = getattr(args, "version", "") or ""
    if not new_version:
        fail_cli("bump-version", "请提供 --version 新版本号（或用 --history 查看历史）")
    result = run_cli_action(
        "bump-version", "版本提升失败", bump_version, skill_dir, new_version,
        description=getattr(args, "description", "") or "",
        dry_run=bool(getattr(args, "dry_run", False)))
    _print_bump_result(result)
def _print_bump_result(result) -> None:
    if not isinstance(result, dict):
        fail_cli("bump-version", f"版本提升返回异常结构：{result!r}")
    message = field_of(result, "message", "")
    if result.get("status") != "ok":
        fail_cli("bump-version",
                  message or f"版本提升失败（status={result.get('status')!r}）")
    data = to_mapping(result.get("data"))
    if message:
        print(message)
    if field_of(data, "dry_run", False):
        print("(dry_run 预览，未写盘未通知)")
    else:
        print(f"历史落盘: {norm_display(data.get('history_recorded'))}"
              f"  监听器通知: {norm_display(data.get('notified'))} 个")
def cmd_bump_version(args: argparse.Namespace) -> None:
    skill_dir = _nonblank(getattr(args, "skill_dir", ""))
    if not skill_dir:
        fail_cli("bump-version",
                  "技能目录不能为空白（省略该参数时默认当前目录）")
    skill_dir = normalize_skill_dir(skill_dir)
    if not os.path.isfile(os.path.join(skill_dir, "SKILL.md")):
        fail_cli("bump-version", f"目录下无 SKILL.md: {skill_dir}")
    if getattr(args, "history", False):
        _print_version_history(skill_dir)
        return
    _execute_bump_and_report(skill_dir, args)
SKILL_COMMANDS = {
    "init": cmd_init,
    "package": cmd_package,
    "validate": cmd_validate,
    "diag": cmd_diag,
    "optimize": cmd_optimize,
    "bump-version": cmd_bump_version,
}
def register_cli_skill(sub) -> None:
    p_init = sub.add_parser("init", help="初始化新技能目录")
    p_init.add_argument("skill_name", help="技能名称（kebab-case）")
    p_init.add_argument("--path", default="", help="输出目录（默认 WORKSPACE_DIR 或当前目录）")
    p_init.add_argument("--description", default="", help="技能描述")
    p_init.add_argument("--resources", default="", help="资源目录，逗号分隔：scripts,references,assets")
    p_pkg = sub.add_parser("package", help="打包技能为 .skill 文件")
    p_pkg.add_argument("skill_dir", help="技能目录路径")
    p_pkg.add_argument("--output", default="", help="输出目录（默认当前目录）")
    p_val = sub.add_parser("validate", help="校验技能目录")
    p_val.add_argument("skill_dir", help="技能目录路径")
    p_diag = sub.add_parser("diag", help=f"代码诊断（{_PACKAGE_NAME} 增强）")
    p_diag.add_argument("skill_dir", help="技能目录路径")
    p_opt = sub.add_parser("optimize", help=f"可发现性优化（{_PACKAGE_NAME} 增强）")
    p_opt.add_argument("skill_dir", help="技能目录路径")
    p_opt.add_argument("--fix", action="store_true", help="将优化结果写回 SKILL.md frontmatter")
    p_bv = sub.add_parser("bump-version", help="技能版本提升（SKILL.md 同步+历史落盘+监听器广播）")
    p_bv.add_argument("skill_dir", nargs="?", default=".", help="技能目录（默认当前目录）")
    p_bv.add_argument("--version", help="新版本号（如 1.2.0）")
    p_bv.add_argument("--description", default="", help="变更描述（记入历史）")
    p_bv.add_argument("--dry-run", action="store_true", help="仅预览不实际执行")
    p_bv.add_argument("--history", action="store_true", help="查看版本变更历史")
def _normalize_validation_result(result: Any, tag: str) -> tuple[bool, list[str]]:
    if not isinstance(result, (tuple, list)) or len(result) != 2:
        fail_cli(tag, "校验结果违约（期望 (bool, 错误列表)）: "
                  f"{type(result).__name__}")
    valid, errors = result
    if not isinstance(valid, bool):
        fail_cli(tag, "校验状态类型违约（期望 bool）: "
                 f"{type(valid).__name__}")
    if errors is None:
        return valid, []
    if isinstance(errors, str):
        return valid, [errors]
    if isinstance(errors, (list, tuple)):
        return valid, [str(err) for err in errors]
    fail_cli(tag, f"校验错误列表违约: {type(errors).__name__}")
_BYTES_PER_MB = 1024 * 1024
@logged_cli_command("cmd_prune_backups")
def cmd_prune_backups(args: argparse.Namespace) -> int:
    if args.retention_days < 0:
        fail_cli("prune-backups",
                  f"保留期不能为负数: {args.retention_days}"
                  "（负值会使裁剪截止点落到未来，全部备份被误判超期删除）",
                  detail=f"非法保留期: {args.retention_days} 天（负值 cutoff 落在未来，全量误删备份）")
    report = run_cli_action(
        "prune-backups", "备份裁剪执行失败", prune_all_backup_roots,
        retention_days=args.retention_days,
        dry_run=not args.apply,
    )
    report = require_dict(report, "prune-backups", "裁剪产物")
    _render_prune_report(report, retention_days=args.retention_days, apply=bool(args.apply))
    total = to_mapping(report.get("total"))
    return 1 if num_of(total.get("errors")) else 0
def _format_prune_root_line(item: dict) -> str:
    stats = item.get("stats")
    if not item.get("exists"):
        state = "不存在"
    elif not isinstance(stats, dict):
        state = "-"
    else:
        state = (f"文件 {field_of(stats, 'deleted_files')} / 目录 {field_of(stats, 'deleted_dirs')}"
                 f" / 释放 {num_of(stats.get('freed_bytes')) / _BYTES_PER_MB:.1f}MB"
                 f" / 保护 {field_of(stats, 'protected')}")
    return f"  - {field_of(item, 'path', '?')}: {state}"
def _format_prune_total(total: dict) -> str:
    return (f"合计: 扫描 {field_of(total, 'scanned')} 项, "
            f"删除文件 {field_of(total, 'deleted_files')} / "
            f"目录 {field_of(total, 'deleted_dirs')}, "
            f"释放 {num_of(total.get('freed_bytes')) / _BYTES_PER_MB:.1f}MB, "
            f"错误 {field_of(total, 'errors')}")
def _render_prune_report(report: dict, retention_days: int, apply: bool) -> None:
    mode = "已执行删除" if apply else "预览(dry-run)"
    print(f"备份根清理 [{mode}]  保留期: {retention_days} 天")
    for item in _as_entries(report.get("roots")):
        if not isinstance(item, dict):
            continue
        print(_format_prune_root_line(item))
    total = to_mapping(report.get("total"))
    print(_format_prune_total(total))
    if not apply and (total.get("deleted_files") or total.get("deleted_dirs")):
        print("提示: 以上为预览，未实际删除；加 --apply 执行清理")
@logged_cli_command("cmd_log_coverage")
def cmd_log_coverage(args: argparse.Namespace) -> None:
    report = run_cli_action(
        "log-coverage", "日志覆盖度审计失败", audit_log_coverage,
        target_dir=args.target_dir,
        include_tests=args.include_tests,
    )
    report = require_dict(report, "log-coverage", "审计产物")
    if args.json:
        emit_json_report(report)
        if report.get("status") != "ok":
            sys.exit(1)
        return
    if report.get("status") != "ok":
        fail_cli("log-coverage", str(field_of(report, "message", "unknown error")))
    _render_log_coverage_report(report)
def _render_log_coverage_report(report: dict) -> None:
    s = to_mapping(report.get("summary"))
    cb = to_mapping(report.get("codebase"))
    sp = to_mapping(report.get("silent_paths"))
    _render_lc_overview(report, s, sp)
    _render_zero_samples(cb)
    _render_silent_hotspots(sp)
    _render_lc_findings(s, report)
    print("提示: 加 --json 获取机器可读全量报告（含零暴露模块完整清单）")
def _render_lc_overview(report: dict, s: dict, sp: dict) -> None:
    print(f"日志覆盖度审计  目标: {field_of(report, 'target_dir', '')}")
    print(f"  模块总数 {field_of(s, 'total_modules')} | 埋点率 {num_of(s.get('instrumentation_rate')) * 100:.0f}%"
          f" | 运行时覆盖率 {num_of(s.get('runtime_coverage_rate')) * 100:.0f}%"
          f" | 耗时 {field_of(s, 'elapsed_s')}s")
    print(f"  零埋点模块 {field_of(s, 'zero_instrumentation_count')} 个"
          f" | 运行时盲区(未执行) {field_of(s, 'blind_not_executed_count')} 个")
    print(f"  静默 except 块 {field_of(s, 'silent_except_total')} 处"
          f"（{field_of(sp, 'modules_with_silent')} 模块）"
          f" | log_swallowed 生产者 {field_of(s, 'swallow_producers')}")
    _render_test_channel(report)
def _render_test_channel(report: dict) -> None:
    tc = to_mapping(report.get("test_channel"))
    if not tc.get("applicable"):
        return
    if tc.get("active"):
        print(f"  测试面已接入统一日志（写 {field_of(tc, 'writer', 'log_config')}"
              f" / 读 {field_of(tc, 'reader', 'log_analysis')}）"
              f" | 覆盖模块 {field_of(tc, 'covered_modules')} 个"
              f" | 留痕用例 {field_of(tc, 'cases')} 条"
              f" | 窗口内有证据模块 {field_of(tc, 'modules_with_evidence')} 个")
        stale = field_of(tc, "no_recent_evidence", [])
        if stale:
            print(f"  无近期证据模块 {len(stale)} 个（滚动窗口外，非未执行）")
    else:
        print(f"  测试面未接入统一日志: hooks={field_of(tc, 'wiring', {})}")
def _render_zero_samples(cb: dict) -> None:
    zero_src = _as_entries(cb.get("zero_instrumentation_sample"))
    zero_sample = [field_of(z, "module", "?")
                   for z in zero_src
                   if isinstance(z, dict)]
    if zero_sample:
        print(f"  零埋点样本: {', '.join(str(m) for m in zero_sample)}")
def _render_silent_hotspots(sp: dict) -> None:
    hotspots = sp.get("hotspots")
    if not isinstance(hotspots, list):
        return
    for hotspot in hotspots[:5]:
        if not isinstance(hotspot, dict):
            continue
        print(f"  静默热点: {field_of(hotspot, 'module', '?')} "
              f"x{field_of(hotspot, 'count')} "
              f"@line {field_of(hotspot, 'positions', [])}")
def _render_lc_findings(s: dict, report: dict) -> None:
    print(f"  发现 {field_of(s, 'finding_count')} 条:")
    findings = _as_entries(report.get("findings"))
    for f in findings:
        if not isinstance(f, dict):
            continue
        print(f"   - [{field_of(f, 'severity', '?')}] {field_of(f, 'title', '')}")
        print(f"     动作: {field_of(f, 'suggested_action', '')}")
def _load_memory_results(args: argparse.Namespace) -> list:
    memory_path = _nonblank(getattr(args, "memory", ""))
    if not memory_path:
        return []
    loaded = load_json_file("memory-enhance", memory_path,
                             missing_label="记忆搜索结果文件不存在",
                             parse_label="记忆搜索结果解析失败")
    if isinstance(loaded, list):
        return loaded
    if isinstance(loaded, dict):
        results = loaded.get("results")
        if not isinstance(results, list):
            fail_cli(
                "memory-enhance",
                "记忆搜索结果违约：results 字段须为列表，"
                f"实际为 {type(results).__name__}",
            )
        return results
    fail_cli(
        "memory-enhance",
        "记忆搜索结果须为列表或包含 results 列表的 JSON 对象，"
        f"实际为 {type(loaded).__name__}",
    )
@logged_cli_command("cmd_memory_enhance")
def cmd_memory_enhance(args: argparse.Namespace) -> None:
    report_path = args.report
    pipeline_result = require_dict(
        load_json_file("memory-enhance", report_path,
                        missing_label="管线报告不存在",
                        parse_label="报告解析失败"),
        "memory-enhance", "管线报告")
    memory_results: list = _load_memory_results(args)
    enhanced = run_cli_action(
        "memory-enhance", "记忆增强执行失败",
        enhance_pipeline_with_memory,
        pipeline_result, prepare_diagnostic_context(memory_results))
    enhanced = require_dict(enhanced, "memory-enhance", "记忆增强产物")
    out_path = (_nonblank(getattr(args, "output", ""))
                or (os.path.splitext(report_path)[0]
                    + ".memory_enhanced.json"))
    _write_enhanced_report(out_path, enhanced)
    emit_json_report(_memory_enhance_summary(out_path, enhanced))
def _write_enhanced_report(path: str, enhanced: dict) -> None:
    out_dir = os.path.dirname(os.path.abspath(path))
    if not os.path.isdir(out_dir):
        fail_cli("memory-enhance", f"增强报告写入失败: 输出目录不存在: {out_dir}")
    try:
        write_json_payload(enhanced, path)
    except JSON_REPORT_ERRORS as e:
        fail_cli("memory-enhance", f"增强报告写入失败: {e}", cause=e)
def _memory_enhance_summary(out_path: str, enhanced: dict) -> dict:
    bridge = to_mapping(enhanced.get("_memory_bridge"))
    memory_ops = _as_entries(enhanced.get("_memory_operations"))
    osc_warnings = _as_entries(enhanced.get("_oscillation_warnings"))
    return {
        "status": "ok",
        "data": {
            "output": out_path,
            "bridge_status": field_of(bridge, "status", "unknown"),
            "bridge_version": field_of(bridge, "version", ""),
            "cv_tunings": field_of(bridge, "cv_tunings_generated"),
            "memory_ops": len(memory_ops),
            "oscillation_warnings": len(osc_warnings),
        },
    }
def _extract_trigger_probe_views(res: dict) -> tuple[dict, dict]:
    data = to_mapping(res.get("data"))
    probe = to_mapping(data.get("probe"))
    return probe, to_mapping(probe.get("evidence"))
def _record_soft_probe_if_needed(executed: bool, status: str,
                                 args: argparse.Namespace, probe: dict,
                                 evidence: dict) -> None:
    if executed or status != "soft" or not args.skill:
        return
    record_trigger_event(args.skill, "soft",
                         str(field_of(probe, "confidence", "")),
                         args.text, evidence, source="cli",
                         extra={"executed": False})
def _print_evidence_values(label: str, values: Any) -> None:
    items = _as_entries(values)
    if items:
        print(f"  {label}: {', '.join(str(v) for v in items)}")
@logged_cli_command("cmd_trigger")
def cmd_trigger(args: argparse.Namespace) -> None:
    executed = bool(args.execute or args.force)
    if executed and not args.skill:
        fail_cli("trigger", "--execute/--force 需要 --skill 指定目标技能/项目目录")
    res = run_cli_action(
        "trigger", "触发探测执行失败", run_pipeline_from_trigger,
        args.text, args.skill or "",
        execute=executed,
        allow_soft=bool(args.allow_soft),
        force=bool(args.force),
        full=not bool(getattr(args, "single_step", False)))
    res = require_dict(res, "trigger", "触发探测产物")
    status = field_of(res, "status", "unknown")
    probe, evidence = _extract_trigger_probe_views(res)
    _record_soft_probe_if_needed(executed, status, args, probe, evidence)
    if args.json:
        emit_json_report(res)
    else:
        _render_trigger_probe(res, probe, evidence)
    if status == "error":
        sys.exit(1)
def _render_trigger_probe(res: dict, probe: dict, evidence: dict) -> None:
    print(f"触发探测: {field_of(res, 'status', 'unknown')} | "
          f"{field_of(res, 'message', '')}")
    if probe:
        print(f"  decision={norm_display(probe.get('decision'))} "
              f"confidence={norm_display(probe.get('confidence'))} "
              f"recommendation={norm_display(probe.get('recommendation'))}")
    for label, key in (("强词命中", "strong_hits"), ("自定义词", "custom_hits"),
                       ("弱词", "weak_tokens"), ("语境词", "context_tokens")):
        _print_evidence_values(label, evidence.get(key))
    fuzzy = to_mapping(evidence.get("fuzzy"))
    if fuzzy.get("seed"):
        print(f"  模糊近义: {fuzzy.get('seed')} "
              f"(score={norm_display(fuzzy.get('score'))})")
    _print_evidence_values("否定语境拦截", evidence.get("negatives_blocked"))
    data = to_mapping(res.get("data"))
    pipeline_status = data.get("pipeline_status")
    if pipeline_status:
        print(f"  管线状态: status={norm_display(pipeline_status)} "
              f"phase={norm_display(data.get('phase'))}")
    step = to_mapping(data.get("pipeline_step"))
    if step:
        print(f"  管线步骤: phase={norm_display(step.get('phase'))} "
              f"is_terminal={norm_display(step.get('is_terminal'))}")
@logged_cli_command("cmd_trigger_mine")
def cmd_trigger_mine(args: argparse.Namespace) -> None:
    if args.min_weight is not None and args.min_weight < 1:
        fail_cli("trigger-mine",
                  f"--min-weight 须为正整数: {args.min_weight}")
    weight_kwargs = {} if args.min_weight is None else {"min_weight": args.min_weight}
    report = run_cli_action(
        "trigger-mine", "留痕挖掘执行失败", mine_trigger_events,
        args.skill, **weight_kwargs)
    report = require_dict(report, "trigger-mine", "挖掘产物")
    if args.json:
        emit_json_report(report)
        return
    print(render_miner_report(report))
@logged_cli_command("cmd_deps")
def cmd_deps(args: argparse.Namespace) -> int:
    if args.timeout is not None and args.timeout <= 0:
        fail_cli("deps", f"超时须为正整数秒数: {args.timeout}",
                  detail=f"非法 pip 超时: {args.timeout}s")
    timeout_kwargs = {} if args.timeout is None else {"timeout": args.timeout}
    payload = to_mapping(
        ensure_dependencies(auto_install=not args.check, **timeout_kwargs))
    if args.json:
        print(json_text(payload))
    else:
        print(norm_display(field_of(payload, "message", "")))
    return 0 if field_of(payload, "status", "") == "ok" else 1
def register_cli_maintenance(sub) -> None:
    p_pb = sub.add_parser("prune-backups",
                          help="备份根生命周期清理（归口根+旧独立根超期快照，默认预览）")
    p_pb.add_argument("--retention-days", type=int,
                      default=BACKUP_RETENTION_DAYS,
                      help="保留天数（默认与 BACKUP_RETENTION_DAYS 同口径）")
    p_pb.add_argument("--apply", action="store_true",
                      help="实际删除（默认 dry_run 只统计不删除）")
    p_lc = sub.add_parser("log-coverage",
                          help="日志覆盖度审计（埋点/运行时暴露/静默通道三层，代码增删自动反映）")
    p_lc.add_argument("--target-dir", default=None,
                      help=f"被审计代码库根目录（默认 {_PACKAGE_NAME} 包自身）")
    p_lc.add_argument("--include-tests", action="store_true",
                      help="把 tests/ 纳入扫描（默认排除）")
    p_lc.add_argument("--json", action="store_true",
                      help="输出机器可读 JSON 全量报告")
    p_me = sub.add_parser("memory-enhance",
                          help="管线报告记忆增强（v4 全链路事后增强）")
    p_me.add_argument("report", help="管线报告 JSON 路径（含 stage1_diagnosis/stage4_treatment_execution 等键）")
    p_me.add_argument("--memory", help="memory(search) 结果 JSON 路径（列表或 {results: [...]}；省略则无记忆上下文）")
    p_me.add_argument("-o", "--output", help="增强后报告输出路径（默认 <report>.memory_enhanced.json）")
    p_tg = sub.add_parser(
        "trigger",
        help=("管线触发探测（三层漏斗：强词/弱词语境门/模糊近义；"
              "强命中默认推进完整管线到 all_completed）"))
    p_tg.add_argument("--text", required=True, help="用户话语原文")
    p_tg.add_argument("--skill", default=None,
                      help="目标技能/项目目录（自定义词表与留痕用；省略则仅探测）")
    p_tg.add_argument("--json", action="store_true",
                      help="输出机器可读 JSON（含 probe 证据链）")
    p_tg.add_argument("--execute", action="store_true",
                      help=("命中后推进管线（默认全管线到 all_completed；"
                            "软命中需 --allow-soft）"))
    p_tg.add_argument("--single-step", action="store_true",
                      help=("仅单步推进（诊断用；触发强制门禁会判为未完成并阻断交付）"))
    p_tg.add_argument("--allow-soft", action="store_true",
                      help="软命中（弱词语境/模糊近义）亦允许执行（人工确认后使用）")
    p_tg.add_argument("--force", action="store_true",
                      help="miss 强制接管推进（AI 判定命中场景；隐含 --execute，须配 --skill）")
    p_tm = sub.add_parser("trigger-mine",
                          help="触发留痕词表挖掘（读 log/trigger_events.jsonl → 建议新词报告）")
    p_tm.add_argument("--skill", required=True,
                      help="目标技能/项目目录（只作自定义词表来源；留痕统一读工具日志目录 log/，不随该参数变化）")
    p_tm.add_argument("--min-weight", type=int, default=None,
                      help="候选词最小权重（省略时由挖掘器取自身默认；1 为全量探索）")
    p_tm.add_argument("--json", action="store_true",
                      help="输出机器可读 JSON 报告")
    p_sc = sub.add_parser("self-check",
                          help=f"{_PACKAGE_NAME} 技能包自健康检查"
                               "（门面可导入性/Python版本/依赖可用性）")
    p_sc.add_argument("--json", action="store_true", help="输出 JSON 报告到报告目录")
    p_sc.add_argument("--fix", action="store_true", help="对 SKILL.md 工作流违规执行自动修复并复验")
    p_sc.add_argument("--output", help="JSON 报告输出路径（默认报告目录/self_check_report.json）")
    p_dep = sub.add_parser(
        "deps", help="依赖治理：第三方包/测试工具链/外部工具检测与 pip 补装")
    p_dep_group = p_dep.add_mutually_exclusive_group(required=True)
    p_dep_group.add_argument("--check", action="store_true",
                             help="仅检测缺失，不安装")
    p_dep_group.add_argument("--install", action="store_true",
                             help="检测缺失并自动 pip 安装（含测试工具链与 pytest/ruff）")
    p_dep.add_argument("--json", action="store_true",
                       help="以 JSON 输出结果（供 AI/脚本消费）")
    p_dep.add_argument("--timeout", type=int, default=None,
                       help="pip 安装超时秒数（省略时由依赖管理器取自身默认，须为正整数）")
MAINTENANCE_COMMANDS = {
    "deps": cmd_deps,
    "self-check": cmd_self_check,
    "log-coverage": cmd_log_coverage,
    "memory-enhance": cmd_memory_enhance,
    "prune-backups": cmd_prune_backups,
    "trigger": cmd_trigger,
    "trigger-mine": cmd_trigger_mine,
}
def deps_gate_needed(argv: list[str]) -> bool:
    if os.environ.get(SKIP_DEPS_ENV_VAR) == "1":
        return False
    if not argv or "--help" in argv or "-h" in argv:
        return False
    return argv[:1] != ["deps"]
def deps_gate() -> None:
    try:
        missing = check_missing()
        if not has_missing(missing):
            return
        logger.warning(
            "[deps_gate] 检测到依赖缺失: modules=%s tools=%s toolchain=%s，自动补装中",
            missing["missing_modules"], missing["missing_tools"],
            missing["missing_toolchain"],
        )
        print(f"[{_PACKAGE_NAME}] 检测到依赖缺失，自动补装中"
              f"（首次约 1-3 分钟；{SKIP_DEPS_ENV_VAR}=1 可跳过）...")
        result = ensure_dependencies(auto_install=True)
        logger.info("[deps_gate] 依赖自举: %s", result["message"])
        print(f"[{_PACKAGE_NAME}] 依赖自举: {result['message']}")
    except Exception as exc:
        logger.warning("[deps_gate] 依赖自检异常，降级放行: %s", exc)
        print(f"[{_PACKAGE_NAME}] 依赖自检跳过: {exc}")

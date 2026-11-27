from __future__ import annotations

import argparse
import inspect
import json
import logging
import math
import os
import sys
import time
from functools import wraps
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    _pkg_parent = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    if _pkg_parent not in sys.path:
        sys.path.insert(0, _pkg_parent)
from jwsgj.build_contract import (
    INIT_CONTRACT,
    SKILL_CREATION_CONTRACT,
    requires_contract,
)
from jwsgj.build_discover_sixdim import (
    apply_six_dim_enhancement,
    average_optimization_score,
    build_discoverability_section,
    build_script_score_section,
    compose_optimization_score,
    generate_skill_md_template,
)
from jwsgj.build_preflight_guard import (
    _ensure_structure,
    _path_arg,
    _read_raw_bytes,
    _read_skill_md_checked,
    _write_back_result_content,
    attach_validation_result,
    build_creation_validation_assets,
    check_runtime_temp_residue,
    create_resource_dirs,
    create_skill_directories,
    ensure_fupan_hook,
    ensure_init_module_safety,
    ensure_root_dir,
    ensure_safe_content,
    parse_resources,
    record_fix_entries,
    resolve_target_dir,
    run_post_create_quality_gates,
    validate_skill,
)
from jwsgj.build_script_generation import (
    build_creation_script_assets,
    generate_optimized_example_script,
    write_init_module,
)
from jwsgj.build_skill_consistency import (
    MetadataOptimizationResult,
    SkillMetadataOptimizer,
    generate_optimized_frontmatter,
    validate_creation_inputs,
)
from jwsgj.build_skill_discovery import (
    apply_full_discoverability,
    optimize_creation_discoverability,
)
from jwsgj.build_skill_md_generate import (
    build_creation_result,
    ensure_valid_skill_name,
    is_path_input,
    prepare_skill_metadata,
    profile_created_skill,
)
from jwsgj.build_skill_md_optimize import (
    DescriptionOptimizer,
    attach_best_practices,
    run_trigger_test_gate,
)
from jwsgj.build_skill_md_quality import (
    SKILL_MD_MAX_LINES,
    validate_create_input,
)
from jwsgj.build_skill_md_rewrite import (
    append_role_scenario_section,
    existing_skill_category,
    inject_script_usage_guide,
    merged_frontmatter_preview,
    read_skill_md_text,
    update_skill_md,
    write_optimized_frontmatter,
    write_skill_md,
)
from jwsgj.build_text_document import (
    iter_skill_dirs,
    normalize_newlines,
    normalize_str_list,
    normalize_text,
    write_text_preserving_form,
)
from jwsgj.build_text_frontmatter import (
    DEFAULT_SKILL_VERSION,
    INLINE_KEYWORDS_MAX,
    ensure_complete_frontmatter,
    frontmatter_keywords,
    parse_frontmatter_dict,
    parse_frontmatter_text,
    parse_skill_md_text,
    read_skill_md,
    render_minimal_skill_md,
)
from jwsgj.diag_guard_io import (
    normalize_out_path,
    safe_delete,
)
from jwsgj.diag_types_vocab import (
    CAT_DISCOVERABILITY,
    FIELD_DISCOVERABILITY_INDEX,
    FIELD_OPTIMIZED_DESCRIPTION,
    FIELD_OPTIMIZED_KEYWORDS,
)
from jwsgj.log_config import (
    log_swallowed,
    setup_logging,
    write_module_run,
)

_log = logging.getLogger(__name__)
__all__ = [
    "DEFAULT_OPTIMIZE_DRY_RUN",
    "DEFAULT_OPTIMIZE_FIX",
    "apply_trigger_feedback",
    "build_init",
    "build_init_result",
    "build_preflight",
    "check_engineering_practices",
    "create_skill_with_full_discoverability",
    "generate_guided_template",
    "get_existing_skills",
    "init_skill",
    "optimize_main",
    "optimize_single_skill",
    "optimize_skill",
    "optimize_skills_batch",
    "parse_skill_metadata",
    "quick_optimize",
    "quick_optimize_batch",
    "run_guided_creation",
]
_log.info("build_preflight 已加载: %d 项导出", len(__all__))
if __package__ in (None, ""):
    _pkg_parent = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    if _pkg_parent not in sys.path:
        sys.path.insert(0, _pkg_parent)
_FALLBACK_SKILL_NAME = "skill"
DEFAULT_OPTIMIZE_FIX = False
DEFAULT_OPTIMIZE_DRY_RUN = False
def guided_skill_content(skill_name: str, description: str,
                         content: str = "",
                         version: str = DEFAULT_SKILL_VERSION) -> tuple[str, dict]:
    skill_name = normalize_text(skill_name)
    description = normalize_text(description)
    version = normalize_text(version)
    content = normalize_newlines(normalize_text(content))
    report = {"name": skill_name, "steps": [], "fixed": False,
              "step_groups": {}}
    def _record(group: str, entries: list[str]) -> None:
        if not entries:
            return
        report["step_groups"].setdefault(group, []).extend(entries)
        report["steps"].extend(entries)
    if not content:
        content, template_step = generate_guided_template(
            skill_name, description, version)
        _record("content", [template_step])
        report["fixed"] = True
    content, fm_logs = ensure_complete_frontmatter(content, skill_name, description, version)
    _record("frontmatter", fm_logs)
    if any("无法" not in entry for entry in fm_logs):
        report["fixed"] = True
    content, fupan_logs = ensure_fupan_hook(content)
    _record("fupan_hook", fupan_logs)
    if fupan_logs:
        report["fixed"] = True
    content, safety_logs = ensure_safe_content(content)
    _record("safety", safety_logs)
    if any("已修复" in entry or "已脱敏" in entry for entry in safety_logs):
        report["fixed"] = True
    report["content"] = content
    return content, report
def check_engineering_practices(content: Any) -> tuple[bool, str]:
    if not isinstance(content, str) or not content.strip():
        return (False, '工程实践检查: 内容为空')
    issues = []
    line_count = len(content.splitlines())
    if line_count > SKILL_MD_MAX_LINES:
        issues.append(f'SKILL.md 行数 {line_count} > {SKILL_MD_MAX_LINES}，建议拆分到 references/')
    if issues:
        return (False, '工程实践建议: ' + '; '.join(issues))
    return (True, '工程实践检查通过')
def _run_content_fixes(name: str, description: str, content: str,
                       version: str, fixes: list[dict],
                       warnings: list[dict]) -> tuple[str, bool]:
    result_content, content_report = guided_skill_content(
        name, description, content, version
    )
    groups = content_report.get("step_groups")
    if not isinstance(groups, dict):
        groups = {"content": content_report.get("steps", [])}
    content_blocked = False
    for step, entries in groups.items():
        warning_start = len(warnings)
        record_fix_entries(step, entries, fixes, warnings)
        for warning in warnings[warning_start:]:
            detail = str(warning.get("detail", ""))
            if "无法自动修复" in detail or "不可自动修复" in detail:
                warning["severity"] = "blocker"
                content_blocked = True
    return result_content, content_blocked
def _collect_description_suggestions(description: str,
                                     keywords: list[str] | None = None) -> list:
    suggestions: list = []
    if not description:
        return suggestions
    try:
        opt = DescriptionOptimizer()
        r = opt.analyze(description, keywords=keywords)
        suggestions = r.suggestions
    except Exception as exc:  # noqa: BLE001
        _log.warning("_collect_description_suggestions: 描述优化器异常，按无建议降级: %s",
                     exc)
    return suggestions
def _normalize_creation_inputs(
        description: str, content: str, version: str) -> tuple[str, str, str]:
    return (normalize_text(description), normalize_text(content),
            normalize_text(version) or DEFAULT_SKILL_VERSION)
def _normalize_creation_target(
        skill_dir: Any, output_dir: Any) -> tuple[str, str | None]:
    if skill_dir and output_dir:
        return "", "目标目录参数冲突：skill_dir 与 output_dir 只能提供一个"
    raw_target = skill_dir or output_dir
    if raw_target is None or (isinstance(raw_target, str)
                              and not raw_target.strip()):
        return "", "目标目录为空：必须提供 skill_dir 或 output_dir"
    if not is_path_input(raw_target):
        return "", f"目标目录路径类型无效: {type(raw_target).__name__}"
    target = _path_arg(raw_target)
    if not target:
        return "", f"目标目录路径无效: {raw_target!r}"
    return target, None
def _discover_creation_existing_skills(
        target_dir: str, existing_skills: list[str] | None) -> list[str]:
    if existing_skills is not None:
        return existing_skills
    if not target_dir:
        return []
    # 相对路径（如 "my-skill"）的 normpath 父目录是空串，实际父目录是 cwd；
    # 提前返回空清单会让相对路径下的兄弟技能名冲突检测静默失效。
    parent = os.path.dirname(os.path.normpath(target_dir)) or "."
    discovered = get_existing_skills(parent)
    own = os.path.basename(os.path.normpath(target_dir))
    if not own:
        return discovered
    return [name for name in discovered
            if os.path.normcase(name) != os.path.normcase(own)]
def _enrich_created_skill(result_name: str, description: str,
                          result_content: str,
                          warnings: list[dict]) -> dict[str, Any]:
    effective_desc = (description if description.strip()
                      else parse_frontmatter_text(result_content)[1])
    skill_type, design_pattern, _pattern_hint = profile_created_skill(
        result_name, effective_desc, result_content)
    keywords = frontmatter_keywords(
        parse_frontmatter_dict(result_content).get("keywords"))
    desc_suggestions = _collect_description_suggestions(effective_desc, keywords)
    six_dim_enhanced, six_dim_result, result_content = apply_six_dim_enhancement(
        result_name, effective_desc, skill_type, result_content)
    eng_ok, eng_msg = check_engineering_practices(result_content)
    if not eng_ok:
        warnings.append({"step": "engineering_practices",
                         "severity": "warning", "detail": eng_msg})
    return {"content": result_content, "skill_type": skill_type,
            "design_pattern": design_pattern,
            "description_suggestions": desc_suggestions,
            "six_dim_enhanced": six_dim_enhanced,
            "six_dim_result": six_dim_result}
def _reject_invalid_guided_target(func):
    signature = inspect.signature(func)
    @wraps(func)
    def _checked(*args, **kwargs):
        bound = signature.bind(*args, **kwargs)
        bound.apply_defaults()
        raw_target = (bound.arguments.get("skill_dir")
                      or bound.arguments.get("output_dir"))
        if raw_target and not is_path_input(raw_target):
            raw_name = bound.arguments.get("skill_name", "")
            return _error_result(
                normalize_text(raw_name) or _FALLBACK_SKILL_NAME,
                f"目标目录路径类型无效: {type(raw_target).__name__}")
        return func(*args, **kwargs)
    return _checked
@_reject_invalid_guided_target
@requires_contract(SKILL_CREATION_CONTRACT)
def run_guided_creation(skill_name: str, description: str = "",
                        content: str = "", skill_dir: str = "",
                        output_dir: str = "",
                        resources: list[str] | None = None,
                        existing_skills: list[str] | None = None,
                        version: str = DEFAULT_SKILL_VERSION,
                        create_missing: bool = True,
                        dry_run: bool = False) -> dict:
    fixes = []
    warnings = []
    description, content, version = _normalize_creation_inputs(
        description, content, version)
    result_dir, target_error = _normalize_creation_target(skill_dir, output_dir)
    existing_skills = _discover_creation_existing_skills(
        result_dir, existing_skills)
    fixed_name, name_logs = ensure_valid_skill_name(skill_name, existing_skills)
    if fixed_name != skill_name:
        fixes.append({"step": "naming", "action": "normalize", "detail": f"{skill_name} → {fixed_name}"})
    record_fix_entries("naming", name_logs, fixes, warnings)
    result_name = fixed_name
    if target_error is not None:
        return {
            "ok": False,
            "status": "error",
            "error": target_error,
            "skill_name": result_name,
            "fixes": fixes,
            "warnings": warnings,
            "blocked": True,
            "content_written": False,
            "target_dir": "",
            "skill_md_path": "",
        }
    target_dir_name = _dir_basename(result_dir)
    target_name_blocked = bool(
        target_dir_name and result_name != target_dir_name)
    if target_name_blocked:
        warnings.append({
            "step": "naming", "severity": "blocker",
            "detail": (f"目标目录名 '{target_dir_name}' 与规范化技能名 "
                       f"'{result_name}' 不一致；请使用同名 kebab-case 目录，"
                       "已阻断写盘"),
        })
    skill_md_existed = _core_file_present(result_dir, "SKILL.md")
    init_py_existed = _core_file_present(result_dir, "__init__.py")
    result_content, content_blocked = _run_content_fixes(
        result_name, description, content, version, fixes, warnings)
    blocked = (content_blocked or target_name_blocked or _ensure_structure(
        result_dir, resources, fixes, warnings, create_missing, dry_run))
    if create_missing and not dry_run:
        warnings.extend(check_runtime_temp_residue(result_dir))
    if result_dir and create_missing and not dry_run and not blocked:
        init_fixes, init_warnings = ensure_init_module_safety(result_dir)
        fixes.extend(init_fixes)
        warnings.extend(init_warnings)
        if any(item.get("severity") == "blocker"
               for item in init_warnings):
            blocked = True
    enrich = _enrich_created_skill(
        result_name, description, result_content, warnings)
    persisted = _persist_created_content(
        result_dir, enrich["content"], existed=skill_md_existed,
        blocked=blocked, create_missing=create_missing and not dry_run,
        fixes=fixes, warnings=warnings)
    if persisted is False:
        blocked = True
        warnings.append({
            "step": "write_back", "severity": "blocker",
            "detail": "新建 SKILL.md 最终内容未持久化，创建结果不可用",
        })
    # 阻断即不落盘：回收本次新建且最终内容未持久化的骨架核心文件，
    # 避免重试时被误判为已存在技能而丢弃调用方传入的描述与正文。
    if (blocked and persisted is None and create_missing and not dry_run
            and is_path_input(result_dir)):
        _discard_unpersisted_skeleton(
            result_dir, skill_md_existed, init_py_existed, warnings)
    creation_result = build_creation_result(
        result_name, fixes, warnings, blocked, enrich)
    creation_result["content_written"] = persisted is True
    creation_result["status"] = "ok" if not blocked else "error"
    creation_result["target_dir"] = result_dir
    creation_result["skill_md_path"] = (
        os.path.join(result_dir, "SKILL.md") if result_dir else "")
    if blocked and not creation_result.get("error"):
        blocker_details = [
            str(item.get("detail", "")) for item in warnings
            if isinstance(item, dict)
            and item.get("severity") == "blocker"
            and item.get("detail")]
        creation_result["error"] = (
            "；".join(blocker_details) or "创建被门禁阻断")
    if create_missing and not dry_run and not blocked and result_dir:
        validation_ok, validation_errors = _validate_created_skill(result_dir)
        run_post_create_quality_gates(
            result_dir, creation_result["skill_md_path"])
        _apply_post_create_validation_outcome(
            creation_result, validation_ok, validation_errors)
    return creation_result
def _core_file_present(result_dir: Any, filename: str) -> bool:
    if not is_path_input(result_dir):
        return False
    try:
        return os.path.isfile(os.path.join(str(result_dir), filename))
    except OSError as exc:
        _log.debug("_core_file_present: %s 存在性探测失败: %s",
                   filename, exc)
        return True
def _recycle_fresh_skeleton_file(path: str) -> str | None:
    if os.name == "nt":
        return None if safe_delete(path) else "回收站通道不可用"
    try:
        os.remove(path)
    except FileNotFoundError:
        return None
    except OSError as exc:
        log_swallowed(__name__, exc, context=(
            f'_recycle_fresh_skeleton_file:{type(exc).__name__}'))
        return f"{type(exc).__name__}: {exc}"
    return None
def _discard_unpersisted_skeleton(result_dir: str,
                                  skill_md_existed: bool,
                                  init_py_existed: bool,
                                  warnings: list[dict]) -> None:
    for name, existed in (("SKILL.md", skill_md_existed),
                          ("__init__.py", init_py_existed)):
        if existed:
            continue
        path = os.path.join(result_dir, name)
        failure = _recycle_fresh_skeleton_file(path)
        if failure is not None:
            warnings.append({
                "step": "write_back", "severity": "warning",
                "detail": (f"创建已阻断，但本次新建的骨架 {name} 未能回收: "
                           f"{path}（{failure}）；重试前请手动删除，"
                           "否则会被判定为已存在技能"),
            })
def _persist_created_content(result_dir: Any, content: str, *,
                             existed: bool, blocked: bool,
                             create_missing: bool,
                             fixes: list[dict],
                             warnings: list[dict]) -> bool | None:
    if (blocked or existed or not create_missing or not content
            or not is_path_input(result_dir)):
        return None
    md_path = os.path.join(str(result_dir), "SKILL.md")
    try:
        raw = _read_raw_bytes(md_path) if os.path.isfile(md_path) else b""
    except OSError as exc:
        _log.warning("_persist_created_content: SKILL.md 读取失败: %s", exc)
        warnings.append({
            "step": "write_back", "severity": "blocker",
            "detail": f"SKILL.md 读取失败，已阻断写回以防覆盖原内容: {exc}",
        })
        return False
    try:
        write_text_preserving_form(md_path, content, raw)
    except (OSError, ValueError, RuntimeError) as exc:
        log_swallowed(__name__, exc,
                      context=f'_persist_created_content:{type(exc).__name__}')
        warnings.append({"step": "write_back", "severity": "warning",
                         "detail": f"SKILL.md 内容写回失败: {exc}"})
        return False
    fixes.append({"step": "write_back", "action": "auto_fix",
                  "detail": f"已写入技能内容: {md_path}"})
    return True
def _dir_basename(skill_dir: str) -> str:
    if not skill_dir:
        return ""
    base = os.path.basename(os.path.normpath(skill_dir))
    return "" if base in (".", "..") else base
def _entry_list(value: Any) -> list:
    if isinstance(value, (list, tuple)):
        return list(value)
    return [] if value is None else [value]
def _preflight_result_snapshot(preflight_result: dict) -> dict:
    snapshot = {
        "passed": preflight_result.get("ok", False),
        "skill_name": preflight_result.get("skill_name", ""),
        "fixes": _entry_list(preflight_result.get("fixes")),
        "warnings": _entry_list(preflight_result.get("warnings")),
        "blocked": preflight_result.get("blocked", False),
        "skill_type": preflight_result.get("skill_type", ""),
        "design_pattern": preflight_result.get("design_pattern", ""),
        "description_suggestions": _entry_list(
            preflight_result.get("description_suggestions")),
        "content_written": preflight_result.get("content_written", False) is True,
        "status": preflight_result.get(
            "status", "ok" if preflight_result.get("ok") else "error"),
        "error": preflight_result.get("error", ""),
        "target_dir": preflight_result.get("target_dir", ""),
        "skill_md_path": preflight_result.get("skill_md_path", ""),
    }
    for key in ("dependencies_passed", "dependency_suggestions"):
        if key in preflight_result:
            snapshot[key] = preflight_result[key]
    return snapshot
def _skip_preflight_contracts(result: dict[str, Any], reason: str) -> None:
    result["contracts_checked"] = False
    result["contracts_passed"] = None
    result["validation"] = {
        "ok": None, "errors": [], "skipped": True, "reason": reason}
def _sync_preflight_outcome(result: dict[str, Any]) -> None:
    if not result.get("contracts_checked"):
        return
    contracts_passed = result.get("contracts_passed")
    if contracts_passed is True:
        return
    details = _entry_list(result.get("contract_errors"))
    if not details:
        validation = result.get("validation")
        if isinstance(validation, dict):
            details = _entry_list(validation.get("errors"))
    detail_text = "; ".join(str(item) for item in details) or "未返回错误明细"
    prefix = "契约校验失败" if contracts_passed is False else "契约校验未完成"
    result["passed"] = False
    result["blocked"] = True
    result["status"] = "error"
    if not result.get("error"):
        result["error"] = f"{prefix}: {detail_text}"
    result["warnings"].append({
        "step": "contracts", "severity": "blocker",
        "detail": f"{prefix}: {detail_text}",
    })
def build_preflight(skill_dir: Any, check_contracts: bool = True, write_back: bool = False) -> dict:
    skill_dir = _path_arg(skill_dir)
    _name, _desc, _content, read_errors = _read_skill_md_checked(skill_dir)
    skill_name = _name or _dir_basename(skill_dir) or _FALLBACK_SKILL_NAME
    create_missing = not (skill_dir and os.path.isdir(skill_dir)
                          and os.path.isfile(
                              os.path.join(skill_dir, "SKILL.md")))
    if read_errors:
        return _blocked_preflight_result(
            skill_dir, skill_name, read_errors, check_contracts)
    preflight_result = run_guided_creation(
        skill_name=skill_name,
        description=_desc or "",
        content=_content or "",
        skill_dir=skill_dir,
        create_missing=create_missing,
        dry_run=not write_back,
    )
    result = _preflight_result_snapshot(preflight_result)
    result["create_missing"] = create_missing
    if write_back:
        _write_back_or_warn(skill_dir, preflight_result, result)
    if create_missing and not write_back:
        _skip_preflight_contracts(result, "目标尚未创建；已校验只读创建计划，落盘后再校验目录契约")
    elif check_contracts and skill_dir:
        _check_preflight_contracts(skill_dir, result)
        _sync_preflight_outcome(result)
    else:
        _skip_preflight_contracts(result, "未请求契约校验或目标路径为空")
    return result
def _blocked_preflight_result(skill_dir: str, skill_name: str,
                              read_errors: list[str],
                              check_contracts: bool) -> dict[str, Any]:
    result = _preflight_result_snapshot({
        "ok": False,
        "status": "error",
        "blocked": True,
        "skill_name": skill_name,
        "error": ("SKILL.md 读取失败，已阻断写回以防覆盖原内容: "
                  + "; ".join(read_errors)),
        "warnings": [
            {"step": "read_back", "severity": "blocker", "detail": item}
            for item in read_errors
        ],
        "fixes": [],
        "content_written": False,
        "target_dir": skill_dir,
        "skill_md_path": (
            os.path.join(skill_dir, "SKILL.md") if skill_dir else ""),
    })
    result["create_missing"] = False
    if check_contracts and skill_dir:
        _check_preflight_contracts(skill_dir, result)
        _sync_preflight_outcome(result)
    else:
        _skip_preflight_contracts(result, "未请求契约校验或目标路径为空")
    return result
def _write_back_or_warn(skill_dir: str | None,
                        preflight_result: dict[str, Any],
                        result: dict[str, Any]) -> None:
    if preflight_result.get("content_written") is True:
        result["content_written"] = True
        return
    if result["blocked"]:
        result["warnings"].append({
            "step": "write_back",
            "severity": "blocker",
            "detail": "预检阻断，已跳过 SKILL.md 写回",
        })
        return
    final_content = preflight_result.get("content", "")
    if not isinstance(final_content, str) or not final_content.strip():
        return
    if not skill_dir:
        return
    if not _write_back_result_content(skill_dir, final_content, result):
        result["passed"] = False
        result["blocked"] = True
        result["status"] = "error"
        if not result.get("error"):
            result["error"] = "修复结果写回失败，源文件保持原样"
def _check_preflight_contracts(skill_dir: str,
                               result: dict[str, Any]) -> None:
    result["contracts_checked"] = True
    try:
        contracts_passed, contract_errors = validate_skill(skill_dir)
    except Exception as exc:  # noqa: BLE001
        _log.warning("_check_preflight_contracts: 契约检查异常: %s", exc)
        result["contracts_passed"] = None
        result["contract_errors"] = [f"契约检查异常: {exc}"]
        result["validation"] = {
            "ok": None, "errors": list(result["contract_errors"])}
        return
    result["contracts_passed"] = contracts_passed
    result["validation"] = {
        "ok": contracts_passed, "errors": list(contract_errors)}
    if contract_errors:
        result["contract_errors"] = contract_errors
def get_existing_skills(skills_dir: Any) -> list:
    if not is_path_input(skills_dir):
        return []
    skills_dir = Path(skills_dir)
    if not skills_dir.is_dir():
        return []
    try:
        return [d.name for d in skills_dir.iterdir()
                if d.is_dir()
                and not d.name.startswith((".", "_"))
                and (d / "SKILL.md").is_file()]
    except OSError as exc:
        _log.debug("get_existing_skills: 目录列举失败，按空技能清单降级: %s", exc)
        return []
def generate_guided_template(skill_name: str, description: str,
                             version: str) -> tuple[str, str]:
    try:
        content = generate_skill_md_template(
            skill_name=skill_name, description=description,
            skill_type='generic', version=version)
        return content, '已生成含五大必备区块的黄金模板'
    except Exception as exc:  # noqa: BLE001
        _log.warning('preflight template generation fallback: %s', exc,
                     exc_info=True)
        content = render_minimal_skill_md(skill_name, description, version)
        return content, '已生成默认内容模板（回退版）'
def _error_result(name: str, message: str) -> dict:
    return {
        "ok": False,
        "status": "error",
        "error": message,
        "skill_name": name,
        "blocked": True,
        "content_written": False,
        "fixes": [],
        "warnings": [],
        "target_dir": "",
        "skill_md_path": "",
    }
def _preflight_error(name: str, description: str) -> str | None:
    try:
        issues = validate_create_input(name, description)
    except Exception as e:  # noqa: BLE001
        _log.warning("[init] preflight check error: %s", e)
        return f"创建前预检异常: {e}"
    return f"创建前预检失败: {'; '.join(issues)}" if issues else None
def _resolve_declared_resources(
        resources: list | None) -> tuple[list, str | None]:
    if resources is None:
        return [], None
    try:
        return parse_resources(resources), None
    except ValueError as rve:
        _log.warning("[init] 资源类型校验失败: %s", rve)
        return [], f"资源类型校验失败: {rve}"
def _prepare_creation_context(
        skill_name: str, target_dir: str | None, description: str,
        design_pattern: str | None,
        resources: list | None,
        skill_type: str | None) -> tuple[dict | None, dict | None]:
    meta = prepare_skill_metadata(
        skill_name, description, design_pattern, skill_type)
    name = meta["name"]
    if not name:
        return None, _error_result(
            name, "技能名称规范化后为空：须至少包含一个字母或数字")
    effective_description = normalize_text(description).strip()
    if not effective_description:
        effective_description = f"{meta['display_name'] or name} 技能"
    try:
        target_dir = resolve_target_dir(target_dir, name)
    except ValueError as exc:
        return None, _error_result(name, str(exc))
    preflight = _preflight_error(name, effective_description)
    if preflight:
        return None, _error_result(name, preflight)
    parsed_resources, resource_error = _resolve_declared_resources(resources)
    if resource_error:
        return None, _error_result(name, resource_error)
    for relative_path in ("SKILL.md", "__init__.py",
                          os.path.join("scripts", "main.py")):
        existing_path = os.path.join(target_dir, relative_path)
        if os.path.lexists(existing_path):
            return None, _error_result(
                name,
                f"目标目录已存在 {relative_path}，拒绝覆盖既有技能: "
                f"{existing_path}")
    dir_logs: list[str] = []
    if not ensure_root_dir(target_dir, dir_logs):
        return None, _error_result(
            name, dir_logs[-1] if dir_logs else f"目标目录不可创建: {target_dir}")
    return {
        **meta,
        "description": effective_description,
        "target_dir": target_dir,
        "parsed_resources": parsed_resources,
    }, None
def _run_scaffold_enhancement(step: str, action, default: Any,
                              warnings: list[dict]) -> Any:
    try:
        return action()
    except Exception as exc:  # noqa: BLE001
        log_swallowed(__name__, exc,
                      context=f'_write_skill_scaffold:{step}:{type(exc).__name__}')
        warnings.append({"step": step, "severity": "warning",
                         "detail": f"{step} 增强失败，已跳过: {exc}"})
        return default
def _rollback_incomplete_core_files(
        core_paths: tuple[str, ...], preexisting: set[str]) -> None:
    for path in core_paths:
        if path in preexisting:
            continue
        try:
            os.remove(path)
        except FileNotFoundError:
            continue
        except OSError as exc:
            _log.error(
                "_rollback_incomplete_core_files: 无法回收半成品 %s: %s",
                path, exc)
def _write_skill_scaffold(context: dict, description: str,
                          warnings: list[dict]) -> dict:
    name = context["name"]
    display_name = context["display_name"]
    skill_type = context["skill_type"]
    pattern = context["pattern"]
    category = context["category"]
    target_dir = context["target_dir"]
    created = create_skill_directories(target_dir)
    parsed_resources = context["parsed_resources"]
    resource_dirs = (create_resource_dirs(target_dir, parsed_resources)
                     if parsed_resources else [])
    optimized_description, optimized_keywords = generate_optimized_frontmatter(
        name, display_name, description, skill_type)
    core_paths = (
        os.path.join(target_dir, "SKILL.md"),
        os.path.join(target_dir, "__init__.py"),
    )
    preexisting = {path for path in core_paths if os.path.lexists(path)}
    try:
        skill_md_path = write_skill_md(
            target_dir, name, display_name, category, pattern,
            optimized_description, optimized_keywords)
        write_init_module(target_dir, name)
    except Exception:
        _rollback_incomplete_core_files(core_paths, preexisting)
        raise
    final_description, final_keywords = _run_scaffold_enhancement(
        "discoverability",
        lambda: _apply_discoverability(
            target_dir, name, description, display_name, skill_type,
            optimized_description, optimized_keywords),
        (optimized_description, optimized_keywords), warnings)
    _run_scaffold_enhancement(
        "role_scenario",
        lambda: append_role_scenario_section(
            os.path.join(target_dir, "SKILL.md"),
            name, final_description, final_keywords),
        None, warnings)
    _run_scaffold_enhancement(
        "trigger_test",
        lambda: run_trigger_test_gate(
            name, final_description, final_keywords),
        None, warnings)
    _run_scaffold_enhancement(
        "example_script",
        lambda: generate_optimized_example_script(
            target_dir, display_name, final_keywords),
        None, warnings)
    _run_scaffold_enhancement(
        "script_guide", lambda: inject_script_usage_guide(target_dir),
        None, warnings)
    return {
        "skill_md_path": skill_md_path,
        "created_dirs": created,
        "resource_dirs": resource_dirs,
        "optimized_keywords": final_keywords,
    }
def _apply_discoverability(
        target_dir: str, name: str, description: str, display_name: str,
        skill_type: str, optimized_description: str,
        optimized_keywords: list) -> tuple[str, list]:
    enhanced = apply_full_discoverability(
        target_dir, name,
        description or f"{display_name} 技能",
        skill_type, optimized_keywords)
    if (not isinstance(enhanced, dict)
            or enhanced.get("frontmatter_written") is not True):
        if isinstance(enhanced, dict) and enhanced.get("error"):
            _log.warning(
                "discoverability 写回失败，保留脚手架元数据: %s",
                enhanced["error"])
        return optimized_description, optimized_keywords
    final_description = enhanced.get("enhanced_description")
    if not isinstance(final_description, str) or not final_description.strip():
        final_description = optimized_description
    final_keywords = (normalize_str_list(enhanced.get("expanded_keywords"))
                      or optimized_keywords)
    return final_description, final_keywords
@requires_contract(INIT_CONTRACT)
def _init_skill_impl(skill_name: str, target_dir: str | None,
                     description: str, design_pattern: str | None,
                     resources: list | None,
                     skill_type: str | None) -> dict:
    setup_logging()
    _log.info("init_skill 启动", extra={
        "event": "init_start",
        "phase": "build_init",
        "payload": {"skill_name": skill_name},
    })
    context, error_result = _prepare_creation_context(
        skill_name, target_dir, description, design_pattern, resources,
        skill_type)
    if error_result is not None:
        return error_result
    warnings: list[dict] = []
    scaffold = _write_skill_scaffold(
        context, context["description"], warnings)
    validation_ok, validation_errors = _validate_created_skill(
        context["target_dir"])
    run_post_create_quality_gates(
        context["target_dir"], scaffold["skill_md_path"])
    result = build_init_result(context, scaffold)
    result["warnings"] = warnings
    _apply_post_create_validation_outcome(
        result, validation_ok, validation_errors)
    return result
def _record_init_run(result: object, started: float) -> None:
    is_dict = isinstance(result, dict)
    details = result if is_dict else {}
    ok = is_dict and details.get("status") == "ok"
    try:
        write_module_run(
            "build_preflight", "init_skill",
            outcome="ok" if ok else "fail",
            duration_ms=(time.monotonic() - started) * 1000.0,
            skill_name=details.get("skill_name", ""),
            status=details.get("status") if is_dict else "error",
            created_dirs=len(details.get("created_dirs") or []))
    except Exception as exc:  # noqa: BLE001
        _log.warning("[init] 创建运行留痕失败，不阻断创建结果: %s", exc)
def init_skill(skill_name: str, target_dir: str | None = None,
               description: str = "", design_pattern: str | None = None,
               resources: list | None = None,
               skill_type: str | None = None) -> dict:
    started = time.monotonic()
    try:
        result = _init_skill_impl(
            skill_name=skill_name, target_dir=target_dir,
            description=description, design_pattern=design_pattern,
            resources=resources, skill_type=skill_type)
    except Exception as exc:  # noqa: BLE001
        _record_init_run(None, started)
        _log.error("[BuildFactory] init_skill 异常: %s", skill_name,
                   exc_info=True)
        return _error_result(
            normalize_text(skill_name) or _FALLBACK_SKILL_NAME,
            f"初始化异常: {exc}")
    _record_init_run(result, started)
    return result
def build_init(
        skill_name: str,
        description: str = "",
        skill_type: str | None = None,
        *,
        target_dir: str | None = None,
        design_pattern: str | None = None,
        resources: list | None = None) -> str:
    try:
        result = init_skill(
            skill_name=skill_name,
            target_dir=target_dir,
            description=description,
            design_pattern=design_pattern,
            resources=resources,
            skill_type=skill_type,
        )
    except Exception:  # noqa: BLE001
        _log.error("[BuildFactory] build_init 异常: %s", skill_name, exc_info=True)
        return ""
    if not isinstance(result, dict) or result.get("status") != "ok":
        _log.error("[BuildFactory] build_init 失败: %s",
                   result.get("error") if isinstance(result, dict) else repr(result))
        return ""
    return result.get("target_dir", "")
def _validate_created_skill(target_dir: str) -> tuple[bool, list[str]]:
    try:
        valid, errors = validate_skill(target_dir)
        _log.info(
            "[init] Post-create validation: ok=%s, errors=%s", valid, errors)
    except Exception as exc:  # noqa: BLE001
        _log.warning("[init] Post-create validation 异常，创建结果阻断: %s", exc)
        return False, [f"创建后契约校验异常: {exc}"]
    return bool(valid), list(errors or [])
def _apply_post_create_validation_outcome(
        result: dict, validation_ok: bool, validation_errors: list[str]) -> None:
    if validation_ok:
        return
    details = "; ".join(
        str(item) for item in validation_errors if str(item).strip())
    message = "创建后契约校验失败: " + (details or "未返回错误明细")
    result["ok"] = False
    result["blocked"] = True
    result["status"] = "error"
    result["error"] = message
    result.setdefault("warnings", []).append({
        "step": "post_create_validation", "severity": "blocker",
        "detail": message,
    })
def _compute_discoverability_score(trigger_score: float, example_score: float,
                                   func_score: float) -> float:
    return round((trigger_score * 10) * 0.4 + example_score * 0.3 + func_score * 0.3, 1)
def _compute_creation_scores(opt_result: MetadataOptimizationResult,
                              discoverability_result: dict
                              ) -> tuple[float, float, bool]:
    old_score = _compute_discoverability_score(opt_result.trigger_score, 50.0, 50.0)
    payload = (discoverability_result
               if isinstance(discoverability_result, dict) else {})
    raw_index = payload.get(FIELD_DISCOVERABILITY_INDEX)
    if raw_index is None:
        raw_index = payload.get("quality_score")
    if isinstance(raw_index, bool) or not isinstance(raw_index, (int, float)):
        return old_score, old_score, False
    try:
        score = float(raw_index)
    except (TypeError, ValueError, OverflowError):
        return old_score, old_score, False
    if not math.isfinite(score):
        return old_score, old_score, False
    return old_score, score, True
def _assemble_creation_result(state: dict) -> dict:
    opt_result = state["opt_result"]
    return {
        "ok": True,
        FIELD_OPTIMIZED_DESCRIPTION: opt_result.optimized_description,
        FIELD_OPTIMIZED_KEYWORDS: opt_result.optimized_keywords,
        "discoverability_score": state["new_score"],
        "old_score": state["old_score"],
        "discoverability_measured": state.get("discoverability_measured", True),
        "semantic_index": state["assets"]["semantic_index"],
        "func_result": state["assets"]["func_result"],
        "example_result": state["assets"]["example_result"],
        "example_section": state["assets"]["example_section"],
        "desc_eval": state["assets"]["desc_eval"],
        "cli_template": state["cli_template"],
        "module_template": state["module_template"],
        "script_gen_result": state["script_gen_result"],
        "discoverability_result": state["discoverability_result"],
        "depends_on": state["depends_on"],
    }
def create_skill_with_full_discoverability(
    skill_name: str,
    description: str = "",
    skill_type: str = "",
    user_keywords: list[str] | None = None,
    depends_on: list[str] | None = None,
    existing_descriptions: list[str] | None = None,
    skill_dir: str = "",
) -> dict:
    skill_name, description, error_result = validate_creation_inputs(
        skill_name, description)
    if error_result is not None:
        return error_result
    opt_result, discoverability_result = optimize_creation_discoverability(
        skill_name=skill_name, description=description,
        skill_type=skill_type, user_keywords=user_keywords,
        existing_descriptions=existing_descriptions)
    optimized_description = opt_result.optimized_description
    optimized_keywords = opt_result.optimized_keywords
    script_assets = build_creation_script_assets(
        skill_dir, skill_name, optimized_description, optimized_keywords)
    old_score, new_score, measured = _compute_creation_scores(
        opt_result, discoverability_result)
    assets = build_creation_validation_assets(
        skill_name, opt_result, existing_descriptions)
    script_gen_result = script_assets["script_result"]
    _log.info(
        "[SkillCreation] 一站式可发现性优化完成: skill=%s, score %.1f -> %s, "
        "keywords=%d, script_written=%s",
        skill_name, old_score, f"{new_score:.1f}" if measured else "未度量",
        len(optimized_keywords), script_gen_result is not None)
    return _assemble_creation_result({
        "opt_result": opt_result,
        "discoverability_result": discoverability_result,
        "old_score": old_score,
        "new_score": new_score,
        "discoverability_measured": measured,
        "assets": assets,
        "cli_template": script_assets["cli_template"],
        "module_template": script_assets["module_template"],
        "script_gen_result": script_gen_result,
        "depends_on": normalize_str_list(depends_on),
    })
def parse_skill_metadata(skill_dir: str) -> dict[str, Any]:
    normalized = normalize_out_path(skill_dir)
    if normalized is None:
        return {"error": f"技能目录非法: {skill_dir!r}"}
    skill_md = Path(normalized) / "SKILL.md"
    if not skill_md.exists():
        return {"error": f"SKILL.md 不存在: {normalized}"}
    try:
        content = read_skill_md_text(skill_md)
        metadata = dict(parse_skill_md_text(content, Path(normalized).name))
        metadata["content"] = content
    except (OSError, UnicodeDecodeError) as exc:
        log_swallowed(__name__, exc, context=f'parse_skill_metadata:{type(exc).__name__}')
        return {"error": f"SKILL.md 读取失败: {exc}"}
    metadata["skill_md_path"] = str(skill_md)
    metadata["skill_dir"] = normalized
    return metadata
def _partition_trigger_keywords(keywords: list[str],
                                 recs: dict[str, Any]
                                 ) -> tuple[list[str], dict[str, str]]:
    deduped: list[str] = []
    seen: set[str] = set()
    for raw_word in keywords or []:
        if not isinstance(raw_word, str) or not raw_word.strip():
            continue
        word = raw_word.strip()
        key = word.casefold()
        if key in seen:
            continue
        seen.add(key)
        deduped.append(word)
    normalized_recs = {
        key.casefold(): value for key, value in (recs or {}).items()
        if isinstance(key, str)
    }
    boosted, kept, reduced = [], [], []
    actions: dict[str, str] = {}
    for word in deduped:
        rec = normalized_recs.get(word.casefold())
        action = rec.strip().lower() if isinstance(rec, str) else ""
        if action == "remove":
            actions[word] = "remove"
            continue
        if action == "boost":
            boosted.append(word)
            actions[word] = "boost"
        elif action == "reduce":
            reduced.append(word)
            actions[word] = "reduce"
        else:
            kept.append(word)
            if rec:
                actions[word] = rec
    return boosted + kept + reduced, actions
def _load_feedback_metadata(skill_dir: str) -> tuple[dict[str, Any] | None,
                                                    dict[str, Any]]:
    if not (Path(skill_dir) / "SKILL.md").exists():
        return None, {"applied": False,
                      "error": f"SKILL.md 不存在: {skill_dir}",
                      "keywords": [], "actions": {}}
    try:
        return read_skill_md(skill_dir), {}
    except (OSError, UnicodeDecodeError) as exc:
        _log.warning("apply_trigger_feedback: 读取 %s/SKILL.md 失败: %s",
                     skill_dir, exc)
        return None, {"applied": False, "error": f"SKILL.md 读取失败: {exc}",
                      "keywords": [], "actions": {}}
def _attempt_keyword_writeback(skill_dir: str,
                               new_keywords: list[str]) -> tuple[bool, dict[str, str]]:
    if not new_keywords:
        return False, {
            "skipped_reason": "全部触发词被判定 remove，为避免清空 keywords 已跳过写回"}
    try:
        applied = update_skill_md(
            skill_dir, None, new_keywords, inject_capability=False,
            inject_script_guide=False)
    except (OSError, ValueError, RuntimeError) as exc:
        log_swallowed(__name__, exc, context=f'_attempt_keyword_writeback:{type(exc).__name__}')
        return False, {"error": f"SKILL.md 写回失败: {exc}"}
    if not applied:
        return False, {
            "skipped_reason": "frontmatter 写回未发生（缺少 name/description 锚点或内容未变化）"}
    return applied, {}
def _iter_recommendation_items(recommendations: Any):
    if isinstance(recommendations, dict):
        yield from recommendations.items()
        return
    for item in recommendations or []:
        if isinstance(item, dict):
            yield item.get("trigger_word"), item.get("recommendation")
        else:
            yield (getattr(item, "trigger_word", None),
                   getattr(item, "recommendation", None))
def _feedback_recommendations(loop: Any) -> tuple[dict[str, Any], str]:
    getter = getattr(loop, "get_recommendations", None)
    if not callable(getter):
        return {}, f"触发反馈循环非法（缺 get_recommendations）: {type(loop).__name__}"
    try:
        recommendations = getter()
    except Exception as exc:  # noqa: BLE001
        log_swallowed(__name__, exc, context=f"_feedback_recommendations:get:{type(exc).__name__}")
        return {}, f"触发反馈回读失败: {exc}"
    recs: dict[str, Any] = {}
    dropped = 0
    try:
        for word, rec in _iter_recommendation_items(recommendations):
            if not isinstance(word, str) or not word:
                dropped += 1
                continue
            recs[word] = rec
    except Exception as exc:  # noqa: BLE001
        log_swallowed(__name__, exc, context=f"_feedback_recommendations:iterate:{type(exc).__name__}")
        return {}, f"触发反馈回读失败: {exc}"
    if dropped:
        _log.warning("apply_trigger_feedback: 忽略 %d 条形态非法的触发建议", dropped)
    return recs, ""
def apply_trigger_feedback(skill_dir: str, loop: Any, apply: bool = True) -> dict[str, Any]:
    target = normalize_out_path(skill_dir)
    if target is None:
        return {"applied": False, "error": f"技能目录非法: {skill_dir!r}",
                "keywords": [], "actions": {}}
    meta, failure = _load_feedback_metadata(target)
    if meta is None:
        return failure
    keywords = normalize_str_list(meta.get("keywords"))
    recs, rec_error = _feedback_recommendations(loop)
    if rec_error:
        return {"applied": False, "error": rec_error,
                "keywords": [], "actions": {}}
    new_keywords, actions = _partition_trigger_keywords(keywords, recs)
    applied = False
    write_failure: dict[str, Any] = {}
    if apply and new_keywords != keywords:
        applied, write_failure = _attempt_keyword_writeback(
            target, new_keywords)
        # 应用模式下的 keywords 表示持久化状态，而不是未生效的调整计划。
        # 被别名引用的关键词可能在写回时保留，因此成功后同样必须回读。
        persisted_meta, _read_failure = _load_feedback_metadata(target)
        if persisted_meta is not None:
            new_keywords = normalize_str_list(persisted_meta.get("keywords"))
        elif not applied:
            new_keywords = keywords
        for reason in write_failure.values():
            _log.warning("apply_trigger_feedback: %s (%s)", reason, target)
    return {"applied": applied, "keywords": new_keywords,
            "actions": actions, **write_failure}
def optimize_skill(skill_dir: str, fix: bool = DEFAULT_OPTIMIZE_FIX,
                   dry_run: bool = DEFAULT_OPTIMIZE_DRY_RUN) -> dict[str, Any]:
    meta = parse_skill_metadata(skill_dir)
    if "error" in meta:
        return meta
    target = meta["skill_dir"]
    report: dict[str, Any] = {
        "skill_name": meta["name"],
        "skill_dir": str(Path(target).resolve()),
        "original_description": meta["description"],
        "original_keywords": meta["keywords"],
        "fix_applied": False,
        "dry_run": dry_run,
    }
    report[CAT_DISCOVERABILITY] = build_discoverability_section(meta)
    report["script_optimization"] = build_script_score_section(target)
    report["overall_score"] = compose_optimization_score(
        report[CAT_DISCOVERABILITY][FIELD_DISCOVERABILITY_INDEX],
        report["script_optimization"],
    )
    if fix and not dry_run:
        expected_description = report[CAT_DISCOVERABILITY][
            FIELD_OPTIMIZED_DESCRIPTION]
        expected_keywords = report[CAT_DISCOVERABILITY][
            FIELD_OPTIMIZED_KEYWORDS]
        try:
            written = update_skill_md(
                target, expected_description, expected_keywords)
            metadata_matches = _frontmatter_matches_optimization(
                target, expected_description, expected_keywords)
        except Exception as exc:  # noqa: BLE001
            _log.warning("更新 %s/SKILL.md 异常: %s", target, exc)
            report["error"] = f"SKILL.md 写回失败: {exc}"
        else:
            report["fix_applied"] = bool(written and metadata_matches)
            if metadata_matches:
                if written:
                    _log.info("已更新 %s/SKILL.md", target)
                else:
                    report["fix_unchanged"] = True
                    _log.info("%s/SKILL.md 已达到优化目标，幂等跳过写回", target)
            else:
                report["error"] = "SKILL.md frontmatter 写回未生效"
                _log.warning("未能更新 %s/SKILL.md frontmatter", target)
    if dry_run:
        report["dry_run_note"] = "预览模式，未实际修改文件。使用 --fix 应用修改。"
    return report
def _optimize_batch_entry(skill_dir: Path, fix: bool, dry_run: bool) -> dict[str, Any]:
    _log.info("优化: %s", skill_dir.name)
    try:
        result = optimize_skill(str(skill_dir), fix=fix, dry_run=dry_run)
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e, context=f'_optimize_batch_entry:{type(e).__name__}')
        return {"skill_name": skill_dir.name, "error": str(e)}
    if isinstance(result, dict) and result.get("error"):
        return {"skill_name": skill_dir.name, "error": str(result["error"])}
    return result
def optimize_skills_batch(
        skills_root: str, fix: bool = DEFAULT_OPTIMIZE_FIX,
        dry_run: bool = DEFAULT_OPTIMIZE_DRY_RUN) -> dict[str, Any]:
    root_arg = normalize_out_path(skills_root)
    if root_arg is None:
        return {"error": f"skills_root 不存在或不是目录: {skills_root!r}"}
    skills, error = iter_skill_dirs(root_arg)
    if error:
        return {"error": error}
    root = Path(root_arg)
    ok_results: list[dict[str, Any]] = []
    failed_results: list[dict[str, Any]] = []
    for skill_dir in skills:
        entry = _optimize_batch_entry(skill_dir, fix, dry_run)
        (failed_results if entry.get("error") else ok_results).append(entry)
    return {
        "skills_root": str(root.resolve()),
        "skills_optimized": len(ok_results),
        "skills_failed": len(failed_results),
        "average_overall_score": average_optimization_score(ok_results),
        "results": ok_results + failed_results,
    }
def _build_optimize_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="技能可发现性与脚本调用率综合优化工具",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  python -m jwsgj.build_preflight --skill-dir ./my-skill --json
  python -m jwsgj.build_preflight --skill-dir ./my-skill --fix
  python -m jwsgj.build_preflight --skills-root ./skills --dry-run
  python -m jwsgj.build_preflight --skill-dir ./my-skill --fix --yes
        """,
    )
    parser.add_argument("--skill-dir", "-d", help="单个技能目录路径")
    parser.add_argument("--skills-root", "-r", help="技能根目录（批量）")
    parser.add_argument(
        "--fix",
        "-f",
        action="store_true",
        help="自动修复（写回 SKILL.md）")
    parser.add_argument(
        "--dry-run",
        "-n",
        action="store_true",
        help="预览模式，不修改文件")
    parser.add_argument("--json", "-j", action="store_true", help="JSON 格式输出")
    parser.add_argument("--yes", "-y", action="store_true", help="跳过确认提示")
    parser.add_argument("--quiet", "-q", action="store_true", help="静默模式")
    return parser
def _cli_summary_lines(result: dict, args: argparse.Namespace) -> list[str]:
    skill_label = result.get("skill_name", result.get("skills_root", "?"))
    score_label = result.get("overall_score",
                             result.get("average_overall_score", "?"))
    lines = [f"技能: {skill_label}", f"综合评分: {score_label}"]
    if result.get("fix_applied"):
        lines.append("已应用修复")
    if args.dry_run:
        lines.append("[预览模式] 未实际修改文件")
    return lines
def _emit_cli_result(result: dict, args: argparse.Namespace) -> None:
    if args.json:
        json.dump(result, sys.stdout, ensure_ascii=False, indent=2,
                  default=str)
        sys.stdout.write("\n")
        return
    if not isinstance(result, dict):
        print(result)
        return
    for line in _cli_summary_lines(result, args):
        _log.info("%s", line)
        if not getattr(args, "quiet", False):
            print(line)
def _confirm_batch_write(args: argparse.Namespace) -> bool:
    if args.yes or not args.fix or args.dry_run:
        return True
    print(
        f"将批量修改 {args.skills_root} 下所有技能的 SKILL.md，需显式传 --yes 确认；"
        "本次已取消（可加 --dry-run 先预览）", file=sys.stderr)
    return False
def _run_optimize_cli(parser: argparse.ArgumentParser,
                      args: argparse.Namespace) -> int:
    try:
        if args.skills_root:
            if not _confirm_batch_write(args):
                return 0
            result = optimize_skills_batch(
                args.skills_root, fix=args.fix, dry_run=args.dry_run)
        elif args.skill_dir:
            result = optimize_skill(
                args.skill_dir,
                fix=args.fix,
                dry_run=args.dry_run)
        else:
            print("错误: 必须指定 --skill-dir 或 --skills-root", file=sys.stderr)
            parser.print_help()
            return 1
        _emit_cli_result(result, args)
        if isinstance(result, dict) and (
                result.get("error") or result.get("skills_failed", 0)):
            message = result.get("error") or (
                f"{result['skills_failed']} 个技能优化失败")
            _log.error("优化失败: %s", message)
            print(f"优化失败: {message}", file=sys.stderr)
            return 1
    except (OSError, ValueError, RuntimeError, TypeError) as e:
        if args.json:
            json.dump({"status": "error", "error": str(e)}, sys.stderr,
                      ensure_ascii=False, indent=2)
        else:
            _log.exception("错误")
            print(f"错误: {e}\n用法: python -m jwsgj.build_preflight --help",
                  file=sys.stderr)
        return 1
    return 0
def optimize_main(argv: list[str] | None = None) -> int:
    parser = _build_optimize_parser()
    args = parser.parse_args(argv)
    _quiet_prev_level: int | None = (
        logging.getLogger().level if args.quiet else None)
    if args.quiet:
        logging.getLogger().setLevel(logging.WARNING)
    try:
        return _run_optimize_cli(parser, args)
    finally:
        if _quiet_prev_level is not None:
            logging.getLogger().setLevel(_quiet_prev_level)
def _optimize_metadata(optimizer: SkillMetadataOptimizer, skill_dir: str) -> tuple[dict, Any]:
    normalized = normalize_out_path(skill_dir)
    if normalized is None:
        raise ValueError(f"技能目录非法: {skill_dir!r}")
    meta = read_skill_md(normalized)
    opt = optimizer.optimize(
        meta["name"], meta["description"],
        existing_skill_category(normalized), meta["keywords"])
    return meta, opt
def _opt_entry(meta: dict, opt: Any) -> dict:
    return {
        "skill_name": meta["name"],
        "optimized_description": opt.optimized_description,
        "optimized_keywords": opt.optimized_keywords,
        "trigger_score": opt.trigger_score,
        "issues": opt.issues,
        "warnings": opt.warnings,
        "frontmatter_written": False,
    }
def _frontmatter_matches_optimization(
        skill_dir: str, optimized_description: Any,
        optimized_keywords: Any) -> bool:
    meta = read_skill_md(skill_dir)
    expected_description = normalize_text(optimized_description).strip()
    actual_description = normalize_text(meta.get("description", "")).strip()
    # 写路径（replace_frontmatter_desc_keywords）只落盘前 INLINE_KEYWORDS_MAX 个关键词，
    # 比对侧必须按同一上限截断，否则优化关键词超过上限时会把已成功写回误判为未生效。
    expected_keywords = normalize_str_list(optimized_keywords)[:INLINE_KEYWORDS_MAX]
    actual_keywords = normalize_str_list(meta.get("keywords"))
    return (bool(expected_description or expected_keywords)
            and actual_description == expected_description
            and actual_keywords == expected_keywords)
def _apply_frontmatter_write(entry: dict, skill_dir: str, opt: Any,
                             fix: bool, caller: str) -> None:
    if not fix:
        return
    try:
        written = write_optimized_frontmatter(skill_dir, opt)
        entry["frontmatter_written"] = bool(written)
        metadata_matches = _frontmatter_matches_optimization(
            skill_dir, getattr(opt, "optimized_description", ""),
            getattr(opt, "optimized_keywords", None))
        if metadata_matches:
            if not written:
                entry["frontmatter_unchanged"] = True
                _log.info("%s: %s frontmatter 已达到优化目标，幂等跳过写回",
                          caller, skill_dir)
            return
        entry["frontmatter_error"] = "frontmatter 写回未生效"
        _log.warning("%s: 写回 %s 未生效", caller, skill_dir)
    except Exception as e:  # noqa: BLE001
        entry["frontmatter_error"] = str(e)
        _log.warning("%s: 写回 %s 失败，跳过: %s", caller, skill_dir, e)
def quick_optimize_batch(
        skills_root: str, fix: bool = DEFAULT_OPTIMIZE_FIX) -> dict:
    optimizer = SkillMetadataOptimizer()
    optimized: list[dict] = []
    failed: list[dict] = []
    root_arg = normalize_out_path(skills_root)
    if root_arg is None:
        return {"ok": False,
                "error": f"skills_root 不存在或不是目录: {skills_root!r}"}
    entries, error = iter_skill_dirs(root_arg)
    if error:
        return {"ok": False, "error": error}
    for entry in entries:
        try:
            meta, opt = _optimize_metadata(optimizer, str(entry))
            item = _opt_entry(meta, opt)
            _apply_frontmatter_write(item, str(entry), opt, fix, "batch optimize")
        except Exception as e:  # noqa: BLE001
            _log.warning("batch optimize: 读取/优化 %s 失败，跳过: %s", entry, e)
            failed.append({"skill_name": entry.name, "error": str(e)})
            continue
        if item.get("frontmatter_error"):
            failed.append({"skill_name": entry.name,
                           "error": str(item["frontmatter_error"]),
                           "result": item})
            continue
        optimized.append(item)
    return {"ok": not failed, "result": optimized, "failed": failed,
            "skills_failed": len(failed), "mode": "batch",
            "apply_fixes_requested": fix}
def optimize_single_skill(
        skill_dir: str, fix: bool = DEFAULT_OPTIMIZE_FIX) -> dict:
    target = normalize_out_path(skill_dir)
    if target is None:
        return {"ok": False,
                "error": f"读取或优化技能元数据失败: 技能目录非法: {skill_dir!r}"}
    if not os.path.isdir(target):
        return {"ok": False, "error": f"技能目录不存在: {target}"}
    if not os.path.isfile(os.path.join(target, "SKILL.md")):
        return {"ok": False, "error": f"SKILL.md 不存在: {target}"}
    optimizer = SkillMetadataOptimizer()
    try:
        meta, opt = _optimize_metadata(optimizer, target)
    except Exception as e:  # noqa: BLE001
        _log.warning("single optimize: 读取/优化 %s 失败: %s", target, e)
        return {"ok": False, "error": f"读取或优化技能元数据失败: {e}"}
    report = _opt_entry(meta, opt)
    report["frontmatter"] = (
        merged_frontmatter_preview(target, opt) or opt.frontmatter)
    report["domain_hint"] = opt.domain_hint
    report["category"] = opt.category
    _apply_frontmatter_write(report, target, opt, fix, "single optimize")
    payload: dict[str, Any] = {
        "ok": True, "result": report, "mode": "single",
        "apply_fixes_requested": fix}
    if fix and report.get("frontmatter_error"):
        payload["ok"] = False
        payload["error"] = f"frontmatter 写回失败: {report['frontmatter_error']}"
    return payload
def _attach_comprehensive(result: dict, skill_dir: str) -> None:
    try:
        merged = optimize_skill(skill_dir, fix=False)
    except Exception as e:  # noqa: BLE001
        _log.warning("综合优化链异常（不影响主流程）: %s", e)
        return
    if not (isinstance(merged, dict) and "error" not in merged):
        _log.warning("综合优化链跳过: %s", merged)
        return
    result["result"]["comprehensive_optimization"] = {
        key: merged[key]
        for key in (CAT_DISCOVERABILITY, "script_optimization", "overall_score")
        if key in merged
    }
def _quick_optimize_single(skill_dir: str, fix: bool) -> dict:
    result = optimize_single_skill(skill_dir, fix)
    if not result.get("ok"):
        return result
    attach_best_practices(result, skill_dir)
    _attach_comprehensive(result, skill_dir)
    attach_validation_result(result, "post_optimize_validation", skill_dir, "优化后验证")
    validation = result.get("post_optimize_validation")
    if isinstance(validation, dict) and validation.get("ok") is False:
        errors = [str(item) for item in validation.get("errors") or []]
        result["ok"] = False
        result["error"] = "优化后验证失败: " + "; ".join(errors)
    return result
def quick_optimize(
        skill_dir: str | None = None, skills_root: str | None = None,
        batch: bool = False, fix: bool = DEFAULT_OPTIMIZE_FIX) -> dict:
    if batch:
        if not skills_root:
            return {"ok": False,
                    "error": "batch 模式需要 skills_root（批量优化目标根目录）"}
        return quick_optimize_batch(skills_root, fix)
    if skill_dir:
        return _quick_optimize_single(skill_dir, fix)
    if skills_root:
        return {"ok": False,
                "error": "skills_root 仅在 batch=True 时生效；单技能模式请提供 skill_dir"}
    return {"ok": False, "error": "Must provide skill_dir or skills_root"}
def build_init_result(context: dict, scaffold: dict) -> dict:
    return {
        "status": "ok",
        "skill_name": context["name"],
        "display_name": context["display_name"],
        "skill_type": context["skill_type"],
        "target_dir": context["target_dir"],
        "skill_md_path": scaffold["skill_md_path"],
        "created_dirs": scaffold["created_dirs"],
        "resource_dirs": scaffold["resource_dirs"],
        FIELD_OPTIMIZED_KEYWORDS: scaffold["optimized_keywords"],
    }
if __name__ == "__main__":
    sys.exit(optimize_main())

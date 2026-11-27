from __future__ import annotations

import logging
import os
import re
from typing import Any

from jwsgj.build_skill_api_contract import (
    build_function_schema,
    run_architecture_quality_gate,
    run_code_quality_gate,
    run_io_standardization_gate,
)
from jwsgj.build_skill_consistency import (
    MetadataOptimizationResult,
    build_creation_semantic_index,
    validate_semantic_consistency,
)
from jwsgj.build_skill_md_generate import (
    build_creation_doc_assets,
    dir_creation_blocker,
    ensure_valid_skill_name,
    run_document_completeness_gate,
)
from jwsgj.build_skill_md_quality import skill_name_issues
from jwsgj.build_text_document import (
    iter_fence_lines,
    normalize_newlines,
    normalize_text,
    write_text_preserving_form,
)
from jwsgj.build_text_frontmatter import (
    ensure_complete_frontmatter,
    load_frontmatter,
    parse_frontmatter_dict,
    parse_frontmatter_text,
    render_minimal_skill_md,
    split_frontmatter,
)
from jwsgj.cleanup_residue import scan_skill_root_hygiene
from jwsgj.diag_guard_io import (
    SKILL_DOC_FILENAME,
    guarded_open,
    normalize_out_path,
)
from jwsgj.diag_guard_state import SecurityConstraintSet
from jwsgj.diag_types_defs import ContractViolationError
from jwsgj.diag_types_vocab import (
    ALLOWED_RESOURCES,
    PROJECT_ROOT_MARKERS,
)
from jwsgj.log_config import (
    emit_fix_logs,
    log_swallowed,
    observation_gate,
)
from jwsgj.runtime_scope import RUNTIME_DIR_NAME
from jwsgj.skill_scan_kernels import (
    scan_dangerous_calls,
    scan_security_issues,
)

_log = logging.getLogger(__name__)
__all__ = [
    "attach_validation_result",
    "build_creation_validation_assets",
    "check_cie_antipatterns",
    "check_frontmatter",
    "check_fupan_hook",
    "check_naming",
    "check_runtime_temp_residue",
    "check_security",
    "check_structure",
    "create_resource_dirs",
    "create_skill_directories",
    "ensure_fupan_hook",
    "ensure_root_dir",
    "ensure_safe_content",
    "ensure_valid_structure",
    "load_skill_md",
    "parse_resources",
    "read_frontmatter_scalar",
    "record_fix_entries",
    "resolve_target_dir",
    "run_post_create_quality_gates",
    "run_semantic_consistency_gate",
    "validate_skill",
]
_log.info("build_preflight_guard 已加载: %d 项导出", len(__all__))
_SILENT_EXCEPT_RE = re.compile(
    r"(?P<indent>^[ \t]*)except\b(?!\*)\s*(?P<clause>[^:]*):"
    r"(?P<comment>[ \t]+#[^\n]*)?"
    r"(?P<gap>[ \t]*(?:\n[ \t]*(?:#[^\n]*)?)*)\bpass\b"
    r"(?=[ \t]*;?[ \t]*(?:#[^\n]*)?(?:\n|$))",
    re.MULTILINE)
_SILENT_EXCEPT_AS_RE = re.compile(
    r"\bas\s+(?P<var>[^\W\d]\w*)\s*$", re.IGNORECASE)
def read_frontmatter_scalar(content: str, key: str) -> str:
    if not isinstance(content, str) or not content:
        return ""
    value = parse_frontmatter_dict(content).get(key, "")
    if value is None or isinstance(value, (dict, list, tuple, set)):
        return ""
    return value if isinstance(value, str) else str(value)
def _read_skill_md_checked(skill_dir: Any
                           ) -> tuple[str, str, str, list[str]]:
    skill_dir = _path_arg(skill_dir)
    if not skill_dir:
        return "", "", "", []
    md_path = os.path.join(skill_dir, "SKILL.md")
    if not os.path.isfile(md_path):
        return "", "", "", []
    content, _raw, read_errors = _read_skill_md_with_raw(md_path)
    if content is None:
        return "", "", "", read_errors
    skill_name, description = parse_frontmatter_text(content)
    return skill_name, description, content, []
def load_skill_md(skill_dir: str) -> tuple[str, str, str]:
    skill_name, description, content, errors = _read_skill_md_checked(skill_dir)
    if errors:
        _log.warning(
            "load_skill_md: SKILL.md 不可读，按空内容降级"
            "（写盘入口须先阻断，避免模板覆盖原文件）: %s",
            "; ".join(errors))
        return "", "", ""
    return skill_name, description, content
def ensure_safe_content(content: str, filepath: str = SKILL_DOC_FILENAME
                        ) -> tuple[str, list[str]]:
    logs = []
    result = normalize_newlines(normalize_text(content))
    if not result:
        return result, logs
    sanitized, sanitize_logs = SecurityConstraintSet.auto_sanitize(result, filepath)
    if sanitize_logs:
        result = sanitized
        logs.extend(sanitize_logs)
    if _SILENT_EXCEPT_RE.search(result):
        result = _SILENT_EXCEPT_RE.sub(_silent_except_replacement, result)
        logs.append(f"已修复反模式: {_SILENT_EXCEPT_RE.pattern[:40]}...")
    dangerous_still_present = scan_dangerous_calls(result, basic_only=True)
    if dangerous_still_present:
        logs.append(f"警告: 仍存在不可自动修复的危险函数: {', '.join(dangerous_still_present)}")
    emit_fix_logs(logs, _log, prefix="preflight fixer",
                  warn_prefixes=("警告", "无法"))
    return result, logs
_SILENT_EXCEPT_LOG_ALIAS = "_exc_log"
def _available_generated_name(source: str, preferred: str) -> str:
    candidate = preferred
    while re.search(rf"\b{re.escape(candidate)}\b", source):
        candidate = f"_{candidate}"
    return candidate
def _silent_except_replacement(match: re.Match) -> str:
    indent = match.group("indent")
    gap = match.group("gap") or ""
    pad = gap.rsplit("\n", 1)[-1] if "\n" in gap else f"{indent}    "
    clause = match.group("clause").strip()
    as_match = _SILENT_EXCEPT_AS_RE.search(clause)
    var_name = (as_match.group("var") if as_match
                else _available_generated_name(match.string, "exc"))
    if as_match:
        clause = clause[:as_match.start()].rstrip()
    clause = clause or "BaseException"
    if "," in clause and not (
            clause.startswith("(") and clause.endswith(")")):
        clause = f"({clause})"
    comment = match.group("comment") or ""
    log_alias = _available_generated_name(match.string, _SILENT_EXCEPT_LOG_ALIAS)
    header = f"{indent}except {clause} as {var_name}:{comment}"
    body_prefix = gap if "\n" in gap else f"\n{pad}"
    return (f"{header}{body_prefix}import logging as {log_alias}\n"
            f"{pad}{log_alias}.getLogger(__name__).warning("
            f"\"静默异常已修复: %s\", {var_name})")
_RETROSPECTIVE_MARKERS: tuple[str, ...] = (
    "复盘", "交付复盘", "回顾",
    "retrospective", "postmortem", "post-mortem", "lessons learned",
    "debrief", "finalize_session", "fupan",
)
def _has_retrospective_section(content: str) -> bool:
    if not isinstance(content, str) or not content:
        return False
    markers = tuple(marker.casefold() for marker in _RETROSPECTIVE_MARKERS)
    parts = split_frontmatter(content)
    body = parts[2] if len(parts) >= 3 else parts[0]
    for line, in_fence in iter_fence_lines(body.splitlines()):
        if in_fence:
            continue
        leading = line[:len(line) - len(line.lstrip(" \t"))]
        if len(leading) > 3 or "\t" in leading:
            continue
        stripped = line[len(leading):]
        hashes = stripped[:len(stripped) - len(stripped.lstrip("#"))]
        if not 1 <= len(hashes) <= 6:
            continue
        heading_text = stripped[len(hashes):]
        if heading_text[:1] and not heading_text[:1].isspace():
            continue
        title = heading_text.strip().casefold()
        if title and any(marker in title for marker in markers):
            return True
    return False
def ensure_fupan_hook(content: str) -> tuple[str, list[str]]:
    logs = []
    content = normalize_newlines(normalize_text(content))
    has_fupan = _has_retrospective_section(content)
    if not has_fupan:
        fupan_template = """

## 交付复盘

> 每次交付前按目标项目流程核查结果、风险与后续事项。
> - 结果核对 → 风险检查 → 后续行动
"""
        content = content.rstrip() + fupan_template + "\n"
        logs.append("已自动注入交付复盘 hook")
        emit_fix_logs(logs, _log, prefix="preflight fixer",
                      warn_prefixes=("警告", "无法"))
    return content, logs
def _require_text(content: Any, tag: str) -> str:
    if not isinstance(content, str) or not content:
        raise ContractViolationError(f"约束违反 [{tag}]: 内容为空或非字符串")
    return content
def _emit_fixed_content(out: dict[str, Any] | None, content: str) -> None:
    if isinstance(out, dict):
        out["content"] = content
def _reject_uncaptured_fix(content: str, fixed_content: str,
                           out: dict[str, Any] | None, tag: str) -> None:
    if isinstance(out, dict):
        return
    if normalize_newlines(fixed_content) != normalize_newlines(content):
        raise ContractViolationError(
            f"约束违反 [{tag}]: 原文存在可自动修复问题，但只读校验未接收修复正文；"
            "请提供 out 接收修复结果，或在写入流程中完成修复后复检")
def check_naming(skill_name: Any, existing_skills: Any) -> tuple:
    fixed_name, _logs = ensure_valid_skill_name(skill_name, existing_skills)
    if not fixed_name or fixed_name == "unnamed-skill":
        raise ContractViolationError("约束违反 [naming]: 技能名无法自动修复，必须至少包含一个字母或数字")
    if fixed_name != skill_name:
        _log.info("check_naming: 名称已自动修复 '%s' → '%s'", skill_name, fixed_name)
    return True, f"命名约束通过: {fixed_name}"
def check_security(content: Any,
                   out: dict[str, Any] | None = None, *,
                   filepath: str = SKILL_DOC_FILENAME) -> tuple:
    content = _require_text(content, "security")
    sanitized = SecurityConstraintSet.enforce_no_secrets_in_source(
        content, filepath)
    _reject_uncaptured_fix(content, sanitized, out, "security")
    _log.info("check_security: 已执行安全脱敏与敏感信息检查")
    _emit_fixed_content(out, sanitized)
    issues = [f"危险函数: {name}" for name in scan_dangerous_calls(sanitized)]
    if issues:
        raise ContractViolationError("约束违反 [security]: 安全风险 — " + "; ".join(issues))
    return True, "安全硬约束通过（已自动修复）"
def check_frontmatter(content: Any,
                      out: dict[str, Any] | None = None) -> tuple:
    content = _require_text(content, "frontmatter")
    fixed_content, logs = ensure_complete_frontmatter(content)
    if "无法自动修复" in " ".join(logs):
        raise ContractViolationError("约束违反 [frontmatter]: " + "; ".join(logs))
    if logs:
        _log.info("check_frontmatter: 已自动修复 %d 个问题", len(logs))
    _reject_uncaptured_fix(content, fixed_content, out, "frontmatter")
    _emit_fixed_content(out, fixed_content)
    missing = _check_frontmatter_fields(fixed_content)
    if missing:
        raise ContractViolationError(
            "约束违反 [frontmatter]: " + "; ".join(missing))
    return True, "frontmatter 硬约束通过（已自动修复）"
def check_cie_antipatterns(content: Any,
                           out: dict[str, Any] | None = None) -> tuple:
    content = _require_text(content, "cie_antipatterns")
    fixed_content, logs = ensure_safe_content(content)
    if logs:
        _log.info("check_cie_antipatterns: 已自动修复 %d 个问题", len(logs))
    _reject_uncaptured_fix(content, fixed_content, out, "cie_antipatterns")
    _emit_fixed_content(out, fixed_content)
    issues = [f"不可自动修复: {name}"
              for name in scan_dangerous_calls(fixed_content, basic_only=True)]
    if issues:
        raise ContractViolationError("约束违反 [cie_antipatterns]: " + "; ".join(issues))
    return True, "CIE 反模式约束通过（已自动修复）"
def check_fupan_hook(content: Any) -> tuple:
    content = _require_text(content, "fupan_hook")
    if not _has_retrospective_section(content):
        _log.info("check_fupan_hook: 正文缺少交付复盘章节，只读硬约束阻断")
        raise ContractViolationError(
            "约束违反 [fupan_hook]: 正文缺少交付复盘章节；"
            "请在写入流程中通过 ensure_fupan_hook 补齐后复检")
    return True, "复盘 hook 已就绪"
def _frontmatter_field_issues(content: str) -> list[str]:
    name, description = parse_frontmatter_text(content)
    issues: list[str] = []
    if not name.strip() or name.lstrip().startswith("#"):
        issues.append("frontmatter 缺少 'name' 字段或字段为空")
    else:
        issues.extend(skill_name_issues(name))
    if not description.strip() or description.lstrip().startswith("#"):
        issues.append("frontmatter 缺少 'description' 字段或字段为空")
    return issues
def _check_frontmatter_fields(content: str) -> list[str]:
    parts = split_frontmatter(content)
    if len(parts) < 3:
        return ["YAML frontmatter 格式不完整"
                if content.lstrip().startswith("---")
                else "SKILL.md 缺少 YAML frontmatter"]
    _meta, reason, detail = load_frontmatter(parts[1])
    if reason == "parse_error":
        return [f"YAML frontmatter 不可解析: {detail}"]
    if reason == "not_dict":
        return ["YAML frontmatter 必须是键值映射"]
    return _frontmatter_field_issues(content)
def _read_skill_md_with_raw(md_path: str) -> tuple[str | None, bytes | None, list[str]]:
    try:
        with open(md_path, "rb") as md_file:
            raw = md_file.read()
    except OSError as e:
        log_swallowed(__name__, e, context=f'_read_skill_md_with_raw:{type(e).__name__}')
        return None, None, [f"SKILL.md 读取失败: {e}"]
    try:
        return raw.decode("utf-8-sig"), raw, []
    except UnicodeDecodeError as e:
        log_swallowed(__name__, e, context=f'_read_skill_md_with_raw:{type(e).__name__}')
        return None, None, [f"SKILL.md 读取失败: {e}"]
def _check_skill_root_hygiene(skill_dir: str) -> list[str]:
    try:
        hits = scan_skill_root_hygiene(skill_dir)
    except Exception as _e:
        _log.warning("技能根卫生检查失败，校验按失败关闭: %s", _e)
        return [f"技能根卫生检查失败（无法完成运行态残留扫描）: {_e}"]
    return [
        f"技能根存在运行态残留: {name}（Temp 治理契约：产物只落会话工作空间；"
        "修复入口 cleanup_residue.purge_skill_root_temp(skill_dir) 归口迁移后回收）"
        for name in hits
    ]
def validate_skill(skill_dir: str) -> tuple[bool, list[str]]:
    skill_dir = _path_arg(skill_dir)
    if not skill_dir or not os.path.isdir(skill_dir):
        return False, [f"目录不存在: {skill_dir}"]
    md_path = os.path.join(skill_dir, "SKILL.md")
    if not os.path.isfile(md_path):
        return False, ["缺少 SKILL.md"]
    content, _raw_md, read_errors = _read_skill_md_with_raw(md_path)
    if content is None:
        return False, read_errors
    errors = _check_frontmatter_fields(content)
    if not os.path.isfile(os.path.join(skill_dir, "__init__.py")):
        errors.append("缺少 __init__.py")
    directory_name = os.path.basename(os.path.abspath(skill_dir))
    errors.extend(skill_name_issues(directory_name))
    frontmatter_name, _description = parse_frontmatter_text(content)
    if frontmatter_name and frontmatter_name != directory_name:
        errors.append(
            f"frontmatter 技能名 '{frontmatter_name}' 与目录名 "
            f"'{directory_name}' 不一致")
    errors.extend(scan_security_issues(skill_dir))
    errors.extend(_check_skill_root_hygiene(skill_dir))
    return not errors, errors
def attach_validation_result(result: dict, key: str, skill_dir: str,
                       label: str) -> None:
    if not isinstance(result, dict) or not isinstance(key, str) or not key:
        _log.warning("%s: 结果包络或挂载键形态非法(result=%s, key=%r)，跳过挂载",
                     label, type(result).__name__, key)
        return
    try:
        ok, errors = validate_skill(skill_dir)
        result[key] = {"ok": ok, "errors": errors}
        if not ok:
            _log.warning("%s发现问题: %s", label, errors)
    except Exception as e:
        _log.warning("%s异常: %s", label, e)
        result[key] = {"ok": False, "errors": [str(e)]}
@observation_gate("Semantic consistency check")
def run_semantic_consistency_gate(target_dir: str) -> None:
    target_dir = _path_arg(target_dir)
    if not target_dir:
        _log.warning(
            "[init] Semantic consistency check skipped: target_dir 为空或非法")
        return
    skills_root = os.path.dirname(os.path.normpath(target_dir)) or '.'
    semantic_report = validate_semantic_consistency(skills_root)
    semantic_ok = (
        not getattr(semantic_report, 'semantic_gaps', ())
        and getattr(semantic_report, 'total_skills', 0) > 0
    )
    _log.info(
        "[init] Semantic consistency check: ok=%s, total=%d, issues=%d",
        semantic_ok, getattr(semantic_report, 'total_skills', 0),
        len(getattr(semantic_report, 'issues', ())),
    )
def _run_post_create_gate(label: str, gate, *args) -> None:
    try:
        gate(*args)
    except Exception as exc:
        _log.warning("[init] %s 门禁异常，已隔离: %s", label, exc)
def run_post_create_quality_gates(target_dir: str, skill_md_path: str) -> None:
    _run_post_create_gate(
        "Semantic consistency", run_semantic_consistency_gate, target_dir)
    _run_post_create_gate(
        "Document completeness", run_document_completeness_gate, skill_md_path)
    _run_post_create_gate(
        "Code quality", run_code_quality_gate, target_dir)
    _run_post_create_gate(
        "Architecture quality", run_architecture_quality_gate, target_dir)
    _run_post_create_gate(
        "IO standardization", run_io_standardization_gate, target_dir)
def _read_raw_bytes(path: str) -> bytes:
    with open(path, "rb") as raw_file:
        return raw_file.read()
def _write_back_init_module_safety(init_py_path: str, safe_content: str,
                                   raw: bytes) -> bool:
    try:
        write_text_preserving_form(init_py_path, safe_content, raw)
        return True
    except (OSError, ValueError, RuntimeError) as exc:
        log_swallowed(__name__, exc,
                      context=f'_write_back_init_module_safety:{type(exc).__name__}')
        return False
def ensure_init_module_safety(result_dir: str) -> tuple[list[dict], list[dict]]:
    init_py_path = os.path.join(result_dir, "__init__.py")
    if not os.path.isfile(init_py_path):
        return [], []
    try:
        raw_init = _read_raw_bytes(init_py_path)
        init_content = raw_init.decode("utf-8-sig")
        init_safe_content, init_safe_logs = ensure_safe_content(
            init_content, filepath="__init__.py")
        basic_dangers = scan_dangerous_calls(
            init_safe_content, basic_only=True)
        extra_dangers = [
            name for name in scan_dangerous_calls(init_safe_content)
            if name not in basic_dangers
        ]
        if extra_dangers:
            init_safe_logs.append(
                "警告: 仍存在不可自动修复的危险函数: "
                + ", ".join(extra_dangers))
    except (OSError, UnicodeDecodeError) as exc:
        _log.warning("Init.py safety scan failed: %s", exc)
        return [], [{
            "step": "init_safety",
            "severity": "blocker",
            "detail": f"__init__.py 安全扫描失败，未执行写回: {exc}",
        }]
    fixes: list[dict] = []
    warnings: list[dict] = []
    content_changed = init_safe_content != init_content
    write_failed = bool(
        content_changed and not _write_back_init_module_safety(
            init_py_path, init_safe_content, raw_init))
    record_fix_entries(
        "init_safety", init_safe_logs, fixes, warnings,
        all_warnings=write_failed)
    for warning in warnings:
        warning["severity"] = "blocker"
    if write_failed:
        warnings.append({"step": "init_safety", "severity": "blocker",
                         "detail": "脱敏结果写回失败，__init__.py 仍保留原内容"})
    return fixes, warnings
def _probe_structure(result_dir: str, resources: list,
                     logs: list[str]) -> bool:
    if not os.path.isdir(result_dir):
        logs.append(f"技能目录不存在: {result_dir}")
        return False
    ok = True
    for filename in ("SKILL.md", "__init__.py"):
        if not os.path.isfile(os.path.join(result_dir, filename)):
            logs.append(f"缺少 {filename}")
            ok = False
    for name in resources:
        if not os.path.isdir(os.path.join(result_dir, name)):
            logs.append(f"缺少资源目录: {name}")
            ok = False
    return ok
def _probe_creation_structure(
        result_dir: str, resources: list[str], logs: list[str]) -> bool:
    if _is_filesystem_root(result_dir):
        logs.append(
            "无法自动创建技能目录（文件系统根拒绝写入技能文件，防外部污染）: "
            f"{result_dir}")
        return False
    if not os.path.isdir(result_dir):
        blocker = dir_creation_blocker(result_dir)
        if blocker:
            logs.append(f"无法自动创建技能目录（{blocker}）: {result_dir}")
            return False
        return True
    if not os.access(result_dir, os.W_OK):
        logs.append(f"无法写入技能目录（不可写）: {result_dir}")
        return False
    valid = True
    for filename in ("SKILL.md", "__init__.py"):
        path = os.path.join(result_dir, filename)
        if os.path.lexists(path) and not os.path.isfile(path):
            logs.append(f"无法创建 {filename}（目标不是文件）: {path}")
            valid = False
    for name in resources:
        path = os.path.join(result_dir, name)
        if os.path.lexists(path) and not os.path.isdir(path):
            logs.append(f"无法创建资源目录 {name}（目标不是目录）: {path}")
            valid = False
    return valid
def _ensure_structure(result_dir: str, resources: Any,
                      fixes: list, warnings: list,
                      create_missing: bool, dry_run: bool = False) -> bool:
    blocked = False
    if result_dir:
        struct_logs: list[str] = []
        normalized_resources, resources_valid = _normalize_resource_declarations(
            resources, struct_logs)
        if not resources_valid:
            record_fix_entries(
                "structure", struct_logs, fixes, warnings, all_warnings=True)
            warnings.append({
                "step": "structure", "severity": "blocker",
                "detail": "资源声明包含非法或未知类型，已阻断创建",
            })
            return True
        if create_missing and dry_run:
            struct_valid = _probe_creation_structure(
                result_dir, normalized_resources, struct_logs)
        elif create_missing:
            struct_valid, write_logs = ensure_valid_structure(
                result_dir, normalized_resources)
            struct_logs.extend(write_logs)
        else:
            struct_valid = _probe_structure(
                result_dir, normalized_resources, struct_logs)
        record_fix_entries("structure", struct_logs, fixes, warnings,
                            all_warnings=not create_missing)
        if not struct_valid:
            blocked = True
            warnings.append({"step": "structure", "severity": "blocker",
                             "detail": "目录结构无法自动修复"})
    return blocked
def _path_arg(value: Any) -> str:
    return normalize_out_path(value) or ""
def _runtime_dir_name(value: Any) -> str:
    name = normalize_out_path(value) or RUNTIME_DIR_NAME
    if (name in (".", "..") or os.path.isabs(name)
            or os.path.basename(name) != name):
        _log.warning("运行时目录名必须是单段目录名，回落默认值: %r", value)
        return RUNTIME_DIR_NAME
    return name
def check_runtime_temp_residue(
        skill_dir: Any, runtime_dir_name: str = RUNTIME_DIR_NAME) -> list[dict]:
    skill_dir = _path_arg(skill_dir)
    if not skill_dir:
        return []
    dir_name = _runtime_dir_name(runtime_dir_name)
    warnings: list[dict] = []
    try:
        if not os.path.isdir(skill_dir):
            return warnings
        if not any(
                os.path.exists(os.path.join(skill_dir, marker))
                for marker in (*PROJECT_ROOT_MARKERS, "__init__.py")):
            return warnings
        temp_dir = os.path.join(os.path.realpath(skill_dir), dir_name)
        if not os.path.isdir(temp_dir):
            return warnings
        entries = os.listdir(temp_dir)
        if entries:
            warnings.append({
                "step": "runtime_temp_residue",
                "severity": "warning",
                "detail": (
                    "项目根 " + dir_name + "/ 存在 " + str(len(entries))
                    + " 项内容；请按目标项目约定核查是否为运行时残留，"
                    + "不得在未确认用途前自动清理"
                ),
            })
    except OSError as exc:
        _log.debug("runtime temp residue check skipped: %s", exc)
    return warnings
def _write_back_result_content(skill_dir: str, final_content: str,
                                 result: dict) -> bool:
    md_path = os.path.join(skill_dir, "SKILL.md")
    raw = b""
    if os.path.isfile(md_path):
        try:
            raw = _read_raw_bytes(md_path)
        except OSError as _e:
            log_swallowed(
                __name__, _e,
                context=f'_write_back_result_content:{type(_e).__name__}')
            result["warnings"].append({
                "step": "write_back", "severity": "blocker",
                "detail": f"SKILL.md 读取失败，已阻断写回: {_e}",
            })
            return False
    if raw:
        try:
            existing = raw.decode("utf-8-sig")
        except UnicodeDecodeError as _e:
            log_swallowed(
                __name__, _e,
                context=f'_write_back_result_content:{type(_e).__name__}')
            result["warnings"].append({
                "step": "write_back", "severity": "blocker",
                "detail": f"SKILL.md 不是有效 UTF-8，已阻断写回: {_e}",
            })
            return False
        if (normalize_newlines(existing)
                == normalize_newlines(final_content)):
            result["warnings"].append({
                "step": "write_back", "severity": "info",
                "detail": "内容未变化，已跳过写回: " + md_path})
            return True
    try:
        write_text_preserving_form(md_path, final_content, raw)
        result["content_written"] = True
        result["warnings"].append({
            "step": "write_back", "severity": "info",
            "detail": "已写回 " + md_path})
        return True
    except (OSError, ValueError, RuntimeError) as exc:
        log_swallowed(__name__, exc,
                      context=f'_write_back_result_content:{type(exc).__name__}')
        result["warnings"].append({
            "step": "write_back", "severity": "warning",
            "detail": "写回失败: " + str(exc)})
        return False
def build_creation_validation_assets(
    skill_name: str, opt_result: MetadataOptimizationResult,
    existing_descriptions: list[str] | None = None,
) -> dict[str, Any]:
    doc_assets = build_creation_doc_assets(
        skill_name, opt_result.optimized_description, existing_descriptions)
    return {
        "semantic_index": build_creation_semantic_index(skill_name, opt_result),
        "func_result": build_function_schema(
            skill_name, opt_result.optimized_description),
        **doc_assets,
    }
_DEFAULT_SCAFFOLD_DIRS = tuple(sorted(ALLOWED_RESOURCES))
def _declared_resource_items(raw: Any) -> list[Any] | None:
    if isinstance(raw, str):
        return [item for item in re.split(r"[,，]", raw) if item.strip()]
    if isinstance(raw, (set, frozenset)):
        return sorted(raw, key=lambda item: (str(item).strip(), repr(item)))
    if isinstance(raw, (list, tuple)):
        return list(raw)
    return None
def _analyze_resource_declarations(
        resources: Any) -> tuple[list[str], list[str]]:
    if resources is None:
        return [], []
    items = _declared_resource_items(resources)
    if items is None:
        return [], [
            (f"非法资源声明类型: {type(resources).__name__}"
             "（须为逗号分隔字符串或列表）")]
    valid: list[str] = []
    invalid: list[Any] = []
    unknown: list[str] = []
    for item in items:
        if not isinstance(item, str):
            invalid.append(item)
            continue
        key = item.strip().lower()
        if key in ALLOWED_RESOURCES:
            valid.append(key)
        elif key:
            unknown.append(item.strip())
    errors: list[str] = []
    if invalid:
        errors.append(
            f"非法资源声明项类型: {invalid!r}（只接受字符串资源类型）")
    if unknown:
        allowed = ", ".join(sorted(ALLOWED_RESOURCES))
        errors.append(
            f"未知资源类型: {', '.join(unknown)}; 允许值: {allowed}")
    return list(dict.fromkeys(valid)), errors
def _normalize_resource_declarations(
        resources: Any, logs: list[str]) -> tuple[list[str], bool]:
    valid, errors = _analyze_resource_declarations(resources)
    logs.extend(f"无法自动修复: {error}" for error in errors)
    return valid, not errors
def parse_resources(raw_resources: str | list | None) -> list[str]:
    valid, errors = _analyze_resource_declarations(raw_resources)
    if errors:
        raise ValueError("; ".join(errors))
    return valid
def _is_filesystem_root(path) -> bool:
    try:
        normalized = os.path.normpath(os.path.abspath(os.fspath(path)))
    except (OSError, ValueError, TypeError) as _swallow_e:
        log_swallowed(__name__, _swallow_e, context=f'_is_filesystem_root:{type(_swallow_e).__name__}')
        return False
    return os.path.dirname(normalized) == normalized
def _scaffold_target(target_dir: Any) -> str:
    resolved = normalize_out_path(target_dir)
    if resolved is None:
        raise ValueError(f"技能目录为空或非路径类型: {target_dir!r}")
    if _is_filesystem_root(resolved):
        raise ValueError(
            f"拒绝以文件系统根作为技能目录（防外部污染）: {resolved}")
    return resolved
def create_resource_dirs(target_dir: str, resources: list) -> list:
    root = _scaffold_target(target_dir)
    names = parse_resources(resources)
    if not names:
        return []
    if not os.path.isdir(root):
        root_logs: list[str] = []
        if not ensure_root_dir(root, root_logs):
            raise OSError("；".join(root_logs) or f"技能目录不可用: {root}")
    logs: list[str] = []
    if not _ensure_resource_dirs(root, names, logs):
        raise OSError("资源目录创建失败: " + "; ".join(logs))
    emit_fix_logs(logs, _log, prefix="preflight fixer",
                  warn_prefixes=("警告", "无法"))
    return [os.path.join(root, name) for name in names]
def create_skill_directories(target_dir: str) -> list:
    root = _scaffold_target(target_dir)
    logs: list[str] = []
    if not ensure_root_dir(root, logs):
        raise OSError("；".join(logs) or f"技能目录不可用: {root}")
    emit_fix_logs(logs, _log, prefix="preflight fixer",
                  warn_prefixes=("警告", "无法"))
    return [root, *create_resource_dirs(root, _DEFAULT_SCAFFOLD_DIRS)]
def resolve_target_dir(target_dir: str | os.PathLike | None,
                       name: str) -> str:
    if target_dir is None or (isinstance(target_dir, str)
                              and not target_dir.strip()):
        if not isinstance(name, str) or not name.strip():
            raise ValueError("技能名不能为空，无法解析默认目标目录")
        return os.path.join(os.getcwd(), name)
    resolved = normalize_out_path(target_dir)
    if resolved is None:
        raise ValueError(
            f"目标目录路径类型无效: {type(target_dir).__name__}")
    return resolved
def record_fix_entries(step: str, entries: list[str], fixes: list[dict],
                        warnings: list[dict], *,
                        all_warnings: bool = False) -> None:
    for entry in entries:
        if entry is None:
            continue
        text = entry if isinstance(entry, str) else str(entry)
        if not text.strip():
            continue
        if all_warnings or text.startswith(("无法", "警告", "已忽略")):
            warnings.append(
                {"step": step, "severity": "warning", "detail": text})
        else:
            fixes.append(
                {"step": step, "action": "auto_fix", "detail": text})
def ensure_root_dir(skill_dir, logs: list[str]) -> bool:
    if not isinstance(skill_dir, (str, os.PathLike)):
        logs.append(f"无法自动创建技能目录（非路径入参）: {skill_dir!r}")
        return False
    skill_dir = _path_arg(skill_dir)
    if not skill_dir:
        logs.append("无法自动创建技能目录（路径为空或非法）")
        return False
    if _is_filesystem_root(skill_dir):
        _log.error(
            "ensure_root_dir: 拒绝以文件系统根作为技能目录（防外部污染）: %s", skill_dir)
        logs.append(
            f"无法自动创建技能目录（文件系统根拒绝写入技能文件，防外部污染）: {skill_dir}")
        return False
    if os.path.isdir(skill_dir):
        if not os.access(skill_dir, os.W_OK):
            _log.error("ensure_root_dir: 技能目录不可写: %s", skill_dir)
            logs.append(f"无法写入技能目录（不可写）: {skill_dir}")
            return False
        return True
    blocker = dir_creation_blocker(skill_dir)
    if blocker:
        _log.error("ensure_root_dir: 技能目录无法创建（%s）: %s",
                   blocker, skill_dir)
        logs.append(f"无法自动创建技能目录（{blocker}）: {skill_dir}")
        return False
    try:
        os.makedirs(skill_dir, exist_ok=True)
    except (OSError, ValueError) as e:
        _log.exception("ensure_root_dir failed")
        logs.append(f"无法自动创建技能目录: {skill_dir}（{e}）")
        return False
    logs.append(f"已自动创建技能目录: {skill_dir}")
    return True
def _ensure_resource_dirs(skill_dir, resources: list[str],
                           logs: list[str]) -> bool:
    all_valid = True
    for resource_dir in resources:
        target_dir = os.path.join(skill_dir, resource_dir)
        if os.path.isdir(target_dir):
            continue
        blocker = dir_creation_blocker(target_dir)
        if blocker:
            _log.error("_ensure_resource_dirs: 资源目录无法创建 %s（%s）: %s",
                       resource_dir, blocker, target_dir)
            logs.append(f"无法创建资源目录 {resource_dir}（{blocker}）")
            all_valid = False
            continue
        try:
            os.makedirs(target_dir, exist_ok=True)
            logs.append(f"已自动创建资源目录: {resource_dir}")
        except (OSError, ValueError) as e:
            _log.exception(
                "_ensure_resource_dirs failed to create resource dir: %s",
                resource_dir)
            logs.append(f"无法创建资源目录 {resource_dir}（{e}）")
            all_valid = False
    return all_valid
def _ensure_core_files(skill_dir: str, base_name: str,
                       logs: list[str]) -> bool:
    skill_md = os.path.join(skill_dir, "SKILL.md")
    md_ok = _create_file_guarded(
        skill_md, render_minimal_skill_md(base_name), "SKILL.md", logs)
    init_py = os.path.join(skill_dir, "__init__.py")
    init_ok = _create_file_guarded(init_py, f"# {base_name}\n", "__init__.py", logs)
    return md_ok and init_ok
def ensure_valid_structure(skill_dir: str, resources: list[str] | None = None
                           ) -> tuple[bool, list[str]]:
    logs = []
    all_valid = True
    skill_dir = _path_arg(skill_dir)
    if not skill_dir:
        return False, ["无法自动修复: skill_dir 为空或非路径类型"]
    resources, resources_valid = _normalize_resource_declarations(
        resources, logs)
    if not resources_valid:
        return False, logs
    if not ensure_root_dir(skill_dir, logs):
        return False, logs
    base_name = os.path.basename(os.path.abspath(skill_dir))
    if not _ensure_core_files(skill_dir, base_name, logs):
        all_valid = False
    if not _ensure_resource_dirs(skill_dir, resources, logs):
        all_valid = False
    emit_fix_logs(logs, _log, prefix="preflight fixer",
                  warn_prefixes=("警告", "无法"))
    return all_valid, logs
def _create_file_guarded(path: str, content: str, label: str,
                           logs: list[str]) -> bool:
    if os.path.isfile(path):
        return True
    try:
        with guarded_open(path, "x", encoding="utf-8", newline="") as f:
            f.write(content)
        logs.append(f"已自动创建 {label}")
        return True
    except (OSError, ValueError) as _e:
        log_swallowed(__name__, _e, context=f'_create_file_guarded:{type(_e).__name__}')
        logs.append(f"无法创建 {label}（{type(_e).__name__}: {_e}）")
        return False
def check_structure(skill_dir: Any, resources: Any) -> tuple:
    struct_valid, logs = ensure_valid_structure(skill_dir, resources)
    fixed = [entry for entry in logs if not entry.startswith("无法")]
    failed = [entry for entry in logs if entry.startswith("无法")]
    if fixed:
        _log.info("check_structure: 已自动修复 %d 个问题", len(fixed))
    if failed:
        _log.warning("check_structure: %d 个问题无法自动修复", len(failed))
    if not struct_valid:
        raise ContractViolationError("约束违反 [structure]: " + "; ".join(logs))
    return True, "结构硬约束通过（已自动修复）"

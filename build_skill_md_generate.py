# ruff: noqa: I001
import json
import logging
import math
import os
import stat
from collections.abc import Callable, Mapping
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, ClassVar, Self
from jwsgj.build_skill_api_contract import (
    SkillApiScanner,
    scan_skill_api,
)
from jwsgj.build_skill_md_optimize import (
    evaluate_description,
)
from jwsgj.build_skill_md_quality import skill_name_issues
from jwsgj.build_text_document import (
    detect_text_language,
    normalize_str,
    normalize_str_list,
    normalize_text,
    readable_skill_name,
)
from jwsgj.build_text_frontmatter import parse_frontmatter_dict
from jwsgj.build_text_scoring import (
    STANDARD_SECTIONS,
    build_skill_frontmatter,
    extract_boundary_scopes,
    infer_skill_type,
    keyword_matches,
    negative_query_for_boundary,
    sanitize_upload_description,
)
from jwsgj.diag_guard_io import (
    guarded_open,
    normalize_out_path,
)
from jwsgj.diag_self_check import (
    DependencyCheckResult,
    DependencyManager,
    check_python_deps,
    check_system_tools,
    module_available,
    normalize_check_items,
)
from jwsgj.diag_types_vocab import (
    FIELD_TRIGGER_EXAMPLES,
    MAX_SKILL_NAME_LENGTH,
    SKILL_NAME_MIN_LEN,
)
from jwsgj.log_config import log_swallowed, observation_gate
from jwsgj.runtime_paths import is_dir_creation_allowed, normalize_skill_name
from jwsgj.runtime_scope import is_test_source_basename, py_stem
from jwsgj.skill_doc_diagnoser import (
    diag_skill_doc,
    get_doc_diagnoser,
    get_pattern_hint,
    infer_design_pattern,
)
from jwsgj.skill_doc_render import (
    DOMAIN_SKIP_DIRS,
    append_block,
    build_refactored_body,
    build_unified_skill_md_body,
    get_generator,
    member_entries,
    module_display_name,
    normalize_dict_seq,
    normalize_str_seq,
    text_field,
)
__all__ = [
    'ExampleBlock',
    'FeasibilityResult',
    'PromptExampleBuilder',
    'PromptExampleResult',
    'SkillDocCreator',
    'append_dependency_warnings',
    'build_creation_doc_assets',
    'build_creation_result',
    'build_refactor_content',
    'create_skill_doc',
    'dir_creation_blocker',
    'ensure_valid_skill_name',
    'generate_example_section',
    'get_creator',
    'improve_description_from_issues',
    'is_path_input',
    'parse_dependency_spec',
    'prepare_skill_metadata',
    'profile_created_skill',
    'render_report_dict',
    'run_bare_step0',
    'run_document_completeness_gate',
    'step0_bare_evaluation',
    'title_case_skill_name',
]
_log = logging.getLogger(__name__)
@dataclass(frozen=True)
class _CreateInputs:
    skill_name: str
    capabilities: list[str]
    exclusion_scopes: list[str]
    colloquial_examples: list[str]
    body_sections: list[dict[str, str]]
    extra_frontmatter: dict[str, Any]
    scan_result: dict[str, Any] | None
    generated_desc: str
_GENERATOR_HIGH_RULE_THRESHOLD = 2
_DEFAULT_DIAG_AFTER = True
def _text_of(value: Any) -> str:
    return value if isinstance(value, str) else ""
def _seq_len(value: Any) -> int:
    return len(value) if isinstance(value, (list, tuple, set, frozenset, dict)) else 0
def _count_of(value: Any) -> int:
    return value if isinstance(value, int) and not isinstance(value, bool) and value >= 0 else 0
def _issue_field(issue: Any, field_name: str) -> Any:
    if isinstance(issue, Mapping):
        return issue.get(field_name, "")
    return getattr(issue, field_name, "")
def _issue_rule_ids(issue_items: list[Any], severity: str) -> set[str]:
    wanted = normalize_text(severity).strip().casefold()
    return {_text_of(_issue_field(i, "rule_id")).strip().upper()
            for i in issue_items
            if (normalize_text(_issue_field(i, "severity"))
                .strip().casefold() == wanted)}
def _should_use_generator(critical_rule_ids: set,
                            high_rule_ids: set) -> tuple[bool, list[str]]:
    rules = (
        ("DR-001" in critical_rule_ids or "DR-006" in critical_rule_ids,
         "description 严重违规，使用 MatchingDescriptionGenerator 完全重写"),
        (len(high_rule_ids) >= _GENERATOR_HIGH_RULE_THRESHOLD,
         "多处 high 违规，使用生成器重建 description"),
    )
    reasons = [message for hit, message in rules if hit]
    return bool(reasons), reasons
def _rewrite_description_with_generator(desc_generator: Any,
                                        skill_name: str,
                                        current_desc: str,
                                        keywords: list[str],
                                        capabilities: list[str],
                                        file_extensions: list[str],
                                        exclusion_scopes: list[str],
                                        ) -> tuple[str, list[str]]:
    result = desc_generator.generate_from_diag(
        skill_name=skill_name,
        current_description=current_desc,
        keywords=keywords,
        capabilities=capabilities or None,
        file_extensions=file_extensions or None,
        exclusion_scopes=exclusion_scopes or None,
    )
    if not isinstance(result, Mapping):
        return current_desc, []
    new_desc = result.get("improved_description")
    if not isinstance(new_desc, str) or not new_desc.strip():
        return current_desc, []
    return new_desc, normalize_str_list(result.get("improvements"))
def _refine_description_with_generator(desc_generator: Any,
                                        skill_name: str,
                                        current_desc: str,
                                        keywords: list[str],
                                        ) -> tuple[str, list[str]]:
    refine_result = desc_generator.refine_description(
        skill_name, current_desc, keywords,
    )
    if not isinstance(refine_result, Mapping):
        return current_desc, []
    changes = normalize_str_list(refine_result.get("changes"))
    refined = refine_result.get("refined")
    if not isinstance(refined, str) or not refined.strip():
        return current_desc, []
    return refined, changes
def improve_description_from_issues(
        skill_name: str, current_desc: str, keywords: list[str],
        issues: list[Any], *, capabilities: list[str] | None = None,
        file_extensions: list[str] | None = None,
        exclusion_scopes: list[str] | None = None) -> dict[str, Any]:
    desc_generator = get_generator()
    if desc_generator is None:
        return {"description": current_desc, "improvements": []}
    if isinstance(issues, Mapping):
        issue_items = [issues]
    elif isinstance(issues, (list, tuple)):
        issue_items = list(issues)
    else:
        issue_items = []
    keywords = normalize_str_list(keywords)
    capabilities = normalize_str_list(capabilities)
    file_extensions = normalize_str_list(file_extensions)
    exclusion_scopes = normalize_str_list(exclusion_scopes)
    critical_rule_ids = _issue_rule_ids(issue_items, "critical")
    high_rule_ids = _issue_rule_ids(issue_items, "high")
    use_generator, reasons = _should_use_generator(
        critical_rule_ids, high_rule_ids)
    try:
        if use_generator:
            new_desc, gen_improvements = _rewrite_description_with_generator(
                desc_generator, skill_name, current_desc, keywords,
                capabilities or [], file_extensions or [], exclusion_scopes or [])
            return {"description": new_desc,
                    "improvements": list(reasons) + list(gen_improvements)}
        new_desc, refine_changes = _refine_description_with_generator(
            desc_generator, skill_name, current_desc, keywords)
        return {"description": new_desc, "improvements": list(refine_changes)}
    except Exception as e:  #noqa:BLE001
        _log.warning("description 生成器调用失败（保留原描述）: %s", e)
        return {
            "description": current_desc,
            "improvements": [
                f"description 生成器调用失败，已保留原描述: {str(e)[:120]}"],
        }
class SkillDocCreator:
    def __init__(self: Self) -> None:
        self._generator = get_generator()
    def create(self: Self, skill_name: str,
               domain: str = "",
               capabilities: list[str] | None = None,
               keywords: list[str] | None = None,
               file_extensions: list[str] | None = None,
               exclusion_scopes: list[str] | None = None,
               colloquial_examples: list[str] | None = None,
               body_sections: list[dict[str, str]] | None = None,
               extra_frontmatter: dict[str, Any] | None = None,
               skill_dir: str = "") -> dict[str, Any]:
        if not isinstance(skill_name, str) or not skill_name.strip():
            _log.warning("[SkillDocCreator] skill_name 为空或类型无效: %r", skill_name)
            return {"status": "error", "error": "skill_name 必须为非空字符串"}
        skill_name = skill_name.strip()
        if not normalize_skill_name(skill_name):
            _log.warning(
                "[SkillDocCreator] skill_name 归一化后为空: %r", skill_name)
            return {
                "status": "error",
                "error": "skill_name 必须至少包含一个字母或数字",
            }
        skill_name, name_logs = ensure_valid_skill_name(skill_name)
        if name_logs:
            _log.info("[SkillDocCreator] 技能名归一化: %s", "; ".join(name_logs))
        capabilities = normalize_str_seq(capabilities)
        keywords = normalize_str_seq(keywords)
        file_extensions = normalize_str_seq(file_extensions)
        exclusion_scopes = normalize_str_seq(exclusion_scopes)
        colloquial_examples = normalize_str_seq(colloquial_examples)
        if isinstance(body_sections, Mapping):
            body_sections = [dict(body_sections)]
        body_sections = normalize_dict_seq(body_sections)
        extra_frontmatter = (
            dict(extra_frontmatter) if isinstance(extra_frontmatter, Mapping) else {}
        )
        scan_result = self._scan_skill_dir_safe(skill_dir)
        generated_desc = self._generate_description(
            skill_name, domain, capabilities, keywords,
            file_extensions, exclusion_scopes, colloquial_examples,
        )
        return self._render_document(_CreateInputs(
            skill_name=skill_name,
            capabilities=capabilities,
            exclusion_scopes=exclusion_scopes,
            colloquial_examples=colloquial_examples,
            body_sections=body_sections,
            extra_frontmatter=extra_frontmatter,
            scan_result=scan_result,
            generated_desc=generated_desc,
        ))
    def _render_document(self: Self, inputs: _CreateInputs) -> dict[str, Any]:
        frontmatter = build_skill_frontmatter(
            inputs.skill_name, inputs.generated_desc, inputs.extra_frontmatter)
        domains, scripts, file_tree = self._build_scan_artifacts(
            inputs.scan_result)
        body = build_unified_skill_md_body(
            skill_name=inputs.skill_name,
            capabilities=inputs.capabilities,
            exclusion_scopes=inputs.exclusion_scopes,
            domains=domains,
            file_tree=file_tree,
            scripts=scripts,
            trigger_examples=inputs.colloquial_examples or None,
        )
        body, custom_titles = _append_custom_sections(
            body, inputs.body_sections)
        full_content = f"{frontmatter}\n\n{body}"
        return {
            "status": "ok",
            "content": full_content,
            "full_content": full_content,
            "frontmatter": frontmatter,
            "body": body,
            "description": inputs.generated_desc,
            "sections": _resolve_sections_meta(custom_titles),
            "line_count": len(full_content.splitlines()),
            "body_line_count": len(body.splitlines()),
        }
    def _scan_skill_dir_safe(self: Self, skill_dir: str) -> dict[str, Any] | None:
        skill_dir = normalize_out_path(skill_dir)
        if not skill_dir or not os.path.isdir(skill_dir):
            return None
        try:
            scan_result = SkillApiScanner.scan_skill_dir(skill_dir)
        except Exception as e:  #noqa:BLE001
            _log.warning("AST扫描失败: %s", e)
            return None
        if not isinstance(scan_result, dict):
            _log.warning("AST扫描结果非映射，按未扫描处理: %s",
                         type(scan_result).__name__)
            return None
        _log.info(
            "[SkillDocCreator] AST扫描完成: %d 文件, %d 函数, %d 类, %d 脚本",
            _seq_len(scan_result.get("files")),
            _count_of(scan_result.get("total_public_functions")),
            _count_of(scan_result.get("total_public_classes")),
            _seq_len(scan_result.get("scripts")),
        )
        return scan_result
    @staticmethod
    def _infer_file_domain(fname: str, rel_path: str = "") -> str:
        parts = [p for p in rel_path.replace("\\", "/").split("/") if p]
        if len(parts) > 1:
            directories = parts[:-1]
            if directories[0].lower() in ("src", "source") and len(directories) > 1:
                return directories[1]
            return directories[0]
        stem = py_stem(fname)
        prefix, separator, _remainder = stem.partition("_")
        return prefix if separator and prefix else "根模块"
    @staticmethod
    def _domain_entry(f: dict[str, Any], fname: str,
                      rel_path: str = "") -> dict[str, str]:
        if not isinstance(f, dict):
            f = {}
        public_funcs = member_entries(f, "functions")
        entry = text_field(public_funcs[0], "name") if public_funcs else ""
        return {
            "name": module_display_name(rel_path or fname),
            "entry": entry,
        }
    @classmethod
    def _file_domain_entry(cls, f: dict[str, Any]) -> tuple[str, dict[str, str]] | None:
        raw_path = f.get("file", "")
        if not isinstance(raw_path, str):
            return None
        parts = [p for p in raw_path.replace("\\", "/").split("/") if p]
        if not parts:
            return None
        fname = parts[-1]
        if (fname.startswith("_")
                or fname.lower() == "conftest.py"
                or is_test_source_basename(fname)
                or any(p.lower() in DOMAIN_SKIP_DIRS or p.startswith(".")
                       for p in parts[:-1])):
            return None
        rel_path = "/".join(parts)
        return (cls._infer_file_domain(fname, rel_path),
                cls._domain_entry(f, fname, rel_path))
    def _group_files_to_domains(self: Self, files: list[dict[str, Any]]) -> dict[str, list[dict]]:
        domain_map: dict[str, list[dict]] = {}
        for f in files:
            if not isinstance(f, dict):
                continue
            parsed = self._file_domain_entry(f)
            if parsed is None:
                continue
            domain, entry_dict = parsed
            domain_map.setdefault(domain, []).append(entry_dict)
        return domain_map
    def _build_scan_artifacts(self: Self, scan_result: dict[str, Any]
                              ) -> tuple[Any, Any, Any]:
        if not scan_result:
            return None, None, ""
        files = scan_result.get("files")
        domains = self._group_files_to_domains(files) if files else None
        return (domains, _script_entries(scan_result),
                _text_of(scan_result.get("file_tree")))
    def create_and_save(self: Self, target_dir: str,
                        skill_name: str, domain: str = "",
                        capabilities: list[str] | None = None,
                        keywords: list[str] | None = None,
                        file_extensions: list[str] | None = None,
                        exclusion_scopes: list[str] | None = None,
                        colloquial_examples: list[str] | None = None,
                        body_sections: list[dict[str, str]] | None = None,
                        extra_frontmatter: dict[str, Any] | None = None,
                        skill_dir: str = "",
                        diag_after: bool = _DEFAULT_DIAG_AFTER) -> dict[str, Any]:
        _raw_target_dir = target_dir
        target_dir = normalize_out_path(target_dir)
        if target_dir is None:
            _log.warning("[SkillDocCreator] target_dir 非法或空白: %r",
                         _raw_target_dir)
            return {"status": "error", "path": "",
                    "detail": "target_dir 必须为非空字符串路径"}
        if not isinstance(skill_name, str) or not skill_name.strip():
            _log.warning("[SkillDocCreator] skill_name 为空或类型无效: %r",
                         skill_name)
            return {"status": "error", "path": "",
                    "detail": "skill_name 必须为非空字符串"}
        blocker = dir_creation_blocker(target_dir)
        if blocker:
            _log.warning("[SkillDocCreator] 目标目录创建被阻断: %s", blocker)
            return {"status": "error", "path": "", "detail": blocker}
        ast_dir = normalize_out_path(skill_dir) or target_dir
        result = self.create(
            skill_name=skill_name,
            domain=domain,
            capabilities=capabilities,
            keywords=keywords,
            file_extensions=file_extensions,
            exclusion_scopes=exclusion_scopes,
            colloquial_examples=colloquial_examples,
            body_sections=body_sections,
            extra_frontmatter=extra_frontmatter,
            skill_dir=ast_dir,
        )
        if result.get("status") != "ok":
            return {
                "status": "error",
                "path": "",
                "create_result": result,
                "detail": result.get("error", "技能文档创建失败"),
            }
        md_path = os.path.join(target_dir, "SKILL.md")
        _write_err = _write_skill_md(target_dir, md_path, result["full_content"])
        if _write_err is not None:
            _log.error("[SkillDocCreator] SKILL.md 写盘失败: %s", _write_err)
            return {
                "status": "error",
                "path": md_path,
                "create_result": result,
                "detail": f"SKILL.md 写盘失败: {_write_err}",
            }
        output: dict[str, Any] = {
            **result,
            "status": "ok",
            "path": md_path,
            "create_result": result,
        }
        if diag_after:
            output.update(self._post_create_diag(md_path, ast_dir))
        return output
    def _post_create_diag(self: Self, md_path: str,
                          ast_dir: str) -> dict[str, Any]:
        try:
            diag_result = get_doc_diagnoser().diag(md_path, skill_dir=ast_dir)
            return {"diag_result": diag_result.to_dict()}
        except Exception as e:  #noqa:BLE001
            _log.warning("[SkillDocCreator] 创建后自动诊断失败（降级继续）: %s", e)
            return {"diag_error": str(e)[:100]}
    def _generate_description(self: Self, skill_name: str,
                               domain: str,
                               capabilities: list[str],
                               keywords: list[str],
                               file_extensions: list[str],
                               exclusion_scopes: list[str],
                               colloquial_examples: list[str]) -> str:
        if self._generator:
            try:
                gen_result = self._generator.generate_and_validate(
                    skill_name=skill_name,
                    domain=domain,
                    capabilities=capabilities,
                    keywords=keywords,
                    file_extensions=file_extensions,
                    exclusion_scopes=exclusion_scopes,
                    colloquial_examples=colloquial_examples,
                )
                desc = gen_result["template"].generated_description
                if not isinstance(desc, str) or not desc.strip():
                    raise ValueError("生成器返回空 description")
                diag = (gen_result.get("diag")
                        if isinstance(gen_result, Mapping) else None)
                _log.info(
                    "[SkillDocCreator] description 生成完成: score=%s, grade=%s",
                    getattr(diag, "overall_score", "N/A"),
                    getattr(diag, "grade", "N/A"),
                )
                return desc
            except Exception as e:  #noqa:BLE001
                _log.warning(
                    "[SkillDocCreator] description 生成器异常，降级通用生成: %s", e,
                )
        parts = [f"当用户需要 {skill_name} 时使用本技能。"]
        if capabilities:
            parts.append(f"包括：{'，'.join(capabilities[:10])}。")
        if exclusion_scopes:
            parts.append(f"若主要产出为 {'，'.join(exclusion_scopes[:3])}，则不应触发本技能。")
        else:
            parts.append(f"不适用于非 {skill_name} 的任务。")
        return sanitize_upload_description(" ".join(parts))
def _write_skill_md(target_dir: str, md_path: str, content: str) -> str | None:
    try:
        os.makedirs(target_dir, exist_ok=True)
        with guarded_open(md_path, "w", encoding="utf-8", newline="\n") as f:
            f.write(content)
        return None
    except (OSError, ValueError) as e:
        log_swallowed(__name__, e, context=f'_write_skill_md:{type(e).__name__}')
        return str(e)
def _append_custom_sections(body: str,
                            body_sections: list[dict[str, str]]) -> tuple[str, list[str]]:
    custom_titles: list[str] = []
    custom_parts: list[str] = []
    for s in body_sections:
        section = _custom_section(s)
        if section is None:
            continue
        title, part = section
        custom_titles.append(title)
        custom_parts.append(part)
    if custom_parts:
        body = append_block(body, "\n\n".join(custom_parts))
    return body, custom_titles
def _custom_section(s: dict[str, str]):
    raw_title = s.get("title")
    raw_content = s.get("content")
    title = " ".join(raw_title.split()) if isinstance(raw_title, str) else ""
    content = raw_content.strip() if isinstance(raw_content, str) else ""
    if not title or not content:
        return None
    return title, f"## {title}\n\n{content}"
def _script_entries(scan_result: dict[str, Any]) -> list[dict[str, str]] | None:
    scripts = scan_result.get("scripts")
    if not scripts:
        return None
    entries = []
    for script in scripts:
        if not isinstance(script, dict):
            continue
        raw_path = (text_field(script, "rel_path")
                    or text_field(script, "name")).strip().replace("\\", "/")
        if raw_path and "/" not in raw_path:
            raw_path = f"scripts/{raw_path}"
        name = py_stem(os.path.basename(raw_path))
        if not name or not raw_path:
            continue
        invoke = text_field(script, "invoke").strip()
        if not invoke:
            invoke = f"python {json.dumps(raw_path, ensure_ascii=False)}"
        entries.append({
            "name": name,
            "purpose": text_field(script, "doc"),
            "invoke": invoke,
        })
    return entries or None
def _resolve_sections_meta(custom_titles: list[str]) -> list[str]:
    titles = [s["title"] for s in STANDARD_SECTIONS if s.get("title")]
    return list(dict.fromkeys([*titles, *custom_titles]))
def get_creator() -> SkillDocCreator:
    return _creator_instance
def create_skill_doc(skill_name: str, domain: str = "",
                     capabilities: list[str] | None = None,
                     keywords: list[str] | None = None,
                     file_extensions: list[str] | None = None,
                     exclusion_scopes: list[str] | None = None,
                     target_dir: str | None = None,
                     skill_dir: str | None = None,
                     diag_after: bool = _DEFAULT_DIAG_AFTER,
                     colloquial_examples: list[str] | None = None,
                     body_sections: list[dict[str, str]] | None = None,
                     extra_frontmatter: dict[str, Any] | None = None,
                     ) -> dict[str, Any]:
    try:
        if not isinstance(skill_name, str) or not skill_name.strip():
            _log.warning("create_skill_doc: skill_name 为空或类型无效, got=%r", skill_name)
            return {"status": "error", "error": "skill_name 必须为非空字符串"}
        _log.info("create_skill_doc: 开始创建技能文档, skill=%s, domain=%s", skill_name, domain)
        creator = get_creator()
        assembly = {
            "skill_name": skill_name,
            "domain": domain,
            "capabilities": capabilities,
            "keywords": keywords,
            "file_extensions": file_extensions,
            "exclusion_scopes": exclusion_scopes,
            "skill_dir": skill_dir,
            "colloquial_examples": colloquial_examples,
            "body_sections": body_sections,
            "extra_frontmatter": extra_frontmatter,
        }
        if target_dir is None or (
                isinstance(target_dir, str) and not target_dir.strip()):
            return creator.create(**assembly)
        return creator.create_and_save(
            target_dir=target_dir, diag_after=diag_after, **assembly)
    except Exception as e:  #noqa:BLE001
        _log.error("create_skill_doc 异常: %s", e, exc_info=True)
        return {"status": "error", "error": f"create_skill_doc 异常: {e}"}
def build_refactor_content(skill_name: str, body_text: str, description: str,
                           *, skill_dir: str = "",
                           capabilities: list[str] | None = None,
                           exclusion_scopes: list[str] | None = None,
                           colloquial_examples: list[str] | None = None,
                           extra_frontmatter: dict[str, Any] | None = None,
                           ) -> tuple[str, list[Any]]:
    skill_name = normalize_skill_name(normalize_text(skill_name)) or "unnamed-skill"
    description = normalize_text(description)
    body_text = normalize_text(body_text)
    frontmatter = build_skill_frontmatter(
        skill_name, description, extra_frontmatter or {})
    sections = build_refactored_body(
        skill_name, body_text,
        capabilities or [], exclusion_scopes or [],
        scan_skill_api(skill_dir),
        colloquial_examples=colloquial_examples or [])
    return frontmatter, sections
_creator_instance = SkillDocCreator()
@observation_gate("Document completeness check")
def run_document_completeness_gate(skill_md_path: str) -> None:
    doc_report = diag_skill_doc(skill_md_path)
    doc_issues = [i for i in doc_report.issues
                  if i.severity in ('critical', 'high')]
    if doc_issues:
        _log.warning("[init] Document completeness check found %d critical/high issues", len(doc_issues))
        for issue in doc_issues[:5]:
            _log.warning("[init]   %s: %s", issue.rule_id, issue.description[:80])
    else:
        _log.info("[init] Document completeness check: passed (score=%s, grade=%s)",
                   getattr(doc_report, 'overall_score', 'N/A'),
                   getattr(doc_report, 'overall_grade', 'N/A'))
def title_case_skill_name(name: str) -> str:
    if not isinstance(name, str):
        return ""
    words = name.replace('-', ' ').replace('_', ' ').split()
    return ' '.join(w.capitalize() for w in words)
def _normalize_existing_skills(existing_skills: Any,
                               logs: list[str]) -> list[str]:
    if existing_skills is None:
        return []
    if isinstance(existing_skills, str):
        return [existing_skills] if existing_skills else []
    if not isinstance(existing_skills, (list, tuple, set, frozenset)):
        logs.append(f"已忽略非法已存技能清单类型: {type(existing_skills).__name__}")
        return []
    existing = (sorted(existing_skills, key=str)
                if isinstance(existing_skills, (set, frozenset))
                else list(existing_skills))
    bad_elems = [s for s in existing if not isinstance(s, str)]
    if bad_elems:
        logs.append(f"已忽略非法已存技能名项: {bad_elems}")
        existing = [s for s in existing if isinstance(s, str)]
    return existing
def _truncate_skill_name(name: str, logs: list[str]) -> str:
    if len(name) <= MAX_SKILL_NAME_LENGTH:
        return name
    truncated = name[:MAX_SKILL_NAME_LENGTH].rstrip("-")
    logs.append(f"名称过长({len(name)}>{MAX_SKILL_NAME_LENGTH})，已截断至 '{truncated}'")
    return truncated
def _disambiguate_skill_name(name: str, existing: list[str],
                             logs: list[str]) -> str:
    existing_keys = {
        normalized for item in existing
        if (normalized := normalize_skill_name(item))
    }
    if name not in existing_keys:
        return name
    counter = 2
    while True:
        suffix = f"-{counter}"
        base = name[:MAX_SKILL_NAME_LENGTH - len(suffix)].rstrip("-")
        candidate = f"{base}{suffix}"
        if candidate not in existing_keys:
            break
        counter += 1
    logs.append(f"名称冲突，已自动添加后缀: '{candidate}'")
    return candidate
def ensure_valid_skill_name(skill_name: str, existing_skills: list[str] | None = None
                            ) -> tuple[str, list[str]]:
    logs = []
    existing = _normalize_existing_skills(existing_skills, logs)
    name = normalize_text(skill_name)
    normalized = normalize_skill_name(name)
    if normalized != name:
        logs.append(f"名称已归一化: '{name}' → '{normalized}'")
        name = normalized
    if not name:
        name = "unnamed-skill"
        logs.append("名称归一化后为空，使用默认名称 'unnamed-skill'")
    elif len(name) < SKILL_NAME_MIN_LEN:
        expanded = f"{name}-skill"
        logs.append(f"名称过短({len(name)}<{SKILL_NAME_MIN_LEN})，已扩展为 '{expanded}'")
        name = expanded
    name = _truncate_skill_name(name, logs)
    name = _disambiguate_skill_name(name, existing, logs)
    return name, logs
def prepare_skill_metadata(
        skill_name: str,
        description: str,
        design_pattern: str | None = None,
        skill_type: str | None = None) -> dict:
    name = normalize_skill_name(skill_name)
    display_name = title_case_skill_name(name)
    resolved_type = (normalize_text(skill_type).strip()
                     or infer_skill_type(name, description))
    pattern = ((design_pattern.strip() if isinstance(design_pattern, str) else "")
               or infer_design_pattern(name, description))
    return {
        "name": name,
        "display_name": display_name,
        "skill_type": resolved_type,
        "pattern": pattern,
        "category": resolved_type,
    }
def profile_created_skill(name: str, description: str,
                          content: str = "") -> tuple[str, str, str]:
    skill_type = infer_skill_type(name, description)
    design_pattern = infer_design_pattern(name, description, content)
    return skill_type, design_pattern, get_pattern_hint(design_pattern)
def build_creation_result(result_name: str, fixes: list,
                          warnings: list, blocked: bool,
                          enrich: dict[str, Any]) -> dict:
    enrich_map = dict(enrich) if isinstance(enrich, Mapping) else {}
    six_dim_result = enrich_map.get("six_dim_result")
    six_dim: dict = (dict(six_dim_result)
                     if isinstance(six_dim_result, Mapping) else {})
    design_pattern = enrich_map.get("design_pattern", "")
    examples = six_dim.get(FIELD_TRIGGER_EXAMPLES)
    examples_count = len(examples) if isinstance(examples, (list, tuple)) else 0
    six_dim_scores = six_dim.get("six_dim_scores")
    fixes_list = list(fixes) if isinstance(fixes, (list, tuple)) else []
    warnings_list = list(warnings) if isinstance(warnings, (list, tuple)) else []
    result = {
        "ok": not blocked,
        "skill_name": result_name,
        "content": enrich_map.get("content", ""),
        "fixes": fixes_list,
        "warnings": warnings_list,
        "blocked": blocked,
        "skill_type": enrich_map.get("skill_type", ""),
        "design_pattern": design_pattern,
        "design_pattern_hint": get_pattern_hint(design_pattern),
        "description_suggestions": normalize_str_list(
            enrich_map.get("description_suggestions")),
        "six_dim_enhanced": enrich_map.get("six_dim_enhanced", False),
        "six_dim_examples_count": examples_count,
        "six_dim_scores": (dict(six_dim_scores)
                            if isinstance(six_dim_scores, Mapping) else {}),
        "six_dim_quality_score": coerce_report_score(
            six_dim.get("quality_score")),
        "six_dim_quality_grade": _text_of(six_dim.get("quality_grade")),
    }
    append_dependency_warnings(result, result["content"])
    return result
def dir_creation_blocker(target_dir: str) -> str:
    target_dir = normalize_out_path(target_dir)
    if target_dir is None:
        return "目标路径为空或类型无效"
    normalized = os.path.normpath(os.path.abspath(target_dir))
    if os.path.dirname(normalized) == normalized:
        return "文件系统根目录拒绝作为技能目录，防外部污染"
    if os.path.isdir(target_dir):
        return ""
    if os.path.lexists(target_dir):
        return "目标位置已被同名文件占用"
    if not is_dir_creation_allowed(target_dir):
        return "盘根直属路径拒绝隐式创建，防外部污染"
    return ""
def parse_dependency_spec(content: str) -> dict[str, Any]:
    if not isinstance(content, str) or not content:
        return {}
    try:
        parsed = parse_frontmatter_dict(content)
    except (TypeError, ValueError) as exc:
        _log.debug("依赖声明解析失败（按无声明处理）: %s", exc, exc_info=True)
        return {}
    return parsed if isinstance(parsed, dict) else {}
def append_dependency_warnings(result: dict, content: str) -> None:
    try:
        manager = DependencyManager()
        dep_result = manager.check_skill_dependencies(
            result.get("skill_name", "preflight"),
            parse_dependency_spec(content),
        )
        result["dependencies_passed"] = dep_result.passed
        suggestions = [
            f"{label}: {reason}"
            for label, reason in dep_result.details.items()
            if isinstance(reason, str) and reason.strip()
        ]
        if not dep_result.passed:
            suggestions.extend(dep_result.install_commands())
        if not dep_result.passed or suggestions:
            result["dependency_suggestions"] = suggestions
            warnings = result.get("warnings")
            if not isinstance(warnings, list):
                warnings = list(warnings) if isinstance(warnings, tuple) else []
                result["warnings"] = warnings
            for suggestion in suggestions:
                warnings.append({
                    "step": "dependencies",
                    "severity": "warning",
                    "detail": suggestion,
                })
    except Exception as exc:  #noqa:BLE001
        _log.debug("Dependency check skipped: %s", exc)
def _filesystem_path(value: Any) -> str:
    if not isinstance(value, (str, os.PathLike)):
        return ""
    try:
        path = os.fsdecode(os.fspath(value))
    except (TypeError, ValueError, OSError) as exc:
        log_swallowed(__name__, exc,
                      context=f'_filesystem_path:{type(exc).__name__}')
        return ""
    return path if path.strip() else ""
def is_path_input(value: Any) -> bool:
    return bool(_filesystem_path(value))
class FeasibilityResult:
    def __init__(self):
        self.feasible = True
        self.score = 0.0
        self.checks = {}
        self.warnings = []
        self.errors = []
        self.recommendations = []
    def to_dict(self) -> dict:
        return {
            "status": "pass" if self.feasible else "fail",
            "feasible": self.feasible,
            "score": self.score,
            "checks": self.checks,
            "warnings": list(self.warnings),
            "errors": list(self.errors),
            "recommendations": list(self.recommendations),
        }
def dir_write_bits_writable(path: str) -> bool:
    try:
        mode = os.stat(path).st_mode
    except OSError as _e:
        log_swallowed(__name__, _e,
                      context=f'dir_write_bits_writable:{type(_e).__name__}')
        return False
    write_bits = stat.S_IWUSR | stat.S_IWGRP | stat.S_IWOTH
    return bool(mode & write_bits)
def check_directory_writable(skills_dir: Any) -> bool:
    path = _filesystem_path(skills_dir)
    if not path:
        return False
    if not os.path.isdir(path):
        return False
    if not dir_write_bits_writable(path):
        return False
    if not os.access(path, os.W_OK):
        _log.debug("check_directory_writable: 访问位不可写: %s", path)
        return False
    return True
def check_skill_name_conflict(skill_name: str, skills_dir: str) -> bool:
    raw_name = normalize_text(skill_name).strip()
    if skill_name_issues(raw_name):
        return False
    name = normalize_skill_name(raw_name)
    if not name:
        return False
    path = _filesystem_path(skills_dir)
    if not path or not os.path.isdir(path):
        return False
    target = Path(path) / name
    return not os.path.lexists(target)
def eval_name_validity(skill_name: Any) -> Any:
    raw_name = normalize_text(skill_name).strip()
    name = normalize_skill_name(raw_name)
    valid = (not skill_name_issues(raw_name)
             and SKILL_NAME_MIN_LEN <= len(name) <= MAX_SKILL_NAME_LENGTH)
    detail = (f"Normalized name: '{name}' ({len(name)} chars; "
              f"raw {len(raw_name)} chars)")
    return name, valid, detail
def eval_name_conflict(name: Any, skills_dir: Any) -> Any:
    no_conflict = check_skill_name_conflict(name, skills_dir)
    detail = f"Target: {os.path.join(_filesystem_path(skills_dir), name)}"
    return no_conflict, detail
def eval_directory_writable(skills_dir: Any) -> Any:
    writable = check_directory_writable(skills_dir)
    detail = f"Directory: {skills_dir}"
    return writable, detail
_WEIGHT_NAME_VALIDITY = 15.0
_WEIGHT_NAME_CONFLICT = 20.0
_WEIGHT_DIRECTORY_WRITABLE = 10.0
_WEIGHT_TYPE_REQUIREMENTS = 15.0
@dataclass(frozen=True)
class ConditionalStage:
    key: str
    weight: float
    probe: Callable[[Any], dict]
    none_note: str
    missing_label: str
def record_check(result: FeasibilityResult, checks: dict, key: str,
                 passed: bool, detail: Any, error: str = "") -> bool:
    checks[key] = {"passed": passed, "detail": detail}
    if not passed and error:
        result.errors.append(error)
        result.feasible = False
    return passed
def summarize_bool_map(results: dict) -> tuple:
    missing = [name for name, ok in results.items() if not ok]
    score = sum(1 for ok in results.values() if ok) / max(len(results), 1)
    detail = {"results": results, "missing": missing}
    return (not missing), detail, missing, score
PYTHON_DEPS_STAGE = ConditionalStage(
    key="python_dependencies", weight=25.0, probe=check_python_deps,
    none_note="No deps specified", missing_label="Python deps")
SYSTEM_TOOLS_STAGE = ConditionalStage(
    key="system_tools", weight=15.0, probe=check_system_tools,
    none_note="No tools specified", missing_label="system tools")
def recommend_by_status(result) -> None:
    if result.errors or not result.feasible:
        result.recommendations.append("Address errors before skill creation")
        result.feasible = False
    elif result.score >= 80:
        result.recommendations.append("Proceed to Step1: requirements analysis")
    elif result.score >= 60:
        result.recommendations.append("Fix warnings before proceeding to Step1")
    else:
        result.recommendations.append("Address errors before skill creation")
        result.feasible = False
def _pip_install_commands(missing_packages: list) -> list[str]:
    probe = DependencyCheckResult()
    probe.missing_packages = [str(pkg) for pkg in missing_packages]
    return probe.install_commands()
def append_install_recommendations(checks: dict, result) -> None:
    missing_deps = missing_items_of(checks, "python_dependencies")
    if missing_deps is not None:
        commands = _pip_install_commands(missing_deps)
        result.recommendations.append("Install: " + " && ".join(commands))
    missing_tools = missing_items_of(checks, "system_tools")
    if missing_tools is not None:
        result.recommendations.append(
            f"Install system tools: {', '.join(str(t) for t in missing_tools)}")
def build_recommendations(checks: Any, result: Any) -> Any:
    recommend_by_status(result)
    append_install_recommendations(checks, result)
    return result
def missing_items_of(checks: dict, key: str) -> list | None:
    check = checks.get(key) if isinstance(checks, Mapping) else None
    detail = check.get("detail") if isinstance(check, Mapping) else None
    missing = detail.get("missing") if isinstance(detail, Mapping) else None
    if isinstance(missing, (list, tuple)) and missing:
        return list(missing)
    return None
def check_type_requirements(skill_type: Any, requirements: Any = None) -> Any:
    type_key = (normalize_text(skill_type).strip().casefold()
                if isinstance(skill_type, (str, bytes, bytearray)) else "")
    table = requirements if isinstance(requirements, Mapping) else {}
    lookup = {normalize_text(key).strip().casefold(): value
              for key, value in table.items()}
    declared = lookup.get(type_key, ()) if type_key else ()
    modules = list(dict.fromkeys(normalize_str_list(declared)))
    missing = [mod for mod in modules if not module_available(mod)]
    all_ok = not missing
    if not modules:
        detail = "No type requirements declared"
    else:
        detail = (f"Missing modules: {', '.join(missing)}" if missing
                  else "All dependencies satisfied")
    return {"passed": all_ok, "missing": missing,
            "declared": bool(modules), "detail": detail}
def score_name_validity(result: FeasibilityResult, checks: dict,
                        skill_name: str) -> tuple:
    name, valid, detail = eval_name_validity(skill_name)
    record_check(
        result, checks, "name_validity", valid, detail,
        error=(f"Invalid skill name: '{name}' "
               f"({SKILL_NAME_MIN_LEN}-{MAX_SKILL_NAME_LENGTH} chars required)"))
    return _WEIGHT_NAME_VALIDITY, _WEIGHT_NAME_VALIDITY if valid else 0, name
def score_name_conflict(result: FeasibilityResult, checks: dict,
                        name: str, valid: bool, skills_dir: str) -> tuple:
    if valid and os.path.isdir(_filesystem_path(skills_dir)):
        no_conflict, detail = eval_name_conflict(name, skills_dir)
        record_check(result, checks, "name_conflict", no_conflict, detail,
                     error=f"Skill '{name}' already exists in {skills_dir}")
        return (_WEIGHT_NAME_CONFLICT,
                _WEIGHT_NAME_CONFLICT if no_conflict else 0)
    record_check(
        result, checks, "name_conflict", True,
        "Skipped: invalid skill name" if not valid
        else "Skipped: invalid skills directory")
    return 0.0, 0.0
def score_directory_writable(result: FeasibilityResult, checks: dict,
                             skills_dir: str) -> tuple:
    writable, detail = eval_directory_writable(skills_dir)
    record_check(result, checks, "directory_writable", writable, detail,
                 error=f"Directory not writable: {skills_dir}")
    return (_WEIGHT_DIRECTORY_WRITABLE,
            _WEIGHT_DIRECTORY_WRITABLE if writable else 0)
def _stage_items(raw_items: Any) -> list:
    if isinstance(raw_items, (set, frozenset)):
        return normalize_check_items(sorted(raw_items, key=str))
    if isinstance(raw_items, (list, tuple, str, bytes, bytearray, Mapping)):
        return normalize_check_items(raw_items)
    try:
        return normalize_check_items(list(raw_items))
    except TypeError:
        return []
def score_conditional_items(result: FeasibilityResult, checks: dict,
                            raw_items: object, stage: ConditionalStage) -> tuple:
    items = _stage_items(raw_items)
    if not items:
        record_check(result, checks, stage.key, True, stage.none_note)
        return 0.0, 0.0
    all_ok, detail, missing, score = summarize_bool_map(stage.probe(items))
    record_check(result, checks, stage.key, all_ok, detail)
    if not all_ok:
        result.warnings.append(f"Missing {stage.missing_label}: {', '.join(missing)}")
    return stage.weight, stage.weight * score
def score_type_requirements(result: FeasibilityResult, checks: dict,
                            skill_type: str,
                            requirements: Any = None) -> tuple:
    type_checks = check_type_requirements(skill_type, requirements)
    checks["type_requirements"] = type_checks
    if not type_checks.get("passed", True):
        result.warnings.append(type_checks.get("detail", "Type check warning"))
    if not type_checks.get("declared", False):
        return 0.0, 0.0
    passed = type_checks.get("passed", True)
    return _WEIGHT_TYPE_REQUIREMENTS, _WEIGHT_TYPE_REQUIREMENTS if passed else 0
def step0_bare_evaluation(skill_name: str, skills_dir: str,
                          dependencies: list | None = None,
                          system_tools: list | None = None,
                          skill_type: str = 'generic',
                          type_requirements: Any = None) -> FeasibilityResult:
    result = FeasibilityResult()
    checks = {}
    weight, earned, name = score_name_validity(result, checks, skill_name)
    stages = [(weight, earned)]
    valid = checks["name_validity"]["passed"]
    stages.append(score_name_conflict(result, checks, name, valid, skills_dir))
    stages.append(score_directory_writable(result, checks, skills_dir))
    stages.append(score_conditional_items(
        result, checks, dependencies, PYTHON_DEPS_STAGE))
    stages.append(score_conditional_items(
        result, checks, system_tools, SYSTEM_TOOLS_STAGE))
    stages.append(score_type_requirements(
        result, checks, skill_type, type_requirements))
    total_weight = sum(w for w, _ in stages)
    weighted_score = sum(e for _, e in stages)
    result.checks = checks
    result.score = round((weighted_score / total_weight) * 100, 1) if total_weight > 0 else 0
    build_recommendations(checks, result)
    return result
def run_bare_step0(skill_name: str, skills_dir: str, description: str = "",
                   dependencies: list | None = None, system_tools: list | None = None,
                   skill_type: str = "",
                   type_requirements: Any = None) -> dict:
    skill_name = normalize_text(skill_name)
    description = normalize_text(description)
    skill_type = skill_type.strip() if isinstance(skill_type, str) else ""
    if not skill_type:
        skill_type = infer_skill_type(skill_name, description)
    result = step0_bare_evaluation(
        skill_name=skill_name, skills_dir=skills_dir,
        dependencies=dependencies, system_tools=system_tools,
        skill_type=skill_type, type_requirements=type_requirements,
    )
    output = result.to_dict()
    output["skill_type"] = skill_type
    return output
def render_mapping_detail(detail: dict) -> str:
    missing = detail.get("missing")
    if isinstance(missing, (list, tuple)) and missing:
        return "missing: " + ", ".join(str(m) for m in missing)
    results = detail.get("results")
    if isinstance(results, Mapping) and results:
        failed = [name for name, ok in results.items() if not ok]
        if failed:
            return "missing: " + ", ".join(str(name) for name in failed)
        return f"all {len(results)} ok"
    if detail:
        return "; ".join(f"{k}={v}" for k, v in detail.items())
    return "ok"
def render_check_detail(detail) -> str:
    if isinstance(detail, Mapping):
        return render_mapping_detail(dict(detail))
    if detail is None:
        return ""
    return str(detail)
def render_report_section(lines: list, values: Any,
                          header: str, prefix: str) -> None:
    if isinstance(values, (set, frozenset)):
        values = sorted(values, key=str)
    if not isinstance(values, (list, tuple)) or not values:
        return
    lines.append(f"\n  {header}:")
    for item in values:
        lines.append(f"    {prefix}{item}")
def coerce_report_score(value: Any) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return 0.0
    try:
        score = float(value)
    except (OverflowError, ValueError):
        return 0.0
    return score if math.isfinite(score) else 0.0
def render_check_lines(checks: Any) -> list[str]:
    if not isinstance(checks, Mapping):
        return []
    lines = []
    for name, check in checks.items():
        if not isinstance(check, Mapping):
            continue
        status = "OK" if check.get("passed") else "FAIL"
        lines.append(f'  [{status}] {name}: {render_check_detail(check.get("detail", ""))}')
    return lines
def render_report_dict(result: dict) -> str:
    if isinstance(result, FeasibilityResult):
        result = result.to_dict()
    if not isinstance(result, Mapping):
        raise TypeError(
            "render_report_dict: result 须为 FeasibilityResult 或映射，"
            f"得到 {type(result).__name__}")
    result = dict(result)
    status = normalize_text(result.get("status")).strip().casefold()
    lines = ["=" * 60, "  Step0 Bare-Run Feasibility Assessment", "=" * 60]
    lines.append(f"  Status: {'PASS' if status == 'pass' else 'FAIL'}")
    lines.append(f"  Score: {coerce_report_score(result.get('score', 0)):.1f}/100")
    lines.append("")
    lines.extend(render_check_lines(result.get("checks", {})))
    render_report_section(lines, result.get("warnings"), "Warnings", "- ")
    render_report_section(lines, result.get("errors"), "Errors", "- ")
    render_report_section(lines, result.get("recommendations"),
                          "Recommendations", "-> ")
    lines.append("=" * 60)
    return "\n".join(lines)
def build_creation_doc_assets(
    skill_name: str, description: str,
    existing_descriptions: list[str] | None = None,
) -> dict[str, Any]:
    example_result = PromptExampleBuilder().build(skill_name, description)
    language = detect_text_language(description, skill_name)
    return {
        "example_result": example_result,
        "example_section": _render_example_section(example_result, language),
        "desc_eval": evaluate_description(
            description, skill_name, existing_descriptions or []),
    }
@dataclass
class ExampleBlock:
    title: str = ""
    description: str = ""
    code: str = ""
    explanation: str = ""
    tags: list[str] = field(default_factory=list)
@dataclass
class PromptExampleResult:
    skill_name: str = ""
    examples: list[ExampleBlock] = field(default_factory=list)
    positive_count: int = 0
    negative_count: int = 0
    total: int = 0
    score: float = 0.0
    issues: list[str] = field(default_factory=list)
    suggestions: list[str] = field(default_factory=list)
_SCORE_CAP = 100.0
_SCORE_PER_EXAMPLE = 10.0
_SCORE_BALANCE_BONUS = 5.0
_SCORE_POSITIVE_ONLY = 8.0
_MAX_POSITIVE_NEGATIVE_RATIO = 5
_TYPE_POSITIVE = "positive"
_TYPE_NEGATIVE = "negative"
def _example_type(ex: Any) -> str:
    return (_text_of(ex.get("type")).strip().casefold()
            if isinstance(ex, Mapping) else "")
def _is_positive(ex: Any) -> bool:
    return _example_type(ex) == _TYPE_POSITIVE
def _is_negative(ex: Any) -> bool:
    return _example_type(ex) == _TYPE_NEGATIVE
def _count_example_types(raw_examples: list[dict[str, Any]]) -> tuple[int, int]:
    pos = sum(1 for ex in raw_examples if _is_positive(ex))
    neg = sum(1 for ex in raw_examples if _is_negative(ex))
    return pos, neg
_DEFAULT_EXAMPLE_LANGUAGE = "zh"
_EXAMPLE_TEXTS: dict[str, dict[str, str]] = {
    "zh": {
        "call": "调用 {name}",
        "entry": "按技能实际公开入口处理",
        "route": "路由到其他技能",
        "boundary": "边界: {boundary} — {expected}",
        "positive": "应触发 {skill} 技能",
        "positive_func": "应触发 {skill} 技能, 调用 {func}",
        "positive_entry": "应触发 {skill} 技能, 按实际公开入口处理",
        "negative": "不应触发 {skill} 技能, 应路由到其他技能",
        "need_negative": "缺少负例: 未生成任何不应触发的边界示例",
        "suggest_negative": "添加至少2个负例以明确技能触发边界",
        "need_positive": "缺少正例: 未生成任何应触发的示例",
        "suggest_positive": "添加至少3个正例覆盖核心功能",
        "imbalance": "正负例比例失衡: {pos}:{neg}，负例覆盖率不足",
        "suggest_imbalance": "增加负例数量，建议正负例比例约2:1",
        "request_label": "用户请求",
        "behaviour_label": "预期行为",
        "section_title": "## 使用示例",
        "positive_title": "### 应触发场景（正例）",
        "negative_title": "### 不应触发场景（负例）",
        "diagnosis_title": "### 覆盖率诊断",
    },
    "en": {
        "call": "call {name}",
        "entry": "dispatch to the skill's public entry point",
        "route": "route to another skill",
        "boundary": "boundary: {boundary} — {expected}",
        "positive": "should trigger the {skill} skill",
        "positive_func": "should trigger the {skill} skill and call {func}",
        "positive_entry": (
            "should trigger the {skill} skill and dispatch to its public entry point"),
        "negative": "should not trigger the {skill} skill and route to another skill",
        "need_negative": "missing negative examples: no out-of-scope boundary example",
        "suggest_negative": "add at least 2 negative examples to mark the trigger boundary",
        "need_positive": "missing positive examples: no example that should trigger",
        "suggest_positive": "add at least 3 positive examples covering core capabilities",
        "imbalance": "unbalanced examples: {pos}:{neg}, negative coverage too low",
        "suggest_imbalance": "add negative examples; about 2:1 positive:negative is expected",
        "request_label": "User request",
        "behaviour_label": "Expected behaviour",
        "section_title": "## Usage examples",
        "positive_title": "### Should trigger (positive)",
        "negative_title": "### Should not trigger (negative)",
        "diagnosis_title": "### Coverage diagnosis",
    },
}
def _example_text(language: str, key: str, **fields: Any) -> str:
    table = _EXAMPLE_TEXTS.get(language) or _EXAMPLE_TEXTS["en"]
    template = table.get(key) or _EXAMPLE_TEXTS["en"].get(key, key)
    return template.format(**fields) if fields else template
def _to_example_block(ex: dict[str, Any], language: str = _DEFAULT_EXAMPLE_LANGUAGE) -> ExampleBlock:
    if not isinstance(ex, Mapping):
        return ExampleBlock()
    ex_type = _example_type(ex)
    if _is_positive(ex):
        function = ex.get("function", "")
        code_val = (_example_text(language, "call", name=function)
                    if function else _example_text(language, "entry"))
        expl_val = ex.get("expected", "")
    elif _is_negative(ex):
        code_val = _example_text(language, "route")
        boundary = ex.get('boundary', '')
        expl_val = (_example_text(language, "boundary",
                                  boundary=boundary,
                                  expected=ex.get('expected', ''))
                    if boundary else ex.get('expected', ''))
    else:
        code_val = _example_text(language, "entry")
        expl_val = ex.get("expected", "")
    return ExampleBlock(
        title=ex_type or "example",
        description=ex.get("query", ""),
        code=code_val,
        explanation=expl_val,
        tags=[ex_type] if ex_type else [],
    )
def _score_examples(pos: int, neg: int) -> float:
    if pos > 0 and neg > 0:
        balanced = (pos + neg) * _SCORE_PER_EXAMPLE + min(pos, neg) * _SCORE_BALANCE_BONUS
        return min(_SCORE_CAP, balanced)
    if pos > 0:
        return min(_SCORE_CAP, pos * _SCORE_POSITIVE_ONLY)
    return 0.0
def _diagnose_examples(pos: int, neg: int,
                       language: str = _DEFAULT_EXAMPLE_LANGUAGE) -> tuple[list[str], list[str]]:
    rules = (
        (neg == 0,
         _example_text(language, "need_negative"),
         _example_text(language, "suggest_negative")),
        (pos == 0,
         _example_text(language, "need_positive"),
         _example_text(language, "suggest_positive")),
        (pos > 0 and neg > 0 and pos / neg > _MAX_POSITIVE_NEGATIVE_RATIO,
         _example_text(language, "imbalance", pos=pos, neg=neg),
         _example_text(language, "suggest_imbalance")),
    )
    issues: list[str] = []
    suggestions: list[str] = []
    for hit, issue, suggestion in rules:
        if hit:
            issues.append(issue)
            suggestions.append(suggestion)
    return issues, suggestions
def _render_example_lines(lines: list[str], title: str,
                          examples: list[ExampleBlock], limit: int,
                          language: str = _DEFAULT_EXAMPLE_LANGUAGE) -> None:
    if not examples:
        return
    lines.append(title)
    lines.append("")
    request_label = _example_text(language, "request_label")
    behaviour_label = _example_text(language, "behaviour_label")
    for ex in examples[:limit]:
        if not isinstance(ex, ExampleBlock):
            continue
        lines.append(f"- **{request_label}**: {ex.description}")
        lines.append(f"  **{behaviour_label}**: {ex.explanation or ex.code}")
        lines.append("")
class PromptExampleBuilder:
    _QUERY_TEMPLATE: ClassVar[dict[str, str]] = {
        "zh": "请帮我{trigger}",
        "en": "Please help me {trigger}",
    }
    _DEFAULT_PATTERNS: ClassVar[dict[str, list[str]]] = {
        "zh": ["执行", "检查", "优化"],
        "en": ["run", "check", "optimize"],
    }
    _GENERIC_NEGATIVE_QUERIES: ClassVar[dict[str, list[str]]] = {
        "zh": [
            "请帮我安排明天的会议日程",
            "请帮我查询明天的天气预报",
            "帮我播放一首轻音乐",
        ],
        "en": [
            "Please schedule tomorrow's meeting",
            "What's the weather like tomorrow?",
            "Play some light music for me",
        ],
    }
    _GENERIC_NEGATIVE_TOPIC_KEYWORDS: ClassVar[dict[str, tuple[str, ...]]] = {
        "请帮我安排明天的会议日程": (
            "会议", "日程", "日历", "meeting", "schedule", "calendar", "agenda"),
        "请帮我查询明天的天气预报": (
            "天气", "气象", "weather", "forecast", "climate"),
        "帮我播放一首轻音乐": (
            "音乐", "歌曲", "歌单", "音频", "music", "song", "audio", "playlist"),
        "Please schedule tomorrow's meeting": (
            "会议", "日程", "日历", "meeting", "schedule", "calendar", "agenda"),
        "What's the weather like tomorrow?": (
            "天气", "气象", "weather", "forecast", "climate"),
        "Play some light music for me": (
            "音乐", "歌曲", "歌单", "音频", "music", "song", "audio", "playlist"),
    }
    _MAX_POSITIVE_EXAMPLES: ClassVar[int] = 5
    _MAX_NEGATIVE_EXAMPLES: ClassVar[int] = 3
    _MAX_BOUNDARY_CANDIDATES: ClassVar[int] = 5
    _MAX_PATTERN_TAGS: ClassVar[int] = 3
    def _infer_boundaries(self: Self, description: str = "",
                          exclusion_scopes: list[str] | None = None) -> list[str]:
        boundaries = list(exclusion_scopes or [])
        boundaries.extend(extract_boundary_scopes(description))
        return list(dict.fromkeys(boundaries))[: self._MAX_BOUNDARY_CANDIDATES]
    @staticmethod
    def _positive_trigger(func: str, patterns: list[str], index: int,
                          skill_name: str = "", language: str = _DEFAULT_EXAMPLE_LANGUAGE) -> str:
        pattern_text = patterns[index % len(patterns)].strip() if patterns else ""
        subject = (func.replace("_", " ").replace("-", " ").strip()
                   or readable_skill_name(skill_name).strip())
        if not pattern_text or pattern_text.casefold() == subject.casefold():
            return subject
        head = subject[:1]
        separator = "" if (language == _DEFAULT_EXAMPLE_LANGUAGE and head and not head.isascii()) else " "
        return f"{pattern_text}{separator}{subject}".strip()
    def _make_positive_example(self: Self, skill_name: str,
                                func: str, patterns: list[str],
                                index: int = 0,
                                language: str = _DEFAULT_EXAMPLE_LANGUAGE) -> dict[str, Any]:
        trigger = self._positive_trigger(
            func, patterns, index, skill_name, language)
        expected = (_example_text(language, "positive_func",
                                  skill=skill_name, func=func)
                    if func else _example_text(
                        language, "positive_entry", skill=skill_name))
        template = self._QUERY_TEMPLATE.get(
            language, self._QUERY_TEMPLATE["en"])
        return {
            "type": _TYPE_POSITIVE,
            "skill": skill_name,
            "function": func,
            "query": template.format(trigger=trigger),
            "expected": expected,
            "patterns": patterns[: self._MAX_PATTERN_TAGS],
        }
    def _make_negative_example(self: Self, skill_name: str,
                                boundary: str,
                                language: str = _DEFAULT_EXAMPLE_LANGUAGE) -> dict[str, Any]:
        return {
            "type": _TYPE_NEGATIVE,
            "skill": skill_name,
            "boundary": boundary,
            "query": negative_query_for_boundary(boundary, language=language),
            "expected": _example_text(
                language, "negative", skill=skill_name),
        }
    def _positive_examples(self: Self, skill_name: str,
                           functions: list[str],
                           patterns: list[str],
                           language: str = _DEFAULT_EXAMPLE_LANGUAGE) -> list[dict[str, Any]]:
        if not functions:
            return [
                self._make_positive_example(
                    skill_name, "", patterns, index=idx, language=language)
                for idx in range(min(len(patterns), self._MAX_POSITIVE_EXAMPLES))
            ]
        return [
            self._make_positive_example(
                skill_name, func, patterns, index=idx, language=language)
            for idx, func in enumerate(functions[: self._MAX_POSITIVE_EXAMPLES])
        ]
    def _negative_examples(self: Self, skill_name: str,
                           description: str,
                           exclusion_scopes: list[str] | None = None,
                           language: str = _DEFAULT_EXAMPLE_LANGUAGE) -> list[dict[str, Any]]:
        examples: list[dict[str, Any]] = []
        seen_queries: set[str] = set()
        for boundary in self._infer_boundaries(description, exclusion_scopes):
            ex = self._make_negative_example(skill_name, boundary, language)
            if ex.get("query") in seen_queries:
                continue
            seen_queries.add(ex["query"])
            examples.append(ex)
            if len(examples) >= self._MAX_NEGATIVE_EXAMPLES:
                break
        generic = self._GENERIC_NEGATIVE_QUERIES.get(
            language, self._GENERIC_NEGATIVE_QUERIES["en"])
        skill_context = f"{readable_skill_name(skill_name)} {description}".lower()
        for query in generic:
            if len(examples) >= self._MAX_NEGATIVE_EXAMPLES:
                break
            topics = self._GENERIC_NEGATIVE_TOPIC_KEYWORDS.get(query, ())
            if not topics or any(
                    keyword_matches(topic, skill_context) for topic in topics):
                continue
            if query in seen_queries:
                continue
            seen_queries.add(query)
            examples.append({
                "type": _TYPE_NEGATIVE,
                "skill": skill_name,
                "query": query,
                "expected": _example_text(
                    language, "negative", skill=skill_name),
            })
        return examples
    def _build_examples_impl(self: Self, skill_name: str, description: str,
                              functions: list[str], patterns: list[str],
                              exclusion_scopes: list[str] | None = None,
                              language: str = _DEFAULT_EXAMPLE_LANGUAGE) -> list[dict[str, Any]]:
        return (self._positive_examples(
                    skill_name, functions, patterns, language)
                + self._negative_examples(
                    skill_name, description, exclusion_scopes, language))
    def build(self: Self, skill_name: str, description: str,
              functions: list[str] | None = None,
              patterns: list[str] | None = None,
              exclusion_scopes: list[str] | None = None) -> PromptExampleResult:
        skill_name = normalize_str(skill_name).strip()
        description = normalize_str(description).strip()
        if not skill_name or not description:
            _log.warning("PromptExampleBuilder.build: skill_name或description为空")
            raise ValueError("skill_name 和 description 为必填项，不能为空")
        language = detect_text_language(description, skill_name)
        funcs = list(dict.fromkeys(normalize_str_list(functions)))
        pats = list(dict.fromkeys(
            normalize_str_list(patterns)
            or self._DEFAULT_PATTERNS.get(
                language, self._DEFAULT_PATTERNS["en"])))
        scopes = list(dict.fromkeys(normalize_str_list(exclusion_scopes)))
        raw = self._build_examples_impl(
            skill_name, description, funcs, pats, scopes, language)
        return self._assemble_result(skill_name, raw, language)
    def _assemble_result(self: Self, skill_name: str,
                         raw_examples: list[dict[str, Any]],
                         language: str = _DEFAULT_EXAMPLE_LANGUAGE) -> PromptExampleResult:
        items = ([ex for ex in raw_examples if isinstance(ex, Mapping)]
                 if isinstance(raw_examples, (list, tuple)) else [])
        blocks = [_to_example_block(ex, language) for ex in items]
        pos, neg = _count_example_types(items)
        issues, suggestions = _diagnose_examples(pos, neg, language)
        return PromptExampleResult(
            skill_name=skill_name,
            examples=blocks,
            positive_count=pos,
            negative_count=neg,
            total=len(blocks),
            score=_score_examples(pos, neg),
            issues=issues,
            suggestions=suggestions,
        )
def _examples_tagged(examples: list,
                     tag: str) -> list:
    tagged = []
    for ex in examples if isinstance(examples, (list, tuple)) else ():
        tags = getattr(ex, "tags", ())
        if isinstance(tags, (list, tuple, set, frozenset)) and tag in tags:
            tagged.append(ex)
    return tagged
def _render_example_section(result: PromptExampleResult,
                            language: str) -> str:
    lines = [_example_text(language, "section_title"), ""]
    _render_example_lines(
        lines, _example_text(language, "positive_title"),
        _examples_tagged(result.examples, _TYPE_POSITIVE),
        PromptExampleBuilder._MAX_POSITIVE_EXAMPLES, language)
    _render_example_lines(
        lines, _example_text(language, "negative_title"),
        _examples_tagged(result.examples, _TYPE_NEGATIVE),
        PromptExampleBuilder._MAX_NEGATIVE_EXAMPLES, language)
    issues = normalize_str_list(getattr(result, "issues", ()))
    if issues:
        lines.append(_example_text(language, "diagnosis_title"))
        lines.append("")
        for issue in issues:
            lines.append(f"- {issue}")
        lines.append("")
    return "\n".join(lines)
def generate_example_section(skill_name: str, description: str,
                            functions: list[str] | None = None,
                            patterns: list[str] | None = None,
                            exclusion_scopes: list[str] | None = None) -> str:
    result = PromptExampleBuilder().build(
        skill_name, description, functions, patterns, exclusion_scopes)
    language = detect_text_language(description, skill_name)
    return _render_example_section(result, language)

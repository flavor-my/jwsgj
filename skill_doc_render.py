from __future__ import annotations

import keyword as _keyword
import logging
import os
import re
from collections.abc import Callable, Iterator
from dataclasses import dataclass, field
from functools import lru_cache
from typing import Any, Self

from jwsgj.build_matching_diagnoser import (
    DESCRIPTION_MAX_LENGTH,
    DESCRIPTION_MIN_LENGTH,
    MatchingRuleDiagnoser,
    get_matching_hard_rules,
)
from jwsgj.build_text_document import (
    has_cjk,
    iter_fence_lines,
    normalize_domain_key,
    readable_skill_name,
    safe_text,
    strip_atx_closing,
)
from jwsgj.build_text_frontmatter import normalize_description_field
from jwsgj.build_text_scoring import (
    SIX_DIM_SPECS,
    STANDARD_SECTIONS,
    get_standard_sections,
    md_escape_cell,
)
from jwsgj.build_text_signals import (
    NATURAL_BOUNDARY_PATTERNS,
    NEGATIVE_BOUNDARY_PATTERNS,
    VAGUE_WORDS_CN,
    VAGUE_WORDS_EN,
    extract_capabilities,
    mask_exclusion_context,
    normalize_matching_keywords,
    vague_word_spans,
)
from jwsgj.diag_types_defs import DocSection
from jwsgj.diag_types_normalize import int_metric, meta_num
from jwsgj.diag_types_vocab import (
    FIELD_CAPABILITY_COVERAGE,
    FIELD_SYNONYM_COVERAGE,
)
from jwsgj.log_config import log_swallowed
from jwsgj.runtime_scope import (
    DIAG_OUT_OF_SCOPE_DIRS,
    SCAN_IGNORE_DIRS,
    coerce_skill_dir,
    count_test_files,
    is_test_source_basename,
    py_stem,
)
from jwsgj.skill_profile import SOURCE_DIR_NAMES, detect_layout

__all__ = [
    'DOMAIN_SKIP_DIRS',
    'UNIFIED_SECTION_LABELS',
    'UNIFIED_SKILL_SECTIONS',
    'DescriptionTemplate',
    'MatchingDescriptionGenerator',
    'append_block',
    'build_refactored_body',
    'build_unified_skill_md_body',
    'enhance_section_with_api',
    'generate_matching_description',
    'get_generator',
    'infer_skill_domain',
    'member_entries',
    'module_display_name',
    'normalize_dict_seq',
    'normalize_str_seq',
    'text_field',
    'validate_section_registry',
]
_log = logging.getLogger(__name__)
_MAX_TABLE_ROWS = 30
_DOC_SUMMARY_MAX_CHARS = 80
_MAX_PREVIEW_CAPABILITIES = 8
_MAX_TRIGGER_EXAMPLES = 12
_MIN_TRIGGER_EXAMPLES = 6
_MAX_TRIGGER_PREVIEW = 6
_MAX_CAPABILITIES_IN_DESCRIPTION = 12
_MAX_SPOKEN_EXAMPLES = 8
_MAX_SPOKEN_TERMS = 10
_MAX_ROLE_HINTS = 2
_MAX_TRIGGER_CAPABILITIES = 3
_MAX_EXCLUSION_SCOPES = 4
_MAX_IMPROVEMENT_CAPABILITIES = 10
_MAX_BILINGUAL_CAPS = 6
_MAX_EXAMPLE_FUNCS = 10
_DEFAULT_DOMAIN = ""
_FALLBACK_SKILL_LABEL = "本技能"
_log.info("skill_doc_render 文档渲染域已加载: %d 项导出", len(__all__))
def _md_escape_cell(value) -> str:
    if value is None:
        return ""
    return md_escape_cell(safe_text(value).replace("\r\n", "\n").replace("\r", "\n"))
def _md_escape_item(value) -> str:
    text = " ".join(safe_text(value).split())
    if text[:1] in ("`", "~"):
        text = "\\" + text
    return text
def normalize_str_seq(value) -> list[str]:
    if isinstance(value, str):
        value = [value]
    elif isinstance(value, (set, frozenset)):
        value = sorted(x for x in value if isinstance(x, str))
    elif isinstance(value, (dict, bytes, bytearray)) or not value:
        return []
    elif not isinstance(value, (list, tuple)):
        try:
            value = list(value)
        except TypeError as _swallowed_exc:
            log_swallowed(__name__, _swallowed_exc,
                          context='normalize_str_seq:TypeError')
            return []
    return list(dict.fromkeys(
        x.strip() for x in value if isinstance(x, str) and x.strip()))
def normalize_dict_seq(value) -> list[dict]:
    if isinstance(value, (str, bytes, dict)) or not value:
        return []
    if isinstance(value, (list, tuple)):
        items = value
    else:
        try:
            items = list(value)
        except TypeError as _e:
            log_swallowed(__name__, _e, context='normalize_dict_seq:TypeError')
            return []
    return [x for x in items if isinstance(x, dict)]
def _norm_domains(value) -> dict[str, list[dict]]:
    if not isinstance(value, dict):
        return {}
    out: dict[str, list[dict]] = {}
    display_keys: dict[str, str] = {}
    for k, modules in value.items():
        display_key = safe_text(k).strip()
        if not display_key:
            _log.warning("_norm_domains: 域名为空，跳过该域的模块条目")
            continue
        canonical_key = normalize_domain_key(display_key)
        domain_key = display_keys.setdefault(canonical_key, display_key)
        if isinstance(modules, dict):
            entries = [modules]
        elif isinstance(modules, (list, tuple)):
            entries = [m for m in modules if isinstance(m, dict)]
        else:
            entries = []
        out.setdefault(domain_key, []).extend(entries)
    return out
def text_field(entry: dict[str, Any], key: str) -> str:
    if not isinstance(entry, dict):
        return ""
    value = entry.get(key)
    return value if isinstance(value, str) else ""
def _scan_files(api_scan: Any) -> list[dict[str, Any]]:
    if not isinstance(api_scan, dict):
        return []
    raw = api_scan.get("files")
    if not isinstance(raw, list):
        return []
    return [f for f in raw if isinstance(f, dict)]
def member_entries(f_info: dict[str, Any], key: str) -> list[dict[str, Any]]:
    if not isinstance(f_info, dict):
        return []
    raw = f_info.get(key)
    if not isinstance(raw, list):
        return []
    return [e for e in raw if isinstance(e, dict) and text_field(e, "name")]
def module_display_name(module_path: Any) -> str:
    text = module_path.replace("\\", "/") if isinstance(module_path, str) else ""
    return py_stem(text).replace("/", ".")
def _is_package_init(module_name: str) -> bool:
    return py_stem(module_name.rsplit(".", 1)[-1]) == "__init__"
def append_block(content: str, block: str) -> str:
    head = content.rstrip("\r\n")
    tail = block.lstrip("\r\n")
    return f"{head}\n\n{tail}" if head else tail
def _visible_markdown(content: str) -> str:
    return "\n".join(
        " " * len(line) if in_fence else line
        for line, in_fence in iter_fence_lines(content.split("\n")))
_SECTION_PLACEHOLDERS = frozenset({
    "（待从代码扫描填充）",
    "（待从目录扫描填充）",
    "（待从能力扫描填充）",
    "（待从技能定义填充）",
    "（待从触发词矩阵填充）",
    "（待从实践经验填充）",
})
DOMAIN_SKIP_DIRS = frozenset(
    name.lower()
    for name in (*DIAG_OUT_OF_SCOPE_DIRS, *SCAN_IGNORE_DIRS,
                 "references", "assets"))
_UNIFIED_SECTION_SPECS = tuple(
    s for s in STANDARD_SECTIONS if s["key"] != "description_block")
UNIFIED_SKILL_SECTIONS = [s["key"] for s in _UNIFIED_SECTION_SPECS]
UNIFIED_SECTION_LABELS = {s["key"]: s["title"] for s in _UNIFIED_SECTION_SPECS}
UNIFIED_SECTION_ALIASES = {
    s["key"]: tuple(s.get("aliases") or ()) for s in _UNIFIED_SECTION_SPECS}
_REQUIRED_SECTION_KEYS = frozenset(
    s["key"] for s in STANDARD_SECTIONS if s.get("required"))
_KEY_CONSTRAINTS_TITLE = UNIFIED_SECTION_LABELS.get("key_constraints", "关键约束")
_BRACKET_SUFFIX_RE = re.compile(r"^\s*[（(【\[][^）)】\]]*[）)】\]]\s*$")
def _section_label(key: str, fallback: str = "") -> str:
    return UNIFIED_SECTION_LABELS.get(key) or fallback or key
def _resolve_unified_key(title: Any) -> str:
    text = safe_text(title).strip()
    if not text:
        return ""
    folded = text.casefold()
    for key in UNIFIED_SKILL_SECTIONS:
        label = UNIFIED_SECTION_LABELS.get(key) or ""
        if not label:
            continue
        candidates = (label, *UNIFIED_SECTION_ALIASES.get(key, ()))
        for candidate in candidates:
            if not candidate:
                continue
            if folded == candidate.casefold():
                return key
            if (text[:len(candidate)].casefold() == candidate.casefold()
                    and _BRACKET_SUFFIX_RE.match(text[len(candidate):])):
                return key
    return ""
def _word_prefix_hit(text_lower: str, keyword: str) -> bool:
    if not keyword:
        return False
    if not keyword.isascii():
        return keyword in text_lower
    probe = rf"(?:\b|(?<=_)){re.escape(keyword.lower())}"
    return re.search(probe, text_lower) is not None
def _normalized_readable_name(skill_name: str) -> str:
    return (" ".join(readable_skill_name(skill_name).split())
            or _FALLBACK_SKILL_LABEL)
def _auto_generate_trigger_examples(skill_name: str, capabilities: list[str]) -> list[str]:
    readable = _normalized_readable_name(skill_name)
    examples = [
        f'帮我用一下{readable}',
        f'需要{readable}的功能',
        f'请执行{readable}相关操作',
    ]
    examples.extend(
        f'请用{readable}完成以下任务：{cap}'
        for cap in capabilities[:_MAX_PREVIEW_CAPABILITIES]
    )
    if len(examples) < _MIN_TRIGGER_EXAMPLES:
        examples.extend([
            f'如何使用{readable}',
            f'{readable}能处理哪些任务',
            f'请介绍{readable}的使用方式',
            f'调一下{readable}',
        ])
    return list(dict.fromkeys(examples))[:_MAX_TRIGGER_EXAMPLES]
def _script_invoke_for_capability(cap_lower: str,
                                  script_entries: dict[str, str]) -> str:
    for sname, sinvoke in script_entries.items():
        if any(_word_prefix_hit(sname.lower(), word)
               for word in cap_lower.split()[:2]):
            return sinvoke
    return ""
def _script_invoke_index(scripts: list[dict]) -> dict[str, str]:
    return {safe_text(s.get('name') or ''): safe_text(s.get('invoke') or '')
            for s in scripts}
def _auto_generate_use_cases(capabilities: list[str],
                             scripts: list[dict] | None = None) -> list[dict]:
    use_cases = []
    script_entries = _script_invoke_index(scripts or [])
    for cap in capabilities[:_MAX_PREVIEW_CAPABILITIES]:
        entry = _script_invoke_for_capability(cap.lower(), script_entries)
        use_cases.append({
            'scene': cap,
            'entry': entry or '按技能文档选择与该能力对应的已验证入口',
            'desc': f'基于{cap}能力的自动化操作',
        })
    return use_cases[:_MAX_PREVIEW_CAPABILITIES]
_PRINCIPLE_RULES: tuple[tuple[tuple[str, ...], str], ...] = (
    (('diagnos', 'analyz', '诊断', '分析'),
     '诊断独立: 每步独立运行、独立落盘、独立可审查'),
    (('fix', 'repair', '修复', '治疗'),
     '修复安全网: 修复前验证副作用边界，修复后执行回归验证'),
    (('valid', 'cross', '验证', '交叉'),
     '交叉验证: 多源仲裁降低误报，确保真实问题不被掩盖'),
    (('creat', 'build', '创建', '构建'),
     '源头介入: 创建阶段即获得优质设计，从源头减少事后修补'),
)
def _auto_generate_design_principles(capabilities: list[str]) -> list[str]:
    principles = [
        '可发现性优先: description 含六维增强（中英双语 / 近义词 / 用户指令 / 角色视角 / 业务功能 / 关联锚点）',
        '副作用透明: 写操作与外部影响以真实入口契约为准，调用前确认目标和影响',
        '验证与重执行: 按真实公开契约验证结果；去重、预览和强制重执行能力以实际实现为准',
    ]
    cap_text = ' '.join(capabilities).lower()
    principles.extend(
        message for keywords, message in _PRINCIPLE_RULES
        if any(_word_prefix_hit(cap_text, keyword) for keyword in keywords))
    return principles[:6]
_GENERIC_CONSTRAINT_SPECS: tuple[
    tuple[tuple[str, ...], tuple[str, ...], str, str], ...
] = (
    (("能力边界", "已验证入口"), ("capability boundary", "verified entr"),
     '先确认任务属于能力边界，仅使用文档或源码中的已验证入口',
     ('Confirm the task is inside the capability boundary and use only '
      'verified entries from the docs or source')),
    (("输入参数", "返回值"), ("input parameter", "return value"),
     '输入参数与返回值以实际入口契约为准，不臆造 API 或固定返回结构',
     ('Take input parameters and return values from the real entry contract; '
      'do not invent APIs or response shapes')),
    (("写操作", "验证结果"), ("write operation", "verify the result"),
     '涉及写操作时先确认目标和影响，完成后验证结果并保留必要的恢复依据',
     ('For write operations confirm the target and impact first, then verify '
      'the result and keep the evidence needed to roll back')),
)
_SCAN_CONSTRAINT_SPECS: tuple[
    tuple[str, tuple[str, ...], tuple[str, ...], str, str], ...
] = (
    ("file_ops", ("文件写操作", "目标路径"),
     ("file writes", "target path"),
     '文件写操作须确认目标路径与权限，避免覆盖无关文件',
     ('File writes must confirm the target path and permissions so unrelated '
      'files are never overwritten')),
    ("db_ops", ("数据库操作", "参数化查询"),
     ("database operations", "parameterized queries"),
     '数据库操作须使用参数化查询，避免拼接不受信任的输入',
     ('Database operations must use parameterized queries instead of '
      'concatenating untrusted input')),
)
_CJK_DOC_CHAR_RE = re.compile(r"[\u3400-\u4dbf\u4e00-\u9fff]")
_ASCII_DOC_WORD_RE = re.compile(r"[A-Za-z]{2,}")
_LATIN_DOC_MIN_WORDS = 12
def _is_latin_document(text: str) -> bool:
    if not isinstance(text, str) or not text.strip():
        return False
    sample = text[:8000]
    cjk = len(_CJK_DOC_CHAR_RE.findall(sample))
    latin = len(_ASCII_DOC_WORD_RE.findall(sample))
    if not cjk:
        return latin > 0
    return latin >= _LATIN_DOC_MIN_WORDS and latin > cjk * 3
def _is_latin_description(text: str) -> bool:
    text = safe_text(text)
    if not text.strip() or _CJK_DOC_CHAR_RE.search(text):
        return False
    return bool(_ASCII_DOC_WORD_RE.search(text))
def _constraint_text(cn: str, en: str, latin: bool) -> str:
    return en if latin else cn
def _auto_generate_constraints(latin: bool = False) -> list[str]:
    return [_constraint_text(cn, en, latin)
            for _cn_markers, _en_markers, cn, en in _GENERIC_CONSTRAINT_SPECS]
def _auto_compute_six_dim_scores(skill_name: str, capabilities: list[str], trigger_examples: list[str], exclusion_scopes: list[str]) -> dict[str, float]:
    capabilities = capabilities or []
    trigger_examples = trigger_examples or []
    exclusion_scopes = exclusion_scopes or []
    scores: dict[str, float] = {}
    language_samples = [
        safe_text(sample)
        for sample in (skill_name, *capabilities, *trigger_examples,
                       *exclusion_scopes)
    ]
    has_en = any(re.search(r'[A-Za-z]', sample) for sample in language_samples)
    has_local = any(has_cjk(sample) for sample in language_samples)
    scores['bilingual'] = 0.8 if has_en and has_local else 0.3
    scores[FIELD_SYNONYM_COVERAGE] = min(0.9, 0.3 + len(trigger_examples) * 0.08)
    scores['user_examples'] = min(0.9, 0.2 + len(trigger_examples) * 0.1)
    scores['role_perspective'] = min(0.8, 0.3 + len(capabilities) * 0.1)
    scores[FIELD_CAPABILITY_COVERAGE] = min(0.9, 0.2 + len(capabilities) * 0.12)
    scores['skill_anchors'] = min(0.7, 0.3 + len(exclusion_scopes) * 0.15)
    return scores
@dataclass(frozen=True)
class _SixDimSpec:
    key: str
    label: str
    detail: str
    threshold: float
_SIX_DIM_DETAILS: dict[str, str] = {
    'bilingual': 'description 中英双语覆盖',
    FIELD_SYNONYM_COVERAGE: '口语化触发词覆盖',
    'user_examples': '{n_examples} 条示例',
    'role_perspective': '多角色表达覆盖',
    FIELD_CAPABILITY_COVERAGE: '{n_caps} 项能力',
    'skill_anchors': '关联技能与场景标签',
}
_SIX_DIM_SPECS: tuple[_SixDimSpec, ...] = tuple(
    _SixDimSpec(key, label, _SIX_DIM_DETAILS.get(key, label), threshold)
    for key, label, threshold in SIX_DIM_SPECS)
def _is_python_identifier(value: str) -> bool:
    return bool(value) and value.isidentifier() and not _keyword.iskeyword(value)
def _gen_quick_start_section(skill_name: str, capabilities: list[str]) -> list:
    readable = _normalized_readable_name(skill_name)
    lines = [
        f'## {_section_label("quick_start")}',
        '',
        f'1. 在「技能能力边界」确认任务属于 {readable} 的服务范围。',
        '2. 在「域总览」或「脚本清单」选择真实存在且与任务匹配的入口。',
        '3. 按入口源码、签名或 docstring 准备输入，不根据能力名臆造调用。',
        '4. 检查实际返回结果，并按项目技术栈执行必要验证。',
    ]
    if capabilities:
        lines.extend(['', '### 可处理任务', ''])
        lines.extend(f'- {_md_escape_item(cap)}'
                     for cap in capabilities[:_MAX_PREVIEW_CAPABILITIES])
    lines.append('')
    return lines
def _gen_six_dim_section(six_dim_scores: dict[str, float], trigger_examples: list[str], capabilities: list[str]) -> list:
    lines = []
    lines.append(f'## {_section_label("six_dim_diagnosis")}')
    lines.append('')
    lines.append('| 维度 | 状态 | 详情 |')
    lines.append('|------|------|------|')
    n_examples = len(trigger_examples or [])
    n_caps = len(capabilities)
    for spec in _SIX_DIM_SPECS:
        score = meta_num(six_dim_scores.get(spec.key))
        status = '✓' if score >= spec.threshold else '✗'
        detail = spec.detail.format(n_examples=n_examples, n_caps=n_caps)
        detail_with_score = f'{detail} (score: {score:.2f})'
        lines.append(f'| {spec.label} | {status} | {detail_with_score} |')
    lines.append('')
    return lines
def _gen_capability_boundary_lines(readable_name: str, capabilities: list[str], exclusion_scopes: list[str]) -> list:
    lines = [f'## {_section_label("capability_boundary")}', '']
    lines.append('> **使用步骤：** 1）确认技能边界 2）定位已验证入口 3）按工作流执行 4）验证结果。')
    lines.append('')
    readable = readable_name or _FALLBACK_SKILL_LABEL
    lines.append('### 能做（In Scope）')
    if capabilities:
        for c in capabilities:
            lines.append(f'- {_md_escape_item(c)}')
    else:
        lines.append(f'- {readable} 相关操作')
    lines.append('')
    lines.append('### 不能做（Out of Scope）')
    if exclusion_scopes:
        for e in exclusion_scopes:
            lines.append(f'- {_md_escape_item(e)}')
    else:
        lines.append(f'- 与 {readable} 无关的任务')
    lines.append('')
    return lines
def _gen_agent_decision_lines(readable_name: str) -> list:
    lines = [f'## {_section_label("agent_guidance")}', '']
    lines.append('Agent 在以下情况应加载本技能：')
    lines.append(f'1. 用户意图与 {readable_name} 核心能力匹配')
    lines.append('2. 用户提及本技能的触发关键词（详见下方「触发条件」）')
    lines.append('3. 任务需要本技能提供的特定功能（详见下方「技能能力边界」）')
    lines.append('')
    lines.append('加载后，Agent 应：')
    lines.append('1. **先查「技能能力边界」** — 确认任务在 In Scope 范围内，否则不要加载')
    lines.append('2. **查「域总览」** — 定位目标模块、脚本或公开入口，并按其实际文档调用')
    lines.append('3. **遵守「关键约束」** — 严格按工作流顺序调用')
    lines.append('')
    return lines
def _gen_trigger_condition_lines(readable_name: str, exclusion_scopes: list[str], trigger_examples: list[str]) -> list:
    lines = [f'## {_section_label("trigger_conditions")}', '',
             '### 应当触发（Agent 必须加载本技能）']
    lines.append(f'- 用户提到与 {readable_name} 相关的关键词')
    if trigger_examples:
        kw_text = ' / '.join(
            _md_escape_item(e) for e in trigger_examples[:_MAX_TRIGGER_PREVIEW])
        lines.append(f'- 例如：{kw_text}')
    lines.append(f'- 用户要求执行 {readable_name} 相关操作')
    lines.append('')
    lines.append('### 不应触发')
    lines.append('- 与此技能领域完全无关的通用任务')
    for e in exclusion_scopes[:_MAX_EXCLUSION_SCOPES]:
        lines.append(f'- {_md_escape_item(e)}')
    lines.append(f'- 不涉及 {readable_name} 核心能力的纯闲聊或系统操作')
    lines.append('')
    return lines
def _gen_trigger_example_lines(trigger_examples: list[str]) -> list:
    if not trigger_examples:
        return []
    lines = [f'## {_section_label("trigger_examples")}', '',
             '匹配以下任意说法即触发本技能：', '']
    lines.extend(f'- {_md_escape_item(ex)}'
                 for ex in trigger_examples[:_MAX_TRIGGER_EXAMPLES])
    lines.append('')
    return lines
def _gen_domain_overview_lines(domains: dict[str, list[dict]]) -> list:
    if not domains:
        return []
    lines = [f'## {_section_label("domain_overview")}', '']
    lines.append('| 域 | 模块数 | 入口函数 |')
    lines.append('|----|--------|---------|')
    for domain_name, modules in domains.items():
        entry_funcs = [safe_text(m.get('entry')) for m in modules
                       if m.get('entry')]
        entry_str = ' / '.join(entry_funcs[:3])
        lines.append(f'| {_md_escape_cell(domain_name)} | {len(modules)} | {_md_escape_cell(entry_str)} |')
    lines.extend(_module_index_lines(domains))
    lines.append('')
    return lines
def _module_index_lines(domains: dict[str, list[dict]]) -> list:
    rows: list[str] = []
    for domain_name, modules in domains.items():
        for m in modules:
            name = _md_escape_cell(m.get('name'))
            if not name:
                continue
            entry = _md_escape_cell(m.get('entry'))
            rows.append(
                f"| `{name}` | {_md_escape_cell(domain_name)} | {entry} |")
    if not rows:
        return []
    return (['', '### 模块索引', '',
             '| 模块 | 域 | 入口函数 |', '|------|----|---------|']
            + rows)
def _gen_file_tree_lines(file_tree: str) -> list:
    if not file_tree:
        return []
    return [f'## {_section_label("file_structure")}', '', file_tree, '']
def _three_col_table_section(title: str, headers: tuple[str, str, str],
                             rows: list[tuple[Any, Any, Any]]) -> list[str]:
    if not rows:
        return []
    lines = [f'## {title}', ''] if title else []
    lines.append('| ' + ' | '.join(headers) + ' |')
    lines.append('|' + '|'.join('------' for _ in headers) + '|')
    lines.extend(
        '| ' + ' | '.join(_md_escape_cell(cell) for cell in row) + ' |'
        for row in rows)
    lines.append('')
    return lines
def _script_table_lines(scripts: list[dict]) -> list[str]:
    return _three_col_table_section(
        _section_label("script_inventory"), ('脚本', '用途', '调用方式'),
        [(sc.get('name'), sc.get('purpose'), sc.get('invoke'))
         for sc in scripts])
def _script_decision_lines(scripts: list[dict]) -> list[str]:
    if not scripts:
        return []
    lines = [
        f'## {_section_label("script_vs_api")}',
        '',
        '| 场景 | 推荐方式 | 理由 |',
        '|------|---------|------|',
        '| 快速验证 / 测试 | 使用「脚本清单」登记的实际调用方式 | 避免臆造命令 |',
        '| 集成到工作流 | 使用项目已公开的 API（如有） | 按真实契约组合能力 |',
        '| AI Agent 调用 | 选择文档或源码中已验证的入口 | 确保入口与参数存在 |',
        '| 批量处理 | 按入口契约编排并逐项验证 | 控制副作用与失败影响 |',
    ]
    first_script = scripts[0]
    script_name = first_script.get('name', '')
    invoke = first_script.get('invoke', '')
    if script_name or invoke:
        lines.append(
            f'| 脚本化操作 | `{_md_escape_cell(invoke or script_name)}` | '
            f'使用 {_md_escape_cell(script_name or "已登记脚本")} 的实际入口 |')
    lines.append('')
    return lines
def _auto_generate_gotchas(capabilities: list[str]) -> list[str]:
    gotchas = [
        '入口名称、参数和返回结构以实际源码或已审核文档为准',
        '技能名不必然等于 Python 包名或 CLI 命令，调用前须核实真实入口',
        '涉及写操作时应先确认备份与恢复方式，避免影响无关文件',
        '验证方式按项目实际技术栈选择，不能仅依赖文档生成成功',
    ]
    if capabilities:
        gotchas.append(f'处理“{capabilities[0]}”任务前确认输入类型、范围与预期结果')
    return gotchas
def _gen_use_cases_lines(use_cases: list[dict]) -> list:
    return _three_col_table_section(
        _section_label("use_cases"), ('场景', '入口', '说明'),
        [(uc.get('scene'), uc.get('entry'), uc.get('desc'))
         for uc in use_cases])
def _gen_constraints_lines(constraints: list[str]) -> list:
    if not constraints:
        return []
    return [f'## {_KEY_CONSTRAINTS_TITLE}', '',
            *(f'- {_md_escape_item(c)}' for c in constraints), '']
def _gen_numbered_list_lines(title: str, items: list[str],
                             *, bold: bool = False) -> list:
    if not items:
        return []
    lines = [f'## {title}', '']
    for i, item in enumerate(items, 1):
        text = _md_escape_item(item)
        lines.append(f'{i}. **{text}**' if bold else f'{i}. {text}')
    lines.append('')
    return lines
@dataclass
class _UnifiedDocInputs:
    skill_name: str = ""
    capabilities: list[str] = field(default_factory=list)
    exclusion_scopes: list[str] = field(default_factory=list)
    domains: dict[str, list[dict]] = field(default_factory=dict)
    file_tree: str = ""
    use_cases: list[dict] = field(default_factory=list)
    scripts: list[dict] = field(default_factory=list)
    constraints: list[str] = field(default_factory=list)
    design_principles: list[str] = field(default_factory=list)
    six_dim_scores: dict[str, float] = field(default_factory=dict)
    trigger_examples: list[str] = field(default_factory=list)
    gotchas: list[str] = field(default_factory=list)
def _normalize_unified_inputs(raw: dict[str, Any]) -> _UnifiedDocInputs:
    file_tree = raw.get("file_tree")
    six_dim_scores = raw.get("six_dim_scores")
    return _UnifiedDocInputs(
        skill_name=safe_text(raw.get("skill_name") or ""),
        capabilities=normalize_str_seq(raw.get("capabilities")),
        exclusion_scopes=normalize_str_seq(raw.get("exclusion_scopes")),
        domains=_norm_domains(raw.get("domains")),
        file_tree=file_tree if isinstance(file_tree, str) else "",
        use_cases=normalize_dict_seq(raw.get("use_cases")),
        scripts=normalize_dict_seq(raw.get("scripts")),
        constraints=normalize_str_seq(raw.get("constraints")),
        design_principles=normalize_str_seq(raw.get("design_principles")),
        six_dim_scores=six_dim_scores if isinstance(six_dim_scores, dict) else {},
        trigger_examples=normalize_str_seq(raw.get("trigger_examples")),
        gotchas=normalize_str_seq(raw.get("gotchas")),
    )
def _unified_document_sample(inputs: _UnifiedDocInputs) -> str:
    parts: list[str] = [
        inputs.skill_name, *inputs.capabilities, *inputs.exclusion_scopes,
    ]
    for script in inputs.scripts:
        parts.extend(
            text_field(script, key) for key in ("name", "purpose", "invoke"))
    return " ".join(part for part in parts if part)
def _apply_unified_auto_defaults(inputs: _UnifiedDocInputs) -> _UnifiedDocInputs:
    default_factories: tuple[tuple[str, Callable[[], Any]], ...] = (
        ("trigger_examples", lambda: _auto_generate_trigger_examples(
            inputs.skill_name, inputs.capabilities)),
        ("gotchas", lambda: _auto_generate_gotchas(inputs.capabilities)),
        ("use_cases", lambda: _auto_generate_use_cases(
            inputs.capabilities, inputs.scripts)),
        ("design_principles", lambda: _auto_generate_design_principles(
            inputs.capabilities)),
        ("constraints", lambda: _auto_generate_constraints(
            _is_latin_document(_unified_document_sample(inputs)))),
    )
    for field_name, factory in default_factories:
        if not getattr(inputs, field_name):
            setattr(inputs, field_name, factory())
    if not inputs.six_dim_scores:
        inputs.six_dim_scores = _auto_compute_six_dim_scores(
            inputs.skill_name, inputs.capabilities,
            inputs.trigger_examples, inputs.exclusion_scopes)
    return inputs
def _render_capability_boundary(inputs: _UnifiedDocInputs) -> list:
    return _gen_capability_boundary_lines(
        _normalized_readable_name(inputs.skill_name),
        inputs.capabilities, inputs.exclusion_scopes)
def _render_agent_guidance(inputs: _UnifiedDocInputs) -> list:
    return _gen_agent_decision_lines(
        _normalized_readable_name(inputs.skill_name))
def _render_trigger_conditions(inputs: _UnifiedDocInputs) -> list:
    return _gen_trigger_condition_lines(
        _normalized_readable_name(inputs.skill_name),
        inputs.exclusion_scopes, inputs.trigger_examples)
def _render_trigger_examples(inputs: _UnifiedDocInputs) -> list:
    return _gen_trigger_example_lines(inputs.trigger_examples)
def _render_quick_start(inputs: _UnifiedDocInputs) -> list:
    return _gen_quick_start_section(inputs.skill_name, inputs.capabilities)
def _render_domain_overview(inputs: _UnifiedDocInputs) -> list:
    return _gen_domain_overview_lines(inputs.domains)
def _render_file_structure(inputs: _UnifiedDocInputs) -> list:
    return _gen_file_tree_lines(inputs.file_tree)
def _render_use_cases(inputs: _UnifiedDocInputs) -> list:
    return _gen_use_cases_lines(inputs.use_cases)
def _render_script_inventory(inputs: _UnifiedDocInputs) -> list:
    return _script_table_lines(inputs.scripts)
def _render_script_vs_api(inputs: _UnifiedDocInputs) -> list:
    return _script_decision_lines(inputs.scripts)
def _render_key_constraints(inputs: _UnifiedDocInputs) -> list:
    return _gen_constraints_lines(inputs.constraints)
def _render_design_principles(inputs: _UnifiedDocInputs) -> list:
    return _gen_numbered_list_lines(
        _section_label("design_principles"), inputs.design_principles, bold=True)
def _render_gotchas(inputs: _UnifiedDocInputs) -> list:
    return _gen_numbered_list_lines(_section_label("gotchas"), inputs.gotchas)
def _render_six_dim_diagnosis(inputs: _UnifiedDocInputs) -> list:
    return _gen_six_dim_section(
        inputs.six_dim_scores, inputs.trigger_examples, inputs.capabilities)
_SECTION_RENDERERS: dict[str, Callable[[_UnifiedDocInputs], list]] = {
    "capability_boundary": _render_capability_boundary,
    "agent_guidance": _render_agent_guidance,
    "trigger_conditions": _render_trigger_conditions,
    "trigger_examples": _render_trigger_examples,
    "quick_start": _render_quick_start,
    "domain_overview": _render_domain_overview,
    "file_structure": _render_file_structure,
    "use_cases": _render_use_cases,
    "script_inventory": _render_script_inventory,
    "script_vs_api": _render_script_vs_api,
    "key_constraints": _render_key_constraints,
    "design_principles": _render_design_principles,
    "gotchas": _render_gotchas,
    "six_dim_diagnosis": _render_six_dim_diagnosis,
}
def _render_unified_sections(inputs: _UnifiedDocInputs) -> list[str]:
    lines: list[str] = []
    for key in UNIFIED_SKILL_SECTIONS:
        renderer = _SECTION_RENDERERS.get(key)
        if renderer is not None:
            lines.extend(renderer(inputs))
    return lines
def build_unified_skill_md_body(
    skill_name: str,
    capabilities: list[str] | None = None,
    exclusion_scopes: list[str] | None = None,
    domains: dict[str, list[dict]] | None = None,
    file_tree: str = '',
    use_cases: list[dict] | None = None,
    scripts: list[dict] | None = None,
    constraints: list[str] | None = None,
    design_principles: list[str] | None = None,
    six_dim_scores: dict[str, float] | None = None,
    trigger_examples: list[str] | None = None,
    gotchas: list[str] | None = None,
) -> str:
    inputs = _apply_unified_auto_defaults(_normalize_unified_inputs({
        "skill_name": skill_name,
        "capabilities": capabilities,
        "exclusion_scopes": exclusion_scopes,
        "domains": domains,
        "file_tree": file_tree,
        "use_cases": use_cases,
        "scripts": scripts,
        "constraints": constraints,
        "design_principles": design_principles,
        "six_dim_scores": six_dim_scores,
        "trigger_examples": trigger_examples,
        "gotchas": gotchas,
    }))
    lines = _render_unified_sections(inputs)
    _log.info("SKILL.md 正文生成: %s (%d 行)", inputs.skill_name, len(lines))
    return '\n'.join(lines)
_REGISTRY_ONLY_KEYS = frozenset({"description_block"})
def _normalize_enhance_inputs(
        section_content: Any, api_scan: Any,
) -> tuple[str, dict[str, Any], list[dict[str, Any]]]:
    api_scan = api_scan if isinstance(api_scan, dict) else {}
    if not isinstance(section_content, str):
        section_content = ""
    return section_content, api_scan, _scan_files(api_scan)
def enhance_section_with_api(sec_key: str,
                               section_content: str,
                               api_scan: dict[str, Any] | None,
                               skill_name: str) -> str:
    section_content, api_scan, files = _normalize_enhance_inputs(
        section_content, api_scan)
    section_content = _drop_section_placeholders(section_content)
    if not files or not isinstance(sec_key, str):
        return section_content
    _log.info("enhance_section_with_api 分发: 章节=%s, 文件数=%d",
              sec_key, len(files))
    handler = _SECTION_ENHANCERS.get(sec_key)
    if handler is None:
        return section_content
    enhanced = handler(section_content, api_scan, files, skill_name)
    if enhanced == section_content:
        return section_content
    return _drop_section_placeholders(enhanced)
def _drop_section_placeholders(content: str) -> str:
    lines = content.split("\n")
    kept: list[str] = []
    for idx, (line, in_fence) in enumerate(iter_fence_lines(lines)):
        if in_fence or line.strip() not in _SECTION_PLACEHOLDERS:
            kept.append(line)
            continue
        next_blank = idx + 1 < len(lines) and not lines[idx + 1].strip()
        if kept and not kept[-1].strip() and next_blank:
            kept.pop()
    return "\n".join(kept)
def _iter_top_fence_blocks(content: str):
    pos = 0
    open_pos = -1
    body_start = -1
    prev_in = False
    for line, in_fence in iter_fence_lines(content.split("\n")):
        if not prev_in and in_fence:
            open_pos = pos
            body_start = pos + len(line) + 1
        elif prev_in and not in_fence:
            yield open_pos, pos + len(line), content[body_start:pos]
        prev_in = in_fence
        pos += len(line) + 1
_TREE_GLYPHS = ("├", "└", "│")
def _has_tree_glyph(lines: list[str]) -> bool:
    return any(any(glyph in line for glyph in _TREE_GLYPHS) for line in lines)
def _is_py_dominant(lines: list[str]) -> bool:
    py_lines = sum(1 for line in lines
                   if line.lower().endswith(".py") and len(line.split()) == 1)
    return py_lines * 2 >= len(lines)
def _is_tree_block(block_body: str) -> bool:
    body_lines = [ln.strip() for ln in block_body.splitlines() if ln.strip()]
    if not body_lines:
        return False
    return _has_tree_glyph(body_lines) or _is_py_dominant(body_lines)
def _find_tree_block(content: str):
    for _start, _end, _body in _iter_top_fence_blocks(content):
        if _is_tree_block(_body):
            return _start, _end
    return None
_OVERVIEW_STATS_LINE_RE = re.compile(
    r"> 扫描统计: \d+ 个模块，\d+ 个公开函数，\d+ 个公开类，共 \d+ 行代码")
_FILE_STATS_LINE_RE = re.compile(
    r"> 共 \d+ 行，\d+ 个模块，\d+ 个公开函数，\d+ 个公开类")
def _replace_or_append_stats(content: str, stats_line: str,
                             line_re: re.Pattern[str]) -> str:
    lines = content.split("\n")
    visible_lines = _visible_markdown(content).split("\n")
    body = stats_line.lstrip("\n")
    replaced = False
    kept: list[str] = []
    for ln, visible_ln in zip(lines, visible_lines, strict=True):
        if line_re.fullmatch(visible_ln.rstrip()):
            if replaced:
                continue
            kept.append(body)
            replaced = True
        else:
            kept.append(ln)
    if replaced:
        return "\n".join(kept)
    if not content.strip():
        return body
    return content.rstrip("\r\n") + "\n\n" + body
def _build_summary_tree_block(api_scan: dict[str, Any],
                                total_files: int) -> str:
    skill_dir_raw = coerce_skill_dir(api_scan.get('skill_dir'))
    skill_dir_base = os.path.basename(
        skill_dir_raw.rstrip('\\/')) or 'skill'
    lines = [f"{skill_dir_base}/"]
    has_root_init = any(
        _scan_relative_path(text_field(f_info, "file"), skill_dir_raw)
        == "__init__.py"
        for f_info in _scan_files(api_scan))
    if has_root_init:
        lines.append("├── __init__.py")
    n_tests, test_dirs = count_test_files(skill_dir_raw)
    if test_dirs:
        lines.append(f"├── ... ({total_files} 个模块，完整清单见下方统计)")
        lines.append("└── " + " ".join(f"{name}/" for name in test_dirs))
        lines.append(f"    └── ({n_tests} 个测试文件)")
    else:
        lines.append(f"└── ... ({total_files} 个模块，完整清单见下方统计)")
    return "```\n" + "\n".join(lines) + "\n```"
def _splice_block(content: str, span: tuple[int, int], block: str) -> str:
    start, end = span
    return content[:start] + block + content[end:]
def _file_stats_line(api_scan: dict[str, Any], total_files: int) -> str:
    return (
        f"> 共 {int_metric(api_scan.get('total_lines'), 0)} 行，"
        f"{total_files} 个模块，"
        f"{int_metric(api_scan.get('total_public_functions'), 0)} 个公开函数，"
        f"{int_metric(api_scan.get('total_public_classes'), 0)} 个公开类"
    )
def _replace_tree_block(content: str, tree_span: tuple[int, int] | None,
                        file_tree: str, api_scan: dict[str, Any],
                        total_files: int) -> str:
    tree_block = (_build_summary_tree_block(api_scan, total_files)
                  if total_files > _MAX_TABLE_ROWS else file_tree)
    if tree_span:
        return _splice_block(content, tree_span, tree_block)
    if tree_block in content:
        return content
    if not content.strip():
        return tree_block
    return content.rstrip("\r\n") + "\n\n" + tree_block
def _enhance_file_structure(
        content: str, api_scan: dict[str, Any], files: list[dict[str, Any]],
        _skill_name: str,
) -> str:
    file_tree = api_scan.get("file_tree")
    if not isinstance(file_tree, str) or not file_tree:
        return content
    total_files = len(files)
    content = _replace_tree_block(
        content, _find_tree_block(content), file_tree, api_scan, total_files)
    return _replace_or_append_stats(
        content, _file_stats_line(api_scan, total_files), _FILE_STATS_LINE_RE)
_CODE_SPAN_RE = re.compile(r"`([^`\n]+)`")
def _collect_unmentioned_modules(
        content: str, files: list[dict[str, Any]]) -> list[dict[str, Any]]:
    normalized_content = content.replace("\\", "/").lower()
    mentioned = {m.lower() for m in re.findall(
        r'(?<![\w./-])([\w./-]+\.(?i:py))(?![\w./-])',
        normalized_content)}
    mentioned_code = {span.strip() for span in _CODE_SPAN_RE.findall(
        normalized_content)}
    mentioned_stems = {key[:-3] for key in mentioned if key.endswith(".py")}
    mentioned_code_stems = {span[:-3] for span in mentioned_code
                            if span.endswith(".py")}
    module_paths = [
        text_field(f, "file").replace("\\", "/")
        if isinstance(f, dict) else "" for f in files]
    basename_counts: dict[str, int] = {}
    for module_path in module_paths:
        basename = module_path.rsplit("/", 1)[-1].lower()
        if basename:
            basename_counts[basename] = basename_counts.get(basename, 0) + 1
    unmentioned: list[dict[str, Any]] = []
    for f_info, module_path in zip(files, module_paths, strict=True):
        fname = module_path.rsplit("/", 1)[-1]
        if not fname:
            continue
        path_key = module_path.lower()
        fname_key = fname.lower()
        basename_mentioned = (basename_counts[fname_key] == 1
                              and fname_key in mentioned)
        path_mentioned = (path_key in mentioned
                          or ("/" in path_key and any(
                              key.endswith("/" + path_key)
                              for key in mentioned)))
        display_key = module_display_name(module_path).lower()
        display_mentioned = bool(display_key) and (
            display_key in mentioned_code
            or display_key in mentioned_stems
            or display_key in mentioned_code_stems)
        fname_stem_key = py_stem(fname_key)
        stem_mentioned = (basename_counts[fname_key] == 1
                          and (fname_stem_key in mentioned_code
                               or fname_stem_key in mentioned_stems))
        if (path_mentioned or basename_mentioned or display_mentioned
                or stem_mentioned or fname_key == "__init__.py"
                or is_test_source_basename(fname)):
            continue
        unmentioned.append(f_info)
    return unmentioned
_SCRIPT_INVENTORY_HEADER_PREFIX = "> 未列出的 "
_SCRIPT_INVENTORY_FOOTER = "> 请按模块索引和项目实际导入路径调用公开函数或类。"
_SCRIPT_INVENTORY_TABLE_HEAD = ("| 模块 | 核心函数/类 | 用途 |",
                                "|------|------------|------|")
def _script_inventory_header(unmentioned: list[dict[str, Any]]) -> list[str]:
    total_funcs = sum(len(member_entries(f, "functions")) for f in unmentioned)
    total_classes = sum(len(member_entries(f, "classes")) for f in unmentioned)
    header = (f"{_SCRIPT_INVENTORY_HEADER_PREFIX}{len(unmentioned)} 个模块"
              f"（共 {total_funcs} 个函数、{total_classes} 个类）：")
    return [header, "", *_SCRIPT_INVENTORY_TABLE_HEAD]
def _strip_script_inventory_block(content: str) -> tuple[str, int]:
    lines = content.split("\n")
    visible_lines = _visible_markdown(content).split("\n")
    start = next((idx for idx, line in enumerate(visible_lines)
                  if line.startswith(_SCRIPT_INVENTORY_HEADER_PREFIX)), -1)
    if start < 0:
        return content, -1
    end = next((idx for idx in range(start, len(visible_lines))
                if visible_lines[idx].strip() == _SCRIPT_INVENTORY_FOOTER), -1)
    if end < 0:
        end = start
        while end + 1 < len(visible_lines) and (
                not visible_lines[end + 1].strip()
                or visible_lines[end + 1].lstrip().startswith("|")):
            end += 1
    cut_start = start
    while cut_start > 0 and not lines[cut_start - 1].strip():
        cut_start -= 1
    kept = lines[:cut_start] + lines[end + 1:]
    return "\n".join(kept), cut_start
def _enhance_script_inventory(
        content: str, _api_scan: dict[str, Any], files: list[dict[str, Any]],
        _skill_name: str,
) -> str:
    source, block_at = _strip_script_inventory_block(content)
    unmentioned = _collect_unmentioned_modules(source, files)
    if not unmentioned:
        return source
    table_lines = _script_inventory_header(unmentioned)
    table_lines += _script_inventory_rows(unmentioned)
    block = "\n".join(table_lines)
    if block_at < 0:
        return append_block(source, block)
    if not source:
        return block
    lines = source.split("\n")
    pad = [""] if block_at > 0 and lines[block_at - 1].strip() else []
    return "\n".join([*lines[:block_at], *pad, block, *lines[block_at:]])
def _script_inventory_rows(unmentioned: list[dict[str, Any]]) -> list[str]:
    rows = []
    for f_info in unmentioned[:_MAX_TABLE_ROWS]:
        module_name = module_display_name(text_field(f_info, "file"))
        funcs = member_entries(f_info, "functions")[:3]
        classes = member_entries(f_info, "classes")[:2]
        symbols = [fn["name"] for fn in funcs]
        symbols += [c["name"] for c in classes]
        symbol_str = ", ".join(f"`{s}`" for s in symbols[:4]) if symbols else "-"
        purpose = _infer_module_purpose(f_info)
        rows.append(
            f"| `{module_name}` | {symbol_str} | {_md_escape_cell(purpose)} |")
    if len(unmentioned) > _MAX_TABLE_ROWS:
        rows.append(
            f"| ... | 共 {len(unmentioned) - _MAX_TABLE_ROWS} 个更多模块 | "
            "按实际模块路径定位并阅读入口文档 |")
    rows.append("")
    rows.append(_SCRIPT_INVENTORY_FOOTER)
    return rows
_FUNCTION_PURPOSE_RULES = (
    ("run", "执行入口"),
    ("scan", "扫描分析"),
    ("check", "检查验证"),
    ("运行", "执行入口"),
    ("扫描", "扫描分析"),
    ("检查", "检查验证"),
)
def _purpose_from_functions(funcs: list[dict[str, Any]]) -> str:
    return next(
        (purpose for signal, purpose in _FUNCTION_PURPOSE_RULES
         if any(_word_prefix_hit(f["name"].lower(), signal)
                for f in funcs)),
        "工具模块",
    )
def _first_doc_line(f_info: dict[str, Any]) -> str:
    module_doc = text_field(f_info, "module_doc").strip()
    if module_doc:
        return module_doc.splitlines()[0][:_DOC_SUMMARY_MAX_CHARS]
    for func in member_entries(f_info, "functions"):
        doc = text_field(func, "doc").strip()
        if doc:
            return doc.splitlines()[0][:_DOC_SUMMARY_MAX_CHARS]
    return ""
def _infer_module_purpose(f_info: dict[str, Any]) -> str:
    doc = _first_doc_line(f_info)
    if doc:
        return doc
    return _purpose_from_functions(member_entries(f_info, "functions"))
def _derived_domains(files: list[dict[str, Any]],
                     ctx: _ModulePathContext) -> dict[str, list[dict]]:
    grouped: dict[str, list[dict]] = {}
    for f_info in files:
        raw_path = text_field(f_info, "file")
        module = (_module_import_path(raw_path, ctx)
                  or module_display_name(raw_path))
        if not module:
            continue
        member_parts = _module_path_parts(raw_path, ctx)[0]
        domain = member_parts[0] if len(member_parts) > 1 else "root"
        entry = next(
            (func["name"] for func in member_entries(f_info, "functions")
             if not func["name"].startswith("_")), "")
        grouped.setdefault(domain, []).append({"name": module, "entry": entry})
    return {name: sorted(items, key=lambda item: item["name"])
            for name, items in sorted(grouped.items())}
_DOMAIN_OVERVIEW_GENERATED_TABLE_HEADERS = frozenset({
    "| 域 | 模块数 | 入口函数 |",
    "| 模块 | 域 | 入口函数 |",
})
def _enhance_domain_overview(
        content: str, api_scan: dict[str, Any], files: list[dict[str, Any]],
        _skill_name: str,
) -> str:
    total_funcs = int_metric(api_scan.get("total_public_functions"), 0)
    total_classes = int_metric(api_scan.get("total_public_classes"), 0)
    total_lines = int_metric(api_scan.get("total_lines"), 0)
    heading = ""
    has_custom_content = False
    in_generated_table = False
    for line, in_fence in iter_fence_lines(content.split("\n")):
        if not heading and not in_fence and _H2_TITLE_RE.match(line):
            heading = line
        if in_fence:
            has_custom_content = True
            break
        stripped = line.strip()
        if not stripped:
            in_generated_table = False
            continue
        if (_H2_TITLE_RE.match(line)
                or _OVERVIEW_STATS_LINE_RE.fullmatch(line.rstrip())):
            in_generated_table = False
            continue
        if stripped == "### 模块索引":
            in_generated_table = False
            continue
        if stripped in _DOMAIN_OVERVIEW_GENERATED_TABLE_HEADERS:
            in_generated_table = True
            continue
        if in_generated_table and stripped.startswith("|"):
            continue
        has_custom_content = True
        break
    derived = (_derived_domains(files, _module_path_context(api_scan))
               if not has_custom_content else {})
    if derived:
        overview_lines = _gen_domain_overview_lines(derived)
        if heading:
            overview_lines[0] = heading
        content = "\n".join(overview_lines).strip("\n")
    stats_line = (
        f"> 扫描统计: {len(files)} 个模块，"
        f"{total_funcs} 个公开函数，"
        f"{total_classes} 个公开类，"
        f"共 {total_lines} 行代码"
    )
    return _replace_or_append_stats(content, stats_line,
                                    _OVERVIEW_STATS_LINE_RE)
def _documented_capabilities(files: list[dict[str, Any]]) -> dict[str, str]:
    capabilities: dict[str, str] = {}
    for f_info in files:
        module_name = module_display_name(text_field(f_info, "file"))
        if _is_package_init(module_name):
            continue
        doc = _first_doc_line(f_info)
        if module_name and doc and not _is_placeholder_line(doc):
            capabilities[module_name] = doc
    return capabilities
_IN_SCOPE_CAPABILITY_HEADING_RE = re.compile(
    r"(?im)^[ \t]{0,3}#{1,6}[ \t]+"
    r"(?!.*(?:不能做|\bnot\s+in\s+scope\b|\bout\s+of\s+scope\b))"
    r"[^\n]*(?:能做|\bin\s+scope\b)")
def _enhance_capability_boundary(
        content: str, _api_scan: dict[str, Any], files: list[dict[str, Any]],
        _skill_name: str,
) -> str:
    capabilities = _documented_capabilities(files)
    visible_content = _visible_markdown(content)
    if (not capabilities
            or _IN_SCOPE_CAPABILITY_HEADING_RE.search(visible_content)):
        return content
    items = list(capabilities.items())
    can_do = "\n".join(
        f"| {_md_escape_cell(module)} | {_md_escape_cell(doc)} |"
        for module, doc in items[:_MAX_TABLE_ROWS]
    )
    if len(items) > _MAX_TABLE_ROWS:
        can_do += (
            f"\n| ... | 共 {len(items) - _MAX_TABLE_ROWS} 个更多模块"
            "（完整清单见「域总览」模块索引） |")
    enhancement = (
        "### 能做（In Scope）\n\n"
        "| 模块 | 已记录能力 |\n|------|----------|\n" + can_do + "\n"
    )
    return append_block(content, enhancement)
def _scan_relative_path(file_path: str, skill_dir: str) -> str:
    path = file_path.replace("\\", "/")
    if skill_dir and os.path.isabs(file_path):
        try:
            path = os.path.relpath(file_path, skill_dir).replace("\\", "/")
        except (OSError, ValueError) as _swallowed_exc:
            log_swallowed(
                __name__, _swallowed_exc,
                context=f'_scan_relative_path:{type(_swallowed_exc).__name__}')
            return path
    return "/".join(p for p in path.split("/") if p and p != ".")
def _layout_scan_signature(
        api_scan: dict[str, Any], skill_dir: str,
) -> tuple[str, ...]:
    try:
        with open(
                os.path.join(skill_dir, "pyproject.toml"),
                encoding="utf-8-sig", errors="replace") as handle:
            project_metadata = handle.read()
    except FileNotFoundError:
        project_metadata = ""
    except (OSError, ValueError) as exc:
        project_metadata = ""
        log_swallowed(
            __name__, exc, context="_layout_scan_signature:project_metadata")
    # detect_layout 用项目名在主包候选间消歧；文件清单不变时元数据仍须失效。
    return (
        "\0pyproject.toml\0" + project_metadata,
        *sorted(
            _scan_relative_path(text_field(f_info, "file"), skill_dir)
            for f_info in _scan_files(api_scan)
        ),
    )
@lru_cache(maxsize=32)
def _cached_layout(
        skill_dir: str, _scan_signature: tuple[str, ...],
):
    return detect_layout(skill_dir)
@dataclass(frozen=True)
class _ModulePathContext:
    skill_dir: str
    package_prefix: tuple[str, ...] = ()
    package_dir: tuple[str, ...] = ()
    blocked: bool = False
def _module_path_context(api_scan: dict[str, Any]) -> _ModulePathContext:
    skill_dir = coerce_skill_dir(api_scan.get("skill_dir")) or ""
    layout = (_cached_layout(
        skill_dir, _layout_scan_signature(api_scan, skill_dir))
        if skill_dir else None)
    if layout is not None and layout.package_name and layout.package_root:
        try:
            package_rel = os.path.relpath(layout.package_root, layout.root)
        except (OSError, ValueError) as exc:
            log_swallowed(
                __name__, exc,
                context=f"_module_path_context:{type(exc).__name__}")
        else:
            if package_rel == ".":
                if not _is_python_identifier(layout.package_name):
                    return _ModulePathContext(skill_dir=skill_dir, blocked=True)
                return _ModulePathContext(
                    skill_dir=skill_dir, package_prefix=(layout.package_name,))
            package_dir = tuple(
                part for part in package_rel.replace("\\", "/").split("/")
                if part and part != ".")
            package_prefix: tuple[str, ...] = (layout.package_name,)
            if (len(package_dir) == 1
                    and package_dir[0].casefold() in SOURCE_DIR_NAMES
                    and not os.path.isfile(os.path.join(
                        layout.package_root, "__init__.py"))):
                package_prefix = ()
            return _ModulePathContext(
                skill_dir=skill_dir,
                package_prefix=package_prefix,
                package_dir=package_dir)
    root_has_init = any(
        _scan_relative_path(text_field(f, "file"), skill_dir) == "__init__.py"
        for f in _scan_files(api_scan)
    )
    if not root_has_init:
        return _ModulePathContext(skill_dir=skill_dir)
    package_name = os.path.basename(skill_dir.rstrip("\\/"))
    if not _is_python_identifier(package_name):
        return _ModulePathContext(skill_dir=skill_dir, blocked=True)
    return _ModulePathContext(
        skill_dir=skill_dir, package_prefix=(package_name,))
def _module_path_parts(
        file_path: str, ctx: _ModulePathContext,
) -> tuple[list[str], tuple[str, ...]]:
    if ctx.blocked:
        return [], ()
    relative = _scan_relative_path(file_path, ctx.skill_dir)
    parts = [part for part in relative.split("/") if part]
    package_dir = ctx.package_dir
    if not package_dir:
        return parts, ctx.package_prefix
    prefix_len = len(package_dir)
    if tuple(parts[:prefix_len]) == package_dir:
        return parts[prefix_len:], ctx.package_prefix
    source_dir = package_dir[:-1]
    source_len = len(source_dir)
    if source_len and tuple(parts[:source_len]) == source_dir:
        return parts[source_len:], ()
    return parts, ()
def _module_import_path(file_path: str, ctx: _ModulePathContext) -> str:
    parts, package_prefix = _module_path_parts(file_path, ctx)
    if not parts:
        return ""
    parts[-1] = py_stem(parts[-1])
    if parts[-1] == "__init__":
        parts = parts[:-1]
    parts = [*package_prefix, *parts]
    if not parts or any(not _is_python_identifier(part) for part in parts):
        return ""
    return ".".join(parts)
def _collect_public_funcs(api_scan: dict[str, Any]) -> list[dict[str, Any]]:
    ctx = _module_path_context(api_scan)
    public_funcs = []
    for f_info in _scan_files(api_scan):
        module = _module_import_path(text_field(f_info, "file"), ctx)
        for func in member_entries(f_info, "functions"):
            if not func["name"].startswith("_"):
                public_funcs.append({
                    "name": func["name"],
                    "params": func.get("params"),
                    "is_async": func.get("is_async") is True,
                    "doc": text_field(func, "doc"),
                    "module": module,
                })
    return public_funcs
def _required_params(func: dict[str, Any]) -> list[dict[str, Any]]:
    params = func.get("params")
    if not isinstance(params, list):
        return []
    return [param for param in params
            if isinstance(param, dict)
            and param.get("default") is None
            and param.get("kind") in ("positional", "keyword")]
def _runnable_examples(funcs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [func for func in funcs
            if func.get("module") and not _required_params(func)]
_ASYNCIO_IMPORT_LINE = "import asyncio"
def _example_lines(func: dict[str, Any]) -> list[str]:
    module = text_field(func, "module")
    if not module:
        return []
    lines: list[str] = []
    desc = text_field(func, "doc").split("\n")[0][:_DOC_SUMMARY_MAX_CHARS]
    if desc:
        lines.append("# " + desc)
    lines.append(f"from {module} import {func['name']}")
    call = f"{func['name']}()"
    if func.get("is_async") is True:
        call = f"asyncio.run({call})"
    lines.append("result = " + call)
    lines.append("")
    return lines
def _compose_example_block(funcs: list[dict[str, Any]]) -> str:
    lines: list[str] = []
    needs_asyncio = False
    for func in funcs:
        func_lines = _example_lines(func)
        if not func_lines:
            continue
        lines.extend(func_lines)
        needs_asyncio = needs_asyncio or func.get("is_async") is True
    if needs_asyncio:
        lines.insert(0, _ASYNCIO_IMPORT_LINE)
    return "\n".join(lines)
def _has_fenced_block(content: str) -> bool:
    return any(in_fence for _line, in_fence
               in iter_fence_lines(content.split("\n")))
_QUICK_START_TABLE_HEADER = "| 入口 | 用途 | 耗时 |"
def _enhance_quick_start(
        content: str, api_scan: dict[str, Any], _files: list[dict[str, Any]],
        _skill_name: str,
) -> str:
    funcs = _runnable_examples(_collect_public_funcs(api_scan))[:_MAX_EXAMPLE_FUNCS]
    if not funcs:
        return content
    blocks: list[str] = []
    if _QUICK_START_TABLE_HEADER not in _visible_markdown(content):
        blocks.append(
            _QUICK_START_TABLE_HEADER + "\n"
            "|------|------|------|\n"
            f"| `{funcs[0]['name']}` | 主要入口 | 视技能规模 |")
    example_block = _compose_example_block(funcs)
    if example_block and not _has_fenced_block(content):
        blocks.append("```python\n" + example_block + "```")
    if not blocks:
        return content
    return append_block(content, "\n\n".join(blocks))
_USE_CASE_TABLE_HEADER_RE = re.compile(r"(?m)^\|[ \t]*场景[ \t]*\|")
def _use_case_rows(
        files: list[dict[str, Any]],
        ctx: _ModulePathContext | None = None,
) -> list[tuple[Any, Any, Any]]:
    rows: list[tuple[Any, Any, Any]] = []
    for f_info in files:
        raw_path = text_field(f_info, "file")
        display_module = module_display_name(raw_path)
        if not display_module or _is_package_init(display_module):
            continue
        module = display_module
        if ctx is not None:
            module = _module_import_path(raw_path, ctx) or display_module
        scene = _first_doc_line(f_info)
        if not scene:
            continue
        functions = [func for func in member_entries(f_info, "functions")
                     if not func["name"].startswith("_")]
        classes = [cls for cls in member_entries(f_info, "classes")
                   if not cls["name"].startswith("_")]
        entry_func = functions[0] if functions else None
        entry = entry_func["name"] if entry_func is not None else ""
        call_shape = f"{entry}()"
        required_params = (_required_params(entry_func)
                           if entry_func is not None else [])
        if required_params:
            arguments: list[str] = []
            for param in required_params:
                name = text_field(param, "name")
                if not name:
                    arguments = []
                    break
                arguments.append(
                    name if param.get("kind") == "positional"
                    else f"{name}={name}")
            call_shape = (f"{entry}({', '.join(arguments)})"
                          if arguments else f"{entry}(...)")
        if all(_is_python_identifier(part) for part in module.split(".")):
            callable_entry = (f"`{module}.{call_shape}`" if entry
                              else f"`{module}`")
        else:
            callable_entry = f"`{raw_path}`"
        detail = (f"{len(functions)} 个公开函数 / "
                  f"{len(classes)} 个公开类")
        rows.append((scene, callable_entry, detail))
    return rows
def _enhance_use_cases(
        content: str, api_scan: dict[str, Any], files: list[dict[str, Any]],
        _skill_name: str,
) -> str:
    if _USE_CASE_TABLE_HEADER_RE.search(_visible_markdown(content)):
        return content
    table = _three_col_table_section(
        "", ('场景', '入口', '说明'),
        _use_case_rows(files, _module_path_context(api_scan))[:_MAX_TABLE_ROWS])
    if not table:
        return content
    return append_block(content, "\n".join(table).rstrip("\n"))
def _iter_api_texts(files: list[dict[str, Any]]) -> Iterator[str]:
    for f_info in files:
        yield text_field(f_info, "file").lower()
        for func in member_entries(f_info, "functions"):
            yield func["name"] + " " + text_field(func, "signature")
_FILE_WRITE_SIGNALS = ("write", "save", "dump", "export", "open")
_DB_SIGNALS = ("db", "sql", "database")
def _api_ops_flags(files: list[dict[str, Any]]) -> tuple[bool, bool]:
    has_file_ops = False
    has_db_ops = False
    for text in _iter_api_texts(files):
        has_file_ops = has_file_ops or any(
            _word_prefix_hit(text, word) for word in _FILE_WRITE_SIGNALS)
        has_db_ops = has_db_ops or any(
            _word_prefix_hit(text, word) for word in _DB_SIGNALS)
    return has_file_ops, has_db_ops
def _scan_constraint_specs(
    api_scan: dict[str, Any], latin: bool = False,
) -> list[tuple[tuple[tuple[str, ...], ...], str]]:
    has_file_ops, has_db_ops = _api_ops_flags(_scan_files(api_scan))
    flags = {"file_ops": has_file_ops, "db_ops": has_db_ops}
    return [((cn_markers, en_markers), _constraint_text(cn, en, latin))
            for key, cn_markers, en_markers, cn, en in _SCAN_CONSTRAINT_SPECS
            if flags.get(key, False)]
_LIST_BULLET_MARKERS = ("- ", "* ", "+ ")
def _constraint_bullet_texts(content: str) -> list[str]:
    texts: list[str] = []
    lines = content.split("\n")
    span = _section_span(lines, "key_constraints")
    if span is None:
        return texts
    start, end = span
    for line, in_fence in iter_fence_lines(lines[start + 1:end]):
        if in_fence:
            continue
        stripped = line.lstrip()
        for marker in _LIST_BULLET_MARKERS:
            if stripped.startswith(marker):
                texts.append(stripped[len(marker):])
                break
    return texts
def _normalize_constraint_text(text: str) -> str:
    return "".join(text.replace("`", "").split()).lower()
def _constraint_covered(marker_groups: tuple[tuple[str, ...], ...],
                        bullets: list[str]) -> bool:
    normalized = [_normalize_constraint_text(b) for b in bullets]
    return any(
        all(_normalize_constraint_text(marker) in bullet for marker in group)
        for group in marker_groups if group
        for bullet in normalized)
def _heading_section_key(line: str) -> str:
    match = _H2_TITLE_RE.match(line)
    return (_resolve_unified_key(strip_atx_closing(match.group(1)))
            if match else "")
def _section_span(lines: list[str], section_key: str) -> tuple[int, int] | None:
    start = -1
    for idx, (line, in_fence) in enumerate(iter_fence_lines(lines)):
        if in_fence:
            continue
        matched = _heading_section_key(line) == section_key
        if start < 0:
            if matched:
                start = idx
            continue
        if _H2_TITLE_RE.match(line) or re.match(r"[ \t]{0,3}#[ \t]", line):
            return start, idx
    return None if start < 0 else (start, len(lines))
def _insert_constraint_bullets(content: str, bullets: list[str]) -> str:
    lines = content.split("\n")
    title = _KEY_CONSTRAINTS_TITLE
    span = _section_span(lines, "key_constraints")
    if span is None:
        section = "\n\n".join((f"## {title}", "\n".join(bullets)))
        return append_block(content, section)
    start, end = span
    bullet_at = -1
    last_text = start
    placeholder_at = -1
    for offset, (line, in_fence) in enumerate(
            iter_fence_lines(lines[start + 1:end])):
        idx = start + 1 + offset
        if in_fence:
            continue
        stripped = line.strip()
        if not stripped:
            continue
        last_text = idx
        if stripped in _SECTION_PLACEHOLDERS:
            placeholder_at = idx
        elif line.lstrip().startswith(_LIST_BULLET_MARKERS):
            bullet_at = idx
    if bullet_at >= 0:
        insert_at = bullet_at + 1
        cursor = insert_at
        while cursor < end:
            nxt = lines[cursor]
            if not nxt.strip():
                cursor += 1
                continue
            if nxt.startswith((" ", "\t", *_LIST_BULLET_MARKERS)):
                insert_at = cursor + 1
                cursor += 1
                continue
            break
        lines[insert_at:insert_at] = bullets
        return "\n".join(lines)
    if placeholder_at >= 0:
        lines[placeholder_at:placeholder_at + 1] = bullets
        return "\n".join(lines)
    insert_at = last_text + 1
    needs_gap = lines[insert_at - 1].strip() != ""
    block = ([""] + bullets) if needs_gap else bullets
    lines[insert_at:insert_at] = block
    return "\n".join(lines)
def _document_language_sample(content: str, api_scan: Any) -> str:
    parts: list[str] = [content]
    if isinstance(api_scan, dict):
        parts.append(safe_text(api_scan.get("skill_name") or ""))
        for f_info in _scan_files(api_scan):
            parts.append(text_field(f_info, "module_doc"))
            parts.extend(
                text_field(func, "doc")
                for func in member_entries(f_info, "functions"))
    return "\n".join(part for part in parts if part)[:8000]
def _enhance_constraints(
        content: str, api_scan: dict[str, Any], _files: list[dict[str, Any]],
        _skill_name: str,
) -> str:
    bullets = _constraint_bullet_texts(content)
    latin = _is_latin_document(_document_language_sample(content, api_scan))
    generic = [((cn_markers, en_markers), _constraint_text(cn, en, latin))
               for cn_markers, en_markers, cn, en in _GENERIC_CONSTRAINT_SPECS]
    specs = _scan_constraint_specs(api_scan, latin) + generic
    missing = [f"- {text}" for markers, text in specs
               if not _constraint_covered(markers, bullets)]
    if not missing:
        return content
    return _insert_constraint_bullets(content, missing)
_SECTION_ENHANCERS: dict[str, Callable[[str, dict, list, str], str]] = {
    "file_structure": _enhance_file_structure,
    "script_inventory": _enhance_script_inventory,
    "domain_overview": _enhance_domain_overview,
    "capability_boundary": _enhance_capability_boundary,
    "quick_start": _enhance_quick_start,
    "use_cases": _enhance_use_cases,
    "key_constraints": _enhance_constraints,
}
def validate_section_registry() -> dict[str, Any]:
    registry_keys = {s["key"] for s in get_standard_sections()}
    builder_keys = set(UNIFIED_SKILL_SECTIONS)
    missing_in_registry = sorted(builder_keys - registry_keys)
    extra_in_registry = sorted(registry_keys - builder_keys - _REGISTRY_ONLY_KEYS)
    enhancer_orphans = sorted(set(_SECTION_ENHANCERS) - builder_keys)
    renderer_missing = sorted(builder_keys - set(_SECTION_RENDERERS))
    renderer_orphans = sorted(set(_SECTION_RENDERERS) - builder_keys)
    return {
        "ok": ((not missing_in_registry) and (not extra_in_registry)
               and (not enhancer_orphans) and (not renderer_missing)
               and (not renderer_orphans)),
        "registry_count": len(registry_keys),
        "builder_count": len(builder_keys),
        "missing_in_registry": missing_in_registry,
        "extra_in_registry": extra_in_registry,
        "enhancer_count": len(_SECTION_ENHANCERS),
        "enhancer_orphans": enhancer_orphans,
        "renderer_count": len(_SECTION_RENDERERS),
        "renderer_missing": renderer_missing,
        "renderer_orphans": renderer_orphans,
    }
_H2_HEADING_RE = re.compile(r"[ \t]{0,3}##[ \t]")
_H2_TITLE_RE = re.compile(r"[ \t]{0,3}##[ \t](.+)")
def _split_body_sections(body: str) -> list[str]:
    chunks: list[str] = []
    current: list[str] = []
    for line, in_fence in iter_fence_lines(body.split("\n")):
        if not in_fence and _H2_HEADING_RE.match(line) and current:
            chunks.append("\n".join(current))
            current = [line]
        else:
            current.append(line)
    if current:
        chunks.append("\n".join(current))
    return chunks
@dataclass(frozen=True)
class _ParsedBody:
    unified: dict[str, str] = field(default_factory=dict)
    extras: tuple[tuple[str, str], ...] = ()
    preamble: tuple[str, ...] = ()
def _parse_original_sections(original_body: str) -> _ParsedBody:
    unified: dict[str, str] = {}
    extras: list[tuple[str, str]] = []
    preamble_chunks: list[str] = []
    for _raw_chunk in _split_body_sections(original_body):
        chunk = _raw_chunk.strip()
        if not chunk:
            continue
        title_match = _H2_TITLE_RE.match(_raw_chunk)
        if not title_match:
            preamble_chunks.append(chunk)
            continue
        title = strip_atx_closing(title_match.group(1))
        body = chunk.partition("\n")[2].strip("\n")
        section_key = _resolve_unified_key(title)
        if not section_key:
            extras.append((title, chunk))
        elif not body:
            unified.setdefault(section_key, "")
        elif unified.get(section_key):
            unified[section_key] = f"{unified[section_key]}\n\n{body}"
        else:
            unified[section_key] = body
    return _ParsedBody(unified=unified, extras=tuple(extras),
                       preamble=tuple(preamble_chunks))
_PLACEHOLDER_HEAD_MARKERS = ("（待", "(待", "（todo", "(todo", "todo",
                             "待填充", "待从", "待补充", "待完善")
_PLACEHOLDER_LINE_MAX_CHARS = 60
def _body_content_lines(text: str) -> list[str]:
    return [line for line in text.split("\n")
            if line.strip() and not line.lstrip().startswith("#")]
def _is_placeholder_line(line: str) -> bool:
    text = line.strip().lstrip("-*+> ").strip()
    if not text or len(text) > _PLACEHOLDER_LINE_MAX_CHARS:
        return False
    return (text.lower().startswith(_PLACEHOLDER_HEAD_MARKERS)
            or text in _SECTION_PLACEHOLDERS)
def _is_placeholder_content(text: str) -> bool:
    body_lines = _body_content_lines(text)
    if not body_lines:
        return True
    return all(_is_placeholder_line(line) for line in body_lines)
def _enhance_section_safe(sec_key: str, sec_content: str,
                          api_scan: dict[str, Any] | None,
                          skill_name: str) -> str:
    try:
        return enhance_section_with_api(sec_key, sec_content, api_scan, skill_name)
    except Exception as e:  # noqa: BLE001
        _log.warning("重构时章节增强失败（保留原文）[%s]: %s", sec_key, e)
        return sec_content
def _append_section(sections: list[DocSection], title: str, content: str,
                    required: bool = False) -> None:
    normalized = content.strip("\n") if isinstance(content, str) else ""
    if title and normalized and not _H2_TITLE_RE.match(normalized):
        normalized = f"## {title}\n\n{normalized}"
    sections.append(DocSection(
        title=title, content=normalized, required=required,
        order=len(sections) + 1))
def _append_unified_sections(sections: list[DocSection],
                             original_bodies: dict[str, str],
                             fallback_map: dict[str, str],
                             api_scan: dict[str, Any] | None,
                             skill_name: str) -> None:
    for sec_key in UNIFIED_SKILL_SECTIONS:
        section_label = UNIFIED_SECTION_LABELS.get(sec_key, sec_key)
        original = original_bodies.get(sec_key, "")
        body = (original if original.strip()
                and not _is_placeholder_content(original)
                else fallback_map.get(sec_key, ""))
        base = f"## {section_label}\n\n{body}" if body.strip() else ""
        sec_content = _enhance_section_safe(
            sec_key, base, api_scan, skill_name)
        if not sec_content.strip():
            continue
        _append_section(
            sections, section_label, sec_content,
            required=(sec_key in _REQUIRED_SECTION_KEYS))
def _append_extra_sections(sections: list[DocSection],
                           extras: tuple[tuple[str, str], ...]) -> None:
    for title, sec_text in extras:
        if not title:
            continue
        _append_section(sections, title, sec_text)
def build_refactored_body(skill_name: str,
                            original_body: str,
                            capabilities: list[str],
                            exclusion_scopes: list[str],
                            api_scan: dict[str, Any] | None = None,
                            colloquial_examples: list[str] | None = None) -> list[DocSection]:
    original_body = (original_body if isinstance(original_body, str)
                     else "")
    sections: list[DocSection] = []
    parsed = _parse_original_sections(original_body)
    fallback_body = build_unified_skill_md_body(
        skill_name=skill_name,
        capabilities=capabilities,
        exclusion_scopes=exclusion_scopes,
        trigger_examples=colloquial_examples,
    )
    fallback_map = _parse_original_sections(fallback_body).unified
    if not colloquial_examples:
        fallback_map.pop("trigger_examples", None)
    if parsed.preamble:
        _append_section(sections, "", "\n\n".join(parsed.preamble))
    _append_unified_sections(
        sections, parsed.unified, fallback_map, api_scan, skill_name)
    _append_extra_sections(sections, parsed.extras)
    _log_refactor_body_summary(
        skill_name, sections, parsed.preamble, parsed.unified, api_scan)
    return sections
def _log_refactor_body_summary(skill_name: str, sections: list,
                               preamble_chunks: tuple[str, ...],
                               unified_sections: dict, api_scan: dict | None) -> None:
    _log.info(
        "build_refactored_body 完成: 技能=%s, 章节数=%d（序言=%d,"
        " 统一章节=%d, API扫描=%s）",
        skill_name, len(sections),
        1 if preamble_chunks else 0, len(unified_sections),
        "可用" if api_scan else "不可用",
    )
def _norm_str(value: Any) -> str:
    if isinstance(value, str):
        return value.strip()
    return "" if value is None else str(value).strip()
def _norm_description(value: Any) -> str:
    text = normalize_description_field(value)
    return " ".join(
        part for part in (line.strip() for line in text.splitlines()) if part
    )
_MAX_SKILL_NAME_CHARS = 200
def _norm_skill_name(value: Any) -> str:
    return _norm_str(value)[:_MAX_SKILL_NAME_CHARS]
_TERMINAL_PUNCT = ("。", "！", "？", ".", "!", "?")
_BOUNDARY_SENTENCE_SEPS = "。！？!?；;\n"
_TAIL_BOUNDARY_MAX_CHARS = 300
_TAIL_BOUNDARY_RE = re.compile(
    "|".join(f"(?:{_p})" for _p in
             (*NATURAL_BOUNDARY_PATTERNS, *NEGATIVE_BOUNDARY_PATTERNS)),
    re.IGNORECASE)
def _split_tail_boundary(core: str) -> tuple[str, str]:
    for match in reversed(list(_TAIL_BOUNDARY_RE.finditer(core))):
        sentence_start = max(
            core.rfind(_sep, 0, match.start()) for _sep in _BOUNDARY_SENTENCE_SEPS
        ) + 1
        for start in dict.fromkeys((sentence_start, match.start())):
            tail = core[start:]
            if tail.strip() and len(tail) <= _TAIL_BOUNDARY_MAX_CHARS:
                return core[:start], tail
    return core, ""
_NEUTRAL_TRIGGER_SENTENCE = "当用户需要此类操作时使用本技能。"
_NEUTRAL_EXCLUSION_SENTENCE = "不适用于无关的通用任务。"
_NEUTRAL_TRIGGER_SENTENCE_EN = "Use this skill when the user needs this task."
_NEUTRAL_EXCLUSION_SENTENCE_EN = "Not applicable to unrelated general tasks."
def _trigger_sentence(skill_name: str, latin: bool) -> str:
    if latin:
        return (f"Use this skill when the user needs {skill_name}."
                if skill_name else _NEUTRAL_TRIGGER_SENTENCE_EN)
    return (f"当用户需要{skill_name}时使用本技能。"
            if skill_name else _NEUTRAL_TRIGGER_SENTENCE)
def _exclusion_sentence(skill_name: str, latin: bool) -> str:
    if latin:
        return (f"Not applicable to tasks outside {skill_name}."
                if skill_name else _NEUTRAL_EXCLUSION_SENTENCE_EN)
    return (f"不适用于非{skill_name}的任务。"
            if skill_name else _NEUTRAL_EXCLUSION_SENTENCE)
def _capability_sentence(items: list[str], latin: bool) -> str:
    if latin:
        return f"Including: {', '.join(items)}."
    return f"包括：{'，'.join(items)}。"
def _needs_space(left: str, right: str) -> bool:
    return bool(left) and bool(right) and left[-1].isascii() \
        and not left[-1].isspace() and right[0].isascii() \
        and right[0].isalnum()
def _join_parts(parts: list[str]) -> str:
    out = ""
    for part in parts:
        if not part:
            continue
        if _needs_space(out, part):
            out += " "
        out += part
    return out
def _has_violation(diag_report: Any, rule_id: str) -> bool:
    return any(v.rule_id == rule_id for v in diag_report.violations)
def _violation_ids(diag_report: Any) -> set[str]:
    return {v.rule_id for v in diag_report.violations}
def _introduces_new_violations(current_diag: Any, improved_diag: Any) -> bool:
    return bool(_violation_ids(improved_diag) - _violation_ids(current_diag))
def _fix_scaffold_segments(result: Any, skill_name: str, changes: list[str],
                           latin: bool = False) -> tuple[str, str]:
    prefix = ""
    suffix = ""
    if _has_violation(result, "DR-001"):
        prefix = _trigger_sentence(skill_name, latin)
        changes.append("补充触发条件前缀")
    if _has_violation(result, "DR-003"):
        suffix = _exclusion_sentence(skill_name, latin)
        changes.append("补充排除边界声明")
    return prefix, suffix
def _find_vague_words(core: str) -> list[str]:
    return [
        w for w in sorted(VAGUE_WORDS_EN)
        if vague_word_spans(w, core)
    ] + [w for w in sorted(VAGUE_WORDS_CN, key=len, reverse=True)
         if vague_word_spans(w, core)]
def _remove_vague_words(core: str, vague_found: list[str]) -> str:
    for word in vague_found:
        word_stripped = word.strip()
        if not word_stripped:
            continue
        for start, end in reversed(vague_word_spans(word_stripped, core)):
            core = core[:start] + core[end:]
    return core
def _normalize_punct_residue(core: str) -> str:
    core = re.sub(r'([，、；,;])[，、；,;]+', r'\1', core)
    core = re.sub(r'([。！？.!?])\1+', r'\1', core)
    core = re.sub(r'[，、；,;]+(?=[。！？.!?])', '', core)
    core = re.sub(r'^[，、；,;。！？.!?]+', '', core)
    return re.sub(r'[，、；,;]+$', '', core)
def _strip_vague_words(core: str) -> tuple[str, list[str]]:
    vague_found = _find_vague_words(core)
    if not vague_found:
        return core, []
    core = re.sub(r'\s{2,}', " ", _remove_vague_words(core, vague_found)).strip()
    return _normalize_punct_residue(core), vague_found
_CAP_SEPARATOR = "、"
_CAP_SEPARATOR_EN = ", "
def _cap_separator(latin: bool) -> str:
    return _CAP_SEPARATOR_EN if latin else _CAP_SEPARATOR
def _fit_caps_budget(keywords: list[str], budget: int,
                     separator: str) -> tuple[str, bool]:
    caps = ""
    for item in keywords:
        candidate = f"{caps}{separator}{item}" if caps else item
        if len(candidate) > budget:
            return caps or item[:budget], True
        caps = candidate
    return caps, False
def _caps_payload(skill_name: str, keywords: list[str], budget: int,
                  separator: str) -> tuple[str, bool]:
    caps, truncated = _fit_caps_budget(keywords, budget, separator)
    if not caps:
        caps = (f"{skill_name}能力" if skill_name else "对应任务的处理能力")
        if len(caps) > budget:
            caps = caps[:budget]
    return caps, truncated
def _expand_short_description(skill_name: str, segments: _RefineSegments,
                              keywords: list[str],
                              min_len: int, max_len: int,
                              latin: bool = False) -> str:
    body = _terminated(segments.core)
    capability_wrapper = _capability_sentence([""], latin)
    fixed_len = len(_join_parts(
        [segments.prefix, body, capability_wrapper, segments.suffix]))
    budget = max(1, max_len - fixed_len)
    caps, truncated = _caps_payload(
        skill_name, keywords or [], budget, _cap_separator(latin))
    if truncated:
        _log.warning(
            "refine_description DR-004 扩写 caps 载荷超预算截断"
            "（keywords %d 项，预算 %d 字符）",
            len(keywords or []), budget)
    capability = _capability_sentence([caps], latin) if caps else ""
    detail = ""
    fillers = (("Used for the concrete tasks declared in the description.",
                "Suitable for automating related tasks and verifying results.")
               if latin else
               ("用于执行描述中声明的具体任务。",
                "适用于相关任务的自动化处理与结果验证。"))
    for filler in fillers:
        candidate = _join_parts(
            [segments.prefix, body, capability, detail, segments.suffix])
        if len(candidate) >= min_len:
            break
        with_filler = _join_parts(
            [segments.prefix, body, capability, detail + filler,
             segments.suffix])
        if len(with_filler) > max_len:
            break
        detail += filler
    return _join_parts(
        [segments.prefix, body, capability, detail, segments.suffix])
def _truncate_long_description(segments: _RefineSegments,
                               min_len: int, max_len: int) -> str:
    prefix, core, suffix = segments.prefix, segments.core, segments.suffix
    body, tail = _split_tail_boundary(core)
    reserve = len(tail)
    budget = max(0, max_len - len(prefix) - len(suffix) - reserve)
    def render(raw_budget: int) -> str:
        cut_budget = raw_budget
        if (cut_budget
                and not body[:cut_budget].rstrip().endswith(_TERMINAL_PUNCT)):
            cut_budget -= 1
        cut = _truncate_at_boundary(body[:cut_budget], min_len)
        if cut and not cut.rstrip().endswith(_TERMINAL_PUNCT):
            cut = _terminated(cut)
        return _join_parts([prefix, cut, tail, suffix])
    refined = render(budget)
    overflow = len(refined) - max_len
    if overflow > 0:
        refined = render(max(0, budget - overflow))
    return refined
_CJK_SENTENCE_MARKS = ("。", "！", "？")
_ASCII_SENTENCE_MARKS = (".", "!", "?")
_CLAUSE_END_MARKS = ("、", "；", ";")
def _last_mark_end(cut: str, marks: tuple[str, ...],
                   *, need_space: bool) -> int:
    best = -1
    for mark in marks:
        pos = cut.find(mark)
        while pos >= 0:
            end = pos + len(mark)
            if not need_space or end >= len(cut) or cut[end].isspace():
                best = max(best, end)
            pos = cut.find(mark, end)
    return best
def _truncate_at_boundary(cut: str, min_len: int) -> str:
    for marks, need_space in ((_CJK_SENTENCE_MARKS, False),
                              (_ASCII_SENTENCE_MARKS, True),
                              (_CLAUSE_END_MARKS, False)):
        end = _last_mark_end(cut, marks, need_space=need_space)
        if end > min_len:
            return cut[:end]
    trimmed = cut.rstrip()
    if trimmed and trimmed[-1].isascii() and trimmed[-1].isalnum():
        trimmed = re.sub(r"[A-Za-z0-9_]+$", "", trimmed).rstrip()
        if len(trimmed) >= min_len:
            return trimmed
    return cut
_EXTENSION_SIGNAL_LIMIT = 6
def _extension_signal(file_extensions: list[str]) -> str:
    return " / ".join(file_extensions[:_EXTENSION_SIGNAL_LIMIT])
def _length_bounds() -> tuple[int, int]:
    try:
        for rule in get_matching_hard_rules():
            if rule.get("id") == "DR-004":
                min_len = int_metric(
                    rule.get("min_length"), DESCRIPTION_MIN_LENGTH)
                max_len = int_metric(
                    rule.get("max_length"), DESCRIPTION_MAX_LENGTH)
                if 0 < min_len <= max_len:
                    return min_len, max_len
                break
    except Exception as exc:  # noqa: BLE001
        _log.warning("读取 DR-004 长度阈值降级: %s", exc)
    return DESCRIPTION_MIN_LENGTH, DESCRIPTION_MAX_LENGTH
def _length_message(_inputs: _ImproveInputs) -> str:
    min_len, max_len = _length_bounds()
    return f"调整 description 长度至 {min_len}-{max_len} 字符范围"
def _trigger_part(skill_name: str, capabilities: list[str],
                  file_extensions: list[str], readable: str) -> str:
    if file_extensions:
        trigger_part = f"[MUST USE] 当用户需要处理 {_extension_signal(file_extensions)} 文件时使用本技能。"
    else:
        trigger_part = (
            f"[MUST USE] 当用户需要执行 {skill_name} 任务时使用本技能。"
            if skill_name
            else "[MUST USE] 当用户需要执行此类任务时使用本技能。"
        )
    if capabilities:
        cap_preview = "、".join(
            capabilities[:_MAX_TRIGGER_CAPABILITIES])
        trigger_part += f" 适用于：{cap_preview}等场景。"
    elif readable:
        trigger_part += f" 适用于：{readable} 类任务。"
    return trigger_part
_SPOKEN_CUE_FAMILIES: tuple[tuple[tuple[str, ...], tuple[str, ...]], ...] = (
    (("创建", "生成", "新建", "build", "create", "generate"),
     ("做个", "建个", "生成个", "弄个")),
    (("分析", "诊断", "检查", "审查", "analyze", "check", "review"),
     ("看看", "查查", "分析下", "检查下")),
    (("编辑", "修改", "更新", "edit", "update", "modify"),
     ("改一下", "调整下", "编辑下")),
    (("转换", "导出", "转化", "convert", "export"),
     ("转一下", "换成", "变一下")),
    (("搜索", "查找", "查询", "search", "find"),
     ("找一下", "搜一下", "查一下")),
    (("优化", "提升", "改进", "optimize", "improve"),
     ("优化下", "改进下", "调一下")),
)
def _spoken_cues_for(capability: str) -> list[str]:
    c_lower = capability.lower()
    for triggers, cues in _SPOKEN_CUE_FAMILIES:
        if any(_word_prefix_hit(c_lower, w) for w in triggers):
            return list(cues)
    return []
def _collect_spoken_terms(
        capabilities: list[str],
        colloquial_examples: list[str]) -> list[str]:
    if colloquial_examples:
        return colloquial_examples[:_MAX_SPOKEN_EXAMPLES]
    action_cues = []
    for c in (capabilities or []):
        action_cues.extend(_spoken_cues_for(c))
    spoken_terms = list(dict.fromkeys(action_cues))
    if not spoken_terms:
        spoken_terms = ["帮我弄一下", "我需要用这个技能", "请帮我做一下"]
    return spoken_terms
def _bilingual_part_from(capabilities: list[str]) -> str:
    caps = capabilities or []
    groups = [
        [c for c in caps if has_cjk(c)],
        [c for c in caps if c.isascii() and re.search(r"[A-Za-z]", c)],
    ]
    rendered = ["、".join(group[:_MAX_BILINGUAL_CAPS])
                for group in groups if group]
    if len(rendered) < 2:
        return ""
    return f"中英双语覆盖：{' | '.join(rendered)}。"
_ROLE_HINT_FAMILIES: tuple[tuple[tuple[str, ...], str], ...] = (
    (("管理", "配置", "部署", "发布", "admin", "config", "deploy"),
     "[管理] 管理 / 配置 / 部署"),
    (("分析", "诊断", "审计", "审查", "检查", "diag", "audit", "review"),
     "[分析] 分析 / 诊断 / 审查"),
    (("创建", "生成", "编写", "撰写", "创作", "build", "create", "generate", "write"),
     "[创作] 创作 / 编写 / 生成"),
    (("编辑", "修改", "转换", "整理", "edit", "modify", "convert", "transform"),
     "[编辑] 编辑 / 转换 / 整理"),
    (("搜索", "检索", "查询", "提取", "search", "find", "query", "extract"),
     "[检索] 检索 / 查询 / 提取"),
)
def _role_hints_from(capabilities: list[str]) -> list[str]:
    # jwsgj:suppress large_list_alloc
    role_hints = [
        hint
        for capability in (capabilities or [])
        for triggers, hint in _ROLE_HINT_FAMILIES
        if any(_word_prefix_hit(capability.lower(), word) for word in triggers)
    ]
    return list(dict.fromkeys(role_hints)) or ["[通用] 通用任务"]
def _exclusion_part(exclusion_scopes: list[str], readable: str) -> str:
    if exclusion_scopes:
        return (f"不适用于："
                f"{'、'.join(exclusion_scopes[:_MAX_EXCLUSION_SCOPES])}。")
    if readable:
        return f"不适用于与 {readable} 无关的通用任务。"
    return _NEUTRAL_EXCLUSION_SENTENCE
_GENERIC_DESCRIPTION_MAX_CHARS = 600
_ELLIPSIS = "..."
def _fit_text(text: str, budget: int) -> str:
    if budget <= 0 or not text:
        return ""
    if len(text) <= budget:
        return text
    if budget <= len(_ELLIPSIS):
        return text[:budget]
    return text[:budget - len(_ELLIPSIS)].rstrip() + _ELLIPSIS
def _fit_generic_description(parts: list[str]) -> str:
    parts = [part for part in parts if part]
    if not parts:
        return _trigger_part("", [], [], "")
    result = " ".join(parts)
    if len(result) <= _GENERIC_DESCRIPTION_MAX_CHARS:
        return result
    prefix = parts[0]
    suffix = parts[-1] if len(parts) > 1 else _NEUTRAL_EXCLUSION_SENTENCE
    middle = parts[1:-1] if len(parts) > 1 else []
    if (len(prefix) + len(_NEUTRAL_EXCLUSION_SENTENCE) + 2
            > _GENERIC_DESCRIPTION_MAX_CHARS):
        prefix = _trigger_part("", [], [], "")
    remaining = _GENERIC_DESCRIPTION_MAX_CHARS - len(prefix) - 2
    suffix = _fit_text(suffix, max(0, remaining))
    remaining -= len(suffix)
    rendered_middle = _fit_text(" ".join(middle), max(0, remaining))
    return " ".join(
        part for part in (prefix, rendered_middle, suffix) if part
    )
@dataclass(frozen=True)
class _ImproveInputs:
    skill_name: str
    current_description: str
    current_diag: Any
    all_caps: list[str]
    file_extensions: list[str]
    exclusion_scopes: list[str]
    latin: bool = False
@dataclass(frozen=True)
class _ImprovementRule:
    rule_id: str
    gate: Callable[[_ImproveInputs], bool]
    message: Callable[[_ImproveInputs], str]
def _always_applicable(_inputs: _ImproveInputs) -> bool:
    return True
def _new_capability_items(inputs: _ImproveInputs) -> list[str]:
    capability_text = mask_exclusion_context(inputs.current_description)
    return [cap for cap in inputs.all_caps
            if cap not in capability_text]
def _has_caps_source(inputs: _ImproveInputs) -> bool:
    return bool(_new_capability_items(inputs))
def _has_extension_source(inputs: _ImproveInputs) -> bool:
    return bool(inputs.file_extensions)
def _constant_message(text: str) -> Callable[[_ImproveInputs], str]:
    def message(_inputs: _ImproveInputs) -> str:
        return text
    return message
def _boundary_message(inputs: _ImproveInputs) -> str:
    if inputs.exclusion_scopes:
        return f"添加排除边界声明（{', '.join(inputs.exclusion_scopes[:2])}）"
    return "添加排除边界声明"
def _caps_message(inputs: _ImproveInputs) -> str:
    return f"扩展能力枚举至 {len(_new_capability_items(inputs))} 项"
def _extension_message(inputs: _ImproveInputs) -> str:
    return f"添加明确的文件扩展名信号（{', '.join(inputs.file_extensions[:3])}）"
_IMPROVEMENT_RULES: tuple[_ImprovementRule, ...] = (
    _ImprovementRule("DR-001", _always_applicable,
                     _constant_message("添加明确的触发条件从句")),
    _ImprovementRule("DR-002", _has_caps_source, _caps_message),
    _ImprovementRule("DR-003", _always_applicable, _boundary_message),
    _ImprovementRule("DR-004", _always_applicable, _length_message),
    _ImprovementRule("DR-005", _always_applicable,
                     _constant_message("移除 description 中的模糊词汇")),
    _ImprovementRule("DR-006", _always_applicable,
                     _constant_message("补充操作动词和目标对象，确保 description 自足")),
    _ImprovementRule("DR-007", _has_extension_source, _extension_message),
    _ImprovementRule("DR-010", _always_applicable,
                     _constant_message("补充缺失的结构要素（操作动词/目标对象/触发条件）")),
)
def _improvement_items(inputs: _ImproveInputs) -> list[str]:
    return [rule.message(inputs)
            for rule in _IMPROVEMENT_RULES
            if rule.gate(inputs)
            and _has_violation(inputs.current_diag, rule.rule_id)]
def _terminated(text: str) -> str:
    text = text.strip()
    if text and not text.endswith(_TERMINAL_PUNCT):
        return text + ("。" if has_cjk(text) else ".")
    return text
def _improvement_trigger_segment(inputs: _ImproveInputs) -> str:
    needs_extension = _has_violation(inputs.current_diag, "DR-007")
    if needs_extension and inputs.file_extensions:
        signal = _extension_signal(inputs.file_extensions)
        return (f"Use this skill when the user needs to process {signal} files."
                if inputs.latin
                else f"当用户需要处理 {signal} 文件时使用本技能。")
    if not _has_violation(inputs.current_diag, "DR-001"):
        return ""
    return _trigger_sentence(inputs.skill_name, inputs.latin)
def _improvement_capability_segment(inputs: _ImproveInputs) -> str:
    if not _has_violation(inputs.current_diag, "DR-002"):
        return ""
    new_items = _new_capability_items(inputs)
    if not new_items:
        return ""
    return _capability_sentence(
        new_items[:_MAX_IMPROVEMENT_CAPABILITIES], inputs.latin)
def _improvement_exclusion_segment(
    inputs: _ImproveInputs, neutral: bool = False
) -> str:
    if not _has_violation(inputs.current_diag, "DR-003"):
        return ""
    scopes = inputs.exclusion_scopes[:_MAX_EXCLUSION_SCOPES]
    if neutral:
        return (_NEUTRAL_EXCLUSION_SENTENCE_EN if inputs.latin
                else _NEUTRAL_EXCLUSION_SENTENCE)
    if scopes and inputs.latin:
        return (f"Not for tasks whose main output is {', '.join(scopes)}.")
    if scopes:
        return f"若主要产出为 {', '.join(scopes)}，则不应触发本技能。"
    return _exclusion_sentence(inputs.skill_name, inputs.latin)
def _improvement_fallback_segment(skill_name: str, latin: bool = False) -> str:
    if latin:
        target = skill_name or "this kind of task"
        return (f"Use this skill when the user needs {target}, including the "
                "tasks declared in the description. Not applicable to "
                "unrelated general tasks.")
    if skill_name:
        return (f"当用户需要 {skill_name} 时使用本技能，包括执行描述中声明的任务。"
                f"不适用于非 {skill_name} 的通用任务。")
    return ("当用户需要此类操作时使用本技能，包括执行描述中声明的任务。"
            "不适用于无关的通用任务。")
def _improved_parts(inputs: _ImproveInputs, neutral: bool = False) -> list[str]:
    parts = [
        _improvement_trigger_segment(inputs),
        _terminated(inputs.current_description),
        _improvement_capability_segment(inputs),
        _improvement_exclusion_segment(inputs, neutral=neutral),
    ]
    present = [p for p in parts if p]
    if not present:
        present.append(
            _improvement_fallback_segment(inputs.skill_name, inputs.latin))
    return present
@dataclass(frozen=True)
class _RefineSegments:
    prefix: str
    core: str
    suffix: str
def _normalize_join_boundary(segments: _RefineSegments) -> _RefineSegments:
    prefix, core, suffix = segments.prefix, segments.core, segments.suffix
    if prefix and core:
        core = re.sub(r'^[，、；,;。！？.!?]+', '', core)
    if suffix and core.strip():
        core = _terminated(re.sub(r'[，、；,;]+$', '', core.rstrip()))
    return _RefineSegments(prefix=prefix, core=core, suffix=suffix)
def _fix_length_violation(skill_name: str, segments: _RefineSegments,
                          keywords: list[str], refined: str,
                          latin: bool = False) -> tuple[str, str | None]:
    try:
        min_len, max_len = _length_bounds()
        if min_len <= len(refined) <= max_len:
            return refined, None
        cur_len = len(refined)
        if cur_len < min_len:
            expanded = _expand_short_description(
                skill_name, segments, keywords, min_len, max_len, latin)
            return expanded, (
                f"description 过短({cur_len}字符)，按现有句段扩写并保留原描述"
            )
        truncated = _truncate_long_description(
            segments, min_len, max_len)
        return truncated, (
            f"description 过长({cur_len}字符)，截断至{len(truncated)}字符"
        )
    except Exception as exc:  # noqa: BLE001
        _log.warning("refine_description DR-004 修复降级: %s", exc)
    return refined, None
@dataclass
class DescriptionTemplate:
    skill_name: str = ""
    domain: str = _DEFAULT_DOMAIN
    capabilities: list[str] = field(default_factory=list)
    file_extensions: list[str] = field(default_factory=list)
    exclusion_scopes: list[str] = field(default_factory=list)
    colloquial_examples: list[str] = field(default_factory=list)
    generated_description: str = ""
class MatchingDescriptionGenerator:
    def __init__(self: Self) -> None:
        self._diagnoser = MatchingRuleDiagnoser()
    def generate(self: Self, skill_name: str, domain: str = _DEFAULT_DOMAIN,
                capabilities: list[str] | None = None,
                file_extensions: list[str] | None = None,
                exclusion_scopes: list[str] | None = None,
                colloquial_examples: list[str] | None = None) -> DescriptionTemplate:
        skill_name = _norm_skill_name(skill_name)
        capabilities = normalize_str_seq(capabilities)
        file_extensions = normalize_str_seq(file_extensions)
        exclusion_scopes = normalize_str_seq(exclusion_scopes)
        colloquial_examples = normalize_str_seq(colloquial_examples)
        resolved_domain = normalize_domain_key(domain)
        generated_description = self._generate_generic(
            skill_name, capabilities, file_extensions,
            exclusion_scopes, colloquial_examples,
        )
        return DescriptionTemplate(
            skill_name=skill_name,
            domain=resolved_domain,
            capabilities=capabilities,
            file_extensions=file_extensions,
            exclusion_scopes=exclusion_scopes,
            colloquial_examples=colloquial_examples,
            generated_description=generated_description,
        )
    def generate_and_validate(self: Self, skill_name: str, domain: str = _DEFAULT_DOMAIN,
                               capabilities: list[str] | None = None,
                               keywords: list[str] | None = None,
                               file_extensions: list[str] | None = None,
                               exclusion_scopes: list[str] | None = None,
                               colloquial_examples: list[str] | None = None) -> dict[str, Any]:
        template = self.generate(
            skill_name=skill_name,
            domain=domain,
            capabilities=capabilities,
            file_extensions=file_extensions,
            exclusion_scopes=exclusion_scopes,
            colloquial_examples=colloquial_examples,
        )
        diag = self._diagnoser.diag(
            skill_name=template.skill_name,
            description=template.generated_description,
            keywords=keywords,
        )
        return {"template": template, "diag": diag}
    def _generate_generic(self: Self, skill_name: str,
                          capabilities: list[str],
                          file_extensions: list[str],
                          exclusion_scopes: list[str],
                          colloquial_examples: list[str]) -> str:
        parts = []
        readable = readable_skill_name(skill_name)
        parts.append(_trigger_part(skill_name, capabilities,
                                   file_extensions, readable))
        if capabilities:
            parts.append(
                f"核心能力："
                f"{'、'.join(capabilities[:_MAX_CAPABILITIES_IN_DESCRIPTION])}。")
        spoken_terms = _collect_spoken_terms(capabilities, colloquial_examples)
        parts.append(
            f"口语化表达：{'、'.join(spoken_terms[:_MAX_SPOKEN_TERMS])}。")
        bilingual_part = _bilingual_part_from(capabilities)
        if bilingual_part:
            parts.append(bilingual_part)
        parts.append(
            f"适用角色："
            f"{' | '.join(_role_hints_from(capabilities)[:_MAX_ROLE_HINTS])}。")
        parts.append(_exclusion_part(exclusion_scopes, readable))
        return _fit_generic_description(parts)
    def generate_from_diag(self: Self, skill_name: str,
                           current_description: str,
                           keywords: list[str] | None = None,
                           capabilities: list[str] | None = None,
                           file_extensions: list[str] | None = None,
                           exclusion_scopes: list[str] | None = None,
                           ) -> dict[str, Any]:
        current_description = _norm_description(current_description)
        skill_name = _norm_skill_name(skill_name)
        capabilities = normalize_str_seq(capabilities)
        file_extensions = normalize_str_seq(file_extensions)
        exclusion_scopes = normalize_str_seq(exclusion_scopes)
        current_diag = self._diagnoser.diag(
            skill_name, current_description, keywords)
        existing_caps = extract_capabilities(current_description)
        inputs = _ImproveInputs(
            skill_name=skill_name,
            current_description=current_description,
            current_diag=current_diag,
            all_caps=list(dict.fromkeys(
                existing_caps + capabilities))[:_MAX_IMPROVEMENT_CAPABILITIES],
            file_extensions=file_extensions,
            exclusion_scopes=exclusion_scopes,
            latin=_is_latin_description(current_description),
        )
        improved_description, improvements, improved_diag = (
            self._improve_from_inputs(inputs, keywords)
        )
        return {
            "current_diag": current_diag,
            "improved_description": improved_description,
            "improvements": improvements,
            "improved_diag": improved_diag,
        }
    @staticmethod
    def _accept_candidate(
        candidate: dict[str, Any], improvements: list[str]
    ) -> tuple[str, list[str], Any]:
        merged = list(improvements)
        merged.extend(f"收口: {c}" for c in candidate["changes"])
        return candidate["refined"], merged, candidate["diag"]
    def _improve_from_inputs(
        self: Self, inputs: _ImproveInputs, keywords: list[str] | None = None
    ) -> tuple[str, list[str], Any]:
        improvements = _improvement_items(inputs)
        if not improvements:
            return inputs.current_description, [], inputs.current_diag
        primary = self.refine_description(
            inputs.skill_name, " ".join(_improved_parts(inputs)), keywords)
        if (primary["refined"] != inputs.current_description
                and not _introduces_new_violations(
                    inputs.current_diag, primary["diag"])):
            return self._accept_candidate(primary, improvements)
        neutral = self.refine_description(
            inputs.skill_name, " ".join(_improved_parts(inputs, neutral=True)),
            keywords)
        if (neutral["refined"] != inputs.current_description
                and not _introduces_new_violations(
                    inputs.current_diag, neutral["diag"])):
            return self._accept_candidate(neutral, improvements)
        minimal = self.refine_description(
            inputs.skill_name, inputs.current_description, keywords)
        if (minimal["refined"] != inputs.current_description
                and not _introduces_new_violations(
                    inputs.current_diag, minimal["diag"])):
            return self._accept_candidate(minimal, [])
        return inputs.current_description, [], inputs.current_diag
    def refine_description(self: Self, skill_name: str,
                           description: str,
                           keywords: list[str] | None = None) -> dict[str, Any]:
        description = _norm_description(description)
        skill_name = _norm_skill_name(skill_name)
        keywords = normalize_matching_keywords(keywords)
        latin = _is_latin_description(description)
        result = self._diagnoser.diag(skill_name, description, keywords)
        changes: list[str] = []
        prefix, suffix = _fix_scaffold_segments(
            result, skill_name, changes, latin)
        core = description
        if _has_violation(result, "DR-005"):
            core, vague_found = _strip_vague_words(core)
            if vague_found:
                changes.append(f"移除模糊词汇: {', '.join(vague_found[:5])}")
        segments = _normalize_join_boundary(
            _RefineSegments(prefix=prefix, core=core, suffix=suffix))
        refined = _join_parts([segments.prefix, segments.core, segments.suffix])
        refined, _msg = _fix_length_violation(
            skill_name, segments, keywords, refined, latin)
        if _msg:
            changes.append(_msg)
        refined_diag = self._diagnoser.diag(skill_name, refined, keywords)
        post_changes: list[str] = []
        post_prefix, post_suffix = _fix_scaffold_segments(
            refined_diag, skill_name, post_changes, latin)
        if post_prefix or post_suffix:
            segments = _normalize_join_boundary(_RefineSegments(
                prefix=post_prefix, core=refined, suffix=post_suffix))
            refined = _join_parts(
                [segments.prefix, segments.core, segments.suffix])
            refined, _msg = _fix_length_violation(
                skill_name, segments, keywords, refined, latin)
            if _msg:
                post_changes.append(_msg)
            changes.extend(post_changes)
            refined_diag = self._diagnoser.diag(skill_name, refined, keywords)
        return {
            "refined": refined,
            "changes": changes,
            "diag": refined_diag,
        }
_generator_instance = MatchingDescriptionGenerator()
def get_generator() -> MatchingDescriptionGenerator:
    return _generator_instance
def infer_skill_domain(
    skill_name: str, keywords: list | None = None, category: str = ""
) -> str:
    for source in (category, skill_name):
        key = normalize_domain_key(source)
        if key:
            return key
    for keyword in normalize_str_seq(keywords):
        key = normalize_domain_key(keyword)
        if key:
            return key
    return "generic"
def generate_matching_description(skill_name: str, domain: str = _DEFAULT_DOMAIN,
                                  capabilities: list[str] | None = None,
                                  keywords: list[str] | None = None,
                                  file_extensions: list[str] | None = None,
                                  exclusion_scopes: list[str] | None = None,
                                  colloquial_examples: list[str] | None = None,
                                  ) -> dict[str, Any]:
    resolved_domain = domain.strip() if isinstance(domain, str) else ""
    return get_generator().generate_and_validate(
        skill_name=skill_name,
        domain=(resolved_domain
                or infer_skill_domain(skill_name, keywords=keywords)),
        capabilities=capabilities,
        keywords=keywords,
        file_extensions=file_extensions,
        exclusion_scopes=exclusion_scopes,
        colloquial_examples=colloquial_examples,
    )

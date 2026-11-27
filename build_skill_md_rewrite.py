import keyword  # noqa: I001
import logging
import os
import re
import time
from collections import Counter
from collections.abc import Callable
from dataclasses import (
    dataclass,
    field,
)
from pathlib import Path
from typing import (
    Any,
    TypedDict,
)
import jwsgj.build_discover_sixdim as _sixdim
import jwsgj.build_discover_sixdim_text as _sixdim_text
from jwsgj.build_script_generation import (
    collect_scripts_info,
    generate_script_call_examples,
    generate_scripts_readme,
)
from jwsgj.build_skill_module_scan import (
    all_capabilities,
    entity_name,
    norm_entity_list,
    norm_text,
    normalize_scan_modules,
    render_capability_boundary,
    render_forced_workflow_constraints,
    render_full_module_capabilities,
    render_module_capability_table,
    render_module_responsibility_list,
    render_scan_summary,
    render_trigger_entrypoint_mapping,
    scan_skill_modules,
    select_entry_func,
)
from jwsgj.build_text_document import (
    SKILL_ACTION_VERBS,
    _restore_line_endings,
    has_section,
    locate_section,
    match_source_eol,
    normalize_str,
    normalize_str_list,
    normalize_text,
    parse_atx_heading,
    replace_atx_level,
    scan_fence_state,
    truncate_description,
    unquote_yaml_scalar,
    word_pattern,
    write_markdown_text,
)
from jwsgj.build_text_frontmatter import (
    DEFAULT_SKILL_VERSION,
    INLINE_KEYWORDS_MAX,
    _field_line_numbers,
    _merge_indented_desc_keywords,
    frontmatter_keywords,
    insert_frontmatter_description,
    parse_frontmatter_description,
    parse_frontmatter_dict,
    parse_skill_md_text,
    purify_skill_md,
    replace_frontmatter_desc_keywords,
    split_frontmatter,
    split_frontmatter_document,
    strip_yaml_control_chars,
    yaml_quote_scalar,
    yaml_scalar_line,
)
from jwsgj.build_text_scoring import (
    KEYWORD_NOISE,
    NEGATIVE_COMMANDS,
    SPOKEN_PATTERNS,
    TRIGGER_COMMANDS,
    keyword_matches,
    md_escape_cell,
    normalize_keywords,
    stem_matches,
)
from jwsgj.diag_guard_io import fs_path_text, guarded_open
from jwsgj.diag_types_normalize import int_metric
from jwsgj.diag_types_vocab import DESC_MAX, LAYER_DEGRADE_EXC
from jwsgj.log_config import log_swallowed, write_module_run
try:
    import yaml as _yaml
except ImportError:
    _yaml = None
@dataclass(frozen=True)
class _ManagedAnchorInfo:
    fields: dict[str, str] = field(default_factory=dict)
    keyword_items: tuple[tuple[str, str], ...] = ()
    description_block: str = ""
    referenced_anchors: frozenset[str] = frozenset()
_DESC_ENRICH_MAX_CHARS = DESC_MAX
_DEFAULT_SKILL_NAME = ""
_DEFAULT_KEYWORDS: list[str] | None = None
_DEFAULT_MD_LABEL = ""
_DEFAULT_MANAGED_ANCHORS: _ManagedAnchorInfo | None = None
_TRIGGER_COMMAND_ALTERNATION = "|".join(
    re.escape(_cmd) for _cmd in sorted(TRIGGER_COMMANDS, key=len, reverse=True))
_MUST_USE_PREFIX_RE = re.compile(
    r"^\s*(?:\[[ \t]*)?(?:" + _TRIGGER_COMMAND_ALTERNATION
    + r")(?![A-Za-z0-9_])(?:[ \t]*\])?[ \t]*"
    + r"(?:[:：.。，,;；]+[ \t]*)?", re.IGNORECASE)
def strip_must_use_prefix(desc: str) -> str:
    return _MUST_USE_PREFIX_RE.sub("", normalize_text(desc), count=1)
def _space_cjk_ascii_boundaries(text: str) -> str:
    return re.sub(
        r"(?<=[\u4e00-\u9fff])(?=[A-Za-z0-9_])"
        r"|(?<=[A-Za-z0-9_])(?=[\u4e00-\u9fff])", " ", text)
_GENERIC_TERM_EN: dict[str, tuple[str, ...]] = {
    "自动": ("auto",),
    "批量": ("batch",),
    "实时": ("realtime",),
    "创建": ("create",),
    "新建": ("create",),
    "生成": ("generate",),
    "构建": ("build",),
    "分析": ("analyze",),
    "诊断": ("diagnosis",),
    "检测": ("detection",),
    "检查": ("check",),
    "扫描": ("scan",),
    "审计": ("audit",),
    "验证": ("verify",),
    "校验": ("validate",),
    "测试": ("test",),
    "修复": ("fix", "repair"),
    "清理": ("cleanup",),
    "优化": ("optimize",),
    "重构": ("refactor",),
    "转换": ("convert",),
    "提取": ("extract",),
    "抽取": ("extract",),
    "抓取": ("fetch", "scrape"),
    "爬取": ("crawl",),
    "获取": ("fetch", "get"),
    "合并": ("merge",),
    "拆分": ("split",),
    "删除": ("delete",),
    "移除": ("remove",),
    "搜索": ("search",),
    "查找": ("find",),
    "查询": ("query",),
    "读取": ("read",),
    "写入": ("write",),
    "保存": ("save",),
    "导出": ("export",),
    "导入": ("import",),
    "上传": ("upload",),
    "下载": ("download",),
    "同步": ("sync",),
    "解析": ("parse",),
    "渲染": ("render",),
    "编译": ("compile",),
    "执行": ("execute",),
    "运行": ("run",),
    "处理": ("process",),
    "计算": ("calculate",),
    "统计": ("statistics",),
    "比较": ("compare",),
    "对比": ("compare",),
    "聚合": ("aggregate",),
    "排序": ("sort",),
    "过滤": ("filter",),
    "分类": ("classify",),
    "预测": ("predict",),
    "推荐": ("recommend",),
    "管理": ("manage",),
    "配置": ("config",),
    "安装": ("install",),
    "部署": ("deploy",),
    "发布": ("release",),
    "监控": ("monitor",),
    "备份": ("backup",),
    "恢复": ("restore",),
    "迁移": ("migrate",),
    "登录": ("login",),
    "认证": ("auth",),
    "授权": ("authorize",),
    "加密": ("encrypt",),
    "解密": ("decrypt",),
    "格式化": ("format",),
    "制作": ("creation",),
    "撰写": ("writing",),
    "代码": ("code",),
    "文档": ("document", "doc"),
    "表格": ("table", "spreadsheet"),
    "演示文稿": ("presentation",),
    "幻灯片": ("slide",),
    "网页": ("web page", "webpage"),
    "网站": ("website",),
    "图像": ("image",),
    "图片": ("image",),
    "视频": ("video",),
    "音频": ("audio",),
    "语音": ("speech",),
    "文本": ("text",),
    "数据": ("data",),
    "数据库": ("database",),
    "文件": ("file",),
    "报告": ("report",),
    "日志": ("log",),
    "脚本": ("script",),
    "接口": ("api",),
    "服务": ("service",),
    "技能": ("skill",),
    "项目": ("project",),
    "任务": ("task",),
    "论文": ("paper",),
    "学术": ("academic",),
    "股票": ("stock",),
    "行情": ("quote",),
    "指标": ("indicator",),
    "财务": ("finance",),
    "邮件": ("email",),
    "日程": ("calendar",),
    "会议": ("meeting",),
    "浏览器": ("browser",),
    "安全": ("security",),
    "质量": ("quality",),
    "性能": ("performance",),
    "错误": ("error",),
    "异常": ("exception",),
    "权限": ("permission",),
    "密钥": ("secret",),
    "漏洞": ("vulnerability",),
    "依赖": ("dependency",),
    "模块": ("module",),
    "函数": ("function",),
    "结构": ("structure",),
    "架构": ("architecture",),
    "设计": ("design",),
    "版本": ("version",),
    "缓存": ("cache",),
}
_GENERIC_TERM_ZH: dict[str, str] = {}
for _zh_term, _en_terms in _GENERIC_TERM_EN.items():
    for _en_term in _en_terms:
        _GENERIC_TERM_ZH.setdefault(_en_term, _zh_term)
_TRANSLATION_KEYS: tuple[str, ...] = tuple(
    sorted(_GENERIC_TERM_EN, key=len, reverse=True))
_ASCII_TERM_STOPWORDS = frozenset({
    "the", "and", "for", "with", "from", "this", "that", "your", "you",
    "use", "using", "used", "tool", "tools", "helper", "helpers", "util",
    "utils", "base", "core", "main", "init", "src", "lib", "app", "module",
    "modules", "python", "py", "skill", "skills", "demo", "example",
    "examples", "readme", "setup", "common", "shared", "index", "default",
    "simple", "quick",
})
_MODULE_TOKEN_STOPWORDS = _ASCII_TERM_STOPWORDS | frozenset({
    "get", "set", "run", "new", "all", "any", "not", "test", "tests",
    "doc", "docs", "file", "files", "data", "const", "constants", "type",
    "types", "model", "models", "manager", "handler", "handlers", "client",
})
_CATEGORY_SEPARATOR_RE = re.compile(r"[\s/、，,;；|+&]+|与|和|及")
def _ascii_tokens(text: str) -> list[str]:
    return [tok.lower() for tok in re.findall(
        r"[A-Za-z][A-Za-z0-9_+-]{1,}", normalize_text(text))
        if tok.lower() not in _ASCII_TERM_STOPWORDS]
def _split_category_terms(value: object) -> list[str]:
    text = normalize_text(value).strip()
    if not text:
        return []
    return [term for term in (
        part.strip(" -_") for part in _CATEGORY_SEPARATOR_RE.split(text))
        if len(term) > 1]
def _translate_pieces(text: str) -> list[str]:
    source = normalize_text(text).lower()
    pieces: list[str] = []
    pos = 0
    while pos < len(source):
        char = source[pos]
        if char.isascii():
            end = pos
            while end < len(source) and (
                    source[end].isascii()
                    and (source[end].isalnum() or source[end] in "_-")):
                end += 1
            token = source[pos:end].strip("_-")
            if (token and token[:1].isalpha()
                    and token not in _ASCII_TERM_STOPWORDS):
                pieces.append(token)
            pos = max(end, pos + 1)
            continue
        matched = next(
            (key for key in _TRANSLATION_KEYS if source.startswith(key, pos)),
            None)
        if matched is not None:
            pieces.append(_GENERIC_TERM_EN[matched][0])
            pos += len(matched)
            continue
        pos += 1
    return list(dict.fromkeys(pieces))
def _english_aliases(text: str) -> list[str]:
    pieces = _translate_pieces(text)
    aliases = [" ".join(pieces)] if pieces else []
    aliases.extend(pieces)
    aliases.extend(_ascii_tokens(text))
    return list(dict.fromkeys(alias for alias in aliases if alias))
def _keywords_from_description(desc_match: str, kws: set) -> None:
    for zh_term, en_terms in _GENERIC_TERM_EN.items():
        if (zh_term in desc_match
                or any(stem_matches(en, desc_match) for en in en_terms)):
            kws.add(zh_term)
            kws.add(en_terms[0])
def _keywords_from_structure(scan: dict, kws: set) -> None:
    categories: set[str] = set()
    for mod in normalize_scan_modules(scan):
        categories.update(_split_category_terms(mod.get("category")))
        for token in re.split(r"[^0-9A-Za-z]+", str(mod.get("name") or "")):
            lowered = token.lower()
            if len(lowered) > 2 and lowered not in _MODULE_TOKEN_STOPWORDS:
                kws.add(lowered)
    for category in categories:
        kws.add(category)
        kws.update(_translate_pieces(category))
_ASCII_NEGATIVE_COMMAND_RE = "|".join(
    re.escape(command).replace(r"\ ", r"\s+")
    for command in NEGATIVE_COMMANDS if command.isascii())
_CN_NEGATIVE_COMMAND_RE = "|".join(
    re.escape(command) for command in NEGATIVE_COMMANDS
    if not command.isascii())
_KEYWORD_SOURCE_CUT_RE = re.compile(
    r"(?:Keywords\s*[:：]|不应触发\s*[:：]?|"
    + _CN_NEGATIVE_COMMAND_RE + r"\s*[:：]?|\b(?:"
    + _ASCII_NEGATIVE_COMMAND_RE + r")\b)",
    re.IGNORECASE)
_NEGATIVE_SECTION_START_RE = re.compile(
    r"(?:不应触发\s*[:：]?|(?:" + _CN_NEGATIVE_COMMAND_RE
    + r")\s*[:：]?|\b(?:" + _ASCII_NEGATIVE_COMMAND_RE + r")\b)",
    re.IGNORECASE)
def _keyword_source_text(description: str) -> str:
    text = _sixdim_text.strip_injected_sections(normalize_text(description))
    match = _KEYWORD_SOURCE_CUT_RE.search(text)
    if match is not None:
        text = text[:match.start()]
    return text.strip()
def extract_functional_keywords(
        scan: dict, skill_name: str = _DEFAULT_SKILL_NAME,
        description: str = "") -> list:
    kws = set()
    desc_match = _space_cjk_ascii_boundaries(
        _keyword_source_text(description).lower())
    _keywords_from_description(desc_match, kws)
    for cap in all_capabilities(scan):
        kws.add(cap)
    _keywords_from_structure(scan, kws)
    kws.add(normalize_text(skill_name))
    kws = {k for k in kws if len(k) > 1 and k.lower() not in KEYWORD_NOISE}
    return _sort_keywords(kws)
def _sort_keywords(kws: set) -> list:
    cn_kws = sorted(k for k in kws if not k.isascii())
    en_kws = sorted(k for k in kws if k.isascii())
    return cn_kws + en_kws
_EXT_TARGET_MAP = {
    ".xlsx": "表格", ".xls": "表格", ".csv": "表格",
    ".docx": "文档", ".doc": "文档",
    ".pptx": "演示文稿", ".ppt": "演示文稿", ".pdf": "PDF",
}
_NAME_TARGET_MAP = {
    "xlsx": "表格", "excel": "表格", "csv": "表格",
    "docx": "文档", "word": "文档",
    "pptx": "演示文稿", "ppt": "演示文稿",
    "pdf": "PDF", "browser": "网页", "web": "网页",
    "paper": "论文", "stock": "股票",
}
_TARGET_ACTION_TERMS: tuple[str, ...] = tuple(sorted({
    "创建", "新建", "生成", "构建", "分析", "诊断", "检测", "检查",
    "扫描", "审计", "验证", "校验", "测试", "修复", "修补", "清理",
    "优化", "重构", "转换", "提取", "抽取", "抓取", "获取", "合并",
    "拆分", "删除", "移除", "搜索", "查找", "查询", "读取", "写入",
    "保存", "导出", "导入", "上传", "下载", "同步", "解析", "渲染",
    "编译", "执行", "运行", "处理", "计算", "统计", "比较", "对比",
    "聚合", "排序", "过滤", "分类", "预测", "推荐", "管理", "配置",
    "安装", "部署", "发布", "监控", "备份", "恢复", "迁移", "登录",
    "认证", "授权", "加密", "解密", "格式化", "制作", "撰写",
}, key=len, reverse=True))
ROLE_EXTRA_VERBS = frozenset({
    "fix", "repair", "test", "修复", "修补", "测试",
})
_TRAILING_PARTICLES = frozenset("的地得了着过之")
_TRAILING_PARTICLE_RE = re.compile(
    r"\s*[" + re.escape("".join(sorted(_TRAILING_PARTICLES))) + r"]+\s*$"
)
def _strip_trailing_action(text: str) -> str:
    result = _TRAILING_PARTICLE_RE.sub(
        "", normalize_text(text).strip()).rstrip()
    changed = True
    while changed:
        changed = False
        for term in _TARGET_ACTION_TERMS:
            if result.endswith(term) and len(result) > len(term):
                result = _TRAILING_PARTICLE_RE.sub(
                    "", result[:-len(term)]).rstrip()
                changed = True
                break
    if not result or all(ch in _TRAILING_PARTICLES for ch in result):
        return ""
    if (result in _TARGET_ACTION_TERMS
            or result.lower() in SKILL_ACTION_VERBS
            or result.lower() in ROLE_EXTRA_VERBS):
        return ""
    return result
_TARGET_LEADING_MODIFIERS: tuple[str, ...] = tuple(sorted({
    "批量", "自动", "实时", "全量", "增量", "一键", "快速", "递归",
    "统一", "并行", "离线", "在线", "定时",
}, key=len, reverse=True))
def _strip_leading_modifiers(text: str) -> str:
    result = normalize_text(text).strip()
    changed = True
    while changed:
        changed = False
        for term in (*_TARGET_ACTION_TERMS, *_TARGET_LEADING_MODIFIERS):
            if not result.startswith(term):
                continue
            remainder = result[len(term):].lstrip()
            if len(remainder) < 2:
                continue
            result = remainder
            changed = True
            break
    return result
def _target_noun(text: str) -> str:
    return _strip_leading_modifiers(_strip_trailing_action(text))
def _target_from_capabilities(caps: list) -> str | None:
    for cap in caps:
        noun = _target_noun(cap)
        if noun and noun not in _TARGET_LEADING_MODIFIERS:
            return noun
    return None
def _target_from_categories(scan: dict) -> str | None:
    counter = Counter(
        cat for cat in (
            norm_text(mod.get("category")).strip()
            for mod in normalize_scan_modules(scan))
        if cat and cat not in _GENERIC_CATEGORY_NOISE)
    for category, _count in counter.most_common():
        for term in _split_category_terms(category):
            noun = _target_noun(term)
            if noun and noun not in _TARGET_LEADING_MODIFIERS:
                return noun
    return None
def _target_from_name(name_lower: str) -> str | None:
    tokens = [token for token in re.split(
        r"[^0-9a-z\u4e00-\u9fff]+", name_lower) if token]
    token_set = set(tokens)
    for key, target in _NAME_TARGET_MAP.items():
        if key in token_set:
            return target
    for token in tokens:
        if token in _GENERIC_TERM_EN:
            return token
        zh_term = _GENERIC_TERM_ZH.get(token)
        if zh_term:
            return zh_term
    return None
def _target_from_extensions(desc_lower: str) -> str | None:
    for ext, target in _EXT_TARGET_MAP.items():
        if re.search(re.escape(ext) + r"(?![A-Za-z0-9_])", desc_lower):
            return target
    return None
def _infer_spoken_target(scan: dict, skill_name: str, existing_desc: str) -> str:
    caps = all_capabilities(scan)
    for target in (
        _target_from_name(normalize_text(skill_name).lower()),
        _target_from_capabilities(caps),
        _target_from_extensions(normalize_text(existing_desc).lower()),
        _target_from_categories(scan),
    ):
        if target:
            return target
    return "任务"
def _check_desc_coverage(all_caps: set, desc_lower: str) -> tuple:
    covered_caps = set()
    desc_match = _space_cjk_ascii_boundaries(desc_lower)
    for cap in all_caps:
        if keyword_matches(cap, desc_lower) or any(
                stem_matches(alias, desc_match)
                for alias in _english_aliases(cap)):
            covered_caps.add(cap)
    return covered_caps, all_caps - covered_caps
_SPOKEN_TEMPLATES = [
    "帮我{verb}{target}",
    "我要{verb}{target}",
    "请帮我{verb}{target}",
    "{verb}{target}",
    "能不能{verb}{target}",
    "麻烦{verb}{target}",
]
_ACTION_CUE_MAP: dict[str, tuple[str, ...]] = {
    "create": ("创建", "新建", "生成", "create", "generate"),
    "build": ("构建", "搭建", "build", "scaffold"),
    "analyze": ("分析", "诊断", "检查", "analyze", "diag", "inspect", "review"),
    "fix": ("修复", "修补", "fix", "repair"),
    "optimize": ("优化", "增强", "optimize", "enhance"),
    "check": ("验证", "校验", "搜索", "查找", "查询", "监控", "监测",
              "verify", "validate", "search", "find", "query",
              "monitor", "track"),
    "extract": ("提取", "抓取", "抽取", "获取", "extract", "fetch", "scrape"),
    "convert": ("转换", "导出", "convert", "export"),
    "merge": ("合并", "merge"),
    "split": ("拆分", "split"),
}
def _action_key_for(text: str) -> str:
    lowered = normalize_text(text).lower()
    for key, cues in _ACTION_CUE_MAP.items():
        if any(keyword_matches(cue, lowered) if cue.isascii() else cue in lowered
               for cue in cues):
            return key
    return ""
def _expand_spoken_phrases(templates: list, verbs: list, target: str) -> list:
    phrases = []
    for verb in verbs:
        for tpl in templates:
            phrase = tpl.format(verb=verb, target=target)
            if len(phrase) >= 5:
                phrases.append(phrase)
    return phrases
_FALLBACK_SPOKEN_TEMPLATES = [
    "帮我{verb}一下{target}", "我要{verb}{target}", "{verb}一下{target}",
]
_GENERIC_CATEGORY_FALLBACKS = ("核心", "引擎", "工具", "辅助", "基础设施", "通用")
def _phrase_batch_from_categories(cat_counter, target: str) -> list:
    phrases = []
    for cat, _count in cat_counter.most_common(6):
        verbs = SPOKEN_PATTERNS.get(_action_key_for(cat), [])
        templates = _SPOKEN_TEMPLATES
        if not verbs:
            if not any(marker in cat for marker in _GENERIC_CATEGORY_FALLBACKS):
                continue
            verbs = ["操作"]
            templates = _FALLBACK_SPOKEN_TEMPLATES
        phrases.extend(_expand_spoken_phrases(templates, verbs[:3], target))
    return phrases
_META_CAPS = frozenset({"构建生成", "测试", "类型定义", "工具函数", "执行"})
_CAP_PHRASE_ROUTES: tuple[tuple[str, str], ...] = (
    ("诊断|检查", "检查一下{target}的{cap}"),
    ("修复|清理", "给{target}做一下{cap}"),
    ("优化|增强", "优化一下{target}的{cap}"),
    ("审计|安全", "对{target}做{cap}"),
    ("验证|交叉", "验证一下{target}的{cap}结果"),
)
_DEFAULT_CAP_PHRASES = ("帮我做{cap}", "执行{cap}")
def _route_cap_phrase(cap: str, target: str) -> list[str]:
    cap_lower = cap.lower()
    for cues, template in _CAP_PHRASE_ROUTES:
        if any(cue in cap_lower for cue in cues.split("|")):
            return [template.format(target=target, cap=cap)]
    return [template.format(cap=cap) for template in _DEFAULT_CAP_PHRASES]
def _phrase_batch_from_caps(all_caps: set, target: str) -> list:
    phrases: list[str] = []
    for cap in sorted(all_caps - _META_CAPS):
        phrases.extend(_route_cap_phrase(cap, target))
    return phrases
def _build_colloquial_phrases(
    scan: dict, skill_name: str, desc_clean: str,
    cat_counter, all_caps: set
) -> list:
    target = _infer_spoken_target(scan, skill_name, desc_clean)
    colloquial_phrases = (
        _phrase_batch_from_categories(cat_counter, target)
        + _phrase_batch_from_caps(all_caps, target)
    )
    unique_phrases = list(dict.fromkeys(colloquial_phrases))
    if unique_phrases:
        unique_phrases.append(
            "触发示例: " + " | ".join(unique_phrases[:8]) + "。"
        )
    return unique_phrases
def _append_en_keyword(target: list[str], keyword: str | None,
                       desc_lower: str) -> None:
    if keyword and not keyword_matches(keyword, desc_lower):
        target.append(keyword)
def _build_en_keywords(cat_counter, all_caps: set, desc_lower: str) -> list:
    en_kws: list[str] = []
    for cat, _count in cat_counter.most_common():
        _append_en_keyword(
            en_kws, " ".join(_translate_pieces(cat)) or None, desc_lower)
    for cap in sorted(all_caps):
        _append_en_keyword(
            en_kws, " ".join(_translate_pieces(cap)) or None, desc_lower)
    return list(dict.fromkeys(en_kws))
def _build_exclusions(desc_lower: str) -> list:
    if ("不适用" in desc_lower or "不应触发" in desc_lower
            or any(keyword_matches(command, desc_lower)
                   for command in NEGATIVE_COMMANDS)):
        return []
    return ["与本技能明示能力边界外的通用任务"]
_GENERIC_CATEGORY_NOISE = frozenset({
    "通用", "未知", "未知分类", "未分类", "其他", "-",
})
def _aggregate_scan_facets(scan: dict) -> tuple:
    all_caps = set(all_capabilities(scan))
    cat_counter = Counter()
    for mod in normalize_scan_modules(scan):
        raw_cat = mod.get("category")
        cat = norm_text(raw_cat).strip() if isinstance(raw_cat, str) else ""
        if cat and cat not in _GENERIC_CATEGORY_NOISE:
            cat_counter[cat] += 1
    return all_caps, cat_counter
_ENRICHMENT_SECTION_LABELS = ("核心能力域", "触发示例", "Keywords", "不适用于")
def _section_label_match(text: str, label: str) -> re.Match[str] | None:
    if not label:
        return None
    pattern = (r"(?:^|(?<=[\s。；;，,、：:]))"
               + re.escape(label) + r"\s*[:：]")
    return re.search(pattern, text)
def _has_section_label(text: str, label: str) -> bool:
    return _section_label_match(text, label) is not None
def _merge_existing_domain_summary(desc_clean: str, part: str) -> str:
    match = _section_label_match(desc_clean, "核心能力域")
    if match is None:
        return desc_clean
    payload = part.split(":", 1)[1].strip().rstrip("。").rstrip()
    if not payload or payload in desc_clean:
        return desc_clean
    remainder = desc_clean[match.end():].lstrip()
    head = desc_clean[:match.end()]
    if not remainder:
        return head + " " + payload + "。"
    if remainder.startswith(("。", ".")):
        return head + " " + payload + remainder
    return head + " " + payload + "；" + remainder
_ENRICHMENT_LABEL_PRIORITY: tuple[str, ...] = (
    "不适用于", "核心能力域", "Keywords", "触发示例")
def _enrichment_label(part: str) -> str:
    return part.split(":", 1)[0].strip()
def _join_enrichment(desc_clean: str, parts: list[str]) -> str:
    base = desc_clean.rstrip().rstrip(".。") if desc_clean else ""
    if not parts:
        return base or desc_clean
    enrichment_text = " ".join(parts)
    if not base:
        return enrichment_text
    separator = (" " if base.endswith(("。", "！", "!", "？", "?", "；", ";"))
                 else "。 ")
    return base + separator + enrichment_text
def _select_enrichment_parts(desc_clean: str, missing_parts: list) -> list:
    def rank(part: str) -> int:
        label = _enrichment_label(part)
        return (_ENRICHMENT_LABEL_PRIORITY.index(label)
                if label in _ENRICHMENT_LABEL_PRIORITY
                else len(_ENRICHMENT_LABEL_PRIORITY))
    kept: list[str] = []
    kept_indices: set[int] = set()
    dropped: list[str] = []
    candidates = sorted(
        enumerate(missing_parts), key=lambda item: (rank(item[1]), item[0]))
    for index, part in candidates:
        if len(_join_enrichment(desc_clean, [*kept, part])) <= _DESC_ENRICH_MAX_CHARS:
            kept.append(part)
            kept_indices.add(index)
            continue
        dropped.append(_enrichment_label(part))
    if dropped:
        _log.warning(
            "描述富化超出 %d 字符硬上限，跳过片段: %s",
            _DESC_ENRICH_MAX_CHARS, ", ".join(dict.fromkeys(dropped)))
    return [part for index, part in enumerate(missing_parts)
            if index in kept_indices]
def _clamp_description_preserving_exclusions(description: str) -> str:
    description = normalize_text(description)
    if len(description) <= DESC_MAX:
        return description
    negative_start = _NEGATIVE_SECTION_START_RE.search(description)
    if negative_start is not None:
        raw_suffix = description[negative_start.start():].strip()
        if not raw_suffix.endswith(("。", ".", "!", "?", "！", "？")):
            raw_suffix += "。"
        suffix = " " + raw_suffix
    else:
        rules = _sixdim_text._extract_negative_rules(description)
        rule_text = ("; ".join(rules[:3])
                     or "与本技能明示能力边界外的通用任务")
        suffix = f" NOT FOR: {rule_text}."
    if len(suffix) >= DESC_MAX:
        suffix = " NOT FOR: 与本技能明示能力边界外的通用任务。"
    positive = description
    source_cut = _KEYWORD_SOURCE_CUT_RE.search(description)
    if source_cut is not None:
        positive = description[:source_cut.start()]
    base = truncate_description(
        positive.strip(), DESC_MAX - len(suffix), "。")
    return (base + suffix).strip()
def _merge_enrichment_parts(desc_clean: str, enrichment_parts: list) -> str:
    missing_parts = []
    for part in enrichment_parts:
        if not part or part in desc_clean:
            continue
        label = _enrichment_label(part)
        if (label in _ENRICHMENT_SECTION_LABELS
                and _has_section_label(desc_clean, label)):
            if label == "核心能力域":
                desc_clean = _merge_existing_domain_summary(desc_clean, part)
            continue
        missing_parts.append(part)
    if not missing_parts:
        return (desc_clean if len(desc_clean) <= _DESC_ENRICH_MAX_CHARS
                else _clamp_description_preserving_exclusions(desc_clean))
    kept_parts = _select_enrichment_parts(desc_clean, missing_parts)
    if not kept_parts:
        return (desc_clean if len(desc_clean) <= _DESC_ENRICH_MAX_CHARS
                else _clamp_description_preserving_exclusions(desc_clean))
    merged = _join_enrichment(desc_clean, kept_parts)
    if len(merged) <= _DESC_ENRICH_MAX_CHARS:
        return merged
    return _clamp_description_preserving_exclusions(merged)
def enrich_description_from_scan(
    scan: dict, existing_desc: str, skill_name: str
) -> str:
    existing_desc = normalize_text(existing_desc)
    skill_name = normalize_text(skill_name)
    if not existing_desc:
        existing_desc = f"{skill_name} 技能" if skill_name else "本技能"
    desc_clean = strip_must_use_prefix(existing_desc)
    desc_lower = desc_clean.lower()
    all_caps, cat_counter = _aggregate_scan_facets(scan)
    negative_text = " ".join(
        _sixdim_text._extract_negative_rules(desc_clean)).lower()
    excluded_caps = set()
    excluded_categories = set()
    if negative_text:
        excluded_caps, _unused = _check_desc_coverage(all_caps, negative_text)
        excluded_categories, _unused = _check_desc_coverage(
            set(cat_counter), negative_text)
    generation_caps = all_caps - excluded_caps
    generation_categories = Counter({
        category: count for category, count in cat_counter.items()
        if category not in excluded_categories})
    _covered_caps, missing_caps = _check_desc_coverage(all_caps, desc_lower)
    if not missing_caps and len(all_caps) >= 10:
        return _merge_enrichment_parts(
            desc_clean, _exclusion_part(desc_lower))
    enrichment_parts = (
        _domain_summary_part(scan, desc_clean, cat_counter, missing_caps)
        + _colloquial_parts(
            scan, skill_name, desc_clean, generation_categories, generation_caps)
        + _keyword_part(generation_categories, generation_caps, desc_lower)
        + _exclusion_part(desc_lower)
    )
    return _merge_enrichment_parts(desc_clean, enrichment_parts)
def _caps_by_category(scan: dict) -> dict[str, list[str]]:
    grouped: dict[str, list[str]] = {}
    for mod in normalize_scan_modules(scan):
        category = norm_text(mod.get("category")).strip()
        if not category or category == "-":
            continue
        raw_caps = mod.get("key_capabilities")
        caps = grouped.setdefault(category, [])
        for cap in (normalize_str_list(raw_caps)
                    if isinstance(raw_caps, list) else []):
            if cap not in caps:
                caps.append(cap)
    return grouped
def _domain_summary_part(scan: dict, desc_clean: str, cat_counter,
                         missing_caps: set) -> list:
    if len(desc_clean) >= 100 and not missing_caps:
        return []
    caps_by_cat = _caps_by_category(scan)
    summaries = []
    for cat, _count in cat_counter.most_common(6):
        caps = caps_by_cat.get(cat, [])
        if not cat or cat == "-":
            continue
        shown = [cap for cap in dict.fromkeys(caps)
                 if (cap and cap != cat and cap in missing_caps
                     and cap not in desc_clean)][:3]
        if (not shown and (cat in desc_clean
                           or any(cap in desc_clean for cap in caps))):
            continue
        summaries.append(cat if not shown else f"{cat}（{'、'.join(shown)}）")
    if not summaries:
        return []
    return ["核心能力域: " + "；".join(summaries) + "。"]
def _colloquial_parts(scan: dict, skill_name: str, desc_clean: str,
                      cat_counter, all_caps: set) -> list:
    return [
        frag for frag in _build_colloquial_phrases(
            scan, skill_name, desc_clean, cat_counter, all_caps)
        if frag.startswith("触发示例") and frag[:50] not in desc_clean
    ]
def _keyword_part(cat_counter, all_caps: set, desc_lower: str) -> list:
    en_kws = _build_en_keywords(cat_counter, all_caps, desc_lower)
    if not en_kws:
        return []
    return ["Keywords: " + ", ".join(en_kws[:15]) + "."]
def _exclusion_part(desc_lower: str) -> list:
    exclusions = _build_exclusions(desc_lower)
    if not exclusions:
        return []
    return ["不适用于: " + "；".join(exclusions[:3]) + "。"]
__all__ = [
    'DOCX_TEMPLATE',
    'GENERIC_TEMPLATE',
    'META_TEMPLATE',
    'PDF_TEMPLATE',
    'PPTX_TEMPLATE',
    'ROLE_EXTRA_VERBS',
    'ROLE_MAPPING',
    'SCENARIO_MAPPING',
    'TEMPLATES',
    'XLSX_TEMPLATE',
    'RoleScenarioReport',
    'RoleScenarioTag',
    'RoleScenarioTagger',
    'append_role_scenario_section',
    'enrich_description_from_scan',
    'existing_skill_category',
    'extract_functional_keywords',
    'generate_role_scenario_section',
    'inject_script_usage_guide',
    'merge_optimized_frontmatter',
    'merged_frontmatter_preview',
    'normalize_guide_as_section',
    'read_skill_md_text',
    'rebuild_skill_md',
    'replace_or_insert_section',
    'strip_must_use_prefix',
    'update_skill_md',
    'write_optimized_frontmatter',
    'write_skill_md',
    'write_skill_md_text',
]
_log = logging.getLogger(__name__)
def _norm_scalar(value: Any) -> str:
    return normalize_text(value).strip()
def _flatten_description_line(text: Any) -> str:
    flat = normalize_text(text)
    for separator in ("\r\n", "\r", "\n", "\t", "\u0085", "\u2028", "\u2029"):
        flat = flat.replace(separator, " ")
    flat = re.sub(r" {2,}", " ", flat)
    return strip_yaml_control_chars(flat).strip()
def _clamp_template_description(skill_md: str) -> str:
    lines = skill_md.split("\n")
    for index, line in enumerate(lines[:-1]):
        if line.strip() != "description: |":
            continue
        description_line = lines[index + 1]
        if not description_line.startswith("  "):
            return skill_md
        raw = description_line[2:]
        clamped = _clamp_description_preserving_exclusions(raw)
        if clamped == raw:
            return skill_md
        lines[index + 1] = "  " + clamped
        return "\n".join(lines)
    return skill_md
GENERIC_TEMPLATE = """---
name: {skill_name}
description: |
  [MUST USE] {description}. 当用户要求与 {display_name} 相关的操作时使用此技能。NOT FOR: 与此技能无关的通用任务。
version: "{version}"
keywords: []
---

# {display_name}

{description}

## Agent 决策指引

Agent 在以下情况应加载本技能：
1. 用户意图与 {display_name} 核心能力匹配
2. 用户提及本技能的触发关键词
3. 任务需要本技能提供的特定功能（详见下方"模块能力全景"和"模块能力详解"）

加载后，Agent 应：
1. 阅读"模块能力全景"快速定位目标模块
2. 在"模块能力详解"中查找对应模块的「Agent 调用时机」和公开 API
3. 优先通过 Python API 调用，需要 CLI 操作时参考"脚本调用指引"

## 触发条件

### 应当触发（Agent 必须加载本技能）
- 用户提及以下关键词时自动触发：{{trigger_keywords}}
- 用户要求执行 {display_name} 相关操作
- 用户表达 {display_name} 领域的明确意图

### 不应触发
- 与此技能领域无关的通用任务
- 完全不同的技术领域或文件格式

## 快速入门

```python
{quickstart_import}

# 根据具体任务选择对应入口函数
# 详见下方"模块能力详解"章节，每个模块均标注「Agent 调用时机」
```

## 典型场景

本技能适用于以下典型场景（AI Agent 应在匹配时加载本技能）：

- 用户需要 {display_name} 的标准操作流程
- 用户请求与 {description} 相关的处理
- 需要对 {category} 类型数据进行的自动化处理
- 用户需要批量处理或自动化执行 {display_name} 相关任务

{{module_responsibility_list}}

## 模块能力全景

{{module_capability_table}}

## 模块能力详解

以下列出技能内所有 .py 文件的完整能力描述，包括每个模块的公开函数签名、公开类及方法、导出列表和「Agent 调用时机」。

AI Agent 可根据以下信息精确判断：
1. 是否应调用本技能 — 检查模块能力是否匹配用户意图
2. 应调用哪个具体模块 — 根据模块分类和「Agent 调用时机」定位
3. 应调用哪个函数/类 — 查看公开 API 列表和参数签名

每个模块包含「Agent 调用时机」说明，明确在什么场景下应加载该模块。

{{module_full_capabilities}}

{{trigger_entrypoint_mapping}}

{{forced_workflow_constraints}}

## 脚本调用指引

本技能 `scripts/` 目录下脚本的实际参数以各脚本源码或 `--help` 输出为准；未声明的标志不得假定可用。

```bash
# 先查看目标脚本真实支持的参数（脚本应实现 help）
python scripts/<script>.py --help
```

**脚本调用原则**：
- 仅使用脚本实际声明的参数；未声明标志不得假定可用
- 脚本失败时检查退出码、标准错误及其真实结构化输出契约
- 是否需要预览、静默或强制模式，以目标脚本实际实现为准

## 脚本 vs API 决策指引

| 场景 | 推荐方式 | 原因 |
|------|---------|------|
| 需要结构化数据继续处理 | Python API | 直接获取返回值，无解析开销 |
| 需要进程隔离执行 | CLI 脚本（脚本支持时） | 进程隔离，错误不影响主流程 |
| 首次不确定结果 | CLI 脚本的预览模式（脚本支持时） | 预览模式不执行实际操作 |
| 批量/自动化任务 | CLI 脚本 + 管道（脚本支持时） | 支持管道和重定向 |

## 设计原则

1. **可发现性优先**: description 含 `[MUST USE]` 强制触发词和场景关键词
2. **规避问题为先**: 创建时预检（命名/结构/安全），从源头规避常见问题
3. **脚本友好**: 仅使用脚本真实声明的 CLI 标志；未声明标志不得假定可用
4. **真实契约**: 输出结构、返回状态与错误处理以公开 API 和 CLI 的真实实现为准
5. **副作用透明**: 是否可重复执行、是否支持预览或强制模式以实际能力为准，调用前确认副作用
6. **依赖明确**: 运行依赖与环境要求以项目声明和实际入口为准，不默认承诺自动自检
7. **模块能力透明**: 所有 .py 文件公开 API 完整暴露，AI Agent 可精确定位
"""
_TEMPLATE_DROP_LINES = frozenset({
    "{{module_responsibility_list}}\n",
    "{{trigger_entrypoint_mapping}}\n",
    "{{forced_workflow_constraints}}\n",
})
_DOMAIN_TRIGGER_ANCHOR = "当用户要求与 {display_name} 相关的操作时"
_TEMPLATE_DOMAIN_PROFILES: dict[str, tuple[str, str, str]] = {
    "xlsx": ("xlsx", " Excel 表格", '["excel", "spreadsheet", "xlsx", "表格", "workbook", "sheet"]'),
    "docx": ("docx", " Word 文档", '["word", "document", "docx", "文档", "文字处理"]'),
    "pptx": ("pptx", " PPT 演示文稿", '["powerpoint", "presentation", "pptx", "演示", "幻灯片", "ppt"]'),
    "pdf": ("pdf", " PDF 文件", '["pdf", "document", "文档", "portable document"]'),
    "skill": ("skill-management", "技能管理", '["skill", "技能", "builder", "构建", "管理"]'),
}
def _quickstart_import_line(skill_name: str,
                            module_scan: dict | None) -> str:
    candidates: list[str] = []
    if isinstance(module_scan, dict):
        import_root = module_scan.get("import_root")
        if isinstance(import_root, str):
            candidates.append(import_root)
        for module in normalize_scan_modules(module_scan):
            import_name = module.get("import_name")
            if isinstance(import_name, str):
                candidates.append(import_name)
    for candidate in candidates:
        parts = candidate.split(".")
        if (candidate and all(part.isidentifier() and not keyword.iskeyword(part)
                              for part in parts)):
            return f"import {candidate}"
    return (f'# 未确认 {normalize_text(skill_name)!r} 的可导入包，'
            '请查下方「模块能力详解」或项目源码定位真实入口')
def _render_domain_template(category: str, domain_phrase: str, keywords_json: str) -> str:
    out: list[str] = []
    for raw_ln in GENERIC_TEMPLATE.splitlines(keepends=True):
        if raw_ln in _TEMPLATE_DROP_LINES:
            if out and not out[-1].strip():
                out.pop()
            continue
        out.append(_transform_template_line(
            raw_ln, category, domain_phrase, keywords_json))
    return "".join(out)
def _transform_template_line(line: str, category: str,
                             domain_phrase: str, keywords_json: str) -> str:
    if _DOMAIN_TRIGGER_ANCHOR in line:
        line = line.replace(
            _DOMAIN_TRIGGER_ANCHOR, f"当用户要求与{domain_phrase}相关的操作时")
    if line != "keywords: []\n":
        return line
    return f'category: "{category}"\nkeywords: {keywords_json}\n'
XLSX_TEMPLATE = _render_domain_template(*_TEMPLATE_DOMAIN_PROFILES["xlsx"])
DOCX_TEMPLATE = _render_domain_template(*_TEMPLATE_DOMAIN_PROFILES["docx"])
PPTX_TEMPLATE = _render_domain_template(*_TEMPLATE_DOMAIN_PROFILES["pptx"])
PDF_TEMPLATE = _render_domain_template(*_TEMPLATE_DOMAIN_PROFILES["pdf"])
META_TEMPLATE = _render_domain_template(*_TEMPLATE_DOMAIN_PROFILES["skill"])
TEMPLATES = {
    "xlsx": XLSX_TEMPLATE,
    "docx": DOCX_TEMPLATE,
    "pptx": PPTX_TEMPLATE,
    "pdf": PDF_TEMPLATE,
    "generic": GENERIC_TEMPLATE,
    "skill": META_TEMPLATE,
}
_TEMPLATE_CATEGORY_ALIASES = {
    "skill-management": "skill",
    "skillops": "skill",
}
def _module_entity_names(mod: dict) -> set[str]:
    names = {entity_name(mod), *map(entity_name, norm_entity_list(mod.get("classes")))}
    names.discard("")
    for entity in norm_entity_list(mod.get("functions")):
        name = entity_name(entity)
        if not name:
            continue
        names.add(name)
        names.update(seg.lower() for seg in name.replace("_", " ").split()
                     if len(seg) > 2)
    return names
def _keyword_is_reportable(term: str) -> bool:
    if not term:
        return False
    return len(term) > 2 if term.isascii() else len(term) > 1
def _extract_trigger_keywords(scan_result: dict, existing_keywords: list) -> str:
    raw = list(normalize_keywords(existing_keywords))
    kws = set(raw)
    for mod in normalize_scan_modules(scan_result):
        kws.update(_module_entity_names(mod))
    kws.update(all_capabilities(scan_result))
    kws = {k for k in kws
           if _keyword_is_reportable(k) and k.lower() not in KEYWORD_NOISE}
    return ", ".join(sorted(kws)[:20]) if kws else "自动推断"
_MAX_ENTRY_PER_DOMAIN = 3
_MAX_MODULE_PER_DOMAIN = 6
def _domain_bucket(module_scan: dict) -> dict[str, list]:
    buckets: dict[str, list] = {}
    for mod in normalize_scan_modules(module_scan):
        cat = norm_text(mod.get("category")).strip() or "-"
        buckets.setdefault(cat, []).append(mod)
    return buckets
def _domain_entry_names(mods: list) -> str:
    names = []
    for mod in mods:
        entry = select_entry_func(
            norm_entity_list(mod.get("functions")), norm_text(mod.get("path")))
        if entry and entry not in names:
            names.append(entry)
    return " / ".join(names[:_MAX_ENTRY_PER_DOMAIN]) or "-"
def _domain_module_refs(mods: list) -> str:
    paths = [norm_text(mod.get("path")) for mod in mods]
    shown = [f"`{md_escape_cell(p)}`" for p in paths[:_MAX_MODULE_PER_DOMAIN] if p]
    if len(paths) > _MAX_MODULE_PER_DOMAIN:
        shown.append(f"等 {len(paths)} 个")
    return " / ".join(shown) or "-"
def _domain_overview_table(module_scan: dict) -> str:
    rows = ["| 域 | 模块数 | 入口函数 | 代表模块 |",
            "|----|--------|---------|---------|"]
    for cat, mods in _domain_bucket(module_scan).items():
        rows.append(f"| {md_escape_cell(cat)} | {len(mods)} "
                    f"| {md_escape_cell(_domain_entry_names(mods))} "
                    f"| {_domain_module_refs(mods)} |")
    return "\n".join(rows)
def _golden_sections_block(name: str, pattern: str, module_scan: dict) -> str:
    return "\n".join([
        render_module_responsibility_list(module_scan),
        "",
        "## 模块能力全景",
        "",
        render_module_capability_table(module_scan),
        "",
        "## 模块能力详解",
        "",
        "> 每个模块的完整函数签名、类方法与调用示例请查阅对应 .py 源文件 docstring；",
        "> 可通过「触发场景与入口函数映射表」定位入口函数。",
        "",
        render_full_module_capabilities(module_scan),
        "",
        render_trigger_entrypoint_mapping(module_scan, name),
        "",
        render_forced_workflow_constraints(name, pattern),
    ]).strip("\n")
def _domain_overview_section(module_scan: dict) -> str:
    return ("## 域总览\n\n"
            "> 按模块分类（域）汇总模块数、入口函数与代表模块；"
            "完整文件清单见「全部 .py 文件清单」。\n\n"
            + _domain_overview_table(module_scan))
def _inject_golden_module_sections(
        skill_md: str,
        name: str,
        pattern: str,
        module_scan: dict) -> str:
    block = _golden_sections_block(name, pattern, module_scan)
    overview = _domain_overview_section(module_scan)
    generated_headers = (
        "## 全部 .py 文件清单",
        "## 模块能力全景",
        "## 模块能力详解",
        f"## {_TRIGGER_MAP_TITLE}",
        "## 强制工作流与约束",
    )
    for header in generated_headers:
        while (stale_span := locate_section(skill_md, header)) is not None:
            start, end = stale_span
            skill_md = skill_md[:start] + skill_md[end:]
    span = locate_section(skill_md, "## 域总览")
    if span is None:
        anchor = locate_section(skill_md, "## 典型应用场景")
        if anchor is None:
            return f"{skill_md.rstrip()}\n\n{overview}\n\n{block}\n"
        head = skill_md[:anchor[0]].rstrip()
        prefix = f"{head}\n\n" if head else ""
        return (f"{prefix}{overview}\n\n{block}\n\n"
                f"{skill_md[anchor[0]:]}")
    start_idx, end_idx = span
    head = f"{skill_md[:start_idx]}{overview}\n\n"
    rest = skill_md[end_idx:]
    tail = locate_section(rest, "## 典型应用场景")
    if tail is None:
        body = rest.rstrip("\n")
        separator = "\n\n" if body else ""
        return f"{head}{body}{separator}{block}\n"
    before = rest[:tail[0]].rstrip("\n")
    prefix = f"{before}\n\n" if before else ""
    return f"{head}{prefix}{block}\n\n{rest[tail[0]:]}"
@dataclass(frozen=True)
class _SkeletonInputs:
    name: str
    display_name: str
    category: str
    pattern: str
    description: str
    keywords: list
    quickstart_import: str
def _generate_skill_md_skeleton(inputs: _SkeletonInputs) -> tuple[str, bool]:
    category_key = _norm_scalar(inputs.category).lower()
    display_category = _sixdim.canonical_skill_category(category_key)
    template_key = _TEMPLATE_CATEGORY_ALIASES.get(display_category, display_category)
    try:
        skill_md = _sixdim.generate_skill_md_template(
            skill_name=inputs.name, description=inputs.description,
            skill_type=category_key, keywords=inputs.keywords,
        )
        return skill_md, True
    except Exception as e:  # noqa: BLE001 — 模板生成失败回退内置模板，降级不阻断创建
        _log.warning(
            "_generate_skill_md_skeleton: 模板生成失败，回退内置模板 %s: %s",
            category_key, e)
        template = TEMPLATES.get(template_key, GENERIC_TEMPLATE)
        skill_md = template.format_map({
            "version": DEFAULT_SKILL_VERSION,
            "skill_name": inputs.name,
            "description": inputs.description,
            "display_name": inputs.display_name,
            "category": display_category,
            "pattern": inputs.pattern,
            "quickstart_import": inputs.quickstart_import,
        })
        skill_md = _clamp_template_description(skill_md)
    if inputs.keywords:
        skill_md = replace_frontmatter_desc_keywords(
            skill_md, None, inputs.keywords)
    return skill_md, False
_EMPTY_MODULE_SCAN_NOTE = "暂无模块扫描结果（技能创建后自动扫描并填充）。\n\n"
def _inject_placeholders(
        skill_md: str, resolvers: dict[str, Callable[[], str]]) -> str:
    for placeholder, resolve in resolvers.items():
        if placeholder in skill_md:
            skill_md = skill_md.replace(placeholder, resolve())
    return skill_md
def _inject_fallback_module_sections(
        skill_md: str, name: str, pattern: str,
        module_scan: dict, keywords: list) -> str:
    return _inject_placeholders(skill_md, {
        "{module_capability_table}":
            lambda: render_module_capability_table(module_scan),
        "{module_full_capabilities}":
            lambda: render_full_module_capabilities(module_scan),
        "{trigger_keywords}":
            lambda: _extract_trigger_keywords(module_scan, keywords),
        "{module_responsibility_list}":
            lambda: render_module_responsibility_list(module_scan),
        "{trigger_entrypoint_mapping}":
            lambda: render_trigger_entrypoint_mapping(module_scan, name),
        "{forced_workflow_constraints}":
            lambda: render_forced_workflow_constraints(name, pattern),
    })
def _inject_empty_module_sections(
        skill_md: str, name: str, pattern: str, keywords: list) -> str:
    return _inject_placeholders(skill_md, {
        "{module_capability_table}":
            lambda: "暂无模块（技能创建后自动扫描）\n\n",
        "{module_full_capabilities}":
            lambda: "暂无模块详情（技能创建后自动扫描）\n\n",
        "{trigger_keywords}":
            lambda: ", ".join(keywords[:5]) if keywords else "自动推断",
        "{module_responsibility_list}":
            lambda: _EMPTY_MODULE_SCAN_NOTE,
        "{trigger_entrypoint_mapping}":
            lambda: _EMPTY_MODULE_SCAN_NOTE,
        "{forced_workflow_constraints}":
            lambda: render_forced_workflow_constraints(name, pattern),
    })
def _resolve_module_scan(target_dir: str, module_scan: dict | None) -> dict | None:
    if module_scan is not None:
        return module_scan if isinstance(module_scan, dict) else {}
    try:
        return scan_skill_modules(target_dir)
    except Exception as e:  # noqa: BLE001 — 扫描失败降级 None，能力矩阵缺省继续
        _log.warning("_resolve_module_scan: 模块扫描失败 %s: %s",
                     target_dir, e)
        return None
def _inject_module_sections(
        skill_md: str, name: str, pattern: str, keywords: list,
        module_scan: dict | None, golden: bool) -> str:
    if normalize_scan_modules(module_scan or {}):
        if golden:
            return _inject_golden_module_sections(
                skill_md, name, pattern, module_scan)
        return _inject_fallback_module_sections(
            skill_md, name, pattern, module_scan, keywords)
    return _inject_empty_module_sections(skill_md, name, pattern, keywords)
def write_skill_md(
        target_dir: str,
        name: str,
        display_name: str,
        category: str,
        pattern: str,
        description: str,
        keywords: list,
        module_scan: dict | None = None) -> str:
    dir_text = fs_path_text(target_dir)
    if not dir_text:
        raise ValueError(
            f"write_skill_md: target_dir 为空或类型非法: {target_dir!r}")
    target_dir = dir_text
    keywords = _merge_keywords(normalize_keywords(keywords))
    _t0 = time.monotonic()
    name = _norm_scalar(name)
    display_name = _norm_scalar(display_name)
    category = _norm_scalar(category).lower()
    pattern = _norm_scalar(pattern)
    description = _flatten_description_line(description)
    module_scan = _resolve_module_scan(target_dir, module_scan)
    skill_md, golden = _generate_skill_md_skeleton(_SkeletonInputs(
        name=name, display_name=display_name, category=category,
        pattern=pattern, description=description, keywords=keywords,
        quickstart_import=_quickstart_import_line(name, module_scan)))
    skill_md = _inject_module_sections(
        skill_md, name, pattern, keywords, module_scan, golden)
    skill_md_path = Path(target_dir) / "SKILL.md"
    write_skill_md_text(skill_md_path, skill_md.rstrip("\n") + "\n")
    write_module_run(
        "build_skill_md_rewrite", "write_skill_md",
        duration_ms=(time.monotonic() - _t0) * 1000.0,
        skill=name, golden=golden, bytes=len(skill_md.encode("utf-8")),
        modules=len(normalize_scan_modules(module_scan or {})))
    return str(skill_md_path)
_KEYWORD_NOUNS: tuple[str, ...] = (
    "skill", "doc", "document", "file", "data", "code", "report",
    "table", "chart", "image", "pdf", "excel", "word", "ppt", "web",
    "page", "site", "api", "script", "test", "bug", "issue", "task",
    "project",
)
def _word_alternation(words) -> re.Pattern[str]:
    return re.compile("|".join(word_pattern(word) for word in words))
_ROLE_VERB_RE = _word_alternation(sorted(
    SKILL_ACTION_VERBS | ROLE_EXTRA_VERBS,
    key=lambda word: (-len(word), word),
))
_ROLE_NOUN_RE = _word_alternation(_KEYWORD_NOUNS)
_INDICATOR_CONFIDENCE_RATIO = 0.3
_MAX_FOCUSED_ROLES = 3
_MAX_MIND_EXPRESSIONS = 6
_MAX_PAIR_DIMENSION = 2
class _CategoryInfo(TypedDict):
    zh: str
    indicators: list[str]
_TAG_ISSUE_NO_ROLE = "未能推断出适用岗位，建议 description 中包含目标用户角色关键词"
_TAG_ISSUE_NO_SCENARIO = "未能推断出典型场景，建议 description 中包含具体使用场景描述"
_TAG_SUGGESTION_TOO_MANY_ROLES = "适用岗位过多可能导致目标用户不明确，建议聚焦到1-2个核心岗位"
_TAG_SUGGESTION_ROLE_SECTION = "在 SKILL.md 中添加 '适用岗位' 和 '典型场景' 区块，帮助用户从角色视角发现技能"
_TAG_SUGGESTION_TRIGGER = "在 trigger 条件中嵌入岗位和场景关键词，提升角色驱动的匹配率"
_ROLE_SCENARIO_SECTION_TITLE = "## 适用岗位与典型场景"
_SCRIPT_GUIDE_SECTION_TITLE = "## 脚本调用指引"
_TRIGGER_MAP_TITLE = "触发场景与入口函数映射表"
_SECTION_HINT_LINES = (
    "> 提示: 为了让 Agent 更容易从角色视角匹配此技能，",
    "> 建议在 description 中嵌入岗位和场景关键词。",
    "",
)
def _first_two_or(items: list, default: str) -> list:
    return items[:_MAX_PAIR_DIMENSION] or [default]
ROLE_MAPPING: dict[str, _CategoryInfo] = {
    "developer": {
        "zh": "开发者",
        "indicators": ["代码", "code", "编程", "脚本", "python", "开发", "调试", "debug", "实现", "重构"],
    },
    "architect": {
        "zh": "架构师",
        "indicators": ["架构", "设计", "审计", "审查", "评估", "选型", "架构师", "architect"],
    },
    "tester": {
        "zh": "测试工程师",
        "indicators": ["测试", "验证", "回归", "覆盖", "pytest", "test", "verify", "validate"],
    },
    "devops": {
        "zh": "运维工程师",
        "indicators": ["部署", "监控", "清理", "预检", "deploy", "monitor", "运维", "devops"],
    },
    "security": {
        "zh": "安全工程师",
        "indicators": ["安全", "漏洞", "污点", "权限", "密钥", "security", "audit", "vulnerability"],
    },
    "data_analyst": {
        "zh": "数据分析师",
        "indicators": ["数据", "统计", "分析", "图表", "可视化", "data", "analyze", "chart"],
    },
}
SCENARIO_MAPPING: dict[str, _CategoryInfo] = {
    "code_review": {
        "zh": "代码审查",
        "indicators": ["审查", "检查", "诊断", "review", "audit", "inspect", "check"],
    },
    "skill_creation": {
        "zh": "创建与生成",
        "indicators": ["创建", "新建", "生成", "创建技能", "create", "build", "skill"],
    },
    "refactoring": {
        "zh": "代码重构",
        "indicators": ["重构", "拆分", "合并", "迁移", "refactor", "split", "merge"],
    },
    "security_audit": {
        "zh": "安全审计",
        "indicators": ["安全审计", "漏洞扫描", "污点追踪", "security audit", "vulnerability"],
    },
    "quality_assessment": {
        "zh": "质量评估",
        "indicators": ["质量", "评分", "健康", "评估", "quality", "score", "health"],
    },
    "cleanup": {
        "zh": "清理维护",
        "indicators": ["清理", "冗余", "死代码", "cleanup", "redundant", "dead code"],
    },
}
@dataclass
class RoleScenarioTag:
    role_key: str = ""
    role_name: str = ""
    confidence: float = 0.0
    matched_indicators: list[str] = field(default_factory=list)
@dataclass
class RoleScenarioReport:
    skill_name: str = ""
    description: str = ""
    keywords: list[str] = field(default_factory=list)
    matched_roles: list[RoleScenarioTag] = field(default_factory=list)
    matched_scenarios: list[RoleScenarioTag] = field(default_factory=list)
    task_mind_expressions: list[str] = field(default_factory=list)
    role_scenario_section: str = ""
    issues: list[str] = field(default_factory=list)
    suggestions: list[str] = field(default_factory=list)
class RoleScenarioTagger:
    def tag(self, skill_name: str, description: str,
            keywords: list[str] | None = _DEFAULT_KEYWORDS) -> RoleScenarioReport:
        skill_name = normalize_str(skill_name)
        description = normalize_str(description)
        keywords = normalize_str_list(keywords)
        business_description = _sixdim_text._positive_business_text(
            _sixdim_text.strip_injected_sections(description))
        combined = f"{skill_name} {business_description} {' '.join(keywords)}".lower()
        report = RoleScenarioReport(
            skill_name=skill_name,
            description=description,
            keywords=keywords,
        )
        report.matched_roles = self._match_category(combined, ROLE_MAPPING)
        report.matched_scenarios = self._match_category(combined, SCENARIO_MAPPING)
        self._generate_tag_issues(report)
        report.task_mind_expressions = self._generate_task_mind_expressions(
            business_description, report.matched_roles, report.matched_scenarios)
        report.role_scenario_section = self._generate_section(report)
        return report
    @staticmethod
    def _matched_indicators(indicators: list[str], combined: str) -> list[str]:
        return [ind for ind in indicators if re.search(word_pattern(ind.lower()), combined) is not None]
    @staticmethod
    def _indicator_confidence(matched_count: int, total: int) -> float:
        ratio = max(total * _INDICATOR_CONFIDENCE_RATIO, 1)
        return round(min(1.0, matched_count / ratio), 2)
    def _match_category(self, combined: str,
                        category_dict: dict[str, _CategoryInfo]) -> list[RoleScenarioTag]:
        results = []
        for key, info in category_dict.items():
            matched = self._matched_indicators(info["indicators"], combined)
            if not matched:
                continue
            results.append(RoleScenarioTag(
                role_key=key,
                role_name=info["zh"],
                confidence=self._indicator_confidence(
                    len(matched), len(info["indicators"])),
                matched_indicators=matched,
            ))
        results.sort(
            key=lambda tag: (-tag.confidence, -len(tag.matched_indicators)))
        return results
    @staticmethod
    def _generate_tag_issues(report: RoleScenarioReport) -> None:
        if not report.matched_roles:
            report.issues.append(_TAG_ISSUE_NO_ROLE)
        if not report.matched_scenarios:
            report.issues.append(_TAG_ISSUE_NO_SCENARIO)
        if len(report.matched_roles) > _MAX_FOCUSED_ROLES:
            report.suggestions.append(_TAG_SUGGESTION_TOO_MANY_ROLES)
        report.suggestions.append(_TAG_SUGGESTION_ROLE_SECTION)
        report.suggestions.append(_TAG_SUGGESTION_TRIGGER)
    @staticmethod
    def _extract_keywords(description: str) -> tuple[list[str], list[str]]:
        desc_lower = description.lower()
        return (list(dict.fromkeys(_ROLE_VERB_RE.findall(desc_lower))),
                list(dict.fromkeys(_ROLE_NOUN_RE.findall(desc_lower))))
    @staticmethod
    def _role_scenario_pairs(roles: list, scenarios: list) -> list[tuple]:
        return [(role, scen)
                for role in roles[:_MAX_PAIR_DIMENSION]
                for scen in scenarios[:_MAX_PAIR_DIMENSION]]
    @staticmethod
    def _verb_noun_pairs(verbs: list, nouns: list) -> list[tuple[str, str]]:
        return [(verb, noun)
                for verb in _first_two_or(verbs, "处理")
                for noun in _first_two_or(nouns, "任务")]
    @classmethod
    def _build_role_scenario_expressions(cls, roles: list, scenarios: list,
                                          verbs: list, nouns: list) -> list:
        expressions: list[str] = []
        for role, scen in cls._role_scenario_pairs(roles, scenarios):
            for verb, noun in cls._verb_noun_pairs(verbs, nouns):
                expr = f"我是{role.role_name}，需要{scen.role_name}时{verb}{noun}"
                if expr not in expressions:
                    expressions.append(expr)
        return expressions
    @staticmethod
    def _build_colloquial_expressions(verbs: list, nouns: list) -> list:
        if not verbs:
            return []
        if not nouns:
            return [f"帮我{verbs[0]}一下", f"能不能{verbs[0]}一下"]
        first_noun = nouns[0]
        second_noun = nouns[1] if len(nouns) > 1 else first_noun
        return [
            f"帮我{verbs[0]}一下这个{first_noun}",
            f"能不能{verbs[0]}一个{second_noun}",
        ]
    def _generate_task_mind_expressions(self, description: str,
                                        roles: list[RoleScenarioTag],
                                        scenarios: list[RoleScenarioTag]) -> list[str]:
        verbs, nouns = self._extract_keywords(description)
        expressions = self._build_role_scenario_expressions(roles, scenarios, verbs, nouns)
        expressions.extend(self._build_colloquial_expressions(verbs, nouns))
        return expressions[:_MAX_MIND_EXPRESSIONS]
    @staticmethod
    def _render_tag_lines(title: str, tags: list[RoleScenarioTag]) -> list[str]:
        if not tags:
            return []
        lines = [f"**{title}**:"]
        lines.extend(
            f"- {tag.role_name} (置信度: {tag.confidence})" for tag in tags)
        lines.append("")
        return lines
    @staticmethod
    def _render_expression_lines(expressions: list[str]) -> list[str]:
        if not expressions:
            return []
        lines = ["**用户可能这样说**:"]
        lines.extend(f'- "{expr}"' for expr in expressions)
        lines.append("")
        return lines
    def _generate_section(self, report: RoleScenarioReport) -> str:
        lines = ["", _ROLE_SCENARIO_SECTION_TITLE, ""]
        lines.extend(self._render_tag_lines("适用岗位", report.matched_roles))
        lines.extend(self._render_tag_lines("典型使用场景", report.matched_scenarios))
        lines.extend(self._render_expression_lines(report.task_mind_expressions))
        lines.extend(_SECTION_HINT_LINES)
        return "\n".join(lines)
def generate_role_scenario_section(
        skill_name: str, description: str,
        keywords: list[str] | None = _DEFAULT_KEYWORDS) -> str:
    report = RoleScenarioTagger().tag(skill_name, description, keywords)
    return report.role_scenario_section
def append_role_scenario_section(skill_md_path: str | Path, skill_name: str,
                                 description: str, keywords: list) -> None:
    path_text = fs_path_text(skill_md_path)
    if not path_text:
        raise ValueError(
            "append_role_scenario_section: 路径为空或类型非法: "
            f"{skill_md_path!r}")
    role_section = generate_role_scenario_section(
        skill_name=skill_name, description=description, keywords=keywords)
    if not role_section:
        return
    path = Path(path_text)
    content = read_skill_md_text(path) if path.exists() else ""
    body = role_section.lstrip("\r\n")
    if not content.strip():
        write_skill_md_text(path, body)
        return
    if body.startswith(_ROLE_SCENARIO_SECTION_TITLE):
        body = body[len(_ROLE_SCENARIO_SECTION_TITLE):].lstrip("\r\n")
    write_skill_md_text(
        path, replace_or_insert_section(
            content, _ROLE_SCENARIO_SECTION_TITLE, body))
def _replace_section_block(content: str, header: str,
                           section: str) -> str | None:
    span = locate_section(content, header)
    if span is None:
        return None
    start, end = span
    _eol, _section = match_source_eol(content, section)
    _section = _section.rstrip("\r\n")
    if end < len(content):
        return content[:start] + _section + _eol + _eol + content[end:]
    trailing = _eol if content.endswith(("\n", "\r")) else ""
    return content[:start] + _section + trailing
def replace_or_insert_section(content: str, header: str, body: str,
                              intro: str = "") -> str:
    _eol, _body = match_source_eol(content, body)
    _body = _body.rstrip("\r\n")
    _intro = match_source_eol(content, intro)[1].rstrip("\r\n")
    section = (f"{header}{_eol}{_eol}{_intro}{_eol}{_eol}{_body}"
               if intro else f"{header}{_eol}{_eol}{_body}")
    replaced = _replace_section_block(content, header, section)
    if replaced is not None:
        return replaced
    guide_span = locate_section(content, _SCRIPT_GUIDE_SECTION_TITLE)
    if guide_span is not None:
        return (content[:guide_span[0]] + section + _eol + _eol
                + content[guide_span[0]:])
    prefix = content.rstrip()
    if not prefix:
        return section + _eol
    return prefix + f"{_eol}{_eol}{section}{_eol}"
def normalize_guide_as_section(guide: str) -> str:
    lines = guide.split("\n")
    while lines and not lines[0].strip():
        lines.pop(0)
    first_heading = parse_atx_heading(lines[0]) if lines else None
    base_level = first_heading[0] if first_heading else None
    if first_heading:
        lines[0] = _SCRIPT_GUIDE_SECTION_TITLE
    else:
        lines.insert(0, _SCRIPT_GUIDE_SECTION_TITLE)
    out: list[str] = []
    in_fence = False
    fence_char = ""
    fence_len = 0
    for idx, line in enumerate(lines):
        in_fence, fence_char, fence_len, _line_kind = scan_fence_state(
            in_fence, fence_char, fence_len, line)
        heading = parse_atx_heading(line) if idx > 0 and not in_fence else None
        if heading is not None:
            old_level = heading[0]
            if base_level is None:
                new_level = max(3, min(6, old_level + 1))
            else:
                new_level = max(3, min(6, 2 + old_level - base_level))
            normalized_line = replace_atx_level(line, new_level)
        else:
            normalized_line = line
        out.append(normalized_line)
    return "\n".join(out)
def _inject_capability_sections(
        content: str, skill_dir: str,
        skill_name: str = _DEFAULT_SKILL_NAME) -> str:
    original_content = content
    try:
        scan = scan_skill_modules(skill_dir)
        if not isinstance(scan, dict) or not normalize_scan_modules(scan):
            return content
        for header, section in (
                ("## 域总览", _domain_overview_section(scan)),
                ("## 全部 .py 文件清单",
                 render_module_responsibility_list(scan)),
                (f"## {_TRIGGER_MAP_TITLE}",
                 render_trigger_entrypoint_mapping(scan, skill_name)),
        ):
            replaced = _replace_section_block(content, header, section)
            if replaced is not None:
                content = replaced
        content = replace_or_insert_section(
            content, "## 模块能力全景",
            render_module_capability_table(scan))
        detail_intro = (
            "以下列出技能内所有 .py 文件的完整能力描述，"
            "包括每个模块的公开函数签名、公开类及方法、导出列表和「Agent 调用时机」。"
        )
        content = replace_or_insert_section(
            content, "## 模块能力详解",
            render_full_module_capabilities(scan), intro=detail_intro)
    except LAYER_DEGRADE_EXC as exc:
        log_swallowed(
            __name__, exc, context='_inject_capability_sections:scan')
        return original_content
    return content
def _append_script_guide_if_absent(content: str, skill_dir: str) -> str:
    if has_section(content, _SCRIPT_GUIDE_SECTION_TITLE):
        return content
    try:
        guide = "\n".join(_build_script_guide(skill_dir)).rstrip()
        if guide:
            content = content.rstrip() + "\n\n" + normalize_guide_as_section(guide) + "\n"
    except LAYER_DEGRADE_EXC as exc:
        log_swallowed(
            __name__, exc, context='_append_script_guide_if_absent:build_guide')
    return content

def read_skill_md_text(skill_md_path: Path) -> str:
    path_text = fs_path_text(skill_md_path)
    if not path_text:
        raise ValueError(
            f"read_skill_md_text: 路径为空或类型非法: {skill_md_path!r}")
    return Path(path_text).read_text(encoding="utf-8-sig")
def _detect_dominant_eol(md_path: str) -> str:
    try:
        raw = Path(md_path).read_bytes()
    except OSError:  # jwsgj:silent-ok 纯值降级：入参不可解析时返回安全默认值，无副作用可留痕
        return "\n"
    crlf = raw.count(b"\r\n")
    counts = {
        "\r\n": crlf,
        "\n": raw.count(b"\n") - crlf,
        "\r": raw.count(b"\r") - crlf,
    }
    if not any(counts.values()):
        return "\n"
    return max(counts, key=counts.get)
def write_skill_md_text(skill_md_path: Path, content: str,
                         has_bom: bool | None = None) -> None:
    path_text = fs_path_text(skill_md_path)
    if not path_text:
        raise ValueError(
            f"write_skill_md_text: 路径为空或类型非法: {skill_md_path!r}")
    if has_bom is None:
        has_bom = _detect_bom(path_text)
    eol = _detect_dominant_eol(path_text)
    normalized = content.replace("\r\n", "\n").replace("\r", "\n")
    try:
        with open(path_text, encoding="utf-8-sig", newline="") as fh:
            previous = fh.read()
    except (OSError, UnicodeDecodeError) as exc:
        _log.debug("write_skill_md_text: 旧文件行尾读取失败，使用主行尾: %s: %s",
                   path_text, exc)
    else:
        normalized = _restore_line_endings(previous, normalized)
        eol = ""
    write_markdown_text(path_text, normalized, has_bom, newline=eol)
def _write_skill_md(skill_md_path: Path, content: str) -> None:
    write_skill_md_text(skill_md_path, content)
    try:
        purify_skill_md(str(skill_md_path))
    except LAYER_DEGRADE_EXC as exc:
        log_swallowed(__name__, exc, context='_write_skill_md:purify_skill_md')
def _skill_name_of(content: str, fallback: str) -> str:
    try:
        name = parse_skill_md_text(content, fallback)["name"]
    except LAYER_DEGRADE_EXC as exc:
        log_swallowed(__name__, exc, context='_skill_name_of:parse_skill_md_text')
        return fallback
    return name.strip() if isinstance(name, str) and name.strip() else fallback
def _description_field_presence(content: str) -> bool | None:
    split = split_frontmatter_document(content)
    if split is None:
        return None
    parts = split_frontmatter(split[0])
    if len(parts) < 3:
        return None
    return bool(_field_line_numbers(parts[1].split("\n"), "description"))
def update_skill_md(skill_dir: str, optimized_desc: str | None,
                    optimized_keywords: list[str], inject_capability: bool = True,
                    inject_script_guide: bool = True) -> bool:
    optimized_keywords = _merge_keywords(normalize_keywords(optimized_keywords))
    if not isinstance(optimized_desc, str) or not optimized_desc.strip():
        optimized_desc = None
    dir_text = fs_path_text(skill_dir)
    if not dir_text:
        _log.warning("update_skill_md: skill_dir 为空或类型非法 %r，跳过写回",
                     skill_dir)
        return False
    skill_md_path = Path(dir_text) / "SKILL.md"
    if not skill_md_path.exists():
        return False
    try:
        content = read_skill_md_text(skill_md_path)
    except (OSError, UnicodeDecodeError) as exc:
        _log.warning("update_skill_md: 读取 %s 失败，跳过写回: %s", skill_md_path, exc)
        return False
    original_content = content
    managed_anchors = _managed_anchors_for_update(content)
    fm_status: dict = {}
    merged_indented, indented_seen = _merge_indented_desc_keywords(
        content, optimized_desc, optimized_keywords, str(skill_md_path))
    if indented_seen:
        if merged_indented is None:
            return False
        content = merged_indented
        fm_status["desc_written"] = optimized_desc is not None
        fm_status["keywords_written"] = bool(optimized_keywords)
    else:
        content = replace_frontmatter_desc_keywords(
            content, optimized_desc, optimized_keywords,
            md_label=str(skill_md_path), status_out=fm_status)
        if (optimized_desc is not None and not fm_status.get("desc_written")
                and _description_field_presence(content) is False):
            inserted = insert_frontmatter_description(content, optimized_desc)
            fm_status["desc_written"] = inserted != content
            content = inserted
    content = _restore_managed_anchors_after_update(
        content, managed_anchors, optimized_desc is not None,
        optimized_keywords)
    if inject_capability:
        content = _inject_capability_sections(
            content, dir_text,
            _skill_name_of(content, Path(dir_text).name))
    if inject_script_guide:
        content = _append_script_guide_if_absent(content, dir_text)
    fm_written = fm_status.get("desc_written") or fm_status.get("keywords_written")
    if content == original_content:
        if not fm_written and (optimized_desc is not None or optimized_keywords):
            _log.warning(
                "update_skill_md: %s frontmatter 无锚点且注入未改变内容，"
                "写回未发生", skill_md_path)
        return False
    _write_skill_md(skill_md_path, content)
    return True
def _detect_bom(md_path: str) -> bool:
    try:
        if not os.path.isfile(md_path):
            return False
        with open(md_path, "rb") as _fb:
            return _fb.read(3) == b"\xef\xbb\xbf"
    except OSError as _e:
        _log.warning("_detect_bom: BOM 探测失败,按无 BOM 处理: %s: %s", md_path, _e)
        return False
def _frontmatter_description_from(frontmatter: str) -> str | None:
    if not frontmatter.strip():
        return None
    split = split_frontmatter_document(frontmatter)
    block = split_frontmatter(split[0]) if split else []
    if len(block) < 3:
        return None
    return parse_frontmatter_description(block[1]).value or None
def _optimized_frontmatter_payload(opt: Any) -> tuple[str | None, list[str]]:
    frontmatter = getattr(opt, "frontmatter", "")
    if not isinstance(frontmatter, str):
        frontmatter = ""
    desc = getattr(opt, "optimized_description", None)
    if not (isinstance(desc, str) and desc.strip()):
        desc = _frontmatter_description_from(frontmatter)
    keywords = _merge_keywords(normalize_keywords(
        getattr(opt, "optimized_keywords", None)))
    if not keywords and frontmatter.strip():
        keywords = _merge_keywords(frontmatter_keywords(
            parse_frontmatter_dict(frontmatter).get("keywords")))
    return desc, keywords
def _merged_frontmatter_head(
        head: str, opt: Any, md_label: str) -> str:
    desc, keywords = _optimized_frontmatter_payload(opt)
    if desc is None and not keywords:
        return head
    managed_anchors = _managed_anchors_for_update(head)
    merged_indented, indented_seen = _merge_indented_desc_keywords(
        head, desc, keywords, md_label)
    if indented_seen:
        if merged_indented is None:
            return head
        return _restore_managed_anchors_after_update(
            merged_indented, managed_anchors, desc is not None, keywords)
    status: dict = {}
    merged = replace_frontmatter_desc_keywords(
        head, desc, [], md_label=md_label, status_out=status)
    if desc is not None and not status.get("desc_written"):
        merged = insert_frontmatter_description(merged, desc)
    merged = replace_frontmatter_desc_keywords(
        merged, None, keywords, md_label=md_label)
    return _restore_managed_anchors_after_update(
        merged, managed_anchors, desc is not None, keywords)
def _replace_frontmatter(text: str, new_frontmatter: str) -> str:
    normalized = text.replace("\r\n", "\n").replace("\r", "\n")
    normalized_head = new_frontmatter.replace(
        "\r\n", "\n").replace("\r", "\n")
    parts = split_frontmatter_document(normalized)
    block = normalized_head + ("" if parts else "\n" * 2)
    merged = block + (parts[1] if parts is not None else normalized)
    return _restore_line_endings(text, merged)
def merge_optimized_frontmatter(
        text: str, opt: Any, md_label: str = _DEFAULT_MD_LABEL) -> str | None:
    normalized = text.replace("\r\n", "\n").replace("\r", "\n")
    split = split_frontmatter_document(normalized)
    if split is None:
        return None
    head, _tail = split
    merged = _merged_frontmatter_head(head, opt, md_label)
    if merged == head:
        return None
    return _replace_frontmatter(text, merged)
def merged_frontmatter_preview(skill_dir: str, opt: Any) -> str:
    dir_text = fs_path_text(skill_dir)
    if not dir_text:
        return ""
    md_path = Path(dir_text) / "SKILL.md"
    if not md_path.exists():
        return ""
    try:
        text = read_skill_md_text(md_path)
    except (OSError, UnicodeDecodeError):
        _log.debug("merged_frontmatter_preview: 读取 %s 失败", md_path,
                   exc_info=True)
        return ""
    normalized = text.replace("\r\n", "\n").replace("\r", "\n")
    split = split_frontmatter_document(normalized)
    if split is None:
        return ""
    return _merged_frontmatter_head(split[0], opt, str(md_path))
def write_optimized_frontmatter(skill_dir: str, opt: Any) -> bool:
    dir_text = fs_path_text(skill_dir)
    if not dir_text:
        return False
    md_path = Path(dir_text) / "SKILL.md"
    if not md_path.exists():
        return False
    text = read_skill_md_text(md_path)
    merged = merge_optimized_frontmatter(text, opt, str(md_path))
    if merged is None:
        return False
    write_skill_md_text(md_path, merged)
    return True
def _quoted_yaml_key_end(line: str) -> int | None:
    quote = line[0]
    index = 1
    while index < len(line):
        ch = line[index]
        if quote == '"' and ch == "\\" and index + 1 < len(line):
            index += 2
            continue
        if ch == quote:
            if quote == "'" and index + 1 < len(line) and line[index + 1] == "'":
                index += 2
                continue
            return index + 1
        index += 1
    return None
def _frontmatter_line_key(line: str) -> str | None:
    if not line or line[0] in (" ", "\t", "#", "-"):
        return None
    if line.strip() in ("---", "..."):
        return None
    if line[0] in ('"', "'"):
        end = _quoted_yaml_key_end(line)
        if end is None:
            return None
        rest = line[end:].lstrip(" \t")
        if not rest.startswith(":"):
            return None
        tail = rest[1:]
        if tail and not tail[0].isspace():
            return None
        return unquote_yaml_scalar(line[:end])
    if line[0] in "[]{},&*!|>%@`":
        return None
    for index, ch in enumerate(line):
        if ch != ":":
            continue
        if index + 1 < len(line) and not line[index + 1].isspace():
            continue
        key = line[:index].strip()
        if not key or " #" in key or "\t#" in key:
            return None
        return key
    return None
def _frontmatter_trivia_start(lines: list[str], start: int) -> int:
    while start > 0:
        previous = lines[start - 1]
        if previous.strip() and not previous.lstrip().startswith("#"):
            break
        start -= 1
    return start
def _select_unmanaged_frontmatter_lines(
        lines: list[str], fields: list[tuple[int, str | None]]) -> list[str]:
    kept: list[str] = []
    if not fields:
        if all(not line.strip() or line.lstrip().startswith("#") for line in lines):
            kept.extend(lines)
    else:
        starts = [_frontmatter_trivia_start(lines, line) for line, _key in fields]
        for index, (_line, key) in enumerate(fields):
            if key in _MANAGED_FRONTMATTER_KEYS:
                continue
            end = starts[index + 1] if index + 1 < len(fields) else len(lines)
            kept.extend(lines[starts[index]:end])
        if fields[-1][1] in _MANAGED_FRONTMATTER_KEYS:
            trailing_start = len(lines)
            while trailing_start > 0:
                previous = lines[trailing_start - 1]
                if previous.startswith("#") or not previous.strip():
                    trailing_start -= 1
                    continue
                break
            kept.extend(lines[trailing_start:])
    while kept and not kept[-1].strip():
        kept.pop()
    return kept
def _unmanaged_frontmatter_lines(md_path: Path) -> list[str]:
    if not md_path.exists():
        return []
    try:
        content = read_skill_md_text(md_path)
    except (OSError, UnicodeDecodeError):
        _log.debug("_unmanaged_frontmatter_lines: 读取 %s 失败", md_path,
                   exc_info=True)
        return []
    normalized_indented, indented_seen = _merge_indented_desc_keywords(
        content, None, [], str(md_path))
    content = normalized_indented if indented_seen and normalized_indented is not None else content
    normalized = content.replace("\r\n", "\n").replace("\r", "\n")
    split = split_frontmatter_document(normalized)
    parts = split_frontmatter(split[0]) if split else []
    if len(parts) < 3:
        return []
    fm_body = parts[1]
    lines = fm_body.split("\n") if fm_body.strip() else []
    if lines and not lines[-1]:
        lines.pop()
    fields: list[tuple[int, str | None]] | None = None
    if _yaml is not None and lines:
        try:
            mapping = _yaml.compose(fm_body)
        except _yaml.YAMLError:
            _log.debug(
                "_unmanaged_frontmatter_lines: YAML 节点定位失败，回退行扫描: %s",
                md_path, exc_info=True)
        else:
            if isinstance(mapping, _yaml.nodes.MappingNode):
                fields = [
                    (key_node.start_mark.line,
                     key_node.value if isinstance(key_node.value, str) else None)
                    for key_node, _value_node in mapping.value
                ]
    if fields is None:
        fields = []
        for index, line in enumerate(lines):
            key = _frontmatter_line_key(line)
            if key is not None:
                fields.append((index, key))
    return _select_unmanaged_frontmatter_lines(lines, fields)
def _insert_unmanaged_frontmatter(lines: list[str],
                                  extra: list[str]) -> list[str]:
    if not extra or not lines or lines[0] != "---":
        return lines
    try:
        close_index = lines.index("---", 1)
    except ValueError:
        _log.debug("frontmatter 缺少关闭围栏，跳过非托管字段插入")
        return lines
    return [*lines[:close_index], *extra, *lines[close_index:]]
def _skip_yaml_collection_events(events, event) -> None:
    starts = (_yaml.events.MappingStartEvent, _yaml.events.SequenceStartEvent)
    ends = (_yaml.events.MappingEndEvent, _yaml.events.SequenceEndEvent)
    if not isinstance(event, starts):
        return
    depth = 1
    for nested in events:
        if isinstance(nested, starts):
            depth += 1
        elif isinstance(nested, ends):
            depth -= 1
            if depth == 0:
                return
def _keyword_item_anchors(events) -> list[tuple[str, str]]:
    items: list[tuple[str, str]] = []
    for event in events:
        if isinstance(event, _yaml.events.SequenceEndEvent):
            break
        if isinstance(event, _yaml.events.ScalarEvent):
            if event.anchor:
                items.append((event.value, event.anchor))
        else:
            _skip_yaml_collection_events(events, event)
    return items
def _managed_frontmatter_anchors(fm: str) -> _ManagedAnchorInfo:
    if _yaml is None:
        return _ManagedAnchorInfo()
    referenced_anchors = frozenset(
        event.anchor for event in _yaml.parse(fm)
        if isinstance(event, _yaml.events.AliasEvent))
    events = iter(_yaml.parse(fm))
    for event in events:
        if isinstance(event, _yaml.events.MappingStartEvent):
            break
        if not isinstance(event, (_yaml.events.StreamStartEvent,
                                  _yaml.events.DocumentStartEvent)):
            return _ManagedAnchorInfo()
    else:
        return _ManagedAnchorInfo()
    field_anchors: dict[str, str] = {}
    keyword_items: list[tuple[str, str]] = []
    description_block = ""
    for key_event in events:
        if isinstance(key_event, _yaml.events.MappingEndEvent):
            break
        key = key_event.value if isinstance(key_event, _yaml.events.ScalarEvent) else None
        _skip_yaml_collection_events(events, key_event)
        value_event = next(events)
        anchor = getattr(value_event, "anchor", None)
        if key in _MANAGED_FRONTMATTER_KEYS and anchor:
            field_anchors[key] = anchor
        if (key == "description"
                and isinstance(value_event, _yaml.events.ScalarEvent)
                and value_event.style in ("|", ">")):
            description_block = value_event.style
            header_line = fm.splitlines()[value_event.start_mark.line]
            for token in header_line.split():
                if token.startswith(value_event.style):
                    if "+" in token:
                        description_block += "+"
                    elif "-" in token:
                        description_block += "-"
                    break
        if key == "keywords" and isinstance(
                value_event, _yaml.events.SequenceStartEvent):
            keyword_items.extend(_keyword_item_anchors(events))
        else:
            _skip_yaml_collection_events(events, value_event)
    return _ManagedAnchorInfo(
        field_anchors, tuple(keyword_items), description_block, referenced_anchors)
def _parse_existing_frontmatter(existing_md, default_name, default_desc):
    existing_name = default_name
    existing_desc = default_desc
    existing_version = DEFAULT_SKILL_VERSION
    existing_keywords: list[str] = []
    existing_anchors = _ManagedAnchorInfo()
    try:
        if not existing_md.exists():
            return (existing_name, existing_desc, existing_version,
                    existing_keywords, existing_anchors)
        existing_content = read_skill_md_text(existing_md)
        existing_content = existing_content.replace("\r\n", "\n").replace("\r", "\n")
        split = split_frontmatter_document(existing_content)
        parts = split_frontmatter(split[0]) if split else []
        if len(parts) < 3:
            return (existing_name, existing_desc, existing_version,
                    existing_keywords, existing_anchors)
        fm = parts[1]
        parsed = parse_skill_md_text(split[0], default_name)
        existing_name = parsed["name"] or default_name
        existing_version = parsed["version"] or DEFAULT_SKILL_VERSION
        existing_desc = (parse_frontmatter_description(fm).value
                         or default_desc or "")
        existing_keywords = normalize_keywords(frontmatter_keywords(
            parse_frontmatter_dict(existing_content).get("keywords")))
        if _yaml is not None:
            try:
                yaml_meta = _yaml.safe_load(fm)
            except _yaml.YAMLError:
                _log.debug(
                    "_parse_existing_frontmatter: YAML 严格读取失败，保留宽容结果: %s",
                    existing_md, exc_info=True)
            else:
                if isinstance(yaml_meta, dict):
                    existing_anchors = _managed_frontmatter_anchors(fm)
                    yaml_name = yaml_meta.get("name")
                    if isinstance(yaml_name, str):
                        existing_name = yaml_name.strip() or default_name
                    elif "name" not in yaml_meta:
                        existing_name = default_name
                    yaml_version = yaml_meta.get("version")
                    if isinstance(yaml_version, str):
                        existing_version = yaml_version.strip() or DEFAULT_SKILL_VERSION
                    elif "version" not in yaml_meta:
                        existing_version = DEFAULT_SKILL_VERSION
                    yaml_desc = yaml_meta.get("description")
                    if isinstance(yaml_desc, str):
                        existing_desc = yaml_desc.rstrip() or default_desc or ""
                    elif "description" not in yaml_meta:
                        existing_desc = default_desc or ""
                    existing_keywords = normalize_keywords(frontmatter_keywords(
                        yaml_meta.get("keywords")))
    except (OSError, UnicodeDecodeError):
        _log.warning(
            "_parse_existing_frontmatter: 读取 SKILL.md 失败,回退默认 frontmatter: %s",
            existing_md, exc_info=True)
    return (existing_name, existing_desc, existing_version,
            existing_keywords, existing_anchors)
def _merge_keywords(*groups: list) -> list[str]:
    merged: list[str] = []
    seen: set[str] = set()
    for group in groups:
        for item in group:
            text = normalize_text(item).strip()
            key = text.lower()
            if text and key not in seen:
                seen.add(key)
                merged.append(text)
    return merged
def _strip_stale_test_metrics(desc: str) -> str:
    stripped = _STALE_TEST_METRIC_RE.sub("", desc)
    if stripped == desc:
        return desc
    stripped = re.sub(r"[ \t]{2,}", " ", stripped)
    stripped = re.sub(r"(?<=[。.！!？?])[，,、；;]+", "", stripped)
    stripped = re.sub(r"。{2,}", "。", stripped)
    stripped = re.sub(r"(?<!\.)\.\.(?!\.)", ".", stripped)
    stripped = re.sub(r"[，,、；;]{2,}", "，", stripped)
    stripped = re.sub(r"^[ \t]*[，,、；;。.！!？?][ \t]*", "", stripped)
    return stripped.rstrip(" \t，,、；;")
_COUNT_CLAIMS: tuple[tuple[str, str, str, str, str], ...] = (
    ("modules", r"个\s*模块", r"modules?", "{n} 个模块", "{n} modules"),
    ("exports", r"个\s*公开导出", r"public\s+exports?",
     "{n} 个公开导出", "{n} public exports"),
)
def _count_claim_patterns() -> tuple[tuple[str, re.Pattern[str], str, str], ...]:
    compiled = []
    for key, zh_unit, en_unit, zh_render, en_render in _COUNT_CLAIMS:
        pattern = re.compile(
            r"(?<![\dA-Za-z_.])(?P<num>\d+)\s*"
            r"(?:(?P<zh>" + zh_unit + r")|(?P<en>" + en_unit + r"))")
        compiled.append((key, pattern, zh_render, en_render))
    return tuple(compiled)
_COUNT_CLAIM_PATTERNS = _count_claim_patterns()
def _rewrite_count_claims(desc: str, actual: dict[str, int]) -> str:
    for key, pattern, zh_render, en_render in _COUNT_CLAIM_PATTERNS:
        if key not in actual:
            continue
        number = actual[key]
        def _render(match: re.Match[str], _zh=zh_render, _en=en_render,
                    _n=number) -> str:
            is_zh = match.group("zh") is not None
            rendered = (_zh if is_zh else _en).format(n=_n)
            if not is_zh and _n == 1:
                rendered = rendered.replace(
                    "modules", "module").replace("exports", "export")
            return rendered
        desc = pattern.sub(_render, desc)
    return desc
def _update_description_numbers(desc, scan):
    if not desc:
        return desc
    scan = scan if isinstance(scan, dict) else {}
    actual: dict[str, int] = {}
    if isinstance(scan.get("modules"), list):
        actual["modules"] = len(normalize_scan_modules(scan))
    elif "total_modules" in scan:
        modules = int_metric(scan.get("total_modules"), default=-1)
        if modules >= 0:
            actual["modules"] = modules
    if "total_exports" in scan:
        exports = int_metric(scan.get("total_exports"), default=-1)
        if exports >= 0:
            actual["exports"] = exports
    desc = _rewrite_count_claims(desc, actual)
    return _strip_stale_test_metrics(desc)
def _write_usage_guide_outputs(
        target_dir: str, scripts_info: list,
        has_guide_section: bool) -> None:
    skill_md_path = os.path.join(target_dir, "SKILL.md")
    scripts_dir = os.path.join(target_dir, "scripts")
    skill_name = os.path.basename(os.path.normpath(target_dir))
    if not has_guide_section:
        guide = generate_script_call_examples(scripts_info)
        if guide:
            eol = _detect_dominant_eol(skill_md_path)
            guide = guide.replace("\r\n", "\n").replace("\r", "\n")
            with guarded_open(skill_md_path, "a", encoding="utf-8", newline="") as f:
                f.write(eol + guide.replace("\n", eol) + eol)
            _log.info("[init] 已注入脚本调用指引")
    readme_path = os.path.join(scripts_dir, "README.md")
    if os.path.exists(readme_path):
        _log.info("[init] scripts/README.md 已存在，保留用户原内容")
        return
    readme_content = generate_scripts_readme(skill_name, scripts_info)
    with guarded_open(readme_path, "w", encoding="utf-8", newline="\n") as f:
        f.write(readme_content)
    _log.info("[init] 已生成 scripts/README.md")
def _emit_guide_run(t0: float, **fields: Any) -> None:
    write_module_run(
        "build_skill_md_rewrite", "inject_script_usage_guide",
        duration_ms=(time.monotonic() - t0) * 1000.0, **fields)
def inject_script_usage_guide(target_dir: str) -> None:
    _t0 = time.monotonic()
    dir_text = fs_path_text(target_dir)
    if not dir_text:
        _emit_guide_run(_t0, outcome="skipped_invalid_target")
        return
    skill_md_path = os.path.join(dir_text, "SKILL.md")
    if not os.path.exists(skill_md_path):
        _emit_guide_run(_t0, outcome="skipped_no_skill_md")
        return
    try:
        scripts_info = collect_scripts_info(dir_text)
        if not scripts_info:
            _emit_guide_run(_t0, outcome="skipped_no_scripts")
            return
        content = read_skill_md_text(Path(skill_md_path))
        has_guide_section = has_section(
            content, _SCRIPT_GUIDE_SECTION_TITLE)
        _write_usage_guide_outputs(
            dir_text, scripts_info, has_guide_section)
        _emit_guide_run(
            _t0, scripts=len(scripts_info), guide_injected=not has_guide_section)
    except Exception as e:  # noqa: BLE001 — 指引注入失败降级不阻断创建
        _log.warning("[init] 脚本调用指引注入失败: %s", e)
        _emit_guide_run(_t0, outcome="failed")
def _build_script_guide(target_dir, actual_scripts=None):
    if actual_scripts is None:
        actual_scripts = collect_scripts_info(target_dir)
    if not actual_scripts:
        return []
    guide = generate_script_call_examples(actual_scripts)
    return guide.splitlines() + [""]
def _clean_fm_description(existing_desc, name) -> str:
    desc_clean = existing_desc or (name + " 技能")
    return _flatten_description_line(strip_must_use_prefix(desc_clean))
def _anchor_managed_yaml_line(
        line: str, key: str, anchors: _ManagedAnchorInfo | None) -> str:
    anchor = (anchors.fields if anchors else {}).get(key)
    if not anchor:
        return line
    head, separator, tail = line.partition(":")
    if re.match(r"\s*&" + re.escape(anchor) + r"(?=\s|$)", tail):
        return line
    return f"{head}{separator} &{anchor}{tail}" if separator else line
def _keyword_items_preserving_anchors(
        keywords: list[str], anchored_items: tuple[tuple[str, str], ...],
        referenced_anchors: frozenset[str] = frozenset(),
) -> list[tuple[str, str]]:
    remaining = list(anchored_items)
    merged: list[tuple[str, str]] = []
    for keyword_text in keywords:
        keyword_key = normalize_text(keyword_text).strip().casefold()
        match_index = next((
            index for index, (value, _anchor) in enumerate(remaining)
            if normalize_text(value).strip().casefold() == keyword_key
        ), None)
        anchor = remaining.pop(match_index)[1] if match_index is not None else ""
        merged.append((keyword_text, anchor))
    merged.extend(
        (value, anchor) for value, anchor in remaining
        if anchor in referenced_anchors)
    return merged
def _managed_anchors_for_update(content: str) -> _ManagedAnchorInfo:
    if _yaml is None:
        return _ManagedAnchorInfo()
    parts = split_frontmatter(content)
    if len(parts) < 3:
        return _ManagedAnchorInfo()
    try:
        return _managed_frontmatter_anchors(parts[1])
    except _yaml.YAMLError:
        _log.debug(
            "元数据更新前 YAML 锚点读取失败，保留宽容替换行为",
            exc_info=True)
        return _ManagedAnchorInfo()
def _replace_field_line(
        lines: list[str], index: int, replacement: str) -> None:
    ending = lines[index][len(lines[index].rstrip("\r\n")):]
    lines[index] = replacement + ending
def _restore_description_anchor(
        lines: list[str], anchors: _ManagedAnchorInfo) -> None:
    if not anchors.fields.get("description"):
        return
    indices = _field_line_numbers(lines, "description")
    if indices:
        index = indices[-1]
        replacement = _anchor_managed_yaml_line(
            lines[index].rstrip("\r\n"), "description", anchors)
        _replace_field_line(lines, index, replacement)
def _restore_keyword_anchors(
        lines: list[str], keywords: list[str],
        anchors: _ManagedAnchorInfo) -> None:
    if not (anchors.fields.get("keywords") or anchors.keyword_items):
        return
    indices = _field_line_numbers(lines, "keywords")
    if not indices:
        return
    index = indices[-1]
    current = lines[index].rstrip("\r\n")
    if not current.lstrip(" \t").startswith("keywords: ["):
        return
    actual_keywords = frontmatter_keywords(keywords)[:INLINE_KEYWORDS_MAX]
    items = _keyword_items_preserving_anchors(
        actual_keywords, anchors.keyword_items, anchors.referenced_anchors)
    rendered_items = ", ".join(
        (f"&{anchor} " if anchor else "") + yaml_quote_scalar(keyword)
        for keyword, anchor in items)
    indent = current[:len(current) - len(current.lstrip(" \t"))]
    replacement = _anchor_managed_yaml_line(
        f"{indent}keywords: [{rendered_items}]", "keywords", anchors)
    _replace_field_line(lines, index, replacement)
def _restore_managed_anchors_after_update(
        content: str, anchors: _ManagedAnchorInfo,
        update_description: bool, keywords: list[str]) -> str:
    if not (anchors.fields or anchors.keyword_items):
        return content
    document = split_frontmatter_document(content)
    if document is None:
        return content
    head, tail = document
    parts = split_frontmatter(head)
    if len(parts) < 3 or not parts[1]:
        return content
    body_start = head.find(parts[1])
    if body_start < 0:
        return content
    lines = parts[1].splitlines(keepends=True)
    if update_description:
        _restore_description_anchor(lines, anchors)
    if keywords:
        _restore_keyword_anchors(lines, keywords, anchors)
    body_end = body_start + len(parts[1])
    return head[:body_start] + "".join(lines) + head[body_end:] + tail
def _fm_yaml_block_lines(
        existing_name, existing_version, desc_with_prefix, func_keywords,
        managed_anchors) -> list[str]:
    description_block = (
        managed_anchors.description_block
        if managed_anchors and managed_anchors.description_block else "|")
    parts = [
        "---",
        _anchor_managed_yaml_line(
            yaml_scalar_line("name", existing_name), "name", managed_anchors),
        _anchor_managed_yaml_line(
            yaml_scalar_line("version", existing_version), "version", managed_anchors),
        _anchor_managed_yaml_line(
            f"description: {description_block}", "description", managed_anchors),
        "  " + desc_with_prefix,
    ]
    anchored_items = managed_anchors.keyword_items if managed_anchors else ()
    keyword_items = _keyword_items_preserving_anchors(
        func_keywords[:25], anchored_items,
        managed_anchors.referenced_anchors if managed_anchors else frozenset())
    if keyword_items:
        parts.append(_anchor_managed_yaml_line(
            "keywords:", "keywords", managed_anchors))
        parts.extend(
            "  - " + (f"&{anchor} " if anchor else "") + yaml_quote_scalar(kw)
            for kw, anchor in keyword_items)
    else:
        parts.append(_anchor_managed_yaml_line(
            "keywords: []", "keywords", managed_anchors))
    parts.append("---")
    return parts
def _fm_header_lines(existing_name, skill_summary, desc_with_prefix) -> list[str]:
    return [
        "",
        f"# {existing_name}",
        "",
        f"> {skill_summary}",
        "",
        desc_with_prefix,
        "",
        "## Agent 决策指引",
        "",
        "Agent 在以下情况应加载本技能：",
        "1. 用户意图与 " + existing_name + " 核心能力匹配",
        "2. 用户提及本技能的触发关键词",
        ('3. 任务需要本技能提供的特定功能'
         f'（详见下方"技能能力边界"和"{_TRIGGER_MAP_TITLE}"）'),
        "",
        "加载后，Agent 应按五步流程操作：",
        '1. **先查「技能能力边界」** — 确认任务在 In Scope 范围内，否则不要加载',
        '2. **查「全部 .py 文件清单」** — 一眼定位目标模块',
        '3. **查「触发场景与入口函数映射表」** — 直接获取入口函数名',
        '4. **查「模块能力详解」** — 获取完整签名和调用示例',
        '5. **遵守「强制工作流与约束」** — 严格按工作流顺序调用',
        "",
    ]
def _fm_trigger_lines(existing_name, func_keywords) -> list[str]:
    return [
        "## 触发条件",
        "",
        "### 应当触发（Agent 必须加载本技能）",
        "",
        f"- 用户提及以下任一触发关键词时: {', '.join(func_keywords[:15])}",
        f"- 用户要求执行 {existing_name} 相关操作",
        f"- 用户意图与 {existing_name} 核心能力匹配",
        "",
        "### 不应触发",
        "- 与此技能领域完全无关的通用任务",
        "- 不涉及本技能核心能力的纯闲聊或系统操作",
        "",
    ]
def _fm_quickstart_lines(existing_name) -> list[str]:
    return [
        "## 快速入门",
        "",
        (f"请根据 {existing_name} 的实际包结构与公开 API 选择入口；"
         "不要仅凭技能目录名推断 Python 导入路径。"),
        "",
        "```python",
        "# from actual_package import public_entry",
        "# result = public_entry(...)",
        "```",
        "",
    ]
def _build_skill_md_frontmatter(scan, existing_name, existing_desc,
                               existing_version, name,
                               existing_keywords=(),
                               managed_anchors=_DEFAULT_MANAGED_ANCHORS):
    desc_clean = _clean_fm_description(existing_desc, name)
    desc_with_prefix = _clamp_description_preserving_exclusions(
        f"[MUST USE] {desc_clean}")
    func_keywords = _merge_keywords(
        list(existing_keywords),
        extract_functional_keywords(scan, existing_name, desc_clean))
    skill_summary = render_scan_summary(scan)
    parts: list[str] = []
    parts.extend(_fm_yaml_block_lines(
        existing_name, existing_version, desc_with_prefix, func_keywords,
        managed_anchors))
    parts.extend(_fm_header_lines(
        existing_name, skill_summary, desc_with_prefix))
    parts.extend(_fm_trigger_lines(existing_name, func_keywords))
    parts.extend(_fm_quickstart_lines(existing_name))
    return parts
def _build_skill_md_body_sections(scan, existing_name, cap_table, target_dir,
                                 skill_type: str):
    parts = []
    boundary = render_capability_boundary(scan, existing_name, skill_type)
    parts.append(boundary)
    parts.append("")
    parts.append(_domain_overview_section(scan))
    parts.append("")
    resp_list = render_module_responsibility_list(scan)
    parts.append(resp_list)
    parts.append("")
    parts.append("## 模块能力全景")
    parts.append("")
    parts.append(cap_table)
    parts.append("")
    parts.append("## 模块能力详解")
    parts.append("")
    parts.append("> 本区块为 **区块3：每个文件的可调用接口** 的索引。")
    parts.append("> 为保持 SKILL.md 精炼（Agent 可完整读取），每个 .py 文件的完整函数签名、")
    parts.append("> 类方法列表和调用示例不在本区块展开；请通过「触发场景与入口函数映射表」")
    parts.append("> 定位入口后，直接查阅对应 .py 源文件的 docstring 获取完整签名。")
    parts.append("")
    parts.append("**如何定位入口**：")
    parts.append("1. 先查本文件「全部 .py 文件清单」定位目标文件")
    parts.append("2. 再查本文件「触发场景与入口函数映射表」获取入口函数名")
    parts.append("")
    trigger_map = render_trigger_entrypoint_mapping(scan, existing_name)
    parts.append(trigger_map)
    parts.append("")
    workflow = render_forced_workflow_constraints(existing_name, "")
    parts.append(workflow)
    parts.append("")
    actual_scripts = collect_scripts_info(target_dir)
    parts.extend(_build_script_guide(target_dir, actual_scripts))
    parts.append("## 脚本 vs API 决策指引")
    parts.append("")
    parts.append("| 场景 | 推荐方式 | 原因 |")
    parts.append("|------|---------|------|")
    parts.append("| 需要直接复用返回对象 | Python API（如项目提供） | 避免解析进程输出 |")
    if actual_scripts:
        parts.append("| 需要进程隔离执行 | CLI 脚本 | 按脚本指南使用真实命令 |")
    if any(script.get("json_flag") for script in actual_scripts):
        parts.append("| 需要跨进程结构化数据 | 声明 JSON 标志的 CLI 脚本 | 使用该脚本实际标志 |")
    if any(script.get("has_dry") for script in actual_scripts):
        parts.append(
            "| 首次不确定结果 | 声明 `--dry-run` / `--dry_run` 的 CLI 脚本 "
            "| 预览模式由脚本真实实现 |")
    parts.append("")
    parts.append("## 设计原则")
    parts.append("")
    parts.append("1. **可发现性优先**: description 含强制触发词和场景关键词")
    parts.append("2. **规避问题为先**: 创建时预检（命名/结构/安全），从源头规避常见问题")
    parts.append('3. **事实驱动**: 脚本指南只列出从源码实际扫描到的入口与 CLI 标志')
    parts.append("4. **契约透明**: 输出结构、错误处理、幂等性与依赖检查以目标项目真实实现为准")
    parts.append("5. **模块能力透明**: 依据扫描结果定位公开 API，不虚构项目能力")
    return parts
def rebuild_skill_md(skill_dir: str, name: str | None = None, description: str | None = None) -> str:
    dir_text = fs_path_text(skill_dir)
    if not dir_text:
        raise ValueError(
            f"rebuild_skill_md: skill_dir 为空或类型非法: {skill_dir!r}")
    target_dir = str(Path(dir_text).resolve())
    if isinstance(name, str):
        name = name.strip() or None
    if isinstance(description, str):
        description = description.strip() or None
    name_given = bool(name and str(name).strip())
    description_given = bool(description and str(description).strip())
    if not name:
        name = Path(target_dir).name
    if not description:
        description = name + " 技能"
    scan = scan_skill_modules(target_dir)
    cap_table = render_module_capability_table(scan)
    existing_md = Path(target_dir) / "SKILL.md"
    (existing_name, existing_desc, existing_version,
     existing_keywords, existing_anchors) = _parse_existing_frontmatter(
        existing_md, name, description)
    if name_given:
        existing_name = name
    if description_given:
        existing_desc = description
    existing_desc = _update_description_numbers(existing_desc, scan)
    existing_desc = enrich_description_from_scan(scan, existing_desc, existing_name)
    parts = _build_skill_md_frontmatter(
        scan, existing_name, existing_desc, existing_version, name,
        existing_keywords, existing_anchors)
    parts = _insert_unmanaged_frontmatter(
        parts, _unmanaged_frontmatter_lines(existing_md))
    parts.extend(_build_skill_md_body_sections(
        scan, existing_name, cap_table, target_dir,
        existing_skill_category(target_dir) or "generic"))
    _write_skill_md(existing_md, "\n".join(parts) + "\n")
    return str(existing_md)
_MANAGED_FRONTMATTER_KEYS = frozenset({"name", "version", "description", "keywords"})
_STALE_TEST_METRIC_RE = re.compile(
    r"[ \t，,、；;]*"
    r"(?<![\dA-Za-z_.])(?:全部|全|all)?[ \t]*\d+[ \t]*个?[ \t]*"
    r"(?:测试[ \t]*(?:全部|全)?[ \t]*通过"
    r"|tests?[ \t]+(?:passed|passing))"
    r"(?=[ \t]*(?:[，,。；;、！!？?.]|$))",
    re.IGNORECASE)
def existing_skill_category(skill_dir: str) -> str:
    dir_text = fs_path_text(skill_dir)
    if not dir_text:
        return ""
    md_path = Path(dir_text) / "SKILL.md"
    if not md_path.exists():
        return ""
    try:
        frontmatter = parse_frontmatter_dict(read_skill_md_text(md_path))
    except (OSError, UnicodeDecodeError, ValueError, TypeError) as exc:
        _log.debug("existing_skill_category: 读取 %s 失败，按未提供处理: %s",
                   md_path, exc)
        return ""
    category = frontmatter.get("category") if isinstance(frontmatter, dict) else None
    return category.strip() if isinstance(category, str) else ""

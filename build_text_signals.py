from __future__ import annotations

import logging
import os
import re
from bisect import bisect_right
from dataclasses import dataclass
from functools import cache
from pathlib import Path
from typing import Any

from jwsgj.build_discover_text_doc import (
    body_opens_with_code_block,
    code_block_mask,
    inline_code_spans,
    referenced_local_paths,
)
from jwsgj.build_text_document import (
    ENTRY_DOC_NAME,
    first_content_paragraph,
    normalize_str_list,
    resource_dir_names,
    word_pattern,
)

_log = logging.getLogger(__name__)
__all__ = [
    'CODE_TOOL_INDICATORS',
    'COLLOQUIAL_INTENT_PATTERNS',
    'COLLOQUIAL_PATTERNS',
    'FILE_FORMAT_SKILL_INDICATORS',
    'FILE_SKILL_INDICATORS',
    'NATURAL_BOUNDARY_PATTERNS',
    'NEGATIVE_BOUNDARY_PATTERNS',
    'STRUCTURE_ACTION_PATTERNS',
    'STRUCTURE_TARGET_PATTERNS',
    'STRUCTURE_TRIGGER_PATTERNS',
    'TRIGGER_PATTERNS',
    'VAGUE_WORDS_CN',
    'VAGUE_WORDS_CN_ORDERED',
    'VAGUE_WORDS_EN',
    'VAGUE_WORDS_EN_ORDERED',
    'compile_patterns',
    'description_is_cjk_dominant',
    'extract_capabilities',
    'fenced_block_spans',
    'find_missing_keywords',
    'first_paragraph_issue',
    'first_sentence',
    'has_explicit_trigger_clause',
    'has_name_explanation',
    'mask_exclusion_context',
    'matches_any',
    'missing_action_target_signals',
    'normalize_matching_keywords',
    'normalize_name_field',
    'opens_with_action_verb',
    'opens_with_trigger_phrase',
    'refs_without_condition',
    'resource_dirs_for',
    'resource_path_pattern',
    'resource_reference_matches',
    'unreferenced_redundant_docs',
    'vague_word_spans',
    'word_boundary_pattern',
]
_CONTAINER_FORMS = (dict, list, tuple, set, frozenset)
def _normalize_text_value(value: Any) -> str:
    if isinstance(value, (bytes, bytearray)):
        return bytes(value).decode("utf-8", "ignore")
    return str(value)
def normalize_matching_keywords(keywords: Any) -> list[str]:
    is_set = isinstance(keywords, (set, frozenset))
    if isinstance(keywords, (bytes, bytearray)):
        items: list[str] = [_normalize_text_value(keywords)]
    elif isinstance(keywords, str):
        items = [keywords]
    elif isinstance(keywords, (list, tuple, set, frozenset)):
        items = [
            _normalize_text_value(k) for k in keywords
            if k and not isinstance(k, _CONTAINER_FORMS)
        ]
    else:
        return []
    parts = [
        part for item in items for part in re.split(r"[,，、]", item)
    ]
    normalized = normalize_str_list(parts)
    return sorted(normalized) if is_set else normalized
def _join_name_parts(raw: Any) -> str:
    return " ".join(
        text for text in (
            _normalize_text_value(x).strip() for x in raw
            if x is not None and not isinstance(x, _CONTAINER_FORMS))
        if text)
def normalize_name_field(raw: Any) -> str:
    if raw is None:
        return ""
    if isinstance(raw, (list, tuple)):
        return _join_name_parts(raw)
    if isinstance(raw, (dict, set, frozenset)):
        _log.debug("[Match] name 容器形态按空处理: %s", type(raw).__name__)
        return ""
    return _normalize_text_value(raw).strip()
VAGUE_WORDS_EN: set[str] = {
    "powerful",
    "flexible",
    "useful",
    "helpful",
    "comprehensive",
    "various",
    "multiple",
    "many",
    "things",
    "stuff",
    "assist",
    "help",
    "support",
    "aid",
    "facilitate",
    "efficient",
    "effective",
    "robust",
    "scalable",
}
VAGUE_WORDS_CN: set[str] = {
    "强大的",
    "灵活的",
    "好用的",
    "全面的",
    "综合的",
    "完善的",
    "各种",
    "多种",
    "很多",
    "一些",
    "相关",
    "辅助",
    "帮助",
    "支持",
    "协助",
    "方便",
    "高效的",
    "有效的",
    "稳健的",
    "可扩展的",
}
VAGUE_WORDS_EN_ORDERED: tuple[str, ...] = tuple(sorted(VAGUE_WORDS_EN))
VAGUE_WORDS_CN_ORDERED: tuple[str, ...] = tuple(sorted(VAGUE_WORDS_CN))
@cache
def compile_patterns(
    patterns: tuple[str, ...], ignorecase: bool
) -> tuple[re.Pattern[str], ...]:
    flags = re.IGNORECASE if ignorecase else 0
    return tuple(re.compile(p, flags) for p in patterns)
@cache
def word_boundary_pattern(word: str, ignore_case: bool = False) -> re.Pattern:
    return re.compile(word_pattern(word), re.IGNORECASE if ignore_case else 0)
_TRIGGER_CLAUSE_MARKER = r"时[，,]?\s*(?:使用|调用|加载|采用)本技能"
_EN_DOC_EXT_TRIGGER_PREFIX = (
    r"(?<![A-Za-z])(?:[A-Za-z]{2,}|[A-Za-z]+(?: and |, )[A-Za-z]+) \."
)
_EN_POSTPOSED_NEGATION_PATTERN = (
    r"\b(?:(?:is|are|was|were)(?:\s+not|n['’]t)\s+"
    r"|(?:(?:will|would|can|could|should|must|may|might|shall)\s+not|"
    r"cannot|can['’]?t|won['’]?t|"
    r"(?:could|would|should|must)n['’]?t)\s+be\s+"
    r"|(?:has|have|had)(?:\s+not|n['’]t)\s+been\s+)"
    r"(?:supported|allowed|handled|covered|processed|included)\b"
)
_EN_CAPABILITY_NEGATION_PATTERN = (
    r"\b(?:(?:should|would|could|can|does|do|did|will|must)\s+not|cannot|"
    r"can['’]?t|won['’]?t|"
    r"(?:should|would|could|does|do|did|must)n['’]?t)"
    r"(?!\s+only\b)\s+[A-Za-z]+"
)
_CN_CAPABILITY_NEGATION_PATTERN = (
    r"(?:不再|无法|不能|不会|不得|不要|不|未|勿)(?:支持|处理|负责|覆盖|提供|包含|包括|涉及|用于|"
    r"创建|编辑|修改|删除|生成|分析|读取|写入|提取|合并|拆分|转换|修复|清理|"
    r"诊断|扫描|检测|检查|测试|验证|优化|重构|管理|导出|导入|发布)"
)
TRIGGER_PATTERNS: list[str] = [
    r"当用户[需要]",
    r"当用户[提要]供",
    r"当用户[要想需]求",
    r"用[户][需提]要",
    r"(?:触发|激发)条件",
    r"(?<!不)适用于",
    r"(?<!不)涉及.*(?:文件|文档|表格|幻灯片|PDF|网页|代码)",
    r"[Ww]hen the user",
    r"(?<![Nn]ot )(?<!never )[Uu]se this (?:skill|when)",
    r"(?<![Nn]ot )(?<!never )[Tt]rigger(?:s?|ing?) when",
    r"(?<![Nn]ot )(?<!never )[Aa]ctivate(?:s?|ing?) (?:when|if)",
    r"(?<![Nn]ot )(?<!never )[Cc]all this skill when",
    r"(?<![Nn]ot )(?<!never )[Ii]nvoke this skill (?:when|for)",
    r"(?<![Nn]ot )(?<!never )[Cc]reates? or (?:edit|manage)",
    r"(?<![Nn]ot )(?<!never )[Pp]rovides? (?:support|capability)",
    _EN_DOC_EXT_TRIGGER_PREFIX + r"[A-Za-z0-9]{1,8}",
    r"\[MUST USE\]",
    r"MUST\s+USE",
    r"MUST\s+BE\s+INVOKED",
]
NEGATIVE_BOUNDARY_PATTERNS: list[str] = [
    r"不适用于",
    r"不(?:是|属于|处理|负责|覆盖|支持|提供|包含|包括|涉及|用于)",
    r"不要用于",
    r"请勿",
    r"不[\s]*应(?:触发|使用|调用|加载)",
    r"则不(?:应|会|能|属于)",
    r"则不应触发(?:本)?技能",
    r"则不应使用本技能",
    r"则不(?:属于|适用(?:于)?)本技能",
    r"若(?:主要|核心)?(?:产出|交付物)",
    r"(?:仅当|只有|只在)",
    r"不涉及(?:本技能|此技能)",
    r"NOT\s+for",
    r"DO\s+NOT\s+(?:use|trigger|invoke)",
    r"NEVER\s+(?:use|call|trigger)",
    _EN_CAPABILITY_NEGATION_PATTERN,
    _CN_CAPABILITY_NEGATION_PATTERN,
    r"not\s+applicable",
    r"not\s+for\s+non-",
    r"(?:If|When)\s+the\s+(?:main|primary)\s+(?:output|deliverable)\s+is",
    r"not\s+(?:intended|designed)\s+for",
    _EN_POSTPOSED_NEGATION_PATTERN,
]
COLLOQUIAL_PATTERNS: list[str] = [
    r"帮我",
    r"给我",
    r"我要",
    r"我想",
    r"能不能",
    r"代码[有没]问题",
    r"检查一下",
    r"(?:弄|搞|写|改)一下",
    r"help\s+me",
    r"i\s+(?:want|need)",
    r"can\s+you",
    r"take\s+a\s+look",
    r"check\s+(?:this|my)\s+code",
]
KEYWORD_SYNONYM_PATTERNS: dict[str, list[str]] = {
    "ocr": [r"(?:OCR|光学字符|文字识别|图片识别)"],
    "nlp": [r"(?:NLP|自然语言|文本处理)"],
    "ai": [r"(?:AI|人工智能|智能)"],
    "api": [r"(?:API|接口|调用)"],
}
CODE_TOOL_INDICATORS: list[str] = [
    r"代码[审诊][计查]",
    r"源码",
    r"代码质量",
    r"代码修复",
    r"反模式",
    r"自动化修复",
    r"代码重构",
    r"技能(?:文档|构建|生成|创建|诊断|打包)",
    r"SKILL\.md",
    r"__init__\.py",
    r"(?:create_skill|build_skill|diag_skill)",
    r"(?<![a-z0-9])python(?![a-z0-9])",
    r"(?<![a-z0-9])(?:shell|bash|powershell)(?![a-z0-9])",
    r"脚本",
    r"代码工具",
    r"编程",
]
FILE_FORMAT_SKILL_INDICATORS: list[str] = [
    r"\.docx",
    r"\.xlsx",
    r"\.pptx",
    r"\.pdf",
    r"\.csv",
    r"\.tsv",
    r"\.xls",
    r"\.dbt",
    r"\.ksheet",
    r"\.otl",
    r"(?<![a-z0-9])word(?:\s文档)?(?![a-z0-9])",
    r"(?<![a-z0-9])excel(?:\s表格)?(?![a-z0-9])",
    r"(?<![a-z0-9])powerpoint(?![a-z0-9])",
    r"(?<![a-z0-9])pdfs?(?:\s文件)?(?![a-z0-9])",
    r"表格文件",
    r"文档文件",
    r"幻灯片",
    r"演示文稿",
]
FILE_SKILL_INDICATORS: list[str] = [
    *FILE_FORMAT_SKILL_INDICATORS,
    r"文件格式",
    r"文件扩展名",
    r"文件",
    r"附件",
    r"(?<![a-z0-9])files?(?![a-z0-9])",
    r"(?<![a-z0-9])(?:format|extension|attachment)(?![a-z0-9])",
]
_COLLOQUIAL_INTENT_VERBS = (
    r"需要|想要|希望|要求|请求|期待|说|问|提到|提供|指定|表达|让|叫|需|要|想|能|可"
)
COLLOQUIAL_INTENT_PATTERNS: tuple[re.Pattern, ...] = compile_patterns(
    (
        r"帮(?:用户|你)?(?:把)?(?:代码|技能|文档)",
        r"(?:用户|使用者)[^。；;！!？?，,\n]*?(?:"
        + _COLLOQUIAL_INTENT_VERBS + r")",
    ),
    False,
)
_CAPABILITY_VERBS_CN: tuple[str, ...] = (
    "创建", "编辑", "修改", "删除", "移除", "清除", "生成", "分析", "处理",
    "读取", "写入", "提取", "合并", "拆分", "转换", "修复", "清理", "诊断",
    "扫描", "检测", "检查", "测试", "验证", "优化", "重构", "构建", "搭建",
    "管理", "维护", "操作", "打包", "初始化", "分发", "下载", "上传", "搜索",
    "查询", "导出", "导入", "格式化", "计算", "对比", "监控", "部署", "备份",
    "恢复", "审查", "审核", "审批", "评估", "识别", "分类", "归档", "校对",
    "排版", "设计", "规划", "预测", "推荐", "匹配", "路由", "调度", "编排",
    "记录", "汇总", "统计", "展示", "渲染", "解析", "采集", "标注", "训练",
    "推理", "评测", "审计", "起草", "录入", "核对", "结算", "对账", "开票",
    "招聘", "排班", "采购", "翻译", "摘要", "归纳", "检索", "追踪", "告警",
    "通知", "提醒", "授权", "认证", "加密", "解密", "压缩", "解压", "安装",
    "配置", "迁移", "同步", "缓存", "抓取", "编译", "调试", "发布", "回滚",
    # 工程/图形域动词：缺登记会让「校准像素标定」「绘制图元」这类合法的
    # 动词+对象能力项在 _dedupe_capabilities 里被当成噪声丢弃。
    "校准", "校正", "绘制", "测量", "量测", "对齐", "叠加", "标定",
)
_CAPABILITY_VERBS_EN: tuple[str, ...] = (
    "create", "edit", "modify", "update", "delete", "remove", "clear",
    "generate", "analyze", "analyse", "process", "read", "write",
    "extract", "merge", "split", "convert", "fix", "clean", "diagnose",
    "diag", "scan", "detect", "check", "test", "validate", "verify",
    "optimize", "refactor", "build", "manage", "maintain", "package",
    "distribute", "download", "upload", "search", "query", "export",
    "import", "format", "calculate", "compute", "compare", "monitor",
    "deploy", "backup", "restore", "review", "assess", "identify",
    "classify", "archive", "proofread", "design", "plan", "forecast",
    "recommend", "match", "route", "schedule", "orchestrate", "record",
    "summarize", "aggregate", "count", "present", "render", "parse",
    "crawl", "collect", "annotate", "train", "infer", "evaluate", "audit",
    "draft", "approve", "reconcile", "invoice", "recruit", "procure",
    "translate",
)
_CAPABILITY_OBJECTS_CN: tuple[str, ...] = (
    "文档", "表格", "幻灯片", "演示文稿", "PDF", "数据", "文件", "代码",
    "脚本", "报告", "网页", "网站", "技能", "记忆", "经验", "规则", "描述",
    "架构", "模块", "函数", "依赖", "死代码", "盲点", "异常", "接口", "循环",
    "凭据", "路径", "论文", "视频", "音频", "图片", "图表", "应用", "项目",
    "合同", "条款", "风险", "合规", "发票", "账单", "订单", "库存", "客户",
    "供应商", "员工", "简历", "日程", "会议", "邮件", "消息", "通知", "日志",
    "配置", "环境", "密钥", "权限", "账号", "数据库", "表结构", "索引",
    "缓存", "队列", "任务", "流程", "工作流", "模型", "语料", "标注",
    "译文", "字幕", "文案", "素材", "版面", "模板", "指标", "报表", "预算",
    "财务", "销售", "采购", "招聘", "排班",
)
_CAPABILITY_OBJECTS_EN: tuple[str, ...] = (
    "documents", "files", "tables", "sheets", "spreadsheets",
    "presentations", "slides", "PDFs", "data", "code", "scripts",
    "skills", "papers", "websites", "applications", "projects", "reports",
    "images", "charts", "contracts", "clauses", "risks", "invoices",
    "orders", "inventory", "customers", "suppliers", "employees",
    "resumes", "schedules", "meetings", "emails", "messages",
    "notifications", "logs", "configurations", "environments", "secrets",
    "permissions", "accounts", "databases", "schemas", "indexes", "caches",
    "queues", "tasks", "workflows", "models", "corpora", "annotations",
    "translations", "subtitles", "copy", "assets", "layouts", "templates",
    "metrics", "budgets", "finances", "sales", "procurement",
)
def _longest_first_alternation(words: tuple[str, ...]) -> str:
    return "|".join(re.escape(w) for w in sorted(words, key=len, reverse=True))
def _plural_alternation(words: tuple[str, ...]) -> str:
    forms: set[str] = set()
    for word in words:
        forms.add(word)
        if word.endswith("s"):
            singular = word[:-2] if word.endswith(("xes", "zes")) else word[:-1]
            forms.add(singular)
        elif (len(word) > 2 and word.endswith("y")
              and word[-2].lower() not in "aeiou"):
            forms.add(word[:-1] + "ies")
        else:
            forms.add(word + "s")
    return "|".join(
        re.escape(word) for word in sorted(forms, key=lambda w: (-len(w), w))
    )
_CAPABILITY_VERBS_CN_ALTERNATION = _longest_first_alternation(_CAPABILITY_VERBS_CN)
_CAPABILITY_VERBS_EN_ALTERNATION = _longest_first_alternation(_CAPABILITY_VERBS_EN)
_CAPABILITY_OBJECTS_CN_ALTERNATION = _longest_first_alternation(
    _CAPABILITY_OBJECTS_CN)
_CAPABILITY_OBJECTS_EN_ALTERNATION = _plural_alternation(_CAPABILITY_OBJECTS_EN)
_EN_VOWEL_CHARS = frozenset("aeiou")
_EN_DOUBLING_ING = frozenset({"split", "scan", "plan", "infer", "format", "diag"})
_EN_DOUBLING_ED = frozenset({"scan", "plan", "infer", "format", "diag"})
_EN_IRREGULAR_FORMS: dict[str, tuple[str, ...]] = {
    "build": ("built",),
    "proofread": ("proofread",),
    "read": ("read",),
    "split": ("split",),
    "write": ("wrote", "written"),
}
def _en_verb_forms(word: str) -> tuple[str, ...]:
    base = word.lower()
    forms = {base, *(_EN_IRREGULAR_FORMS.get(base) or ())}
    irregular = base in _EN_IRREGULAR_FORMS
    if base.endswith("y") and len(base) > 2 and base[-2] not in _EN_VOWEL_CHARS:
        forms.update({base[:-1] + "ies", base[:-1] + "ied", base + "ing"})
    elif base.endswith("e"):
        forms.add(base + "s")
        if base.endswith("ee"):
            forms.add(base + "ing")
        else:
            forms.add(base[:-1] + "ing")
            if not irregular:
                forms.add(base + "d")
    else:
        forms.add(base + "es" if base.endswith(("s", "x", "z", "ch", "sh"))
                  else base + "s")
        if base in _EN_DOUBLING_ING:
            forms.add(base + base[-1] + "ing")
        else:
            forms.add(base + "ing")
        if not irregular:
            if base in _EN_DOUBLING_ED:
                forms.add(base + base[-1] + "ed")
            else:
                forms.add(base + "ed")
    return tuple(sorted(forms))
def _en_verb_alternation(words: tuple[str, ...]) -> str:
    forms: dict[str, None] = {}
    for word in words:
        for form in _en_verb_forms(word):
            forms.setdefault(form, None)
    return "|".join(
        re.escape(form) for form in sorted(forms, key=len, reverse=True))
_EN_VERB_ALTERNATION = _en_verb_alternation(_CAPABILITY_VERBS_EN)
STRUCTURE_ACTION_PATTERNS: list[str] = [
    r"(?:" + _CAPABILITY_VERBS_CN_ALTERNATION + r")",
    r"(?:" + _EN_VERB_ALTERNATION + r")",
]
STRUCTURE_TARGET_PATTERNS: list[str] = [
    r"(?:" + _CAPABILITY_OBJECTS_CN_ALTERNATION + r")",
    r"(?:" + _CAPABILITY_OBJECTS_EN_ALTERNATION + r")",
]
STRUCTURE_TRIGGER_PATTERNS: list[str] = [
    (
        r"(?:当用户|用[户]|(?<!不)涉及|(?<!不)适用于|(?<!不)(?<!不[应会能要])触发"
        r"|(?<!not )(?<!never )Use this|when the user"
        r"|(?<!not )(?<!never )trigger|(?<!not )(?<!never )activate"
        r"|(?<!not )(?<!never )For .* operations|(?<!not )(?<!never )Provides?)"
    ),
]
NATURAL_BOUNDARY_PATTERNS: list[str] = [
    r"不(?:适用于|属于|处理|负责|覆盖|涉及(?:本|此)?(?:技能|模块))",
    r"不(?:应|会|能)(?:触发|使用|调用|加载)(?:本)?技能",
    r"不(?:属于|适用(?:于)?)本技能",
    r"则不(?:应|会|能|属于)",
    r"若(?:主要|核心)?(?:产出|交付物|目的)",
    r"(?:仅当|只有|只在)",
    r"NOT\s+(?:for|applicable|intended)",
    r"DO\s+NOT\s+(?:use|trigger|invoke)",
    r"NEVER\s+(?:use|call|trigger)",
    _EN_CAPABILITY_NEGATION_PATTERN,
    _CN_CAPABILITY_NEGATION_PATTERN,
    r"not\s+applicable",
    r"not\s+for\s+non-",
    r"not\s+(?:intended|designed)\s+for",
    r"(?:If|When)\s+the\s+(?:main|primary)\s+(?:output|deliverable)",
    _EN_POSTPOSED_NEGATION_PATTERN,
]
def matches_any(patterns: Any, text: str) -> bool:
    return any(
        p.search(text) if isinstance(p, re.Pattern)
        else re.search(p, text, re.IGNORECASE)
        for p in patterns
    )
_SENTENCE_TERMINATORS = re.compile(r"[。；;.\n]")
_TRIGGER_OPEN_PATTERN = re.compile(
    r"(?:当用户|Use this|\[?MUST\s+(?:USE|BE\s+INVOKED)\]?)", re.IGNORECASE)
_CN_NEGATION_PREFIXES = frozenset("不无未非没勿")
def first_sentence(description: str) -> str:
    return _SENTENCE_TERMINATORS.split(description.strip(), maxsplit=1)[0].strip()
def opens_with_action_verb(description: str) -> bool:
    head = first_sentence(description)
    if not head:
        return False
    for pattern in STRUCTURE_ACTION_PATTERNS:
        matched = re.match(pattern, head, re.IGNORECASE)
        if matched is None:
            continue
        token = matched.group(0)
        following = head[matched.end():matched.end() + 1]
        if token.isascii() and re.fullmatch(r"[A-Za-z0-9_]", following):
            continue
        return True
    return False
def opens_with_trigger_phrase(description: str) -> bool:
    return _TRIGGER_OPEN_PATTERN.match(first_sentence(description)) is not None
def vague_word_spans(word: str, text: str) -> list[tuple[int, int]]:
    if not word or not text:
        return []
    exclusions = _exclusion_spans(text)
    def is_positive(start: int) -> bool:
        return (
            (start == 0 or text[start - 1] not in _CN_NEGATION_PREFIXES)
            and not _capability_position_is_negative(text, start, exclusions)
        )
    if word.isascii():
        pattern = word_boundary_pattern(word, ignore_case=True)
        return [
            (m.start(), m.end()) for m in pattern.finditer(text)
            if is_positive(m.start())
        ]
    spans: list[tuple[int, int]] = []
    start = text.find(word)
    while start != -1:
        if is_positive(start):
            spans.append((start, start + len(word)))
        start = text.find(word, start + len(word))
    return spans
def has_explicit_trigger_clause(description: str) -> bool:
    for match in re.finditer(_TRIGGER_CLAUSE_MARKER, description):
        head = _SENTENCE_TERMINATORS.split(description[:match.start()])[-1]
        head = re.split(r"[，,]", head)[-1]
        if matches_any(STRUCTURE_ACTION_PATTERNS, head) or matches_any(
                STRUCTURE_TARGET_PATTERNS, head):
            return True
    return False
def _contains_ascii_keyword(description: str, keyword: str) -> bool:
    left = r"(?<![A-Za-z0-9_])" if re.match(r"[A-Za-z0-9_]", keyword[:1]) else ""
    right = r"(?![A-Za-z0-9_])" if re.match(r"[A-Za-z0-9_]", keyword[-1:]) else ""
    return re.search(left + re.escape(keyword) + right, description, re.IGNORECASE) is not None
def _matches_keyword_synonym(patterns: list[str], description: str) -> bool:
    return any(
        re.search(
            r"(?<![A-Za-z0-9_])(?:" + pattern + r")(?![A-Za-z0-9_])",
            description,
            re.IGNORECASE,
        )
        for pattern in patterns
    )
_CJK_CHAR_RE = re.compile(r"[\u4e00-\u9fff]")
_ASCII_WORD_RE = re.compile(r"[A-Za-z]{2,}")
_CAPABILITY_TERM_TOKENS = frozenset(_CAPABILITY_VERBS_CN) | frozenset(
    _CAPABILITY_OBJECTS_CN)
def _tile_capability_terms(keyword: str) -> tuple[str, ...] | None:
    length = len(keyword)
    best: list[tuple[str, ...] | None] = [None] * (length + 1)
    best[0] = ()
    for start in range(length):
        if best[start] is None:
            continue
        for end in range(length, start + 1, -1):
            token = keyword[start:end]
            if token not in _CAPABILITY_TERM_TOKENS:
                continue
            candidate = best[start] + (token,)
            if best[end] is None or len(candidate) > len(best[end]):
                best[end] = candidate
    return best[length]
def description_is_cjk_dominant(description: str) -> bool:
    cjk_count = len(_CJK_CHAR_RE.findall(description))
    ascii_word_count = len(_ASCII_WORD_RE.findall(description))
    return cjk_count >= max(4, ascii_word_count * 2)
def find_missing_keywords(
    description: str, meaningful_kws: list[str],
) -> list[str]:
    capability_text = mask_exclusion_context(description)
    desc_lower = capability_text.lower()
    cjk_dominant = description_is_cjk_dominant(description)
    missing_core = []
    for kw in meaningful_kws:
        kw_lower = kw.lower()
        if _matches_keyword_synonym(
            KEYWORD_SYNONYM_PATTERNS.get(kw_lower, []), capability_text
        ):
            continue
        if kw_lower.isascii() != (not cjk_dominant):
            continue
        kw_root = re.sub(r"[_\-]", " ", kw_lower)
        if kw_lower.isascii():
            direct_hit = any(
                _contains_ascii_keyword(capability_text, candidate)
                for candidate in dict.fromkeys((kw_root, kw_lower))
            )
        else:
            direct_hit = kw_root in desc_lower or kw_lower in desc_lower
        if direct_hit:
            continue
        terms = _tile_capability_terms(kw_lower)
        if terms and len(terms) >= 2 and all(
                term in desc_lower for term in terms):
            continue
        missing_core.append(kw)
    return missing_core
def has_name_explanation(description: str) -> bool:
    for pm in re.finditer(r"[\(（]([^)）]*)[\)）]", description):
        inner = pm.group(1).strip()
        if not inner:
            continue
        if re.fullmatch(
            r"(?:v(?:er(?:sion)?)?[\s.:]*[\d.]+|[\d.]+(?:\s*(?:nd|rd|th|st))?)",
            inner,
            re.IGNORECASE,
        ):
            continue
        if re.search(r"[\u4e00-\u9fff]|[A-Za-z]", inner):
            return True
    return False
def missing_action_target_signals(description: str) -> list[str]:
    capability_text = mask_exclusion_context(description)
    missing = []
    if not matches_any(STRUCTURE_ACTION_PATTERNS, capability_text):
        missing.append("操作动词")
    if not matches_any(STRUCTURE_TARGET_PATTERNS, capability_text):
        missing.append("目标对象")
    return missing
_NEG_DECLARATION_WORDS: tuple[str, ...] = (
    "不支持", "不处理", "不负责", "不适用", "不允许", "不接受", "不包含",
    "不包括", "不用于", "不要用于", "禁止",
)
_NEG_MODAL_WORDS: tuple[str, ...] = (
    "无法", "不能", "不会", "无需", "无须", "不需", "不必", "不需要", "难以",
    "不再",
)
_NEGATIVE_HEAD_WORDS: tuple[str, ...] = _NEG_DECLARATION_WORDS + _NEG_MODAL_WORDS
_NEG_CAP_PREFIX_RE = re.compile(
    r"^(?:" + "|".join(_NEGATIVE_HEAD_WORDS) + r")"
)
_NEG_CLAUSE_HEAD_RE = re.compile(
    r"^\s*(?:" + "|".join(_NEGATIVE_HEAD_WORDS) + r")"
)
_ORDINAL_INT_PATTERN = r"(?:[1-9]\d{0,2})"
_CLAUSE_HEAD_LOOKBEHIND = r"(?:(?<=[\n。；;！!？?：:，,、])|^)"
_BULLET_ITEM_BOUNDARY_PATTERN = (
    r"|" + _CLAUSE_HEAD_LOOKBEHIND + r"[ \t]*(?:[-*•·])[ \t]+"
)
_ORDINAL_OPEN_PREFIX = r"(?:[（(][ \t]*)?"
_NUMBERED_ITEM_BOUNDARY_PATTERN = (
    _ORDINAL_OPEN_PREFIX + r"(?<![\dA-Za-z])" + _ORDINAL_INT_PATTERN
    + r"(?:[.．]\d{1,3})*[.．)）](?!\d)[ \t]*"
    r"|" + _CLAUSE_HEAD_LOOKBEHIND + r"[ \t]*" + _ORDINAL_OPEN_PREFIX
    + _ORDINAL_INT_PATTERN + r"(?:[.．]\d{1,3}){1,3}[ \t]+"
    + _BULLET_ITEM_BOUNDARY_PATTERN
)
_NEG_VERB_PRECEDE_WORDS: tuple[str, ...] = (
    "不负责", "不支持", "不处理", "不适用", "不用于", "不要用于",
    "不", "不要", "未", "勿", "无法", "不能", "不得", "不会", "不用", "无需",
    "无须", "不需", "不必", "不需要", "难以", "不再", "禁止",
)
def _neg_verb_precede_guard(words: tuple[str, ...]) -> str:
    return "".join("(?<!" + re.escape(word) + ")" for word in words)
_NEG_VERB_PRECEDE_GUARD = _neg_verb_precede_guard(_NEG_VERB_PRECEDE_WORDS)
_EN_NEG_WORDS: tuple[str, ...] = (
    r"not(?!\s+only\b)", "never", "cannot",
    "don['’]?t", "doesn['’]?t", "didn['’]?t", "isn['’]?t", "aren['’]?t",
    "wasn['’]?t", "weren['’]?t", "can['’]?t", "couldn['’]?t",
    "shouldn['’]?t", "wouldn['’]?t", "hasn['’]?t", "haven['’]?t",
    "hadn['’]?t", "mustn['’]?t", "needn['’]?t", "won['’]?t", "shan['’]?t",
)
_EN_NEG_SENTINEL_RE = re.compile(
    r"\b(?:" + "|".join(_EN_NEG_WORDS) + r")\b", re.IGNORECASE
)
_EN_NEG_DECLARATION_PATTERNS: tuple[str, ...] = (
    (
        r"\b(?:does|do|did|will|would|can|could|should|is|are|was|were)\s+not\s+"
        r"(?:support|supports|supporting|handle|handles|handling|cover|covering|"
        r"process|processing|include|including|accept|accepting|allow|allowing)\b"
    ),
    r"\bno\s+(?:support|handling|coverage|processing)\b",
    r"\bnot\s+(?:supported|handled|covered|processed|included|allowed)\b",
)
_EN_NEG_DECLARATION_RE = re.compile(
    "|".join(_EN_NEG_DECLARATION_PATTERNS), re.IGNORECASE)
_EN_WITHOUT_CAPABILITY_PATTERN = (
    r"\bwithout\s+(?:(?:" + _EN_VERB_ALTERNATION + r")(?![A-Za-z])"
    r"|support(?:ing)?\b|coverage\b)"
)
_EN_CLAUSE_HEAD_NEG_RE = re.compile(
    r"^(?:no|not(?!\s+only\b)|never|excluding|except|neither|nor)\b"
    r"|^" + _EN_WITHOUT_CAPABILITY_PATTERN
    + r"|^\W{0,3}(?:it|this|that|they|the\s+\w+)\s+"
    r"(?:does|do|did|is|are|was|were|can|could|will|would|should)\s+not\b",
    re.IGNORECASE,
)
_CN_VERB_PATTERN = r"(?:" + _CAPABILITY_VERBS_CN_ALTERNATION + r")"
_CN_OBJ_PATTERN = r"(?:" + _CAPABILITY_OBJECTS_CN_ALTERNATION + r")"
_NEG_ANCHOR_VERB_PATTERN = (
    r"(?:" + _CAPABILITY_VERBS_CN_ALTERNATION + r"|包括|包含|涉及)")
_NEG_SCOPE_ACTIVATION_RE = re.compile(
    "(?:" + "|".join(sorted(_NEG_VERB_PRECEDE_WORDS, key=len, reverse=True))
    + ")(?:" + _NEG_ANCHOR_VERB_PATTERN + ")"
)
_NEG_DECLARATION_SEARCH_RE = re.compile(
    "(?:" + "|".join(_NEG_DECLARATION_WORDS) + ")"
)
_SCOPE_CONDUCTION_COMMA_RE = re.compile(
    r"[，,](?=\s*(?:包括|包含|including)\s*[：:]?)"
)
_SCOPE_CONDUCTION_NEWLINE_RE = re.compile(
    r"\r?\n(?=[ \t\r\n]*(?:包括|包含|including)\s*[：:]?)"
)
_COORDINATED_CAPABILITY_START_PATTERN = (
    r"\s*(?:(?:and|or)\s+|[和及或]\s*)?(?:"
    + _CN_VERB_PATTERN + r"|" + _EN_VERB_ALTERNATION + r"(?![A-Za-z]))"
)
_SCOPE_COORDINATED_COMMA_RE = re.compile(
    r"[，,](?=" + _COORDINATED_CAPABILITY_START_PATTERN + r")",
    re.IGNORECASE,
)
_COORDINATED_CAPABILITY_START_RE = re.compile(
    "^" + _COORDINATED_CAPABILITY_START_PATTERN, re.IGNORECASE)
_NEG_PRECEDE_WINDOW = max(len(_w) for _w in _NEG_VERB_PRECEDE_WORDS)
_SEGMENT_BOUNDARY_CHARS = "。；;！!？?，,\n"
_EN_SENTENCE_END_PATTERN = r"\.(?=\s|$)"
_CN_SENTENCE_END_CHARS = "。！!？?\n"
_SENTENCE_END_PATTERN = (
    "[" + re.escape(_CN_SENTENCE_END_CHARS) + "]|" + _EN_SENTENCE_END_PATTERN
)
_CN_POSITIVE_RESET_PATTERN = r"(?:即可|就能|便可|则可|皆可|就可以|都能够|方能)"
_CN_CONTRASTIVE_BOUNDARY_PATTERN = r"(?:但是|但|然而|却|而是)"
_EN_CONTRASTIVE_BOUNDARY_PATTERN = r"\b(?:but|however|yet|whereas)\b"
_EN_SENTENCE_END_RE = re.compile(_EN_SENTENCE_END_PATTERN)
_SEGMENT_BOUNDARY_RE = re.compile(
    r"[" + re.escape(_SEGMENT_BOUNDARY_CHARS) + r"]"
    r"|" + _EN_SENTENCE_END_PATTERN
    + r"|" + _NUMBERED_ITEM_BOUNDARY_PATTERN
    + r"|" + _CN_CONTRASTIVE_BOUNDARY_PATTERN
    + r"|" + _CN_POSITIVE_RESET_PATTERN
    + r"|" + _EN_CONTRASTIVE_BOUNDARY_PATTERN,
    re.IGNORECASE,
)
_NEG_SCOPE_SEARCH_RES: tuple[re.Pattern[str], ...] = (
    _NEG_DECLARATION_SEARCH_RE,
    _NEG_SCOPE_ACTIVATION_RE,
    _EN_NEG_SENTINEL_RE,
)
_SEGMENT_INDEX_CACHE_TEXT_MIN = 512
_SEGMENT_INDEX_CACHE_LIMIT = 8
def _blank_out(match: re.Match[str]) -> str:
    return " " * len(match.group(0))
def _segment_starts(text: str) -> tuple[int, ...]:
    starts = [0]
    starts.extend(_m.end() for _m in _SEGMENT_BOUNDARY_RE.finditer(text))
    return tuple(starts)
def _segment_anchor_ends(text: str, start: int, end: int) -> tuple[int, ...]:
    segment = text[start:end]
    ends: list[int] = []
    for pattern in _NEG_SCOPE_SEARCH_RES:
        ends.extend(start + _m.end() for _m in pattern.finditer(segment))
    return tuple(sorted(ends))
@dataclass(frozen=True)
class _SegmentIndex:
    raw_starts: tuple[int, ...]
    scope_starts: tuple[int, ...]
    anchor_ends: tuple[tuple[int, ...], ...]
_SEGMENT_INDEX_CACHE: dict[str, _SegmentIndex] = {}
def _build_segment_index(description: str) -> _SegmentIndex:
    neutralized = _SCOPE_CONDUCTION_COMMA_RE.sub(_blank_out, description)
    neutralized = _SCOPE_CONDUCTION_NEWLINE_RE.sub(_blank_out, neutralized)
    neutralized = _SCOPE_COORDINATED_COMMA_RE.sub(_blank_out, neutralized)
    scope_starts = _segment_starts(neutralized)
    bounds = (*scope_starts[1:], len(neutralized))
    return _SegmentIndex(
        _segment_starts(description),
        scope_starts,
        tuple(
            _segment_anchor_ends(neutralized, start, end)
            for start, end in zip(scope_starts, bounds, strict=True)
        ),
    )
def _segment_index(description: str) -> _SegmentIndex:
    if len(description) < _SEGMENT_INDEX_CACHE_TEXT_MIN:
        return _build_segment_index(description)
    index = _SEGMENT_INDEX_CACHE.get(description)
    if index is None:
        index = _build_segment_index(description)
        if len(_SEGMENT_INDEX_CACHE) >= _SEGMENT_INDEX_CACHE_LIMIT:
            _SEGMENT_INDEX_CACHE.clear()
        _SEGMENT_INDEX_CACHE[description] = index
    return index
def _segment_at(starts: tuple[int, ...], pos: int) -> int:
    return bisect_right(starts, pos) - 1
_INCLUDE_INTRO_RE = re.compile(
    r"(?:包括|包含|including)[：:]?\s*(.+?)(?:"
    + _SENTENCE_END_PATTERN + r"|$)",
    re.MULTILINE | re.IGNORECASE,
)
_INTRO_NEG_PREFIX_RE = re.compile(
    r"(?:" + "|".join(
        sorted(_NEG_VERB_PRECEDE_WORDS + ("非",), key=len, reverse=True))
    + r")"
    r"|\b(?:" + "|".join(_EN_NEG_WORDS) + r")",
    re.IGNORECASE,
)
_NEG_INTRO_BEFORE_RE = re.compile(
    r"(?:"
    + _INTRO_NEG_PREFIX_RE.pattern
    + r")[ \t]*(?=(?:包括|包含|including))",
    re.IGNORECASE,
)
_INCLUDE_ENUM_END_RE = re.compile(_SENTENCE_END_PATTERN)
def _negated_include_spans(description: str) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    for _m in _NEG_INTRO_BEFORE_RE.finditer(description):
        end_match = _INCLUDE_ENUM_END_RE.search(description, _m.end())
        spans.append((
            _m.start(),
            end_match.start() if end_match else len(description),
        ))
    return spans
def _in_negative_verb_scope(description: str, pos: int) -> bool:
    index = _segment_index(description)
    anchors = index.anchor_ends[_segment_at(index.scope_starts, pos)]
    return bisect_right(anchors, pos) > 0
_EN_POSTPOSED_NEGATION_RE = re.compile(
    _EN_POSTPOSED_NEGATION_PATTERN, re.IGNORECASE)
_EXCLUSION_CUE_RE = re.compile(
    r"不适用于|不(?:支持|处理|负责|覆盖|提供|包含|包括|涉及|用于|属于)"
    r"|不是(?!只|仅)|并非(?!只|仅)"
    r"|不要用于|请勿|切勿|禁止"
    r"|" + "|".join(sorted(_NEG_MODAL_WORDS, key=len, reverse=True))
    + r"|" + _CN_CAPABILITY_NEGATION_PATTERN
    + r"|若(?:主要|核心)?(?:产出|交付物)"
    r"|NOT\s+for|DO\s+NOT|NEVER|not\s+applicable"
    r"|not\s+(?:intended|designed)\s+for"
    r"|does\s+not\s+(?:handle|cover|process|support)"
    r"|If\s+the\s+(?:main|primary)\s+(?:output|deliverable)\s+is"
    r"|\b(?:excluding|except)\b|" + _EN_WITHOUT_CAPABILITY_PATTERN
    + r"|" + _EN_POSTPOSED_NEGATION_PATTERN
    + r"|" + _EN_NEG_SENTINEL_RE.pattern,
    re.IGNORECASE,
)
_EXCLUSION_CLAUSE_END_RE = re.compile(
    r"[" + re.escape(_SEGMENT_BOUNDARY_CHARS) + r"]"
    r"|" + _EN_SENTENCE_END_PATTERN
    + r"|" + _CN_CONTRASTIVE_BOUNDARY_PATTERN
    + r"|" + _CN_POSITIVE_RESET_PATTERN
    + r"|" + _EN_CONTRASTIVE_BOUNDARY_PATTERN,
    re.IGNORECASE,
)
_EN_FRONTED_EXCLUSION_RE = re.compile(
    r"^(?:without\b|excluding\b|except\b)", re.IGNORECASE)
_EN_BASE_CAPABILITY_START_RE = re.compile(
    r"^\s*(?:(?:and|or)\s+)?(?:"
    + _CAPABILITY_VERBS_EN_ALTERNATION + r")(?![A-Za-z])",
    re.IGNORECASE,
)
def _exclusion_spans(description: str) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    for cue in _EXCLUSION_CUE_RE.finditer(description):
        boundary = _EXCLUSION_CLAUSE_END_RE.search(description, cue.end())
        while boundary is not None and boundary.group(0) in ",，":
            next_boundary = _EXCLUSION_CLAUSE_END_RE.search(
                description, boundary.end()
            )
            continuation_end = (
                next_boundary.start() if next_boundary else len(description)
            )
            continuation = description[boundary.end():continuation_end]
            is_file_list_item = (
                continuation.strip()
                and matches_any(FILE_SKILL_INDICATORS, continuation)
                and not matches_any(STRUCTURE_ACTION_PATTERNS, continuation)
                and re.match(r"\s*(?:this|these|those|it|such)\b",
                             continuation, re.IGNORECASE) is None
            )
            is_coordinated_capability = (
                _COORDINATED_CAPABILITY_START_RE.match(continuation) is not None)
            if (is_coordinated_capability
                    and _EN_FRONTED_EXCLUSION_RE.match(cue.group(0))
                    and _EN_BASE_CAPABILITY_START_RE.match(continuation)):
                is_coordinated_capability = False
            if not (is_file_list_item or is_coordinated_capability):
                break
            boundary = next_boundary
        start = cue.start()
        if _EN_POSTPOSED_NEGATION_RE.fullmatch(cue.group(0)):
            index = _segment_index(description)
            start = index.raw_starts[_segment_at(index.raw_starts, start)]
        spans.append((start, boundary.start() if boundary else len(description)))
    return spans
def mask_exclusion_context(description: str) -> str:
    spans = _exclusion_spans(description)
    if not spans:
        return description
    chars = list(description)
    for start, end in spans:
        chars[start:end] = " " * (end - start)
    return "".join(chars)
def _first_verb_in_negative_scope(text: str) -> bool:
    _m = re.search(_NEG_ANCHOR_VERB_PATTERN, text)
    if _m is None or _m.start() == 0:
        return False
    window_start = max(0, _m.start() - _NEG_PRECEDE_WINDOW)
    _precede = text[window_start:_m.start()]
    if any(_precede.endswith(_w) for _w in _NEG_VERB_PRECEDE_WORDS):
        return True
    return _EN_NEG_SENTINEL_RE.search(_precede) is not None
def _head_declared_negative(text: str) -> bool:
    _m = re.search(_NEG_ANCHOR_VERB_PATTERN, text)
    _head = text[:_m.start()] if _m else text
    return (_NEG_DECLARATION_SEARCH_RE.search(_head) is not None
            or _EN_NEG_DECLARATION_RE.search(_head) is not None)
def _segment_head_is_negative(description: str, pos: int) -> bool:
    index = _segment_index(description)
    seg_start = index.raw_starts[_segment_at(index.raw_starts, pos)]
    head = description[seg_start:pos]
    return (_NEG_CLAUSE_HEAD_RE.match(head) is not None
            or _EN_CLAUSE_HEAD_NEG_RE.match(head) is not None)
def _capability_position_is_negative(
    description: str, pos: int,
    exclusions: list[tuple[int, int]] | None = None,
) -> bool:
    if (_segment_head_is_negative(description, pos)
            or _in_negative_verb_scope(description, pos)):
        return True
    spans = _exclusion_spans(description) if exclusions is None else exclusions
    return any(start <= pos < end for start, end in spans)
_VERB_TAIL_PATTERN = (
    r"(?=((?:[\s，、和及或]*(?:" + _CN_VERB_PATTERN + r"))*))\2"
)
_CAPABILITY_LIST_AUDIENCE_TERM = (
    r"(?:开发者|测试工程师|安全审计|架构师|管理者|用户|工程师|管理员|审计师)"
)
_CAPABILITY_LIST_CONTEXT_RE = re.compile(
    r"任一\s*(?:关键词|词表|标签)(?=\s*(?:$|[，,。；;：:]|时|即|则))"
    r"|(?:关键词|词表|角色|标签)(?:清单|列表)?\s*(?:如下|包括|包含|[:：])"
    r"|面向\s*" + _CAPABILITY_LIST_AUDIENCE_TERM
    + r"(?:\s*、\s*" + _CAPABILITY_LIST_AUDIENCE_TERM + r")+",
    re.IGNORECASE,
)
_LIST_CONTEXT_BOUNDARY_RE = re.compile(
    r"[。！!？?]|(?<!\d)\.(?=\s|$)"
    + r"|\r?\n[ \t]*\r?\n"
    + r"|" + _CN_CONTRASTIVE_BOUNDARY_PATTERN
    + r"|" + _EN_CONTRASTIVE_BOUNDARY_PATTERN,
    re.IGNORECASE,
)
def _clause_containing(description: str, pos: int) -> str:
    start = 0
    for boundary in _LIST_CONTEXT_BOUNDARY_RE.finditer(description, 0, pos):
        start = boundary.end()
    following = _LIST_CONTEXT_BOUNDARY_RE.search(description, pos)
    return description[start:(
        following.start() if following else len(description))]
def _is_capability_list_mention(description: str, pos: int) -> bool:
    return _CAPABILITY_LIST_CONTEXT_RE.search(
        _clause_containing(description, pos)) is not None
_TAIL_STOP_CHARS = "「」『』“”‘’《》【】（）()[]"
_TAIL_DANGLING_CHARS = "和及或与"
_CAP_TAIL_BOUNDARY_RE = re.compile(
    r"时[，,]?\s*(?:使用|调用|加载|采用)本技能"
    r"|(?<![不])(?:但是|但|然而|不过|却|而是)"
    r"|(?:以及|并且|同时|然后|用于|以便|从而)"
    r"|(?:例如|比如|譬如|即|也就是说)"
    + r"|" + _CN_POSITIVE_RESET_PATTERN
    + r"|\b(?:but|however|and|plus|while|whereas)\b",
    re.IGNORECASE,
)
_CAP_TAIL_SUFFIX_RE = re.compile(r"(?:等{1,2}|的时候|时)$")
_CAP_SEQUENTIAL_ACTION_PATTERN = (
    r"(?:以及|并且|同时|然后|而且|并|和|及|或|与)(?=\s*"
    + _CN_VERB_PATTERN + r")"
)
def _clean_capability_tail(tail: str) -> str:
    tail = _CAP_TAIL_BOUNDARY_RE.split(tail, maxsplit=1)[0]
    tail = _CAP_TAIL_SUFFIX_RE.sub("", tail)
    return tail.rstrip(_TAIL_DANGLING_CHARS)
_VERB_OBJECT_TAIL_PATTERN = (
    r"((?:(?!" + _CAP_SEQUENTIAL_ACTION_PATTERN + r")"
    r"[^\s，、。；：！？,;:!?" + re.escape(_TAIL_STOP_CHARS) + r"])*)"
)
_CN_CAPABILITY_MODIFIER_PATTERN = (
    r"(?:(?!(?:[和及或并而与]|" + _CN_VERB_PATTERN + r"))"
    r"[\u4e00-\u9fff]){0,12}?"
)
_CN_CAPABILITY_BRIDGE_SEPARATORS = r"[\s和及或]*"
def _extract_verb_object(description: str) -> list[str]:
    caps: list[str] = []
    exclusions = _exclusion_spans(description)
    for m in re.finditer(
        _NEG_VERB_PRECEDE_GUARD
        + "(" + _CN_VERB_PATTERN + r")" + _VERB_TAIL_PATTERN
        + r"(" + _CN_CAPABILITY_BRIDGE_SEPARATORS
        + _CN_CAPABILITY_MODIFIER_PATTERN + _CN_CAPABILITY_BRIDGE_SEPARATORS
        + r"(?:(?:[A-Za-z][A-Za-z0-9.+-]*|\.[A-Za-z0-9]+)"
        r"(?:\s*/\s*(?:[A-Za-z][A-Za-z0-9.+-]*|\.[A-Za-z0-9]+))*)?"
        + _CN_CAPABILITY_BRIDGE_SEPARATORS
        + r"(?:(?:\(|（)[^)）]{0,12}(?:\)|）))?"
        + _CN_CAPABILITY_BRIDGE_SEPARATORS + r")"
        "(" + _CN_OBJ_PATTERN + r")" + _VERB_OBJECT_TAIL_PATTERN + r"",
        description,
    ):
        if _capability_position_is_negative(
                description, m.start(), exclusions):
            continue
        if _is_capability_list_mention(description, m.start()):
            continue
        first_verb, more_verbs, bridge, obj, tail = m.groups()
        tail = _clean_capability_tail(tail)
        verbs = [first_verb] + re.findall(_CN_VERB_PATTERN, more_verbs)
        caps.extend(v + bridge + obj + tail for v in verbs)
    return caps
_MIN_NUMBERED_ITEM_LEN = 4
_MIN_DOMAIN_LEN = 3
_NUMBERED_DETAIL_RE = re.compile(
    _NEG_VERB_PRECEDE_GUARD
    + _CN_VERB_PATTERN + r"[\s，、和及]*" + _CN_OBJ_PATTERN
    + _VERB_OBJECT_TAIL_PATTERN
)
def _negative_capability_context(text: str) -> bool:
    return _first_verb_in_negative_scope(text) or _head_declared_negative(text)
def _is_negative_capability_text(text: str) -> bool:
    return (_negative_capability_context(text)
            or _EN_POSTPOSED_NEGATION_RE.search(text) is not None)
def _extract_numbered_details(detail: str) -> list[str]:
    exclusions = _exclusion_spans(detail)
    return [
        match.group(0) for match in _NUMBERED_DETAIL_RE.finditer(detail)
        if not _capability_position_is_negative(
            detail, match.start(), exclusions)
    ]
def _extract_numbered_items(description: str) -> list[str]:
    caps: list[str] = []
    numbered_text = mask_exclusion_context(description)
    numbered_item_pattern = (
        r"(?:" + _NUMBERED_ITEM_BOUNDARY_PATTERN + r")"
        r"([^\n]+?)(?=\s*(?:" + _NUMBERED_ITEM_BOUNDARY_PATTERN + r")|$)"
    )
    for numbered_match in re.finditer(
            numbered_item_pattern, numbered_text, re.MULTILINE):
        if _is_capability_list_mention(description, numbered_match.start(1)):
            continue
        item = numbered_match.group(1).strip()
        if len(item) < _MIN_NUMBERED_ITEM_LEN:
            continue
        domain_match = re.match(r"([^：:\n]{1,30})[：:]([^\n]+)", item)
        if domain_match:
            domain = domain_match.group(1).strip()
            if _NEG_CAP_PREFIX_RE.match(domain):
                continue
            if _negative_capability_context(domain):
                continue
            if len(domain) >= _MIN_DOMAIN_LEN:
                caps.append(domain)
            caps.extend(_extract_numbered_details(domain_match.group(2)))
        else:
            if _negative_capability_context(item):
                continue
            details = _extract_numbered_details(item)
            if details:
                caps.extend(details)
            else:
                caps.append(item)
    return caps
_EN_VERB_RE = re.compile(
    r"(?<![A-Za-z])(" + _EN_VERB_ALTERNATION + r")(?![A-Za-z])",
    re.IGNORECASE,
)
_BRACKET_ANCHOR_CONTEXT_RE = re.compile(
    r"([\u4e00-\u9fff\w ]{2,20})\s*[\(（](?=[A-Z][A-Za-z0-9_]+[\)）])")
_BRACKET_ANCHOR_LEAD_RE = re.compile(
    r"^(?:(?:and|or)\s+)+|"
    r"^(?:以及|并且|同时|然后|而且|和|及|或|与|、|，|,)+")
def _has_capability_verb(text: str) -> bool:
    return (re.search(_CN_VERB_PATTERN, text) is not None
            or _EN_VERB_RE.search(text) is not None)
def _extract_bracket_anchors(description: str, existing: list[str]) -> list[str]:
    caps: list[str] = []
    exclusions = _exclusion_spans(description)
    for ctx_match in _BRACKET_ANCHOR_CONTEXT_RE.finditer(description):
        cap = _BRACKET_ANCHOR_LEAD_RE.sub(
            "", ctx_match.group(1).strip()).strip()
        if len(cap) < 2 or not _has_capability_verb(cap):
            continue
        if _is_capability_list_mention(description, ctx_match.start(1)):
            continue
        if _capability_position_is_negative(
                description, ctx_match.start(1), exclusions):
            continue
        if cap not in existing and cap not in caps:
            caps.append(cap)
    return caps
_EN_FORM_TO_BASE: dict[str, str] = {
    form: word.lower()
    for word in _CAPABILITY_VERBS_EN
    for form in _en_verb_forms(word)
}
_EN_CAP_RE = re.compile(
    r"(?<![A-Za-z])((?:" + _EN_VERB_ALTERNATION + r")"
    + r"(?:\s*(?:,|or|and|,\s*and)\s*(?:" + _EN_VERB_ALTERNATION
    + r")){0,8})"
    r"\s+((?:\w+\s+)?(?:[\w.+-]*\.[A-Za-z0-9]+\s+)?)"
    r"(" + _CAPABILITY_OBJECTS_EN_ALTERNATION + r")(?![A-Za-z])",
    re.IGNORECASE,
)
_EN_CLAUSE_DELIM_RE = re.compile(
    r"[" + re.escape(_SEGMENT_BOUNDARY_CHARS) + r"]"
    + r"|" + _EN_CONTRASTIVE_BOUNDARY_PATTERN,
    re.IGNORECASE,
)
def _en_segment_span(text: str, pos: int) -> tuple[int, int]:
    start = 0
    for _delim_m in _EN_CLAUSE_DELIM_RE.finditer(text, 0, pos):
        start = _delim_m.end()
    _next = _EN_CLAUSE_DELIM_RE.search(text, pos)
    return start, (_next.start() if _next else len(text))
def _en_segment_is_negated(text: str, pos: int) -> bool:
    start, _end = _en_segment_span(text, pos)
    return _EN_NEG_SENTINEL_RE.search(text[start:pos]) is not None
def _extract_english_caps(description: str) -> list[str]:
    _en_text = _EN_SENTENCE_END_RE.sub("。", description)
    negated_intros = _negated_include_spans(description)
    exclusions = _exclusion_spans(description)
    caps = []
    for _clause_m in re.finditer(r"[^。；;！!？?\n]+", _en_text):
        _clause = _clause_m.group(0)
        if not _clause.strip():
            continue
        for _cap_m in _EN_CAP_RE.finditer(_clause):
            _cap_pos = _clause_m.start() + _cap_m.start()
            if _is_capability_list_mention(description, _cap_pos):
                continue
            if _en_segment_is_negated(_en_text, _cap_pos):
                continue
            if _capability_position_is_negative(
                    description, _cap_pos, exclusions):
                continue
            if pos_in_spans(_cap_pos, negated_intros):
                continue
            _modifier = _cap_m.group(2)
            _object = _cap_m.group(3)
            for _verb in _EN_VERB_RE.findall(_cap_m.group(1)):
                _verb = _verb.strip()
                _base = _EN_FORM_TO_BASE.get(_verb.lower(), _verb)
                if _verb[:1].isupper():
                    _base = _base[:1].upper() + _base[1:]
                caps.append(f"{_base} {_modifier}{_object}")
    return caps
_INCLUDE_ITEM_SPLIT_RE = re.compile(r"[，,、;；]")
def _include_items_from(segment: str) -> list[str]:
    items: list[str] = []
    for raw_item in _INCLUDE_ITEM_SPLIT_RE.split(segment):
        item = _clean_capability_tail(raw_item.strip()).strip()
        if len(item) < 2 or _INCLUDE_INTRO_RE.match(item):
            continue
        if re.fullmatch(_CN_VERB_PATTERN, item) or _EN_VERB_RE.fullmatch(item):
            continue
        items.append(item)
    return items
def _extract_include_items(description: str) -> list[str]:
    negative_intros = _negated_include_spans(description)
    include_text = mask_exclusion_context(description)
    intros = [
        _intro_m for _intro_m in _INCLUDE_INTRO_RE.finditer(include_text)
        if not pos_in_spans(_intro_m.start(), negative_intros)
        and not _in_negative_verb_scope(description, _intro_m.start())
        and not _is_capability_list_mention(description, _intro_m.start())
    ]
    caps: list[str] = []
    for _index, _intro_m in enumerate(intros):
        end = _intro_m.end(1)
        if _index + 1 < len(intros):
            end = min(end, intros[_index + 1].start())
        caps.extend(_include_items_from(include_text[_intro_m.start(1):end]))
    return caps
def _dn_group_is_negative(description: str, group_start: int, dn_list: str) -> bool:
    if _is_capability_list_mention(description, group_start):
        return True
    if _segment_head_is_negative(description, group_start):
        return True
    if _head_declared_negative(dn_list):
        return True
    if _first_verb_in_negative_scope(dn_list):
        return True
    return _in_negative_verb_scope(description, group_start)
_ENUM_PROSE_CLAUSE_RE = re.compile(
    r"^(?:当|若|如果|一旦)[^、，。；]{0,10}(?:需要|要求|想要|希望|使用|涉及)"
    r"|^(?:本|该|此)技能"
)
def _is_enum_prose_clause(item: str) -> bool:
    return _ENUM_PROSE_CLAUSE_RE.match(item) is not None
def _collect_dn_items(dn_items: list[str], existing: list[str],
                      collected: list[str]) -> list[str]:
    if sum(1 for it in dn_items if re.search(_CN_VERB_PATTERN, it)) < 2:
        return []
    if _NEG_CAP_PREFIX_RE.match(dn_items[0]):
        return []
    seen = set(collected)
    out: list[str] = []
    for raw_item in dn_items:
        dn_item = _clean_capability_tail(raw_item.strip())
        if _is_enum_prose_clause(dn_item):
            continue
        if re.fullmatch(_CN_VERB_PATTERN, dn_item):
            continue
        if 2 <= len(dn_item) <= 10 and dn_item not in existing and dn_item not in seen:
            seen.add(dn_item)
            out.append(dn_item)
    return out
# 能力项字符集：中文 + 英文 + 数字。只允许中文会让「转换图片为DWG」这类
# 中英混排项断链，整条顿号枚举因首项不匹配而全组丢失（历史缺陷：antu-cad
# 的 13 项能力被退化成 5 项错误切分）。
_DN_ITEM_CHARS = r"[\u4e00-\u9fffA-Za-z0-9]"
def _extract_enumeration(description: str, existing: list[str]) -> list[str]:
    caps: list[str] = []
    exclusions = _exclusion_spans(description)
    dn_pattern = (r"(?:^|[：:，,；;。])\s*"
                  r"((?:" + _DN_ITEM_CHARS + r"{2,10}、){2,}"
                  + _DN_ITEM_CHARS + r"{2,10})")
    for dn_match in re.finditer(dn_pattern, description, re.MULTILINE):
        dn_list = dn_match.group(1)
        if (pos_in_spans(dn_match.start(1), exclusions)
                or _dn_group_is_negative(description, dn_match.start(1), dn_list)):
            continue
        dn_items = [it.strip() for it in re.split(r"[、，,]", dn_list) if it.strip()]
        caps.extend(_collect_dn_items(dn_items, existing, caps))
    return caps
_CAP_TRAILING_PUNCT = "。.；;，,：:！!？?"
_CAP_LEAD_CONJUNCTION_CHARS = frozenset("并而和及或与、，,；;")
_CAP_LEAD_CONJUNCTION_RE = re.compile(
    r"^(?:以及|并且|同时|然后|而且|还是|或者|并|而|和|及|或|与|、|，|,|；|;)+")
_CAP_NON_CAPABILITY_RE = re.compile(
    r"^(?:以下|如下|下面|下列|(?:本|该|此)技能)"
    r"|(?:时|的时候)(?:使用|调用|加载|采用)$")
_BRACKET_PAIRS: tuple[tuple[str, str], ...] = (
    ("（", "）"), ("(", ")"), ("「", "」"), ("『", "』"),
    ("【", "】"), ("《", "》"),
)
def _starts_with_capability_verb(text: str) -> bool:
    return (re.match(_CN_VERB_PATTERN, text) is not None
            or _EN_VERB_RE.match(text) is not None)
def _strip_capability_lead(text: str) -> str:
    if not text or text[0] not in _CAP_LEAD_CONJUNCTION_CHARS:
        return text
    candidate = _CAP_LEAD_CONJUNCTION_RE.sub("", text).strip()
    return candidate if _starts_with_capability_verb(candidate) else text
def _capability_key(text: str) -> str:
    """能力项归一化键（去首连词 + 去尾标点）。

    ``_dedupe_capabilities`` 用本键做 trusted 命中判定；调用方构造 trusted
    时必须走同一函数，否则「并删除句柄」这类以连词开头的显式声明项与归一化
    后的 cap「删除句柄」不相等，trusted 豁免失效后被通用目标词表二次过滤，
    作者的显式能力项被静默丢弃。
    """
    text = text if isinstance(text, str) else ""
    return _strip_capability_lead(
        text.strip()).rstrip(_CAP_TRAILING_PUNCT).strip()
def _has_balanced_brackets(text: str) -> bool:
    for open_ch, close_ch in _BRACKET_PAIRS:
        depth = 0
        for ch in text:
            if ch == open_ch:
                depth += 1
            elif ch == close_ch:
                depth -= 1
                if depth < 0:
                    return False
        if depth:
            return False
    return True
def _dedupe_capabilities(
        capabilities: list[str],
        trusted: frozenset[str] | set[str] = frozenset()) -> list[str]:
    """去重并过滤噪声能力项。

    ``trusted`` 是来自包括/顿号枚举、动词开头的编号项或括号锚点、
    已校验「含能力动词」的作者显式声明项：它们不再要求命中通用目标词表。
    双重过滤会把垂直域能力整组丢掉——历史缺陷：antu-cad 的「提取符号画法」
    「校准像素标定」「校正透视变形」「绘制图元」「备份句柄」等 13 项能力
    被压成 5 项，因为词表只有文档/业务域目标词。
    """
    seen: set[str] = set()
    deduped: list[str] = []
    for raw_cap in capabilities:
        cap = _capability_key(raw_cap)
        if not cap or not _has_balanced_brackets(cap):
            continue
        if not _has_capability_verb(cap):
            continue
        if cap not in trusted and not matches_any(
                STRUCTURE_TARGET_PATTERNS, cap):
            continue
        if _is_negative_capability_text(cap) or _CAP_NON_CAPABILITY_RE.search(cap):
            continue
        key = cap.casefold()
        if key in seen:
            continue
        seen.add(key)
        deduped.append(cap)
    return deduped
def extract_capabilities(description: str) -> list[str]:
    if not isinstance(description, str):
        description = ""
    capabilities: list[str] = []
    capabilities.extend(_extract_verb_object(description))
    numbered_items = _extract_numbered_items(description)
    capabilities.extend(numbered_items)
    bracket_anchors = _extract_bracket_anchors(description, capabilities)
    capabilities.extend(bracket_anchors)
    capabilities.extend(_extract_english_caps(description))
    include_items = _extract_include_items(description)
    capabilities.extend(include_items)
    enumeration = _extract_enumeration(description, capabilities)
    capabilities.extend(enumeration)
    # 包括、顿号、动词开头的编号项与括号锚点都是作者显式声明的能力；动词、
    # 否定与噪声检查仍在 _dedupe_capabilities 内生效，仅豁免通用目标词表过滤。
    # trusted 必须与 _dedupe_capabilities 的判定键同源归一化，否则首连词/
    # 尾标点差异会让豁免静默失效。
    explicit_trusted = {
        _capability_key(item)
        for item in (*numbered_items, *bracket_anchors)
        # 先归一化再判动词开头：`_capability_key` 会剥掉首连词（并/而/和/及/或/与），
        # 若用原始 item 判定，「并删除句柄」这类作者显式声明的垂直域能力项会因
        # 首字是连词而被排除出 trusted，随后被通用目标词表二次过滤静默丢弃。
        if _starts_with_capability_verb(_capability_key(item))
    }
    deduped = _dedupe_capabilities(
        capabilities,
        trusted={
            *(_capability_key(item) for item in include_items),
            *(_capability_key(item) for item in enumeration),
            *explicit_trusted,
        },
    )
    if deduped:
        _log.debug("[Match] 能力提取: %d 项（入参 %d 字符）", len(deduped), len(description))
    return deduped[:20]
_RESOURCE_CONTEXT_MAX_CHARS = 200
_PARAGRAPH_GAP_RE: re.Pattern[str] = re.compile(
    r"(?:\r\n|\r|\n)[ \t]*(?:\r\n|\r|\n)")
_COMMAND_CONTEXT_RE: re.Pattern[str] = re.compile(
    r"(?<![\w.])(?:python3?|bash|sh|node|npx|pwsh)\s|SKILL_PATH_[A-Z]+")
_RESOURCE_CONDITION_KEYWORDS: tuple[str, ...] = (
    "详见",
    "参见",
    "参考",
    "查看",
    "读取",
    "加载",
    "需要",
    r"see[:：\s]",
    r"refer\s+to",
    r"read[:：\s]",
    r"load[:：\s]",
    r"when\s",
    r"if\s+you\s+need",
    r"for\s+details",
)
_RESOURCE_CONDITION_RE: re.Pattern[str] = re.compile(
    "|".join(_RESOURCE_CONDITION_KEYWORDS), re.IGNORECASE
)
_PROJECT_RESOURCE_DIR_CANDIDATES: tuple[str, ...] = (
    "docs", "doc", "documentation", "examples", "samples", "templates",
)
def resource_dirs_for(doc_root: str) -> tuple[str, ...]:
    names: list[str] = [
        name.strip() for name in resource_dir_names() if name.strip()]
    if doc_root:
        for candidate in _PROJECT_RESOURCE_DIR_CANDIDATES:
            if (candidate not in names
                    and os.path.isdir(os.path.join(doc_root, candidate))):
                names.append(candidate)
    return tuple(names)
def resource_path_pattern(
    resource_dirs: tuple[str, ...],
) -> re.Pattern[str]:
    names = {
        name.strip() for name in resource_dirs
        if isinstance(name, str) and name.strip()
    }
    if not names:
        return re.compile(r"(?!)")
    alternation = "|".join(
        re.escape(name) for name in sorted(names, key=len, reverse=True))
    return compile_patterns(
        (r"(?<![\w/\\-])(?:" + alternation
         + r")/[\w\-/]+(?:\.[A-Za-z0-9\-]+)*",), True)[0]
def fenced_block_spans(body_text: str) -> list[tuple[int, int]]:
    lines = body_text.split("\n")
    mask = code_block_mask(lines)
    if not mask:
        return []
    spans: list[tuple[int, int]] = []
    offset = 0
    for i, line in enumerate(lines):
        if i in mask:
            spans.append((offset, offset + len(line)))
        offset += len(line) + 1
    return spans
def pos_in_spans(pos: int, spans: list[tuple[int, int]]) -> bool:
    return any(start <= pos < end for start, end in spans)
def line_bounds(text: str, pos: int) -> tuple[int, int]:
    start = text.rfind("\n", 0, pos) + 1
    end = text.find("\n", pos)
    return start, len(text) if end < 0 else end
_COMMAND_PROSE_BOUNDARY_RE = re.compile(
    r"[。；;！!？?，,]"
    r"|(?:随后|然后|接着|之后|另见|参见|参考|查看)"
    r"|后(?=\s*(?:参见|参考|查看|读取|解析|处理|使用))"
    r"|\b(?:then|afterwards)\b|\b(?:see|refer\s+to)\s*$",
    re.IGNORECASE,
)
def is_command_context_line(text: str, pos: int) -> bool:
    start, _end = line_bounds(text, pos)
    prefix = text[start:pos]
    commands = list(_COMMAND_CONTEXT_RE.finditer(prefix))
    if not commands:
        return False
    return _COMMAND_PROSE_BOUNDARY_RE.search(
        prefix, commands[-1].end()) is None
def blank_spans(chars: list[str], spans: list[tuple[int, int]]) -> None:
    for start, end in spans:
        chars[start:end] = " " * (end - start)
def resource_context_window(text: str, start: int, end: int) -> str:
    gaps = list(_PARAGRAPH_GAP_RE.finditer(text, 0, start))
    left = 0
    if gaps:
        left = gaps[-1].end()
        previous_start = gaps[-2].end() if len(gaps) >= 2 else 0
        previous = text[previous_start:gaps[-1].start()].strip()
        is_forward_intro = previous.endswith((":", "：")) or (
            re.match(r"^#{1,6}[ \t]+", previous)
            and _RESOURCE_CONDITION_RE.search(previous))
        if is_forward_intro:
            left = previous_start
    tail = _PARAGRAPH_GAP_RE.search(text, end)
    right = tail.start() if tail else len(text)
    head = text[max(left, start - _RESOURCE_CONTEXT_MAX_CHARS):start]
    trail = text[end:min(right, end + _RESOURCE_CONTEXT_MAX_CHARS)]
    return head + trail
_DOC_EXTENSIONS = (".md", ".txt", ".rst", ".html")
def mentions_local_file(body_text: str, fname: str) -> bool:
    if not fname:
        return False
    pattern = (r"(?<![A-Za-z0-9_.-])" + re.escape(fname)
               + r"(?![A-Za-z0-9_]|\.[A-Za-z0-9])")
    return re.search(pattern, body_text, re.IGNORECASE) is not None
def redundant_doc_names(
    entries: list[str], patterns: list[re.Pattern[str]],
    entry_names: frozenset[str],
) -> list[str]:
    redundant = []
    for fname in entries:
        lowered = fname.lower()
        if not lowered.endswith(_DOC_EXTENSIONS) or lowered in entry_names:
            continue
        if any(pattern.search(fname) for pattern in patterns):
            redundant.append(fname)
    return sorted(redundant)
_WORKFLOW_PATTERNS = compile_patterns(
    (
        (
            r"(?:步骤|(?<![A-Za-z])Steps?(?![A-Za-z])|第一步|首先|开始"
            r"|(?<![\w.])1[\.、)）](?!\d))"
        ),
        r"(?:使用|调用|执行|运行)\s*(?:python|bash|工具|脚本)",
        r"(?:python|bash|工具|脚本)\s*(?:调用|执行|运行|使用)",
        r"(?:核心原则|工作流|快速开始|速查|(?<![A-Za-z])API(?![A-Za-z]))",
    ),
    True,
)
def first_paragraph_issue(body_text: str) -> tuple[str, str] | None:
    if body_opens_with_code_block(body_text):
        return None
    first_para = first_content_paragraph(body_text)
    if not first_para:
        if not body_text.strip():
            return ("正文为空，AI 匹配后无法获取执行指导", "(空)")
        first_line = next(
            (line.strip() for line in body_text.splitlines() if line.strip()),
            "",
        )
        return (
            ("正文仅包含标题行，未提供可执行的首段内容。"
             " AI 匹配后同样无法获取执行指导，建议在正文开头补充"
             "核心原则、步骤列表或快速开始等操作性内容。"),
            first_line[:80],
        )
    if any(p.search(first_para) for p in _WORKFLOW_PATTERNS):
        return None
    return (
        ("正文首段未包含工作流指导信号。AI 匹配后需要立即知道如何执行。"
         " 建议首段包含：核心原则、步骤列表、快速开始、"
         "或工具使用说明等操作性内容。"),
        first_para[:80],
    )
def resource_reference_matches(
    body_text: str, block_spans: list[tuple[int, int]],
    pattern: re.Pattern[str],
) -> list[re.Match[str]]:
    inline_spans = inline_code_spans(body_text)
    return [
        m for m in pattern.finditer(body_text)
        if not pos_in_spans(m.start(), block_spans)
        and not pos_in_spans(m.start(), inline_spans)
        and not is_command_context_line(body_text, m.start())
    ]
def refs_without_condition(
    body_text: str, matches: list[re.Match[str]],
    block_spans: list[tuple[int, int]],
) -> list[str]:
    masked_chars = list(body_text)
    blank_spans(masked_chars, block_spans)
    blank_spans(masked_chars, inline_code_spans(body_text))
    for m in matches:
        start, end = m.start(), m.end()
        masked_chars[start:end] = " " * (end - start)
    masked_text = "".join(masked_chars)
    refs: list[str] = []
    seen: set[str] = set()
    for m in matches:
        context = resource_context_window(masked_text, m.start(), m.end())
        ref = m.group(0)
        if _RESOURCE_CONDITION_RE.search(context) or ref in seen:
            continue
        seen.add(ref)
        refs.append(ref)
    return refs
def unreferenced_redundant_docs(
    skill_dir: str, skill_md_name: str, body_text: str,
    patterns: list[re.Pattern[str]],
) -> list[str]:
    if not os.path.isdir(skill_dir):
        return []
    entries = os.listdir(skill_dir)
    entry_names = frozenset({
        ENTRY_DOC_NAME.casefold(),
        skill_md_name.casefold(),
    })
    file_entries = [
        fname for fname in entries
        if os.path.isfile(os.path.join(skill_dir, fname))
    ]
    candidates = redundant_doc_names(file_entries, patterns, entry_names)
    referenced = referenced_local_paths(body_text, Path(skill_dir))
    return [
        fname for fname in candidates
        if (Path(skill_dir) / fname).resolve() not in referenced
        and not mentions_local_file(body_text, fname)
    ]

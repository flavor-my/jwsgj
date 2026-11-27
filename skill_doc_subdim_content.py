from __future__ import annotations

import ast
import builtins
import io
import logging
import os
import re
import sys
import tokenize

from jwsgj.build_skill_api_contract import (
    collect_api_names,
    collect_skill_py_basenames,
    extract_param_names,
    extract_py_refs,
    get_scan_files,
    has_code_surface,
    has_scan_files,
    is_script_only_skill,
    iter_scan_function_entries,
    strip_url_tokens,
)
from jwsgj.build_text_document import (
    _DEFAULT_DOC_PROFILE,
    _GENERIC_BOUNDARY_RE,
    _REF_DIR_RE,
    _iter_local_links,
    _md_local_paths,
    _normalize_sections_found,
    identifier_pattern,
    iter_fenced_code_blocks,
    strip_fenced_blocks,
)
from jwsgj.diag_types_defs import (
    DocQualityIssue,
    SubDimensionScore,
    make_noscan_issue,
    record_dimension,
)
from jwsgj.diag_types_normalize import (
    normalize_entry_inputs,
)
from jwsgj.diag_types_vocab import (
    NO_CODE_DETAIL,
    NO_CODE_SCORE,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    GENERIC_DIAG_OUT_OF_SCOPE_DIRS,
    GENERIC_SCAN_IGNORE_DIRS_LOWER,
    is_audit_skip_dir,
    is_scan_py_name,
    is_transient_module_name,
    py_stem,
)

__all__ = [
    'check_q9_q10_q11',
    'diag_content',
    'diag_content_q1q4',
    'diag_content_q5q6',
    'diag_content_q7q8',
    'expand_linked_docs',
]
_log = logging.getLogger(__name__)
_UNVERIFIED_SCORE = 50.0
_GENERAL_FLOOR_SCORE = 60.0
_DIM_WEIGHT: dict[str, float] = {
    'Q1': 0.1, 'Q2': 0.1, 'Q3': 0.15, 'Q4': 0.2, 'Q5': 0.15, 'Q6': 0.1,
    'Q7': 0.05, 'Q8': 0.0, 'Q9': 0.15, 'Q10': 0.1, 'Q11': 0.1,
}
_Q1_LANG_TAGS = {
    "python", "py", "python3", "bash", "shell", "sh",
    "javascript", "js", "typescript", "ts", "sql",
    "powershell", "ps1", "ruby", "go", "java",
}
_Q6_PY_TAGS = {"python", "py", "python3"}
_Q6_PATTERN_FACTORS: tuple[tuple[float, re.Pattern[str]], ...] = (
    (15.0, re.compile(r'^(?:from\s+\w+|import\s+\w+)', re.MULTILINE)),
    (10.0, re.compile(r'[a-zA-Z_]\w*\s*\([^)]+\)')),
    (10.0, re.compile(r'\w+\s*=\s*\w+')),
    (10.0, re.compile(r'\bprint\s*\(|\breturn\b\s+\w+|\bresult\b\s*=')),
    (15.0, re.compile(r'\btry:|\bexcept\b|\braise\b|\bif\s+not\s+')),
)
_Q2_BOUNDARY_EXTRA = r'能[做干]|In Scope|Out of Scope|不能[做干]|应触发|不应触发|'
_Q2_BOUNDARY_PATTERN = re.compile(
    _Q2_BOUNDARY_EXTRA + _GENERIC_BOUNDARY_RE.pattern, re.IGNORECASE)
_Q3_EN_CAP_SUFFIXES = (
    'analysis', 'diagnosis', 'detection', 'audit', 'fix', 'refactoring',
    'refactor', 'creation', 'management', 'validation', 'scanning', 'scan',
    'cleanup', 'generation', 'conversion', 'extraction', 'calibration',
    'correction', 'drawing', 'export', 'annotation', 'recognition',
    'measurement', 'verification', 'comparison', 'backup', 'review',
    'enhancement', 'optimization', 'compression', 'decompression',
    'translation', 'segmentation', 'testing', 'deployment', 'training',
    'crawling', 'scheduling', 'rendering', 'formatting', 'cleaning',
    'encryption', 'decryption', 'merging', 'splitting', 'packaging',
    'publishing', 'retrieval', 'sorting', 'calculation', 'parsing',
    'modeling', 'modelling', 'prediction', 'recommendation', 'archiving',
    'printing', 'collection', 'organization', 'organisation', 'scoring',
    'arbitration', 'resolution', 'elimination',
)
_Q3_EN_SUFFIX_PATTERN = '(?:' + '|'.join(
    sorted(_Q3_EN_CAP_SUFFIXES, key=len, reverse=True)) + ')'
_EN_CAP_PATTERN = re.compile(
    r'(?<![A-Za-z0-9_])'
    rf'(?:(?!{_Q3_EN_SUFFIX_PATTERN}\b)'
    r'[A-Za-z][A-Za-z0-9_-]*[ \t]+){0,5}'
    rf'{_Q3_EN_SUFFIX_PATTERN}\b',
    re.IGNORECASE,
)
_Q3_EN_LEADING_BREAKS = frozenset({
    'a', 'an', 'the', 'this', 'that', 'these', 'those', 'my', 'our',
    'your', 'its', 'their', 'his', 'her', 'i', 'we', 'you', 'they',
    'he', 'she', 'it', 'me', 'us', 'them', 'him', 'one', 'ones',
    'which', 'who', 'whom', 'whose', 'what', 'some', 'any', 'all',
    'both', 'each', 'every', 'another', 'other', 'such',
    'of', 'to', 'in', 'on', 'at', 'for', 'with', 'from', 'by', 'as',
    'via', 'into', 'onto', 'about', 'over', 'under', 'through',
    'across', 'without', 'within', 'per', 'between', 'among',
    'against', 'during', 'before', 'after', 'than',
    'and', 'or', 'but', 'nor', 'so', 'yet', 'if', 'when', 'while',
    'where', 'whether', 'because', 'although', 'though', 'since',
    'unless', 'until', 'plus',
    'be', 'am', 'is', 'are', 'was', 'were', 'been', 'being',
    'have', 'has', 'had', 'do', 'does', 'did', 'can', 'could',
    'may', 'might', 'must', 'shall', 'should', 'will', 'would',
    'also', 'then', 'thus', 'therefore', 'very', 'more', 'most',
    'less', 'least', 'only', 'just', 'even', 'still', 'often',
    'always', 'never', 'not', 'no', 'here', 'there', 'now',
    'support', 'supports', 'provide', 'provides', 'include', 'includes',
    'including', 'cover', 'covers', 'offer', 'offers', 'enable',
    'enables', 'help', 'helps', 'use', 'uses', 'using', 'need', 'needs',
    'skill', 'skills', 'tool', 'tools', 'capability', 'capabilities',
    'feature', 'features',
})
_Q3_EN_VERB_ENDINGS = ('s', 'ed')
_Q3_EN_NOUN_ENDINGS = ('ss', 'us', 'is')
_Q3_CN_EN_PAIR_RE = re.compile(
    r'(?P<cn>[\u4e00-\u9fff][\u4e00-\u9fffA-Za-z0-9_/-]{1,30}?)\s*'
    r'[（(]\s*(?P<en>[A-Za-z][A-Za-z0-9 _/-]{1,80}?)\s*[）)]')
_Q3_EN_CN_PAIR_RE = re.compile(
    r'(?P<en>[A-Za-z][A-Za-z0-9 _/-]{1,80}?)\s*[（(]\s*'
    r'(?P<cn>[\u4e00-\u9fff][\u4e00-\u9fffA-Za-z0-9_/-]{1,30}?)\s*[）)]')
_Q3_TRIGGER_PREFIXES = ('帮我', '请帮', '我看', '分析分析', '怎么')
_Q3_CAP_SUFFIXES = ('诊断', '检测', '审计', '修复', '重构', '创建',
                    '管理', '分析', '验证', '扫描', '清理', '生成',
                    '转换', '提取', '校准', '校正', '绘制', '导出',
                    '标注', '识别', '测量', '校验', '对比', '备份',
                    '核对', '叠加', '检查', '删除',
                    '增强', '优化', '压缩', '解压', '翻译', '分割',
                    '测试', '部署', '训练', '抓取', '爬取', '审核',
                    '调度', '渲染', '排版', '清洗', '加密', '解密',
                    '合并', '拆分', '打包', '发布', '检索', '排序',
                    '统计', '计算', '解析', '建模', '预测', '推荐',
                    '归档', '打印', '采集', '录入', '整理')
_Q3_CAP_WORD_PATTERN = re.compile(
    r'[\u4e00-\u9fff]{2,6}(?:' + '|'.join(_Q3_CAP_SUFFIXES) + ')'
)
_Q3_NARRATIVE_FUNC_CHARS = frozenset('的或与和及即则而从')
_Q3_ENUM_CONJS = ('与', '或', '及', '并', '和', '以及')
_Q3_TEMPORAL_FOLLOWERS = frozenset('后时前')
_Q3_LEADING_LIGHT_VERBS = ('提供', '支持', '包括', '负责', '帮助', '实现',
                           '进行', '用于', '具备')
_Q3_MODAL_CHARS = frozenset('能可会需须')
_Q3_NEED_VERBS = ('需要', '想要', '希望', '要求', '要')
_Q3_CAP_PREFIX_VERBS = tuple(dict.fromkeys(
    (*_Q3_LEADING_LIGHT_VERBS, *_Q3_NEED_VERBS)))
_Q3_NEGATION_CLAUSE_RE = re.compile(
    r'(?:不|非|未|无|勿|别)'
    r'(?:支持|包括|包含|覆盖|具备|具有|提供|属于|用于|适用|涉及|需(?:要)?|须|能|可|会|做|干)'
    r'|非代码|\bnon[-\s]+code\b'
    r'|\bnot\s+(?:support(?:s|ed)?|includ(?:e|es|ed)|cover(?:s|ed)?|for)\b'
    r'|\bexclud(?:e|es|ing)\b|\bwithout\b',
    re.IGNORECASE,
)
_Q3_CLAUSE_END_RE = re.compile(r'[。；;！!？?\n]|但|而是|不过|however\b|but\b',
                               re.IGNORECASE)
def _code_like_blocks(blocks: list[tuple[str, str]], lang_tags: set[str]) -> list[str]:
    return [block for lang, block in blocks
            if (lang or "").lower() in lang_tags
            or (not (lang or "").strip()
                and bool(re.search(
                    r'(?:^from |^import |def \w+|\w+\(.*\))',
                    block, re.MULTILINE)))]
_STRING_TOKEN_START_RE = re.compile(r"^[A-Za-z]*(['\"])")
def _is_docstring_string_token(tok_string: str) -> bool:
    match = _STRING_TOKEN_START_RE.match(tok_string)
    if not match:
        return False
    prefix = tok_string[:match.end() - 1].lower()
    return prefix in {'', 'r', 'u'}
def _string_statement_ends_here(tokens, index: int) -> bool:
    for tok in tokens[index + 1:]:
        if tok.type in (tokenize.NL, tokenize.COMMENT):
            continue
        return tok.type in (tokenize.NEWLINE, tokenize.ENDMARKER) or (
            tok.type == tokenize.OP and tok.string == ';')
    return True
def _is_docstring_stmt(tokens, index: int, tok, depth: int,
                       at_stmt_start: bool, empty_block: dict) -> bool:
    return bool(at_stmt_start and empty_block.get(depth, True)
                and tok.type == tokenize.STRING
                and _is_docstring_string_token(tok.string)
                and _string_statement_ends_here(tokens, index))
def _tokens_have_comment_or_docstring(tokens) -> bool:
    depth = 0
    empty_block = {0: True}
    at_stmt_start = True
    for index, tok in enumerate(tokens):
        ttype = tok.type
        if ttype == tokenize.COMMENT:
            return True
        if ttype == tokenize.INDENT:
            depth += 1
            empty_block[depth] = True
            at_stmt_start = True
            continue
        if ttype == tokenize.DEDENT:
            depth = max(0, depth - 1)
            at_stmt_start = True
            continue
        if ttype == tokenize.NEWLINE:
            at_stmt_start = True
            continue
        if ttype in (tokenize.NL, tokenize.ENDMARKER):
            continue
        if _is_docstring_stmt(tokens, index, tok, depth, at_stmt_start,
                              empty_block):
            return True
        empty_block[depth] = False
        at_stmt_start = False
    return False
def _parse_docstring_ast(block: str) -> ast.Module | None:
    try:
        return ast.parse(block)
    except (SyntaxError, ValueError, MemoryError, RecursionError):  # jwsgj:silent-ok 纯值降级：入参不可解析时返回安全默认值，无副作用可留痕
        return None
def _ast_has_docstring(block: str | ast.Module) -> bool:
    tree = (block if isinstance(block, ast.Module)
            else _parse_docstring_ast(block))
    if tree is None:
        return False
    return any(
        ast.get_docstring(node, clean=False) is not None
        for node in walk_nodes(tree)
        if isinstance(node, (ast.Module, ast.FunctionDef,
                             ast.AsyncFunctionDef, ast.ClassDef))
    )
def _block_has_comment_or_docstring(block: str) -> bool:
    tree = _parse_docstring_ast(block)
    if tree is not None and _ast_has_docstring(tree):
        return True
    try:
        tokens = list(tokenize.generate_tokens(io.StringIO(block).readline))
    except (tokenize.TokenError, SyntaxError, ValueError) as _e:
        log_swallowed(__name__, _e,
                      context=(f'_block_has_comment_or_docstring:'
                               f'{type(_e).__name__}'))
        return bool(re.search(r'(?m)^\s*#', block))
    if tree is not None:
        return any(tok.type == tokenize.COMMENT for tok in tokens)
    return _tokens_have_comment_or_docstring(tokens)
def _dir_exists_ci(skill_dir: str, name: str) -> bool:
    if os.path.isdir(os.path.join(skill_dir, name)):
        return True
    entries: list[str] = []
    try:
        entries = os.listdir(skill_dir)
    except OSError as exc:
        _log.warning("[SkillDoc] 技能根目录列举失败，大小写对称回退降级"
                     "判不存在: %s: %s", skill_dir, exc)
    folded = name.casefold()
    return any(
        e.casefold() == folded
        for e in entries
        if os.path.isdir(os.path.join(skill_dir, e)))
_EXPAND_MAX_FILES = 8
_EXPAND_MAX_CHARS = 120_000
def _path_within(root: str, path: str) -> bool:
    try:
        root_n = os.path.normcase(os.path.realpath(os.path.abspath(root)))
        path_n = os.path.normcase(os.path.realpath(os.path.abspath(path)))
        return os.path.commonpath([root_n, path_n]) == root_n
    except (OSError, TypeError, ValueError) as exc:
        log_swallowed(__name__, exc,
                      context=f'_path_within:{type(exc).__name__}')
        return False
def _expand_base_dir(md_path: str, skill_dir: str) -> str:
    if md_path:
        doc_dir = os.path.dirname(os.path.abspath(md_path))
    elif skill_dir:
        doc_dir = os.path.abspath(skill_dir)
    else:
        doc_dir = os.getcwd()
    if skill_dir and not _path_within(skill_dir, doc_dir):
        doc_dir = os.path.abspath(skill_dir)
    return doc_dir
def _doc_key(path: str) -> str:
    return os.path.normcase(os.path.abspath(path))
def _linked_doc_candidate(ref: str, base: str, base_root: str,
                           seen: set[str]) -> str | None:
    candidate = os.path.normpath(os.path.join(base, ref))
    if not candidate.lower().endswith('.md'):
        return None
    if not os.path.isfile(candidate):
        return None
    if base_root and not _path_within(base_root, candidate):
        return None
    key = _doc_key(candidate)
    if key in seen:
        return None
    seen.add(key)
    return candidate
def _read_linked_doc(candidate: str, remaining: int) -> tuple[str, bool] | None:
    try:
        with open(candidate, encoding='utf-8', errors='ignore') as fh:
            linked = fh.read(remaining + 1)
    except OSError as exc:
        log_swallowed(__name__, exc,
                      context=f'_read_linked_doc:{type(exc).__name__}')
        return None
    truncated = len(linked) > remaining
    return linked[:remaining], truncated
def _expand_single_ref(ref: str, base: str, base_root: str,
                       seen: set[str], remaining: int):
    candidate = _linked_doc_candidate(ref, base, base_root, seen)
    if candidate is None:
        return None
    read = _read_linked_doc(candidate, remaining)
    if read is None:
        return None
    linked, truncated = read
    return f"\n\n<!-- linked: {ref} -->\n{linked}", candidate, len(linked), truncated
def _expand_one_level(queue: list, base_root: str, seen: set[str],
                      parts: list[str], total: int) -> tuple[int, bool]:
    text, base, depth = queue.pop(0)
    if depth >= 2:
        return total, False
    for ref in _md_local_paths(strip_fenced_blocks(text)):
        if len(parts) > _EXPAND_MAX_FILES:
            return total, True
        remaining = _EXPAND_MAX_CHARS - total
        if remaining <= 0:
            return total, True
        expanded = _expand_single_ref(ref, base, base_root, seen, remaining)
        if expanded is None:
            continue
        segment, candidate, linked_len, truncated = expanded
        parts.append(segment)
        total += linked_len
        if truncated or total >= _EXPAND_MAX_CHARS:
            return total, True
        queue.append((segment, os.path.dirname(candidate), depth + 1))
    return total, False
def _path_arg(value) -> str:
    if isinstance(value, (str, bytes, os.PathLike)):
        try:
            return os.fsdecode(os.fspath(value)).strip()
        except (TypeError, ValueError) as exc:
            log_swallowed(__name__, exc,
                          context=f'_path_arg:{type(exc).__name__}')
            return ""
    return ""
def expand_linked_docs(md_path: str, body_text: str,
                        skill_dir: str) -> str:
    if not isinstance(body_text, str) or not body_text:
        return body_text if isinstance(body_text, str) else ""
    md_path = _path_arg(md_path)
    skill_dir = _path_arg(skill_dir)
    if not md_path and not skill_dir:
        return body_text
    doc_dir = _expand_base_dir(md_path, skill_dir)
    base_root = skill_dir or doc_dir
    seen = {_doc_key(md_path)} if md_path else set()
    queue = [(body_text, doc_dir, 0)]
    parts = [body_text]
    total = len(body_text)
    if total >= _EXPAND_MAX_CHARS:
        return body_text
    while queue:
        total, stop = _expand_one_level(queue, base_root, seen, parts, total)
        if stop:
            break
    return "\n".join(parts)
def _cq004_issue(d: str) -> DocQualityIssue:
    return DocQualityIssue(
        category="content",
        rule_id="CQ-004",
        severity="high",
        description=f"正文引用了 `{d}/` 目录但实际不存在",
        suggestion=f"创建 {d}/ 目录或从正文中移除引用",
        location=f"body: {d}/",
    )
def _cq005_escape_issue(link_target: str, label: str) -> DocQualityIssue:
    return DocQualityIssue(
        category="content",
        rule_id="CQ-005",
        severity="medium",
        description=f"Markdown 链接越出技能目录: {link_target}",
        suggestion=(f"技能文档须自包含，修正为技能目录内相对路径: "
                    f"{link_target}"),
        location=f"body: [{label}]({link_target})",
    )
def _cq005_missing_issue(link_target: str, label: str) -> DocQualityIssue:
    return DocQualityIssue(
        category="content",
        rule_id="CQ-005",
        severity="medium",
        description=f"Markdown 链接指向不存在的本地文件: {link_target}",
        suggestion=f"创建目标文件 {link_target} 或修正链接",
        location=f"body: [{label}]({link_target})",
    )
def _check_ref_dirs(body_text: str, skill_dir: str) -> list[DocQualityIssue]:
    local_text = strip_url_tokens(body_text)
    return [_cq004_issue(d) for d in sorted(set(_REF_DIR_RE.findall(local_text)))
            if not _dir_exists_ci(skill_dir, d)]
def _check_local_links(body_text: str, skill_dir: str) -> list[DocQualityIssue]:
    issues: list[DocQualityIssue] = []
    for label, raw_target, local_target in _iter_local_links(body_text):
        link_path = os.path.normpath(os.path.join(skill_dir, local_target))
        if not _path_within(skill_dir, link_path):
            issues.append(_cq005_escape_issue(raw_target, label))
            continue
        if not os.path.exists(link_path):
            issues.append(_cq005_missing_issue(raw_target, label))
    return issues
def _check_content_references(body_text: str, skill_dir: str) -> list[DocQualityIssue]:
    issues: list[DocQualityIssue] = []
    if not isinstance(body_text, str) or not body_text:
        return issues
    raw_skill_dir = skill_dir
    skill_dir = _path_arg(skill_dir)
    if not skill_dir:
        _log.debug("[SkillDoc][CQ-004/005] 未提供 skill_dir，跳过引用完整性检查")
        return issues
    if not os.path.isdir(skill_dir):
        _log.warning("[SkillDoc][CQ-004/005] skill_dir 不可用，"
                     "跳过引用完整性检查: %r", raw_skill_dir)
        return issues
    issues.extend(_check_ref_dirs(body_text, skill_dir))
    issues.extend(_check_local_links(body_text, skill_dir))
    return issues
def diag_content(body_text: str,
                 skill_dir: str = "") -> list[DocQualityIssue]:
    if not isinstance(body_text, str):
        body_text = ""
    prose = strip_fenced_blocks(body_text)
    issues: list[DocQualityIssue] = []
    issues.extend(_check_content_references(prose, skill_dir))
    if re.search(r"行数.*分布|文件.*行数|行数.*≈|"
                 r"line\s+count.*(?:distribution|≈)|file.*line\s+count",
                 prose, re.IGNORECASE):
        issues.append(DocQualityIssue(
            category="content", rule_id="CQ-001", severity="low",
            description="正文包含文件行数清单（易过时）",
            suggestion="将行数信息移至 references/，并标注为近似值",
            location="正文",
        ))
    trigger_sections = re.findall(
        r"触发示例|触发条件|典型.*指令|匹配.*说法|"
        r"trigger examples?|trigger conditions?|typical.*commands?|matching.*phrases?",
        prose, re.IGNORECASE)
    if len(trigger_sections) > 1:
        issues.append(DocQualityIssue(
            category="content", rule_id="CQ-002", severity="low",
            description="正文中触发示例与 description 重复",
            suggestion="触发信息主要在 description 中，正文仅保留引用链接",
            location="正文",
        ))
    _log.info("[SkillDoc][diag_content] 阶段4内容质量检查完成: %d 项问题", len(issues))
    return issues
def diag_content_q1q4(body_text, description, all_issues, api_scan, skill_dir,
                      *, doc_profile: str = _DEFAULT_DOC_PROFILE,
                      expanded_body=None) -> list[SubDimensionScore]:
    body_text, all_issues = normalize_entry_inputs(
        body_text, all_issues, text=True)
    description = description if isinstance(description, str) else ""
    content_text = expanded_body if isinstance(expanded_body, str) else body_text
    results: list[SubDimensionScore] = []
    q1_score, q1_detail, q1_issues = _compute_q1_code_existence(
        content_text, api_scan, doc_profile=doc_profile)
    record_dimension(results, all_issues, SubDimensionScore(
        dim_id='Q1',
        dim_name='代码示例存在性',
        category='content',
        weight=_DIM_WEIGHT['Q1'],
        score=q1_score,
        issues=q1_issues,
        detail=q1_detail
    ))
    q2_score, q2_detail, q2_issues = _compute_q2_boundary(
        body_text, description, doc_profile=doc_profile)
    record_dimension(results, all_issues, SubDimensionScore(
        dim_id='Q2',
        dim_name='能力边界声明',
        category='content',
        weight=_DIM_WEIGHT['Q2'],
        score=q2_score,
        issues=q2_issues,
        detail=q2_detail
    ))
    q3_score, q3_issues = _check_description_consistency(
        description, content_text, doc_profile=doc_profile)
    q3_detail = (f"检查{len(q3_issues)}项能力问题" if description
                 else "description为空")
    if doc_profile == "router" and q3_score < 70.0:
        q3_score = 70.0
        q3_detail = ("路由型文档：能力一致性下沉到引用指南"
                     f"（保留{len(q3_issues)}项证据，仅抬分）")
    record_dimension(results, all_issues, SubDimensionScore(
        dim_id='Q3',
        dim_name='description-正文一致性',
        category='content',
        weight=_DIM_WEIGHT['Q3'],
        score=q3_score,
        issues=q3_issues,
        detail=q3_detail
    ))
    q4_score, q4_issues, q4_stale_total = _check_code_doc_consistency(
        skill_dir, content_text)
    record_dimension(results, all_issues, SubDimensionScore(
        dim_id='Q4',
        dim_name='代码-文档一致性',
        category='content',
        weight=_DIM_WEIGHT['Q4'],
        score=q4_score,
        issues=q4_issues,
        detail=_q4_detail(q4_score, q4_issues, q4_stale_total)
    ))
    return results
def _compute_q1_code_existence(body_text, api_scan,
                               *, doc_profile: str):
    code_blocks = _code_like_blocks(iter_fenced_code_blocks(body_text), _Q1_LANG_TAGS)
    if not code_blocks:
        if doc_profile != "template":
            return _GENERAL_FLOOR_SCORE, "无代码示例（通用文档不强制）", [DocQualityIssue(
                category="content", rule_id="SD-Q1", severity="low",
                description="正文中未包含可执行代码示例（通用文档不强制）",
                suggestion="补充Python/bash代码块帮助AI快速理解调用方式",
                location="正文",
            )]
        return 30.0, "无代码示例", [DocQualityIssue(
            category="content", rule_id="SD-Q1", severity="medium",
            description="正文中未包含可执行代码示例",
            suggestion="添加Python/bash代码块帮助AI快速理解调用方式",
            location="正文",
        )]
    has_api, api_referenced = _q1_api_reference(code_blocks, api_scan)
    if api_referenced:
        return 100.0, "有代码示例+引用API", []
    if has_api:
        issue = DocQualityIssue(
            category="content", rule_id="SD-Q1-NOAPI", severity="low",
            description="代码示例未引用技能的公开API",
            suggestion="在代码示例中使用技能的实际函数/类名，提升示例可用性",
            location="正文: 代码块",
        )
        score = 80.0 if doc_profile != "template" else _GENERAL_FLOOR_SCORE
        return score, "有代码示例未引用API", [issue]
    return 70.0, "无可引用公开API", []
def _compute_q2_boundary(body_text: str, description: str,
                         *, doc_profile: str
                         ) -> tuple[float, str, list[DocQualityIssue]]:
    scan_text = f"{description}\n{body_text}"
    if _Q2_BOUNDARY_PATTERN.search(scan_text):
        return 100.0, "有能力边界声明", []
    if doc_profile != "template":
        return _GENERAL_FLOOR_SCORE, "缺少显式能力边界声明", [DocQualityIssue(
            category="content", rule_id="SD-Q2", severity="medium",
            description="description/正文中未发现能力边界声明",
            suggestion="补充不支持/不适用/仅支持等边界说明",
            location="正文",
        )]
    return 30.0, "缺少能力边界声明", [DocQualityIssue(
        category="content", rule_id="SD-Q2", severity="high",
        description="正文中未发现能力边界声明（In Scope/Out of Scope）",
        suggestion="添加能做/不能做列表，帮助AI明确技能边界",
        location="正文",
    )]
def _q1_api_reference(code_blocks: list[str], api_scan) -> tuple[bool, bool]:
    actual_names = collect_api_names(api_scan)
    if not actual_names:
        return False, False
    referenced = any(
        identifier_pattern(name).search(block)
        for block in code_blocks for name in actual_names
    )
    return True, referenced
def _q4_detail(q4_score: float, q4_issues: list, stale_total: int) -> str:
    if any(i.rule_id == "SD-Q4-NOSCAN" for i in q4_issues):
        return "无法扫描技能目录，代码-文档一致性未验证"
    if stale_total:
        return f"{stale_total}个陈旧模块引用（文档提及但不存在）"
    if q4_score < 100.0:
        return "文档未提及任何.py模块"
    return "文档模块引用均有效"
def diag_content_q5q6(body_text, all_issues, api_scan,
                      *, doc_profile: str = _DEFAULT_DOC_PROFILE,
                      expanded_body=None) -> list[SubDimensionScore]:
    body_text, all_issues = normalize_entry_inputs(
        body_text, all_issues, text=True)
    content_text = expanded_body if isinstance(expanded_body, str) else body_text
    results: list[SubDimensionScore] = []
    q5_score, q5_detail, q5_issues = _compute_q5_signature_accuracy(
        content_text, api_scan, doc_profile=doc_profile)
    record_dimension(results, all_issues, SubDimensionScore(
        dim_id='Q5',
        dim_name='函数签名准确性',
        category='content',
        weight=_DIM_WEIGHT['Q5'],
        score=q5_score,
        issues=q5_issues,
        detail=q5_detail
    ))
    q6_score, q6_detail, q6_issues = _compute_q6_code_quality(
        content_text, api_scan, doc_profile=doc_profile)
    record_dimension(results, all_issues, SubDimensionScore(
        dim_id='Q6',
        dim_name='代码示例质量',
        category='content',
        weight=_DIM_WEIGHT['Q6'],
        score=q6_score,
        issues=q6_issues,
        detail=q6_detail
    ))
    return results
def _collect_q5_func_signatures(scan_files: list) -> dict:
    func_signatures: dict[str, list[str]] = {}
    for _f_path, func in iter_scan_function_entries(scan_files):
        name = func.get("name")
        if not isinstance(name, str) or not name:
            continue
        sig = func.get("signature")
        if not isinstance(sig, str):
            continue
        func_signatures.setdefault(name, []).append(sig)
    return func_signatures
_Q5_PLACEHOLDER_ARG_RE = re.compile(r'^[A-Z][A-Z0-9_]*$')
_Q5_STAR_UNPACK_RE = re.compile(r'[(,]\s*\*{1,2}\s*[^\W\d]\w*')
_Q5_OMISSION_RE = re.compile(r'\.\.\.')
_Q5_KEYWORD_ARG_RE = re.compile(r'[(,]\s*([^\W\d]\w*)\s*(?::[^,=]+)?=')
def _q5_doc_param_names(doc_sig: str) -> list[str]:
    return [name for name in extract_param_names(doc_sig)
            if not _Q5_PLACEHOLDER_ARG_RE.fullmatch(name)]
def _q5_signature_arguments(signature: str) -> ast.arguments | None:
    try:
        tree = ast.parse(f"def {signature}:\n    pass\n")
    except (SyntaxError, ValueError, RecursionError):
        return None
    if len(tree.body) != 1 or not isinstance(tree.body[0], ast.FunctionDef):
        return None
    return tree.body[0].args
def _q5_doc_call(doc_sig: str) -> ast.Call | None:
    try:
        tree = ast.parse(doc_sig, mode="eval")
    except (SyntaxError, ValueError, RecursionError):
        return None
    return tree.body if isinstance(tree.body, ast.Call) else None
def _q5_required_param_names(signature: str) -> set[str] | None:
    args = _q5_signature_arguments(signature)
    if args is None:
        return None
    positional = [*args.posonlyargs, *args.args]
    required_count = len(positional) - len(args.defaults)
    required = {arg.arg for arg in positional[:required_count]}
    required.update(
        arg.arg for arg, default in zip(args.kwonlyargs, args.kw_defaults)
        if default is None
    )
    return required - {"self", "cls"}
def _q5_form_verdict(doc_sig: str, actual_sigs) -> bool | None:
    if _Q5_STAR_UNPACK_RE.search(doc_sig) or _Q5_OMISSION_RE.search(doc_sig):
        return None
    doc_call = _q5_doc_call(doc_sig)
    if doc_call is not None and (
            any(isinstance(arg, ast.Starred) for arg in doc_call.args)
            or any(keyword.arg is None for keyword in doc_call.keywords)):
        return None
    doc_definition_args = (
        _q5_signature_arguments(doc_sig) if doc_call is None else None)
    if doc_call is None and doc_definition_args is None:
        return None
    # 文档可能显式写出接收者（``func(self, x)``）：此时 ``self`` 是文档的
    # 第一个实参，必须参与位置映射，不能再按「隐式 self」把实际签名的首参
    # 从位置表中剔除，否则正确签名会被判成不一致、缺参签名反而被判一致。
    doc_passes_receiver = bool(
        doc_call is not None and doc_call.args
        and isinstance(doc_call.args[0], ast.Name)
        and doc_call.args[0].id in {"self", "cls"})
    if doc_call is not None:
        keyword_names = [keyword.arg for keyword in doc_call.keywords]
        if len(keyword_names) != len(set(keyword_names)):
            return False
    doc_params = set(_q5_doc_param_names(doc_sig))
    keyword_params = (
        {keyword.arg for keyword in doc_call.keywords
         if keyword.arg is not None}
        if doc_call is not None
        else set(_Q5_KEYWORD_ARG_RE.findall(doc_sig))
    )
    if doc_definition_args is not None:
        keyword_params.update(
            arg.arg for arg in doc_definition_args.kwonlyargs)
    positional_params = (doc_params - keyword_params
                         if doc_call is None else set())
    if not keyword_params and not doc_params and (
            doc_call is None or not doc_call.args
            or all(isinstance(arg, ast.Name)
                   and _Q5_PLACEHOLDER_ARG_RE.fullmatch(arg.id)
                   for arg in doc_call.args)):
        return None
    for sig in actual_sigs:
        actual_names = set(extract_param_names(sig))
        actual_args = _q5_signature_arguments(sig)
        if actual_args is None:
            if not doc_params <= actual_names:
                continue
        else:
            positional = [*actual_args.posonlyargs, *actual_args.args]
            if doc_call is not None:
                implicit_self = bool(
                    positional and positional[0].arg in {"self", "cls"}
                    and not doc_passes_receiver)
                positional_capacity = len(positional) - int(implicit_self)
                if (len(doc_call.args) > positional_capacity
                        and actual_args.vararg is None):
                    continue
                positional = positional[int(implicit_self):]
                positional_bound_names = {
                    param.arg
                    for _arg, param in zip(doc_call.args, positional)
                    if param in actual_args.args
                }
                if keyword_params & positional_bound_names:
                    continue
            if ((positional_params - actual_names)
                    and actual_args.vararg is None):
                continue
            if ((keyword_params - actual_names)
                    and actual_args.kwarg is None):
                continue
            posonly = {arg.arg for arg in actual_args.posonlyargs}
            kwonly = {arg.arg for arg in actual_args.kwonlyargs}
            if keyword_params & posonly and actual_args.kwarg is None:
                continue
            if positional_params & kwonly:
                continue
        required = _q5_required_param_names(sig)
        covered_params = (set(doc_params) if doc_call is None
                          else set(keyword_params))
        if doc_call is not None and actual_args is not None:
            posonly = {arg.arg for arg in actual_args.posonlyargs}
            covered_params.difference_update(keyword_params & posonly)
        if doc_call is not None and actual_args is not None:
            positional = [*actual_args.posonlyargs, *actual_args.args]
            if (positional and positional[0].arg in {"self", "cls"}
                    and not doc_passes_receiver):
                positional = positional[1:]
            covered_params.update(
                param.arg
                for _arg, param in zip(doc_call.args, positional))
        if required is None or required <= covered_params:
            return True
    return False
def _q5_check_func_forms(func_name, body_text, actual_sigs):
    doc_sig_forms = re.findall(
        rf'`{re.escape(func_name)}\s*\([^`]*\)`',
        body_text,
    )
    verified = False
    for doc_sig_form in doc_sig_forms:
        doc_sig = doc_sig_form.strip('`')
        verdict = _q5_form_verdict(doc_sig, actual_sigs)
        if verdict is None:
            continue
        verified = True
        if not verdict:
            return True, doc_sig
    return verified, None
def _q5_mismatch_issue(func_name, doc_sig, actual_sigs) -> DocQualityIssue:
    return DocQualityIssue(
        category="content", rule_id=f"SD-Q5-{func_name[:15]}",
        severity="medium",
        description=f"函数 {func_name}() 文档签名与实际不一致",
        suggestion=f"文档: {doc_sig[:60]} → 实际: "
                   + " | ".join(actual_sigs)[:60],
        location="正文",
    )
def _q5_nocheck_issue(severity: str = "medium") -> DocQualityIssue:
    return DocQualityIssue(
        category="content", rule_id="SD-Q5-NOCHECK", severity=severity,
        description="文档中无可验证的函数签名，签名准确性未验证",
        suggestion="在快速入门中补充带签名与返回值说明的可验证调用示例",
        location="正文",
    )
def _q5_audit_forms(body_text, func_signatures):
    checked = 0
    mismatches = 0
    issues: list[DocQualityIssue] = []
    doc_func_calls = re.findall(r'`([a-zA-Z_]\w*)\s*\(', body_text)
    for func_name in sorted(set(doc_func_calls)):
        if func_name not in func_signatures:
            continue
        has_forms, bad_sig = _q5_check_func_forms(
            func_name, body_text, func_signatures[func_name])
        if not has_forms:
            continue
        checked += 1
        if bad_sig is None:
            continue
        mismatches += 1
        if mismatches <= 10:
            issues.append(_q5_mismatch_issue(
                func_name, bad_sig, func_signatures[func_name]))
    return checked, mismatches, issues
def _compute_q5_signature_accuracy(body_text, api_scan,
                                   *, doc_profile: str):
    if has_code_surface(api_scan) is False:
        return NO_CODE_SCORE, NO_CODE_DETAIL, []
    q5_issues: list[DocQualityIssue] = []
    q5_score = 100.0
    checked = 0
    mismatches = 0
    scan_files = get_scan_files(api_scan)
    if scan_files:
        checked, mismatches, q5_issues = _q5_audit_forms(
            body_text, _collect_q5_func_signatures(scan_files))
        if checked > 0:
            q5_score = max(0.0, round((1 - mismatches / checked) * 100, 1))
        elif doc_profile != "template":
            q5_score = 70.0
            q5_issues.append(_q5_nocheck_issue("low"))
        else:
            q5_score = _UNVERIFIED_SCORE
            q5_issues.append(_q5_nocheck_issue())
    else:
        q5_score = _UNVERIFIED_SCORE
        q5_issues.append(make_noscan_issue(
            "content", "SD-Q5-NOSCAN", "函数签名准确性"))
    if not scan_files:
        detail = "无法扫描"
    elif checked:
        detail = f"检查{checked}个签名, {mismatches}个不一致"
    else:
        detail = "无可验证的签名形态（文档只提及函数名）"
    return q5_score, detail, q5_issues
def _score_q6_block(block: str, actual_names) -> float:
    block_score = 0.0
    for weight, pattern in _Q6_PATTERN_FACTORS:
        if pattern.search(block):
            block_score += weight
    if actual_names:
        api_hits = sum(1 for name in actual_names
                       if identifier_pattern(name).search(block))
        block_score += min(25.0, api_hits * 8.0)
    else:
        block_score += 5.0
    if _block_has_comment_or_docstring(block):
        block_score += 15.0
    return block_score
def _compute_q6_code_quality(body_text, api_scan,
                             *, doc_profile: str):
    q6_issues: list[DocQualityIssue] = []
    q6_score = 100.0
    all_blocks = iter_fenced_code_blocks(body_text)
    code_blocks = _code_like_blocks(all_blocks, _Q6_PY_TAGS)
    if code_blocks:
        quality_scores: list[float] = []
        actual_names = collect_api_names(api_scan)
        for block in code_blocks:
            quality_scores.append(_score_q6_block(block, actual_names))
        avg_quality = sum(quality_scores) / len(quality_scores)
        q6_score = round(avg_quality, 1)
        if avg_quality < 50:
            q6_issues.append(DocQualityIssue(
                category="content", rule_id="SD-Q6-QUALITY",
                severity="medium",
                description=f"代码示例整体质量偏低（均分{avg_quality:.0f}/100）",
                suggestion="为代码示例添加import语句、注释和实际API调用",
                location="正文: 代码块",
            ))
    elif all_blocks:
        q6_score = 100.0
    elif doc_profile != "template":
        q6_score = _GENERAL_FLOOR_SCORE
    else:
        q6_score = 0.0
        q6_issues.append(DocQualityIssue(
            category="content", rule_id="SD-Q6-NOBLOCK",
            severity="high",
            description="正文中无代码示例",
            suggestion="添加Python/bash代码块展示核心调用方式",
            location="正文",
        ))
    detail = (f"{len(code_blocks)}个代码块, 均分={q6_score:.0f}" if code_blocks
              else (f"{len(all_blocks)}个非Python代码块, 不参与Python质量评分"
                    if all_blocks else "无代码块"))
    return q6_score, detail, q6_issues
_Q7_WORKFLOW_PATTERNS: tuple[str, ...] = (
    r'工作流|workflow|流程',
    r'阶段[1-9]|Phase\s*[1-9]|step\s*[1-9]|步骤[一二三四五六七八九十]',
    (r'(?:(?:输入|读取|采集|解析|分析|诊断|检测|扫描|识别|提取)[^\n]{0,40}?'
     r'(?:处理|修复|改进|转换|生成|写入|输出|执行|优化|构建)[^\n]{0,40}?'
     r'(?:验证|校验|检查|测试|确认|核对|回归)'
     r'|(?:input|read\w*|pars\w*|analy\w*|scan\w*|extract\w*)[^\n]{0,40}?'
     r'(?:process\w*|transform\w*|generat\w*|writ\w*|execut\w*|build\w*)[^\n]{0,40}?'
     r'(?:verif\w*|validat\w*|test\w*|confirm\w*|check\w*))'),
    r'快速入门|Quick\s*Start|快速开始',
    (r'确认范围|定位入口|按需执行|验证结果|前提条件|前置准备|环境准备'
     r'|参数说明|输入说明|执行步骤|prerequisites?|preconditions?|environment setup'
     r'|parameter (?:inputs?|descriptions?)|input descriptions?|execution steps'),
    (r'回归验证|副作用检测|回滚|回退|备份|幂等|错误处理|异常处理|重试|撤销'
     r'|regression|side effects?|rollback|backups?|idempoten\w*|error handling'
     r'|exception handling|retry|retries|undo'),
    r'收敛|迭代|多轮|振荡|converg\w*|iterations?|multi[- ]pass|oscillat\w*',
)
def _q7_workflow_issue(workflow_hits: int) -> DocQualityIssue:
    return DocQualityIssue(
        category="content", rule_id="SD-Q7",
        severity="medium",
        description=(f"工作流文档不完整（{workflow_hits}/"
                     f"{len(_Q7_WORKFLOW_PATTERNS)}项要素）"),
        suggestion="补充完整的工作流描述：步骤指引、阶段编号、诊断→修复→验证链路、模式说明、安全保障、迭代收敛",
        location="正文",
    )
def _diag_q7_workflow(body_text,
                      doc_profile: str) -> SubDimensionScore:
    q7_issues: list[DocQualityIssue] = []
    workflow_hits = sum(
        1 for pattern in _Q7_WORKFLOW_PATTERNS
        if re.search(pattern, body_text, re.IGNORECASE)
    )
    step = 100.0 / len(_Q7_WORKFLOW_PATTERNS)
    if doc_profile != "template":
        q7_score = max(_GENERAL_FLOOR_SCORE, min(100.0, workflow_hits * step))
    else:
        q7_score = min(100.0, workflow_hits * step)
    if workflow_hits < 5:
        q7_issues.append(_q7_workflow_issue(workflow_hits))
    return SubDimensionScore(
        dim_id='Q7',
        dim_name='工作流完整性',
        category='content',
        weight=_DIM_WEIGHT['Q7'],
        score=q7_score,
        issues=q7_issues,
        detail=f'{workflow_hits}/{len(_Q7_WORKFLOW_PATTERNS)}项工作流要素'
    )
_Q8_REF_RE = re.compile(
    r'(?:详见|参见|参考(?![文档资链书库]))\s*'
    r'(?:\[\s*)?[「【]?(.+?)\s*[」】]?(?:\s*\])?'
    r'(?:\s*\([^)]*\))?\s*(?:章节|部分|段落)')
_Q8_REF_EN_RE = re.compile(
    r'\b(?:see(?:\s+also)?|refer\s+to)\s+(?:the\s+)?(.+?)\s+section\b',
    re.IGNORECASE)
def _q8_ref_issue(ref: str) -> DocQualityIssue:
    return DocQualityIssue(
        category="content", rule_id="SD-Q8-REF",
        severity="low",
        description=f"交叉引用 '{ref}' 指向的章节不存在",
        suggestion=f"确认章节名称或添加缺失的章节: {ref}",
        location="正文",
    )
def _q8_noref_issue() -> DocQualityIssue:
    return DocQualityIssue(
        category="content", rule_id="SD-Q8-NOREF", severity="medium",
        description="正文中无交叉引用，章节间关联性不足",
        suggestion="在各章节中添加'详见 XX 章节'类型的交叉引用，提升文档导航性",
        location="正文",
    )
_Q8_MIN_FUZZY_TITLE_LEN = 3
def _q8_ref_matches(ref: str, title: str) -> bool:
    if not ref or not title:
        return False
    if _title_matches(title, ref):
        return True
    return len(title) >= _Q8_MIN_FUZZY_TITLE_LEN and title in ref
def _q8_broken_refs(see_also_refs, all_section_titles):
    broken_refs = 0
    issues: list[DocQualityIssue] = []
    for raw_ref in see_also_refs:
        ref = raw_ref.strip()
        if not ref or not any(_q8_ref_matches(ref, title)
                              for title in all_section_titles):
            broken_refs += 1
            if broken_refs <= 5:
                issues.append(_q8_ref_issue(ref))
    return len(see_also_refs), broken_refs, issues
def _diag_q8_cross_refs(body_text, sections_found,
                        doc_profile: str) -> SubDimensionScore:
    see_also_refs = [*_Q8_REF_RE.findall(body_text),
                     *_Q8_REF_EN_RE.findall(body_text)]
    all_section_titles = {sec_title.strip() for sec_title, _ in sections_found
                          if sec_title.strip()}
    total_refs, broken_refs, q8_issues = _q8_broken_refs(
        see_also_refs, all_section_titles)
    if total_refs > 0:
        q8_score = max(0.0, round((1 - broken_refs / total_refs) * 100, 1))
    elif doc_profile != "template":
        q8_score = _GENERAL_FLOOR_SCORE
    else:
        q8_score = 40.0
        q8_issues.append(_q8_noref_issue())
    return SubDimensionScore(
        dim_id='Q8',
        dim_name='交叉引用完整性',
        category='content',
        weight=_DIM_WEIGHT['Q8'],
        score=q8_score,
        issues=q8_issues,
        detail=f'{broken_refs}/{total_refs}个引用失效' if total_refs > 0 else '无交叉引用'
    )
def diag_content_q7q8(body_text, all_issues, sections_found=None,
                      *, doc_profile: str = _DEFAULT_DOC_PROFILE) -> list[SubDimensionScore]:
    sections_found, all_issues = normalize_entry_inputs(
        sections_found, all_issues)
    sections_found = _normalize_sections_found(sections_found)
    if not isinstance(body_text, str):
        body_text = ""
    prose = strip_fenced_blocks(body_text)
    results: list[SubDimensionScore] = []
    for dim in (_diag_q7_workflow(prose, doc_profile),
                _diag_q8_cross_refs(prose, sections_found, doc_profile)):
        record_dimension(results, all_issues, dim)
    return results
_BACKTICK_CONTENT_RE = re.compile(r'`([^`\n]*)`')
_BACKTICK_CALL_RE = re.compile(r'`([^`\n]*?)\s*\(')
_IDENT_SEGMENT_RE = re.compile(r'[a-zA-Z_]\w*')
def _extract_backtick_refs(text: str, require_call: bool = False) -> list[str]:
    refs: list[str] = []
    pattern = _BACKTICK_CALL_RE if require_call else _BACKTICK_CONTENT_RE
    for captured in pattern.findall(text):
        if captured and all(
                _IDENT_SEGMENT_RE.fullmatch(seg)
                for seg in captured.split('.')):
            refs.append(captured)
    return refs
def _unmapped_api_issues(unmapped, rule_prefix: str, desc_tpl: str,
                         sugg_tpl: str, location: str) -> list:
    return [DocQualityIssue(
        category="content", rule_id=f"{rule_prefix}-{name[:15]}",
        severity="medium",
        description=desc_tpl.format(name=name),
        suggestion=sugg_tpl.format(name=name),
        location=location,
    ) for name in sorted(unmapped)[:5]]
def _title_matches(title: str, keywords) -> bool:
    wanted = (keywords,) if isinstance(keywords, str) else tuple(keywords)
    lowered = title.lower()
    for keyword in wanted:
        if not isinstance(keyword, str) or not keyword:
            continue
        lowered_kw = keyword.lower()
        if lowered_kw.isascii():
            if re.search(rf"(?<![a-z0-9]){re.escape(lowered_kw)}", lowered):
                return True
            continue
        if lowered_kw in lowered:
            return True
    return False
def _find_sections(sections_found, keywords) -> tuple[str, bool]:
    matched = [content for title, content in sections_found
               if _title_matches(title, keywords)]
    return "\n".join(matched), bool(matched)
def check_q9_q10_q11(sections_found: list | None = None,
                     api_scan: dict | None = None,
                     all_issues: list | None = None,
                     *, doc_profile: str = _DEFAULT_DOC_PROFILE,
                     expanded_body=None) -> list[SubDimensionScore]:
    sections_found, all_issues = normalize_entry_inputs(
        sections_found, all_issues)
    sections_found = _normalize_sections_found(sections_found)
    results: list[SubDimensionScore] = []
    for dim in (_check_q9_alignment(sections_found, api_scan,
                                    doc_profile=doc_profile,
                                    expanded_body=expanded_body),
                _check_q10_constraints(sections_found, api_scan,
                                       doc_profile=doc_profile),
                _check_q11_scenario_mapping(sections_found, api_scan,
                                            doc_profile=doc_profile)):
        record_dimension(results, all_issues, dim)
    return results
_Q9_FILE_REF_EXTS = frozenset({
    "py", "pyi", "md", "json", "jsonl", "yaml", "yml", "toml", "txt",
    "rst", "sh", "bash", "ini", "cfg", "csv", "tsv", "html", "xml", "log",
})
_Q9_SECTION_KEYWORDS = ("模块", "详解", "module", "api")
_STDLIB_TOP_LEVEL = frozenset(getattr(sys, "stdlib_module_names", ()))
_BUILTIN_REF_ROOTS = frozenset(dir(builtins))
def _q9_module_ref(ref: str, actual_names=()) -> str | None:
    tail = ref.rsplit('.', 1)[-1]
    if tail in actual_names:
        return tail
    if ref.count('.') and tail.lower() in _Q9_FILE_REF_EXTS:
        return None
    if ref.split('.', 1)[0] in _STDLIB_TOP_LEVEL:
        return None
    if ref.split('.', 1)[0] in _BUILTIN_REF_ROOTS:
        return None
    return tail
def _q9_collect_refs(sections_found, actual_names=()) -> set:
    code_blocks = set()
    for sec_title, sec_content in sections_found:
        if not _title_matches(sec_title, _Q9_SECTION_KEYWORDS):
            continue
        for ref in _extract_backtick_refs(sec_content):
            tail = _q9_module_ref(ref, actual_names)
            if tail:
                code_blocks.add(tail)
    return code_blocks
def _collect_call_refs(text, actual_names=()) -> set:
    if not isinstance(text, str):
        text = ""
    refs = set()
    for ref in _extract_backtick_refs(text, require_call=True):
        tail = _q9_module_ref(ref, actual_names)
        if tail:
            refs.add(tail)
    return refs
def _q9_expanded_score(expanded_body, actual_names,
                       *, no_code_surface: bool = False) -> SubDimensionScore:
    code_blocks = _collect_call_refs(
        expanded_body if isinstance(expanded_body, str) else "", actual_names)
    if no_code_surface and not code_blocks:
        return SubDimensionScore(
            dim_id='Q9',
            dim_name='代码-API对齐度',
            category='content',
            weight=_DIM_WEIGHT['Q9'],
            score=NO_CODE_SCORE,
            issues=[],
            detail=NO_CODE_DETAIL
        )
    if not code_blocks or not actual_names:
        return SubDimensionScore(
            dim_id='Q9',
            dim_name='代码-API对齐度',
            category='content',
            weight=_DIM_WEIGHT['Q9'],
            score=70.0,
            issues=[],
            detail='无足够反引号调用引用，按中性分计'
        )
    mapped = code_blocks & actual_names
    score = max(_GENERAL_FLOOR_SCORE, round(
        len(mapped) / len(code_blocks) * 100, 1))
    return SubDimensionScore(
        dim_id='Q9',
        dim_name='代码-API对齐度',
        category='content',
        weight=_DIM_WEIGHT['Q9'],
        score=score,
        issues=[],
        detail=f'{len(mapped)}/{len(code_blocks)}个调用引用已对齐'
    )
def _check_q9_alignment(sections_found, api_scan,
                        *, doc_profile: str,
                        expanded_body) -> SubDimensionScore:
    q9_issues = []
    q9_score = 100.0
    no_code_surface = (doc_profile != "router"
                       and has_code_surface(api_scan) is False)
    actual_names = collect_api_names(api_scan, include_module_names=True)
    if doc_profile == "router":
        return SubDimensionScore(
            dim_id='Q9',
            dim_name='代码-API对齐度',
            category='content',
            weight=_DIM_WEIGHT['Q9'],
            score=80.0,
            issues=[],
            detail='路由型文档：不校验代码-API对齐'
        )
    if doc_profile != "template":
        if not isinstance(expanded_body, str):
            expanded_body = "\n".join(
                content for _title, content in sections_found)
        return _q9_expanded_score(
            expanded_body, actual_names, no_code_surface=no_code_surface)
    code_blocks = _q9_collect_refs(sections_found, actual_names)
    if no_code_surface and not code_blocks:
        return SubDimensionScore(
            dim_id='Q9',
            dim_name='代码-API对齐度',
            category='content',
            weight=_DIM_WEIGHT['Q9'],
            score=NO_CODE_SCORE,
            issues=[],
            detail=NO_CODE_DETAIL
        )
    if code_blocks and actual_names:
        mapped = code_blocks & actual_names
        unmapped = code_blocks - actual_names
        q9_score = round(len(mapped) / max(len(code_blocks), 1) * 100, 1)
        q9_detail = f"{len(mapped)}/{len(code_blocks)}个API引用已对齐"
        q9_issues.extend(_unmapped_api_issues(
            unmapped, "SD-Q9",
            "文档中引用的 {name}() 不在技能公开API中",
            "确认 {name}() 是否存在，或修正文档引用", "正文"))
    elif code_blocks and not actual_names:
        q9_score = _UNVERIFIED_SCORE
        q9_detail = f"{len(code_blocks)}处引用无可对齐的公开API"
        if not has_scan_files(api_scan):
            q9_issues.append(make_noscan_issue(
                "content", "SD-Q9-NOSCAN", "代码-API对齐度"))
    else:
        q9_score = 70.0
        q9_detail = "模块章节无反引号代码引用"
    return SubDimensionScore(
        dim_id='Q9',
        dim_name='代码-API对齐度',
        category='content',
        weight=_DIM_WEIGHT['Q9'],
        score=q9_score,
        issues=q9_issues,
        detail=q9_detail
    )
_Q10_CONSTRAINT_CHECKS: tuple[tuple[str, str, str, str, str], ...] = (
    ("SEC", "medium", r'\bsafe_|安全|sandbox|可恢复|回收站|删除.*包装|防护|recoverable|recycle\s+bin|trash',
     "关键约束章节未记录删除操作的安全要求",
     "在关键约束中说明删除目标确认、可恢复删除或回收站等安全保护要求"),
    ("DB", "low", r'防注入|参数化|parameteri[sz]ed|sql\s+injection',
     "关键约束章节未记录数据库安全要求",
     "在关键约束中添加 '数据库操作使用参数化查询并避免拼接不受信任输入' 条目"),
)
_Q10_CONSTRAINT_BY_ID = {item[0]: item for item in _Q10_CONSTRAINT_CHECKS}
# 约束章节的关键词命中必须是**肯定**陈述：文档写“无安全要求/不做安全包装”
# 或“禁止直接删除”时，命中落在否定分句里，不能算约束已文档化。
# `safe_` 还需左边界，否则 `unsafe_delete` 会被当成 `safe_delete` 命中。
# 否定作用域取到命中所在分句（句读/换行/逗号）为止，避免跨分句误伤
# “禁止直接删除，使用回收站”这类“否定 + 正确要求”的混合句。
_Q10_CLAUSE_BREAK_RE = re.compile(r"[。；;！!？?\n，,]")
_Q10_NEGATION_RE = re.compile(
    r"(?:不|非|未|无|勿|别|禁止|避免|不得|无需|不必|严禁|切勿"
    r"|\bnot\b|\bno\b|\bwithout\b|\bnever\b)",
    re.IGNORECASE,
)
def _q10_clause_prefix(content: str, start: int) -> str:
    breaks = list(_Q10_CLAUSE_BREAK_RE.finditer(content, 0, start))
    return content[breaks[-1].end():start] if breaks else content[:start]
def _q10_constraint_hit(pattern: str, content: str) -> bool:
    for match in re.finditer(pattern, content, re.IGNORECASE):
        if _Q10_NEGATION_RE.search(_q10_clause_prefix(content, match.start())):
            continue
        return True
    return False
def _q10_missing_issue(applicable_count: int) -> DocQualityIssue:
    return DocQualityIssue(
        category="content", rule_id="SD-Q10-MISSING", severity="medium",
        description="存在需要安全约束的操作，但文档未设关键约束章节",
        suggestion=(f"补充 {applicable_count} 项适用约束（删除安全/数据库）"
                    "所需的关键约束章节"),
        location="正文",
    )
_Q10_SECTION_KEYWORDS = ("约束", "安全", "constraint", "safety", "security")
_DB_MODULE_ROOTS = frozenset({
    'sqlite3', 'pymysql', 'psycopg', 'psycopg2', 'sqlalchemy', 'asyncpg',
    'aiosqlite',
})
_DB_EVIDENCE_RE = re.compile(
    r'\b(?:' + '|'.join(sorted(_DB_MODULE_ROOTS)) + r')\b'
    r'|\.execute\s*\(', re.IGNORECASE)
_DESTRUCTIVE_EVIDENCE_RE = re.compile(
    r'\b(?:os\.(?:remove|removedirs|unlink|rmdir)|shutil\.rmtree|'
    r'send2trash|safe_delete)\b|\.(?:unlink|rmdir)\s*\(')
_DESTRUCTIVE_MODULE_CALLS = {
    "os": frozenset({"remove", "removedirs", "unlink", "rmdir"}),
    "shutil": frozenset({"rmtree"}),
    "send2trash": frozenset({"send2trash"}),
}
def _destructive_import_bindings(tree):
    module_aliases = {}
    direct_calls = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name in _DESTRUCTIVE_MODULE_CALLS:
                    module_aliases[alias.asname or alias.name] = alias.name
            continue
        if (not isinstance(node, ast.ImportFrom) or node.level
                or node.module not in _DESTRUCTIVE_MODULE_CALLS):
            continue
        supported = _DESTRUCTIVE_MODULE_CALLS[node.module]
        for alias in node.names:
            if alias.name == "*":
                direct_calls.update(supported)
            elif alias.name in supported:
                direct_calls.add(alias.asname or alias.name)
    return module_aliases, direct_calls
def _source_ast(source: str | ast.Module) -> ast.Module | None:
    if isinstance(source, ast.Module):
        return source
    try:
        return ast.parse(source)
    except (SyntaxError, ValueError, RecursionError):
        return None
def _ast_has_destructive_alias_call(source: str | ast.Module) -> bool:
    tree = _source_ast(source)
    if tree is None:
        return False
    module_aliases, direct_calls = _destructive_import_bindings(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        if (isinstance(node.func, ast.Name)
                and (node.func.id in direct_calls
                     or node.func.id == 'safe_delete')):
            return True
        if not isinstance(node.func, ast.Attribute):
            continue
        if node.func.attr in {'unlink', 'rmdir'}:
            return True
        if not isinstance(node.func.value, ast.Name):
            continue
        module = module_aliases.get(node.func.value.id)
        if (module is not None
                and node.func.attr in _DESTRUCTIVE_MODULE_CALLS[module]):
            return True
    return False
def _ast_has_db_evidence(source: str | ast.Module) -> bool:
    tree = _source_ast(source)
    if tree is None:
        return False
    for node in walk_nodes(tree):
        if (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == 'execute'):
            return True
        if isinstance(node, ast.Name) and node.id in _DB_MODULE_ROOTS:
            return True
        if isinstance(node, ast.Import) and any(
                alias.name.split('.', 1)[0] in _DB_MODULE_ROOTS
                for alias in node.names):
            return True
        if (isinstance(node, ast.ImportFrom) and node.module
                and node.module.split('.', 1)[0] in _DB_MODULE_ROOTS):
            return True
    return False
_SOURCE_SCAN_MAX_BYTES = 1024 * 1024
_SOURCE_SCAN_SKIP_DIRS = frozenset(
    (*GENERIC_SCAN_IGNORE_DIRS_LOWER,
     *(name.lower() for name in GENERIC_DIAG_OUT_OF_SCOPE_DIRS),
     "references", "assets"))
def _iter_production_sources(skill_dir: str, walk_errors: list | None = None):
    def _on_walk_error(err):
        _log.warning("[SkillDoc][Q10] 源码目录遍历失败，证据不完整: %s", err)
        if walk_errors is not None:
            walk_errors.append(err)
    for root, dirs, files in os.walk(skill_dir, onerror=_on_walk_error):
        dirs[:] = sorted(
            d for d in dirs
            if not d.startswith(".")
            and d.lower() not in _SOURCE_SCAN_SKIP_DIRS
            and not is_audit_skip_dir(d))
        for fname in sorted(files):
            if (is_scan_py_name(fname)
                    and not is_transient_module_name(fname)):
                yield os.path.join(root, fname)
def _read_capped_source(path: str) -> str | None:
    try:
        with open(path, "rb") as fh:
            data = fh.read(_SOURCE_SCAN_MAX_BYTES + 1)
    except OSError as exc:
        log_swallowed(__name__, exc,
                      context=f'_read_capped_source:{type(exc).__name__}')
        return None
    if len(data) > _SOURCE_SCAN_MAX_BYTES:
        return None
    try:
        encoding = tokenize.detect_encoding(io.BytesIO(data).readline)[0]
        return data.decode(encoding)
    except (LookupError, SyntaxError, UnicodeDecodeError) as exc:
        log_swallowed(__name__, exc,
                      context=f'_read_capped_source:{type(exc).__name__}')
        return None
def _executable_evidence_text(source: str) -> str | None:
    try:
        tokens = list(tokenize.generate_tokens(io.StringIO(source).readline))
    except (tokenize.TokenError, SyntaxError, ValueError, MemoryError,
            RecursionError) as exc:
        log_swallowed(__name__, exc,
                      context=f'_executable_evidence_text:{type(exc).__name__}')
        return None
    # Python 3.12+（PEP 701）把 f-string 拆成 FSTRING_START/MIDDLE/END，
    # 字面文本不再是单个 STRING token；不纳入掩码会让日志/提示语里的
    # f"os.remove({p})"、f"cursor.execute({q})" 被当成真实代码证据。
    masked_types = {tokenize.COMMENT, tokenize.STRING}
    masked_types.update(
        tok_type for tok_type in (
            getattr(tokenize, 'FSTRING_START', None),
            getattr(tokenize, 'FSTRING_MIDDLE', None),
            getattr(tokenize, 'FSTRING_END', None),
        ) if tok_type is not None)
    if not any(tok.type in masked_types for tok in tokens):
        return source
    # 行偏移须与 tokenize.generate_tokens 的行号规则一致：readline 只按
    # "\n" 断行；str.splitlines 还会在 \x0b/\x0c/\x85/\u2028 等处断行，
    # 字符串字面量含这些字符时行号表会多出行，掩码区间整体错位。
    line_offsets = [0]
    line_offsets.extend(match.end() for match in re.finditer(r"\n", source))
    chars = list(source)
    for tok in tokens:
        if tok.type not in masked_types:
            continue
        start = line_offsets[tok.start[0] - 1] + tok.start[1]
        end = line_offsets[tok.end[0] - 1] + tok.end[1]
        for index in range(start, min(end, len(chars))):
            if chars[index] not in '\r\n':
                chars[index] = ' '
    return ''.join(chars)
def _skill_source_evidence(api_scan) -> tuple[bool, bool, bool]:
    if not isinstance(api_scan, dict):
        return False, False, False
    skill_dir = api_scan.get("skill_dir")
    if not isinstance(skill_dir, str) or not os.path.isdir(skill_dir):
        return False, False, False
    destructive = uses_db = False
    seen_source = False
    walk_errors: list = []
    for path in _iter_production_sources(skill_dir, walk_errors):
        seen_source = True
        text = _read_capped_source(path)
        if text is None:
            _log.warning("[SkillDoc][Q10] 源文件不可读或超出读取预算，"
                         "约束证据不完整: %s", path)
            return False, False, False
        tree = _source_ast(text)
        if tree is None:
            _log.warning("[SkillDoc][Q10] 源码语法分析失败，约束证据不完整: %s",
                         path)
            return False, False, False
        code_text = _executable_evidence_text(text)
        if code_text is None:
            _log.warning("[SkillDoc][Q10] 源码词法分析失败，约束证据不完整: %s",
                         path)
            return False, False, False
        destructive = (destructive
                       or bool(_DESTRUCTIVE_EVIDENCE_RE.search(code_text))
                       or _ast_has_destructive_alias_call(tree))
        uses_db = (uses_db
                   or bool(_DB_EVIDENCE_RE.search(code_text))
                   or _ast_has_db_evidence(tree))
        if destructive and uses_db:
            break
    if not seen_source or walk_errors:
        return False, False, False
    return destructive, uses_db, True
def _q10_general_constraints(sections_found, api_scan) -> SubDimensionScore:
    if has_code_surface(api_scan) is False:
        return SubDimensionScore(
            dim_id='Q10',
            dim_name='约束文档完整性',
            category='content',
            weight=_DIM_WEIGHT['Q10'],
            score=NO_CODE_SCORE,
            issues=[],
            detail=NO_CODE_DETAIL
        )
    if not has_scan_files(api_scan):
        return SubDimensionScore(
            dim_id='Q10',
            dim_name='约束文档完整性',
            category='content',
            weight=_DIM_WEIGHT['Q10'],
            score=_UNVERIFIED_SCORE,
            issues=[make_noscan_issue('content', 'SD-Q10-NOSCAN', '约束文档完整性')],
            detail='无法扫描'
        )
    uses_destructive, uses_db, evidence_known = _skill_source_evidence(api_scan)
    if not evidence_known:
        return SubDimensionScore(
            dim_id='Q10',
            dim_name='约束文档完整性',
            category='content',
            weight=_DIM_WEIGHT['Q10'],
            score=_UNVERIFIED_SCORE,
            issues=[make_noscan_issue(
                'content', 'SD-Q10-NOSCAN', '约束文档完整性',
                target_label='技能源码')],
            detail='源码证据不可用，适用约束未判定'
        )
    applicable = []
    if uses_destructive:
        applicable.append(_Q10_CONSTRAINT_BY_ID["SEC"])
    if uses_db:
        applicable.append(_Q10_CONSTRAINT_BY_ID["DB"])
    if not applicable:
        return SubDimensionScore(
            dim_id='Q10',
            dim_name='约束文档完整性',
            category='content',
            weight=_DIM_WEIGHT['Q10'],
            score=100.0,
            issues=[],
            detail='无适用约束项（未检出删除/数据库操作）'
        )
    constraint_content, _ = _find_sections(
        sections_found, _Q10_SECTION_KEYWORDS)
    if not constraint_content.strip():
        return SubDimensionScore(
            dim_id='Q10',
            dim_name='约束文档完整性',
            category='content',
            weight=_DIM_WEIGHT['Q10'],
            score=0.0,
            issues=[_q10_missing_issue(len(applicable))],
            detail=f'0/{len(applicable)}项适用约束已文档化'
        )
    passed = 0
    q10_issues: list[DocQualityIssue] = []
    for suffix, severity, pattern, desc_tpl, suggestion in applicable:
        if _q10_constraint_hit(pattern, constraint_content):
            passed += 1
            continue
        q10_issues.append(DocQualityIssue(
            category="content", rule_id=f"SD-Q10-{suffix}",
            severity=severity,
            description=desc_tpl,
            suggestion=suggestion,
            location="正文: 关键约束",
        ))
    score = round(passed / len(applicable) * 100, 1)
    return SubDimensionScore(
        dim_id='Q10',
        dim_name='约束文档完整性',
        category='content',
        weight=_DIM_WEIGHT['Q10'],
        score=score,
        issues=q10_issues,
        detail=f'{passed}/{len(applicable)}项适用约束已文档化'
    )
def _check_q10_constraints(sections_found, api_scan,
                           *, doc_profile: str) -> SubDimensionScore:
    if doc_profile == "router":
        return SubDimensionScore(
            dim_id='Q10',
            dim_name='约束文档完整性',
            category='content',
            weight=_DIM_WEIGHT['Q10'],
            score=100.0,
            issues=[],
            detail='路由型文档：约束说明下沉到引用指南'
        )
    return _q10_general_constraints(sections_found, api_scan)
_Q11_SECTION_KEYWORDS = ("场景", "应用", "use case", "usecase", "scenario")
def _q11_noapi_issue() -> DocQualityIssue:
    return DocQualityIssue(
        category="content", rule_id="SD-Q11-NOAPI", severity="medium",
        description="典型应用场景中未引用具体入口函数",
        suggestion="在场景表中添加 '入口' 列，引用实际的函数名",
        location="正文: 典型应用场景",
    )
def _q11_empty_issue() -> DocQualityIssue:
    return DocQualityIssue(
        category="content", rule_id="SD-Q11-EMPTY", severity="medium",
        description="典型应用场景章节存在但内容为空",
        suggestion="填充场景|入口|说明映射表，引用实际的函数名",
        location="正文: 典型应用场景",
    )
def _q11_nosection_issue() -> DocQualityIssue:
    return DocQualityIssue(
        category="content", rule_id="SD-Q11-NOSECTION", severity="high",
        description="缺少典型应用场景章节",
        suggestion="添加'## 典型应用场景'章节，包含场景|入口|说明映射表",
        location="正文",
    )
_Q11_NO_SECTION_SCORE = 30.0
def _q11_assess_mapping(usecase_content, has_usecase_section, api_scan,
                        actual_names, scenario_funcs):
    if not isinstance(usecase_content, str):
        usecase_content = ""
    if not usecase_content.strip():
        if has_usecase_section:
            return _UNVERIFIED_SCORE, [_q11_empty_issue()], "场景章节内容为空"
        return _Q11_NO_SECTION_SCORE, [_q11_nosection_issue()], "无场景章节"
    if not scenario_funcs:
        if not has_scan_files(api_scan):
            return _UNVERIFIED_SCORE, [make_noscan_issue(
                "content", "SD-Q11-NOSCAN", "应用场景-API映射")], "无法扫描"
        if not actual_names:
            return _UNVERIFIED_SCORE, [], "技能无公开API，场景映射未验证"
        return _UNVERIFIED_SCORE, [_q11_noapi_issue()], "场景未引用入口函数"
    if not actual_names:
        detail = f"技能无公开API，{len(scenario_funcs)}个场景引用未验证"
        if not has_scan_files(api_scan):
            return _UNVERIFIED_SCORE, [make_noscan_issue(
                "content", "SD-Q11-NOSCAN", "应用场景-API映射")], detail
        return _UNVERIFIED_SCORE, [], detail
    mapped = scenario_funcs & actual_names
    unmapped = scenario_funcs - actual_names
    score = round(len(mapped) / len(scenario_funcs) * 100, 1)
    return (score, _unmapped_api_issues(
        unmapped, "SD-Q11",
        "典型应用场景中的入口 {name}() 不在技能公开API中",
        "确认 {name}() 是否存在，或更新场景映射使用真实API",
        "正文: 典型应用场景"),
        f"{len(mapped)}/{len(scenario_funcs)}个场景API已映射")
def _check_q11_scenario_mapping(sections_found, api_scan,
                                *, doc_profile: str
                                ) -> SubDimensionScore:
    usecase_content, has_usecase_section = _find_sections(
        sections_found, _Q11_SECTION_KEYWORDS)
    if doc_profile != "template" and not has_usecase_section:
        return SubDimensionScore(
            dim_id='Q11',
            dim_name='应用场景-API映射',
            category='content',
            weight=_DIM_WEIGHT['Q11'],
            score=70.0,
            issues=[],
            detail='无应用场景章节：按中性分计'
        )
    actual_names = collect_api_names(api_scan)
    scenario_funcs = _collect_call_refs(usecase_content, actual_names)
    if (has_code_surface(api_scan) is False
            and has_usecase_section
            and isinstance(usecase_content, str)
            and usecase_content.strip()
            and not scenario_funcs):
        return SubDimensionScore(
            dim_id='Q11',
            dim_name='应用场景-API映射',
            category='content',
            weight=_DIM_WEIGHT['Q11'],
            score=NO_CODE_SCORE,
            issues=[],
            detail=NO_CODE_DETAIL
        )
    q11_score, q11_issues, detail = _q11_assess_mapping(
        usecase_content, has_usecase_section, api_scan,
        actual_names, scenario_funcs)
    if doc_profile != "template" and q11_score < _GENERAL_FLOOR_SCORE:
        q11_score = _GENERAL_FLOOR_SCORE
    return SubDimensionScore(
        dim_id='Q11',
        dim_name='应用场景-API映射',
        category='content',
        weight=_DIM_WEIGHT['Q11'],
        score=q11_score,
        issues=q11_issues,
        detail=detail
    )
def _strip_enum_conj(cap: str) -> str:
    for conj in _Q3_ENUM_CONJS:
        if cap.startswith(conj):
            return cap[len(conj):] if len(cap) >= len(conj) + 4 else cap
    return cap
_Q3_COMPOUND_SPLIT_RE = re.compile(r'以及|或者|[及与和或]|(?<!合)并')
def _cap_compound_outcomes(cap: str) -> list[str]:
    if not _Q3_COMPOUND_SPLIT_RE.search(cap):
        return [cap]
    sides = [side for side in _Q3_COMPOUND_SPLIT_RE.split(cap) if side]
    valid = [side for side in sides if _is_cap_word_form(side)]
    return valid or [cap]
_Q3_ENUM_MARKER_RE = re.compile(
    r'(?:核心能力|能力|功能)?\s*(?:包括|包含|覆盖|支持)[：:]\s*([^\n。；;]+)')
def _q3_negated_spans(text) -> list[tuple[int, int]]:
    if not isinstance(text, str) or not text:
        return []
    spans: list[tuple[int, int]] = []
    for match in _Q3_NEGATION_CLAUSE_RE.finditer(text):
        end = _Q3_CLAUSE_END_RE.search(text, match.end())
        spans.append((match.start(), end.start() if end else len(text)))
    return spans
def _q3_negated_at(start: int, end: int, spans) -> bool:
    if not spans:
        return False
    return any(start < span_end and span_start < end
               for span_start, span_end in spans)
def _extract_capability_enum(description: str) -> list[str]:
    caps: list[str] = []
    spans = _q3_negated_spans(description)
    for match in _Q3_ENUM_MARKER_RE.finditer(description):
        if _q3_negated_at(match.start(), match.end(), spans):
            continue
        for raw_segment in re.split(r'[、,，/]', match.group(1)):
            segment = raw_segment.strip()
            if not segment:
                continue
            if _Q3_NEGATION_CLAUSE_RE.match(segment):
                continue
            verb = next((v for v in _Q3_CAP_SUFFIXES
                         if segment.startswith(v)), None)
            if verb:
                caps.append(verb)
                continue
            cap = _strip_cap_glue(_strip_enum_conj(segment))
            caps.extend(_cap_outcomes(cap))
    return caps
def _extract_cn_capability_words(description: str) -> list[str]:
    caps: list[str] = list(dict.fromkeys(_extract_capability_enum(description)))
    spans = _q3_negated_spans(description)
    for m in _Q3_CAP_WORD_PATTERN.finditer(description):
        if _q3_negated_at(m.start(), m.end(), spans):
            continue
        cap = m.group()
        if any(cap.startswith(t) for t in _Q3_TRIGGER_PREFIXES):
            continue
        cap = _strip_cap_glue(cap)
        cap = _strip_enum_conj(cap)
        if description[m.end():m.end() + 1] in _Q3_TEMPORAL_FOLLOWERS:
            continue
        caps.extend(_cap_outcomes(cap))
    return list(dict.fromkeys(caps))
def _cap_outcomes(cap: str, *, max_len: int = 12) -> list[str]:
    outcomes: list[str] = []
    for side in _cap_compound_outcomes(cap):
        if not (2 <= len(side) <= max_len and _is_cap_word_form(side)):
            continue
        if any(ch in _cap_core(side) for ch in _Q3_NARRATIVE_FUNC_CHARS):
            continue
        outcomes.append(side)
    return outcomes
def _cut_cap_verb_prefix(cap: str) -> str:
    core = _cap_core(cap)
    cut = -1
    for verb in _Q3_CAP_PREFIX_VERBS:
        idx = core.rfind(verb)
        if idx >= 0:
            cut = max(cut, idx + len(verb))
    return cap[cut:] if cut >= 0 else cap
def _peel_cap_head_once(cap: str) -> str:
    verb = next((v for v in _Q3_LEADING_LIGHT_VERBS
                 if cap.startswith(v)), None)
    if verb:
        return cap[len(verb):]
    if (cap and cap[0] in _Q3_MODAL_CHARS and len(cap) > 3
            and any(cap.startswith(v, 1)
                    for v in _Q3_LEADING_LIGHT_VERBS)):
        return cap[1:]
    return cap
def _strip_cap_glue(cap: str) -> str:
    cap = _cut_cap_verb_prefix(cap)
    for _ in range(3):
        peeled = _peel_cap_head_once(cap)
        if peeled == cap:
            break
        cap = peeled
    return cap
def _cap_suffix_of(word: str) -> str:
    return next((s for s in _Q3_CAP_SUFFIXES if word.endswith(s)), "")
def _cap_core(word: str) -> str:
    suffix = _cap_suffix_of(word)
    return word[:len(word) - len(suffix)] if suffix else word
def _is_cap_word_form(word: str) -> bool:
    if not word.endswith(_Q3_CAP_SUFFIXES):
        return False
    core = _cap_core(word)
    return not core or len(core) >= 2
def _is_en_clause_residue(token: str) -> bool:
    word = token.casefold()
    if word in _Q3_EN_LEADING_BREAKS:
        return True
    return (word.endswith(_Q3_EN_VERB_ENDINGS)
            and not word.endswith(_Q3_EN_NOUN_ENDINGS))
def _normalize_en_capability(cap: str) -> str:
    tokens = cap.strip().split()
    cut = 0
    for index, token in enumerate(tokens[:-1]):
        if _is_en_clause_residue(token):
            cut = index + 1
    return ' '.join(tokens[cut:])
def _extract_en_capability_words(description: str) -> list[str]:
    if not isinstance(description, str) or not description:
        return []
    spans = _q3_negated_spans(description)
    caps = (_normalize_en_capability(match.group())
            for match in _EN_CAP_PATTERN.finditer(description)
            if not _q3_negated_at(match.start(), match.end(), spans))
    return list(dict.fromkeys(cap for cap in caps if cap))
def _bilingual_capability_aliases(*texts: str) -> dict[str, set[str]]:
    aliases: dict[str, set[str]] = {}
    for text in texts:
        if not isinstance(text, str):
            continue
        for pattern in (_Q3_CN_EN_PAIR_RE, _Q3_EN_CN_PAIR_RE):
            for match in pattern.finditer(text):
                cn = _strip_enum_conj(_strip_cap_glue(match['cn'].strip()))
                en = _normalize_en_capability(match['en'].strip())
                if not cn or not en:
                    continue
                aliases.setdefault(cn.casefold(), set()).add(en)
                aliases.setdefault(en.casefold(), set()).add(cn)
    return aliases
def _q3_positive_term_hit(term: str, body_text: str,
                          negated_spans) -> bool:
    if not term:
        return False
    return any(
        not _q3_negated_at(match.start(), match.end(), negated_spans)
        for match in re.finditer(re.escape(term), body_text, re.IGNORECASE)
    )
def _q3_cap_hit(cap: str, body_text: str,
                aliases: dict[str, set[str]]) -> bool:
    core = _cap_core(cap)
    cap_lower = cap.casefold()
    candidates = [cap]
    if core and len(core) >= 3:
        candidates.append(core)
    candidates.extend(aliases.get(cap_lower, set()))
    negated_spans = _q3_negated_spans(body_text)
    return any(
        _q3_positive_term_hit(term, body_text, negated_spans)
        for term in dict.fromkeys(candidates)
    )
def _q3_cross_language_unverified(cap: str, body_text: str) -> bool:
    if not body_text.strip():
        return False
    cap_has_cn = bool(re.search(r'[\u4e00-\u9fff]', cap))
    cap_has_en = bool(re.search(r'[A-Za-z]', cap))
    body_has_cn = bool(re.search(r'[\u4e00-\u9fff]', body_text))
    body_has_en = bool(re.search(r'[A-Za-z]', body_text))
    return bool((cap_has_cn and body_has_en and not body_has_cn)
                or (cap_has_en and body_has_cn and not body_has_en))
def _q3_cross_lingual_issue(caps: list[str]) -> DocQualityIssue:
    return DocQualityIssue(
        category="content", rule_id="SD-Q3-CROSS-LINGUAL", severity="low",
        description=(f"{len(caps)}项能力缺少同文证据或显式双语对应，未验证一致性: "
                     + ", ".join(sorted(caps)[:5])),
        suggestion="在正文保留能力原文，或用'中文（English）'/'English（中文）'标注对应关系",
        location="正文",
    )
def _q3_miss_issue(cap: str) -> DocQualityIssue:
    return DocQualityIssue(
        category="content", rule_id=f"SD-Q3-{cap[:10]}", severity="medium",
        description=f"description中提到的能力 '{cap}' 在正文中无对应说明",
        suggestion=f"在'典型应用场景'或'域总览'中补充'{cap}'的详细说明",
        location="正文",
    )
def _q3_nocap_issue() -> DocQualityIssue:
    return DocQualityIssue(
        category="content", rule_id="SD-Q3-NOCAP", severity="medium",
        description="description中未提取到明确的能力关键词，无法验证一致性",
        suggestion="在description中使用明确的能力动词（如转换/提取/诊断/修复），"
                   "或用'核心能力包括：A、B、C'显式枚举",
        location="frontmatter: description",
    )
def _check_description_consistency(description: str, body_text: str,
                                   *, doc_profile: str = _DEFAULT_DOC_PROFILE):
    q3_issues = []
    if not description:
        return 0.0, q3_issues
    cap_patterns = _extract_cn_capability_words(description)
    en_caps = _extract_en_capability_words(description)
    all_caps = set(cap_patterns + en_caps)
    if all_caps:
        aliases = _bilingual_capability_aliases(description, body_text)
        matched = 0
        unverified = []
        for cap in sorted(all_caps):
            if _q3_cap_hit(cap, body_text, aliases):
                matched += 1
            elif _q3_cross_language_unverified(cap, body_text):
                unverified.append(cap)
            else:
                q3_issues.append(_q3_miss_issue(cap))
        if unverified:
            q3_issues.append(_q3_cross_lingual_issue(unverified))
        credit = matched + len(unverified) * 0.5
        floor = 20.0 if doc_profile == "template" else 50.0
        q3_score = max(floor, round(credit / len(all_caps) * 100, 1))
    else:
        q3_score = 55.0
        q3_issues.append(_q3_nocap_issue())
    return q3_score, q3_issues
def _q4_stale_issues(stale) -> list:
    return [DocQualityIssue(
        category="content", rule_id=f"SD-Q4-STALE-{py_stem(fname)}",
        severity="medium",
        description=f"文档提及的模块 {fname} 在技能目录中不存在",
        suggestion=f"修正或删除对 {fname} 的陈旧引用（可能已重命名/合并）",
        location="正文",
    ) for fname in stale[:5]]
def _check_code_doc_consistency(skill_dir: str, body_text: str):
    q4_issues = []
    raw_skill_dir = skill_dir
    skill_dir = _path_arg(skill_dir)
    if not skill_dir or not os.path.isdir(skill_dir):
        _log.warning("[SkillDoc][Q4] skill_dir 不可用，代码-文档一致性未验证: %r",
                     raw_skill_dir)
        q4_issues.append(make_noscan_issue(
            "content", "SD-Q4-NOSCAN", "代码-文档一致性"))
        return _UNVERIFIED_SCORE, q4_issues, 0
    py_files = collect_skill_py_basenames(skill_dir)
    mentioned = extract_py_refs(
        body_text, include_scripts=is_script_only_skill(skill_dir))
    stale = sorted(m for m in mentioned if m not in py_files)
    if mentioned and stale:
        q4_score = max(0.0, 100.0 - min(len(stale), 10) * 10.0)
        q4_issues.extend(_q4_stale_issues(stale))
    elif mentioned or not py_files:
        q4_score = 100.0
    else:
        q4_score = 90.0
    return q4_score, q4_issues, len(stale)

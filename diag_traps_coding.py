from __future__ import annotations

import ast
import builtins
import io
import logging
import os
import re
import sys
import tokenize
from bisect import bisect_left
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_nodes import (
    TYPE_ALIAS_NODES,
    collect_param_names,
    import_fallback_import_lines,
    is_docstring_stmt,
    is_invariant_assert,
    iter_arg_nodes,
    iter_def_site_nodes,
    iter_unpack_target_names,
)
from jwsgj.diag_shared_ast_views import parent_map as _shared_parent_map
from jwsgj.diag_shared_source_core import (
    extract_code_lines,
    is_regex_pattern_text,
    line_num_fast,
)
from jwsgj.diag_shared_source_scan import (
    apply_rule_suppress,
    normalize_rule_source,
    tokenize_source_cached,
)
from jwsgj.diag_types_defs import (
    DiagnoseFinding,
    finding_scan_exempt,
)
from jwsgj.prevention_scope_facts import walk_nodes

_log = logging.getLogger(__name__)
__all__ = [
    "AI_SECRET_PATTERNS",
    "MCP_POISONING_PATTERNS",
    "check_AI02",
    "check_AI03",
    "check_AS06",
    "check_AS07",
    "check_AW03",
    "check_AW04",
    "check_AW05",
    "check_CC01",
    "check_CQ02",
    "check_CQ03",
    "check_CQ05",
    "check_CQ06",
    "check_CQ07",
    "check_IA01",
    "check_IA02",
    "check_IA03",
    "check_all_AI",
]
_log.info("diag_traps_coding 安全编码规则域已加载: %d 项导出", len(__all__))
_BUILTIN_NAMES: frozenset[str] = frozenset(dir(builtins))
_STDLIB_MODULE_NAMES: frozenset[str] = frozenset(
    getattr(sys, "stdlib_module_names", ()))
_MUTABLE_BUILTIN_NAMES: frozenset[str] = frozenset(
    {"list", "dict", "set", "bytearray"})
def _safe_line_text(lines: list, line_num: int) -> str:
    return lines[line_num - 1].strip() if 1 <= line_num <= len(lines) else ''
class _FindingText(NamedTuple):
    title: str = ""
    description: str = ""
    code_snippet: str = ""
    suggestion: str = ""
    rule_ref: str = ""
def _finding(rule_id: str, severity: str, dimension: str, filepath: Any,
             line: int, text: _FindingText,
             col_offset: int = 0) -> DiagnoseFinding:
    return DiagnoseFinding(
        id=rule_id, severity=severity, dimension=dimension,
        file=filepath, line=line, col_offset=col_offset,
        title=text.title, description=text.description,
        code_snippet=text.code_snippet, suggestion=text.suggestion,
        rule_ref=text.rule_ref)
_CODE_ONLY_ERASE_TOKENS: frozenset[int] = frozenset(
    {tokenize.STRING, tokenize.COMMENT}
    | {
        t
        for t in (
            getattr(tokenize, "FSTRING_START", None),
            getattr(tokenize, "FSTRING_MIDDLE", None),
            getattr(tokenize, "FSTRING_END", None),
        )
        if t is not None
    }
)
def _normalize_scan_newlines(src: str) -> str:
    return re.sub(r"\r(?!\n)", "\n", src)
def _code_only_token_prefix(src: str) -> str:
    masked = [char if char in "\r\n" else " " for char in src]
    offsets = [0]
    for line in io.StringIO(src).readlines():
        offsets.append(offsets[-1] + len(line))
    try:
        for tok in tokenize.generate_tokens(io.StringIO(src).readline):
            if tok.type in _CODE_ONLY_ERASE_TOKENS or not tok.string:
                continue
            start = offsets[tok.start[0] - 1] + tok.start[1]
            end = offsets[tok.end[0] - 1] + tok.end[1]
            masked[start:end] = src[start:end]
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError) as exc:
        _log.debug("代码掩码词法重建提前结束: %s", exc)
    return "".join(masked)
def _code_only_source(src: str) -> str:
    normalized = _normalize_scan_newlines(src)
    lines = normalized.split('\n')
    tokens = tokenize_source_cached(normalized)
    if tokens is None:
        return _code_only_token_prefix(normalized)
    for tok in tokens:
        if tok.type not in _CODE_ONLY_ERASE_TOKENS:
            continue
        sr, sc = tok.start
        er, ec = tok.end
        if sr == er:
            lines[sr - 1] = lines[sr - 1][:sc] + ' ' * (ec - sc) + lines[sr - 1][ec:]
        else:
            lines[sr - 1] = lines[sr - 1][:sc] + ' ' * (len(lines[sr - 1]) - sc)
            for mid in range(sr, er - 1):
                lines[mid] = ' ' * len(lines[mid])
            lines[er - 1] = ' ' * ec + lines[er - 1][ec:]
    return '\n'.join(lines)
def _iter_active_pattern_matches(pattern: str, code: str,
                                 code_only: str):
    for match in re.finditer(pattern, code):
        if code_only[match.start():match.end()].strip():
            yield match
_AI02_DEFINITION_TAIL_RE = re.compile(r"\b(?:def|class)\s+$")
def _ai02_definition_site(code_only: str, start: int) -> bool:
    line_start = code_only.rfind("\n", 0, start) + 1
    return bool(_AI02_DEFINITION_TAIL_RE.search(
        code_only[line_start:start]))
MCP_POISONING_PATTERNS = [
    (r'(?<![A-Za-z0-9_])(?:[A-Za-z_]\w*\.)*\w*(?i:call|invoke|execute|run|dispatch)\w*\s*\(',
     'P0', '工具调用未验证'),
    (r'(?<![A-Za-z0-9_])(?:[A-Za-z_]\w*\.)*\w*(?i:mcp|tool|plugin|agent)\w*server\b',
     'P1', '工具服务器定义（需验证工具声明与行为一致性）'),
    (r'(?<![A-Za-z0-9_])(?:[A-Za-z_]\w*\.)*\w*(?i:tool|plugin|agent)\w*description\s*=\s*["\']',
     'P2', '工具描述（可能与实际行为不一致）'),
]
_AI03_STRING_PREFIX = r"(?i:(?:br|rb|fr|rf|r|b|u|f)?)"
_AI03_ASSIGNMENT = r"\s*(?::[^=\r\n]+)?=\s*"
def _ai03_secret_literal(min_length: int) -> str:
    return (
        rf'{_AI03_STRING_PREFIX}(?:"(?:\\[^\r\n]|[^"\\\r\n]){{{min_length},}}"'
        rf"|'(?:\\[^\r\n]|[^'\\\r\n]){{{min_length},}}')"
    )
AI_SECRET_PATTERNS = [
    (rf'(?i:(?:OPENAI|ANTHROPIC|DEEPSEEK|COHERE|GOOGLE_AI|AZURE_OPENAI)_API_KEY){_AI03_ASSIGNMENT}{_ai03_secret_literal(20)}', 'P0'),
    (rf'(?i:(?:GITHUB|GITLAB|BITBUCKET)_TOKEN){_AI03_ASSIGNMENT}{_ai03_secret_literal(10)}', 'P0'),
    (rf'(?i:(?:AWS|ALIBABA|TENCENT|HUAWEI)_(?:SECRET_ACCESS_KEY|SECRET_KEY)){_AI03_ASSIGNMENT}{_ai03_secret_literal(1)}', 'P0'),
    (rf'(?i:API_KEY|SECRET_KEY|PRIVATE_KEY|TOKEN){_AI03_ASSIGNMENT}{_ai03_secret_literal(8)}', 'P0'),
    (rf'(?i:JWT_SECRET){_AI03_ASSIGNMENT}{_ai03_secret_literal(1)}', 'P0'),
]
_SECRET_REVEAL_MIN_LEN = 12
_SECRET_LITERAL_RE = re.compile(
    rf'{_AI03_STRING_PREFIX}"((?:(?![\x22\x5c\x0a\x0d]).|\x5c[^\x0a])*)"'
    r"|'((?:(?![\x27\x5c\x0a\x0d]).|\x5c[^\x0a])*)'"
)
def _mask_secret_literals(line_text: str) -> str:
    def _mask(match: re.Match) -> str:
        value = match.group(1) if match.group(1) is not None else match.group(2)
        if len(value) >= _SECRET_REVEAL_MIN_LEN:
            return value[:4] + '****' + value[-4:]
        return '****'
    return _SECRET_LITERAL_RE.sub(_mask, line_text)
def _prepare_regex_scan(source_lines: Any):
    code = _normalize_scan_newlines(normalize_rule_source(source_lines))
    if not code:
        return None
    return code, code.split('\n'), _code_only_source(code)
_AI02_CALL_ACTIONS = frozenset({"call", "invoke", "execute", "run", "dispatch"})
_AI02_TOOL_CONTEXTS = frozenset({
    "tool", "tools", "mcp", "plugin", "plugins", "agent", "agents",
    "server", "servers", "client", "clients", "gateway", "gateways",
})
_AI02_STRING_TOKEN_TYPES = frozenset(
    token_type
    for token_type in (
        tokenize.STRING,
        getattr(tokenize, "FSTRING_START", None),
    )
    if token_type is not None
)
_AI02_DECLARATION_LEAVES = {
    ("mcp", "server"), ("tool", "server"),
    ("plugin", "server"), ("agent", "server"),
}
_AI02_DESCRIPTION_LEAVES = {
    ("tool", "description"), ("mcp", "description"),
    ("plugin", "description"), ("agent", "description"),
}
_AI02_LAYOUT_TOKENS = frozenset({
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NL,
    tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
})
_AI02_WORD_RE = re.compile(r"[A-Z]+(?=[A-Z][a-z]|\d|$)|[A-Z]?[a-z]+|\d+")
def _ai02_words(identifier: str) -> tuple[str, ...]:
    return tuple(
        match.group(0).lower()
        for part in identifier.split("_")
        for match in _AI02_WORD_RE.finditer(part)
    )
def _ai02_path_words(parts: list[str]) -> frozenset[str]:
    return frozenset(
        word for part in parts for word in _ai02_words(part))
def _ai02_semantic_category(
        parts: list[str], operator: str, value_token: Any,
) -> tuple[str, str] | None:
    leaf = _ai02_words(parts[-1])
    if operator == "(":
        # 只认「外部」工具调用：必须存在接收者（X.call_tool(...) 形态），
        # 且被调名不能是私有谓词。
        # 反例（不应命中）：
        #   run_tool_process([...])        ← 本地 subprocess 包装器，无接收者
        #   _se29_call_has_user_agent(n)   ← 模块内私有谓词
        #   self._is_plugin_protocol_dispatch(...) ← 私有方法
        # 这些都不是 MCP/外部工具调用，名字里带 tool/call 不构成证据。
        leaf_name = parts[-1] if parts else ""
        if len(parts) < 2 or leaf_name.startswith("_"):
            return None
        contexts = _ai02_path_words(parts)
        if (contexts & _AI02_TOOL_CONTEXTS
                and contexts & _AI02_CALL_ACTIONS):
            return "P0", "工具调用未验证"
        return None
    if operator not in {"=", ":"}:
        return None
    receiver = _ai02_path_words(parts[:-1])
    if (leaf in _AI02_DECLARATION_LEAVES
            or (leaf == ("server",) and receiver & _AI02_TOOL_CONTEXTS)):
        return "P1", "工具服务器定义（需验证工具声明与行为一致性）"
    is_description = (
        leaf in _AI02_DESCRIPTION_LEAVES
        or (leaf == ("description",) and receiver & _AI02_TOOL_CONTEXTS))
    if (is_description and value_token is not None
            and value_token.type in _AI02_STRING_TOKEN_TYPES):
        return "P2", "工具描述（可能与实际行为不一致）"
    return None
def _ai02_issue(lines: list[str], filepath: Any, line_num: int,
                severity: str, description: str) -> dict[str, Any]:
    line_text = _safe_line_text(lines, line_num)
    return {
        "rule_id": "AI-02",
        "severity": severity,
        "dimension": "security",
        "file": filepath,
        "line": line_num,
        "message": f"[AI-02] {description}: {line_text[:80]}",
        "suggestion": (
            "根因: 外部工具调用或声明缺少安全验证，可能引入提示注入或不受控执行。"
            "\n修复策略: 验证工具声明与实际行为一致性；对外部工具执行进行参数校验、"
            "权限控制与沙箱隔离\n参考标准: OWASP / AI security"),
    }
def _ai02_assigned_value_token(significant: list, operator_index: int) -> Any:
    cursor = operator_index + 1
    while cursor < len(significant):
        while (cursor < len(significant)
               and significant[cursor].string == "("):
            cursor += 1
        if (cursor + 1 < len(significant)
                and significant[cursor].type == tokenize.NAME
                and significant[cursor + 1].string == "="):
            cursor += 2
            continue
        break
    return significant[cursor] if cursor < len(significant) else None
def _ai02_annotation_value_token(significant: list,
                                 colon_index: int) -> Any:
    depth = 0
    cursor = colon_index + 1
    while cursor < len(significant):
        current = significant[cursor]
        text = current.string
        if depth == 0 and current.type == tokenize.NEWLINE:
            return None
        if text in {"(", "[", "{"}:
            depth += 1
        elif text in {")", "]", "}"}:
            if depth == 0:
                return None
            depth -= 1
        elif depth == 0 and text == "=":
            return _ai02_assigned_value_token(significant, cursor)
        elif depth == 0 and text in {",", ";"}:
            return None
        cursor += 1
    return None
def _ai02_annotation_targets(tree: Any) -> set[tuple[int, str]]:
    targets: set[tuple[int, str]] = set()
    if tree is None:
        return targets
    for node in walk_nodes(tree):
        if isinstance(node, ast.AnnAssign):
            target = node.target
            while isinstance(target, (ast.Attribute, ast.Subscript)):
                target = target.value
            if isinstance(target, ast.Name):
                targets.add((target.lineno, target.id))
        elif isinstance(node, ast.arg) and node.annotation is not None:
            targets.add((node.lineno, node.arg))
    return targets
_AI02_GROUP_CLOSERS = {")": "(", "]": "[", "}": "{"}
_AI02_GROUP_OPENERS = frozenset(_AI02_GROUP_CLOSERS.values())
_AI02_DEFINITION_LEADERS = frozenset({"def", "class"})
def _ai02_group_end_indexes(significant: list) -> dict[int, int]:
    ends: dict[int, int] = {}
    stack: list[tuple[int, str]] = []
    for index, token in enumerate(significant):
        text = token.string
        if text in _AI02_GROUP_OPENERS:
            stack.append((index, text))
        elif text in _AI02_GROUP_CLOSERS:
            if not stack or stack[-1][1] != _AI02_GROUP_CLOSERS[text]:
                continue
            opener_index, _opener = stack.pop()
            ends[opener_index] = index + 1
    return ends
def _ai02_grouping_indexes(
        significant: list, tree: Any, group_end: dict[int, int],
        lines: list[str],
) -> tuple[frozenset[int], frozenset[int]]:
    if tree is None:
        return frozenset(), frozenset()
    positions = [token.start for token in significant]
    line_bytes = [line.encode("utf-8") for line in lines]
    call_openers: set[int] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        end_row = getattr(func, "end_lineno", None)
        end_col = getattr(func, "end_col_offset", None)
        if (end_row is None or end_col is None
                or not 1 <= end_row <= len(line_bytes)):
            continue
        end_col = len(
            line_bytes[end_row - 1][:end_col].decode("utf-8"))
        cursor = bisect_left(positions, (end_row, end_col))
        while cursor < len(significant) and significant[cursor].string == ")":
            cursor += 1
        if cursor < len(significant) and significant[cursor].string == "(":
            call_openers.add(cursor)
    grouping_closers = frozenset(
        end - 1
        for start, end in group_end.items()
        if significant[start].string == "(" and start not in call_openers
    )
    return grouping_closers, frozenset(call_openers)
def _ai02_postfix_chain(significant: list, index: int,
                        group_end: dict[int, int],
                        grouping_closers: frozenset[int] = frozenset(),
                        call_openers: frozenset[int] | None = None,
                        ) -> tuple[list[str], int, list[list[str]]]:
    parts = [significant[index].string]
    call_sites: list[list[str]] = []
    cursor = index + 1
    while cursor < len(significant):
        if cursor in grouping_closers:
            cursor += 1
            continue
        text = significant[cursor].string
        if (text == "." and cursor + 1 < len(significant)
                and significant[cursor + 1].type == tokenize.NAME):
            parts.append(significant[cursor + 1].string)
            cursor += 2
            continue
        end = group_end.get(cursor)
        if end is None:
            break
        if (text == "(" and (call_openers is None
                             or cursor in call_openers)):
            call_sites.append(list(parts))
        cursor = end
    return parts, cursor, call_sites
def _ai02_call_category(call_sites: list[list[str]]) -> tuple[str, str] | None:
    for site in call_sites:
        category = _ai02_semantic_category(site, "(", None)
        if category is not None:
            return category
    return None
def _ai02_semantic_issues(code: str, lines: list[str], filepath: Any,
                          tree: Any = None):
    tokens = tokenize_source_cached(code)
    if tokens is None:
        return None
    if tree is None:
        try:
            tree = ast.parse(code)
        except (SyntaxError, ValueError):
            tree = None
    annotation_targets = _ai02_annotation_targets(tree)
    significant = [
        token for token in tokens if token.type not in _AI02_LAYOUT_TOKENS]
    group_end = _ai02_group_end_indexes(significant)
    grouping_closers, call_openers = _ai02_grouping_indexes(
        significant, tree, group_end, lines)
    issues = []
    for index, token in enumerate(significant):
        if token.type != tokenize.NAME:
            continue
        if index and significant[index - 1].string == ".":
            continue
        previous = significant[index - 1].string if index else ""
        if previous in _AI02_DEFINITION_LEADERS:
            continue
        parts, cursor, call_sites = _ai02_postfix_chain(
            significant, index, group_end, grouping_closers,
            call_openers if tree is not None else None)
        call_category = _ai02_call_category(call_sites)
        if call_category is not None:
            issues.append(_ai02_issue(
                lines, filepath, token.start[0], *call_category))
            continue
        if cursor >= len(significant):
            continue
        operator = significant[cursor].string
        if operator == ":":
            if (token.start[0], parts[0]) not in annotation_targets:
                continue
            value_token = _ai02_annotation_value_token(significant, cursor)
        elif operator == "=":
            if previous in {":", "->"}:
                continue
            value_token = _ai02_assigned_value_token(significant, cursor)
        else:
            continue
        category = _ai02_semantic_category(parts, operator, value_token)
        if category is not None:
            issues.append(_ai02_issue(
                lines, filepath, token.start[0], *category))
    return issues
def _ai02_regex_issues(code: str, lines: list[str], code_only: str,
                       filepath: Any) -> list[dict[str, Any]]:
    issues = []
    for pattern, severity, desc in MCP_POISONING_PATTERNS:
        for match in _iter_active_pattern_matches(pattern, code, code_only):
            if _ai02_definition_site(code_only, match.start()):
                continue
            line_num = line_num_fast(code, match.start())
            issues.append(_ai02_issue(
                lines, filepath, line_num, severity, desc))
    return issues
def check_AI02(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    prepared = _prepare_regex_scan(source_lines)
    if prepared is None:
        return []
    code, lines, code_only = prepared
    issues = _ai02_semantic_issues(code, lines, filepath, tree)
    if issues is None:
        issues = _ai02_regex_issues(code, lines, code_only, filepath)
    return apply_rule_suppress(issues, code, 'AI-02')
def _ai03_span_taken(spans: dict, line_num: int, start: int, end: int) -> bool:
    return any(start < taken_end and end > taken_start
               for taken_start, taken_end in spans.get(line_num, ()))
def _ai03_mark_span(spans: dict, line_num: int, start: int, end: int) -> None:
    spans.setdefault(line_num, []).append((start, end))
def _ai03_dynamic_fstring_spans(code: str) -> tuple[tuple[int, int], ...] | None:
    start_type = getattr(tokenize, "FSTRING_START", None)
    middle_type = getattr(tokenize, "FSTRING_MIDDLE", None)
    end_type = getattr(tokenize, "FSTRING_END", None)
    if start_type is None or middle_type is None or end_type is None:
        return None
    tokens = tokenize_source_cached(code)
    if tokens is None:
        return None
    offsets = [0]
    for line in io.StringIO(code).readlines():
        offsets.append(offsets[-1] + len(line))
    spans = []
    stack = []
    for tok in tokens:
        if tok.type == start_type:
            if stack:
                stack[-1][1] = True
            stack.append([offsets[tok.start[0] - 1] + tok.start[1], False])
            continue
        if tok.type == end_type:
            if not stack:
                continue
            start, dynamic = stack.pop()
            if dynamic:
                spans.append((start, offsets[tok.end[0] - 1] + tok.end[1]))
            continue
        if stack and tok.type != middle_type:
            stack[-1][1] = True
    return tuple(spans)
_AI03_FSTRING_PREFIX_RE = re.compile(r'(?i)(?:fr|rf|f)(?=["\'])')
def _ai03_dynamic_fstring_match(match: re.Match,
                                spans: tuple[tuple[int, int], ...] | None) -> bool:
    if spans is not None:
        return any(match.start() < end and match.end() > start
                   for start, end in spans)
    prefix = _AI03_FSTRING_PREFIX_RE.search(match.group(0))
    if prefix is None:
        return False
    literal = _SECRET_LITERAL_RE.match(
        match.string, match.start() + prefix.start())
    if literal is None:
        return False
    try:
        value = ast.parse(literal.group(0), mode="eval").body
    except (SyntaxError, ValueError) as exc:
        _log.debug("AI-03 动态字符串判定解析失败，保留原匹配: %s", exc)
        return False
    return (isinstance(value, ast.JoinedStr)
            and any(isinstance(item, ast.FormattedValue)
                    for item in value.values))
def _ai03_regex_literal_match(match: re.Match) -> bool:
    literals = list(_SECRET_LITERAL_RE.finditer(match.group(0)))
    if not literals:
        return False
    try:
        value = ast.literal_eval(literals[-1].group(0))
    except (ValueError, TypeError, SyntaxError, MemoryError, RecursionError) as exc:
        _log.debug("AI-03 字面值解析失败，保留原匹配: %s", exc)
        return False
    return isinstance(value, str) and is_regex_pattern_text(value)

def check_AI03(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    prepared = _prepare_regex_scan(source_lines)
    if prepared is None:
        return []
    code, lines, code_only = prepared
    issues = []
    dynamic_fstrings = _ai03_dynamic_fstring_spans(code)
    _reported_spans: dict[int, list[tuple[int, int]]] = {}
    for pattern, severity in AI_SECRET_PATTERNS:
        for match in _iter_active_pattern_matches(pattern, code, code_only):
            if (_ai03_dynamic_fstring_match(match, dynamic_fstrings)
                    or _ai03_regex_literal_match(match)):
                continue
            line_num = line_num_fast(code, match.start())
            line_text = _safe_line_text(lines, line_num)
            if _ai03_span_taken(_reported_spans, line_num,
                                match.start(), match.end()):
                continue
            _ai03_mark_span(_reported_spans, line_num,
                            match.start(), match.end())
            masked = _mask_secret_literals(line_text)[:80]
            issues.append({
                'rule_id': 'AI-03',
                'severity': severity,
                'dimension': 'security',
                'file': filepath,
                'line': line_num,
                'message': f'[AI-03] AI代码硬编码密钥: {masked}',
                'suggestion': '根因: 代码使用了不规范或有风险的实现方式。该问题属于AI安全类别。\n修复策略: 使用环境变量或密钥管理服务;pre-commit hook检测;.gitignore排除.env\n参考标准: OWASP / AI security'
            })
    return apply_rule_suppress(issues, code, 'AI-03')
def check_all_AI(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    all_issues = []
    all_issues.extend(check_AI02(tree, source_lines, filepath))
    all_issues.extend(check_AI03(tree, source_lines, filepath))
    return all_issues
def _ia01_package_prefix(filepath: Any) -> str:
    text = str(filepath or "")
    if not text or not os.path.isfile(text):
        return ""
    parts: list[str] = []
    directory = os.path.dirname(os.path.abspath(text))
    while os.path.isfile(os.path.join(directory, "__init__.py")):
        parts.append(os.path.basename(directory))
        parent = os.path.dirname(directory)
        if parent == directory:
            break
        directory = parent
    return ".".join(reversed(parts))
def check_IA01(tree: Any, source: Any, filepath: Any) -> Any:
    if tree is None: return []
    if finding_scan_exempt(filepath):
        return []
    issues = []
    prefix = _ia01_package_prefix(filepath)
    # 双模式导入回退（``try: from ._shared import X`` / ``except ImportError:
    # from _shared import X``）里的裸导入是有意为之，不是“绕过包边界”。
    fallback_lines = import_fallback_import_lines(tree)
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.ImportFrom) and node.module
                and node.module.startswith('_')
                and not node.module.startswith('__') and node.level == 0):
            continue
        if node.module.split('.', 1)[0] in _STDLIB_MODULE_NAMES:
            continue
        if node.lineno in fallback_lines:
            continue
        fixed = (f"{prefix}.{node.module}" if prefix
                 else f"<package>.{node.module}")
        issues.append(_finding(
            "IA-01", "P2", "imports", filepath, node.lineno,
            _FindingText(
                title=f"bare import from _xxx module: {node.module}",
                description=(
                    f"裸导入 'from {node.module} import ...' 未指定包前缀."
                    f"应按项目实际包链补全（如 {fixed}）."
                ),
                code_snippet=extract_code_lines(source, node.lineno),
                suggestion=f'根因: bare import from _xxx module: {node.module}。该问题属于内部API类别。\n修复策略: 改为: from {fixed} import ...\n参考标准: PEP 8 / encapsulation',
                rule_ref="CS-100"),
            col_offset=node.col_offset))
    return apply_rule_suppress(issues, source, 'IA-01')
_IA02_COMPREHENSION_SCOPES = (
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
)
_IA02_SCOPE_TYPES = (
    ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef,
    *_IA02_COMPREHENSION_SCOPES,
    *TYPE_ALIAS_NODES,
)
def _ia02_type_param_names(scope: ast.AST) -> set[str]:
    return {
        param.name
        for param in getattr(scope, "type_params", ()) or ()
        if isinstance(getattr(param, "name", None), str)
    }
class _IA02ScopeFacts(NamedTuple):
    aliases: dict[str, str]
    bound: set[str]
    builtin_names: set[str]
    global_names: set[str]
    nonlocal_names: set[str]
def _ia02_iter_own_nodes(scope: ast.AST):
    stack = [scope.body] if isinstance(scope, ast.Lambda) else list(scope.body)
    while stack:
        node = stack.pop()
        if isinstance(node, _IA02_SCOPE_TYPES):
            if TYPE_ALIAS_NODES and isinstance(node, TYPE_ALIAS_NODES):
                yield node
                continue
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef,
                                 *_IA02_COMPREHENSION_SCOPES)):
                yield node
            if not isinstance(node, _IA02_COMPREHENSION_SCOPES):
                stack.extend(reversed(list(iter_def_site_nodes(node))))
            continue
        yield node
        stack.extend(ast.iter_child_nodes(node))
def _ia02_walrus_bindings(node: ast.AST) -> set[str]:
    names: set[str] = set()
    stack = list(ast.iter_child_nodes(node))
    while stack:
        child = stack.pop()
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda, ast.ClassDef)):
            continue
        if (isinstance(child, ast.NamedExpr)
                and isinstance(child.target, ast.Name)):
            names.add(child.target.id)
        stack.extend(ast.iter_child_nodes(child))
    return names
def _ia02_register_import(node: ast.AST, aliases: dict[str, str],
                            bound: set[str], builtin_names: set[str]) -> None:
    for imported in node.names:
        head = imported.name.split(".")[0]
        local_name = imported.asname or head
        if imported.asname and imported.asname != head:
            aliases[head] = imported.asname
            bound.add(imported.asname)
        else:
            bound.add(head)
        if (isinstance(node, ast.ImportFrom) and node.module == "builtins"
                and imported.name in _MUTABLE_BUILTIN_NAMES):
            builtin_names.add(local_name)
class _IA02ScopeState:
    __slots__ = ("aliases", "bound", "builtin_names", "global_names",
                 "nonlocal_names")
    def __init__(self, bound: set[str]):
        self.aliases: dict[str, str] = {}
        self.bound = bound
        self.builtin_names: set[str] = set()
        self.global_names: set[str] = set()
        self.nonlocal_names: set[str] = set()
    def consume(self, node: ast.AST) -> None:
        handler = _IA02_NODE_HANDLERS.get(type(node))
        if handler is not None:
            handler(self, node)
    def finish(self) -> _IA02ScopeFacts:
        self.bound.difference_update(self.global_names | self.nonlocal_names)
        return _IA02ScopeFacts(
            self.aliases, self.bound, self.builtin_names,
            self.global_names, self.nonlocal_names)
def _ia02_bind_def_name(state: _IA02ScopeState, node: ast.AST) -> None:
    state.bound.add(node.name)
def _ia02_bind_type_alias(state: _IA02ScopeState, node: ast.AST) -> None:
    if isinstance(node.name, ast.Name):
        state.bound.add(node.name.id)
def _ia02_bind_comprehension(state: _IA02ScopeState, node: ast.AST) -> None:
    state.bound |= _ia02_walrus_bindings(node)
def _ia02_bind_optional_name(state: _IA02ScopeState, node: ast.AST) -> None:
    if node.name:
        state.bound.add(node.name)
def _ia02_bind_match_rest(state: _IA02ScopeState, node: ast.AST) -> None:
    if node.rest:
        state.bound.add(node.rest)
def _ia02_note_global(state: _IA02ScopeState, node: ast.AST) -> None:
    state.global_names.update(node.names)
def _ia02_note_nonlocal(state: _IA02ScopeState, node: ast.AST) -> None:
    state.nonlocal_names.update(node.names)
def _ia02_consume_import(state: _IA02ScopeState, node: ast.AST) -> None:
    _ia02_register_import(
        node, state.aliases, state.bound, state.builtin_names)
def _ia02_bind_store_name(state: _IA02ScopeState, node: ast.AST) -> None:
    if isinstance(node.ctx, (ast.Store, ast.Del)):
        state.bound.add(node.id)
_IA02_NODE_HANDLERS = {
    ast.FunctionDef: _ia02_bind_def_name,
    ast.AsyncFunctionDef: _ia02_bind_def_name,
    ast.ClassDef: _ia02_bind_def_name,
    **dict.fromkeys(TYPE_ALIAS_NODES, _ia02_bind_type_alias),
    **dict.fromkeys(_IA02_COMPREHENSION_SCOPES, _ia02_bind_comprehension),
    ast.MatchAs: _ia02_bind_optional_name,
    ast.MatchStar: _ia02_bind_optional_name,
    ast.MatchMapping: _ia02_bind_match_rest,
    ast.Global: _ia02_note_global,
    ast.Nonlocal: _ia02_note_nonlocal,
    ast.Import: _ia02_consume_import,
    ast.ImportFrom: _ia02_consume_import,
    ast.Name: _ia02_bind_store_name,
    ast.ExceptHandler: _ia02_bind_optional_name,
}
def _ia02_scope_facts(scope: ast.AST) -> _IA02ScopeFacts:
    if isinstance(scope, _IA02_COMPREHENSION_SCOPES):
        bound: set[str] = set()
        for generator in scope.generators:
            bound |= set(iter_unpack_target_names(generator.target))
        return _IA02ScopeFacts({}, bound, set(), set(), set())
    if TYPE_ALIAS_NODES and isinstance(scope, TYPE_ALIAS_NODES):
        return _IA02ScopeFacts(
            {}, _ia02_type_param_names(scope), set(), set(), set())
    bound_names = set(collect_param_names(scope)) | _ia02_type_param_names(scope)
    state = _IA02ScopeState(bound_names)
    for node in _ia02_iter_own_nodes(scope):
        state.consume(node)
    if isinstance(scope, ast.Module):
        state.global_names.clear()
        state.nonlocal_names.clear()
    return state.finish()
def _ia02_in_first_iter(comp: ast.AST, node: ast.AST, parents: dict) -> bool:
    if not comp.generators:
        return False
    target = comp.generators[0].iter
    current = node
    while current in parents:
        if current is target:
            return True
        parent = parents[current]
        if parent is comp:
            return False
        current = parent
    return False
def _ia02_type_scoped_definition_nodes(scope: ast.AST) -> list[ast.AST]:
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        nodes = [
            arg.annotation
            for arg in iter_arg_nodes(scope.args)
            if arg.annotation is not None
        ]
        if scope.returns is not None:
            nodes.append(scope.returns)
        return nodes
    if isinstance(scope, ast.ClassDef):
        return [*scope.bases, *(kw.value for kw in scope.keywords)]
    return []
def _ia02_in_root_nodes(scope: ast.AST, node: ast.AST, parents: dict,
                        roots: list[ast.AST]) -> bool:
    root_ids = {id(root) for root in roots}
    if not root_ids:
        return False
    current = node
    while current in parents:
        if id(current) in root_ids:
            return True
        parent = parents[current]
        if parent is scope:
            return False
        current = parent
    return False
def _ia02_in_outer_definition_expr(scope: ast.AST, node: ast.AST,
                                   parents: dict) -> bool:
    roots = list(iter_def_site_nodes(scope))
    if _ia02_type_param_names(scope):
        type_scoped_ids = {
            id(root) for root in _ia02_type_scoped_definition_nodes(scope)
        }
        roots = [root for root in roots if id(root) not in type_scoped_ids]
    return _ia02_in_root_nodes(scope, node, parents, roots)
def _ia02_preserves_class_visibility(scope: ast.AST, node: ast.AST,
                                     parents: dict) -> bool:
    if TYPE_ALIAS_NODES and isinstance(scope, TYPE_ALIAS_NODES):
        return True
    if (isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
            and _ia02_type_param_names(scope)):
        return _ia02_in_root_nodes(
            scope, node, parents, _ia02_type_scoped_definition_nodes(scope))
    return False
def _ia02_skip_class_scope(name: str, scopes: list, index: int,
                           node: ast.AST, parents: dict) -> bool:
    scope = scopes[index]
    if not isinstance(scope, ast.ClassDef) or index == 0:
        return False
    if name in _ia02_type_param_names(scope):
        return False
    return not all(
        _ia02_preserves_class_visibility(inner, node, parents)
        for inner in scopes[:index]
    )
def _ia02_scope_chain(node: ast.AST, parents: dict) -> list:
    scopes = []
    current = node
    while current in parents:
        current = parents[current]
        if not isinstance(current, _IA02_SCOPE_TYPES):
            continue
        if (isinstance(current, _IA02_COMPREHENSION_SCOPES)
                and _ia02_in_first_iter(current, node, parents)):
            continue
        if _ia02_in_outer_definition_expr(current, node, parents):
            continue
        scopes.append(current)
    return scopes
def _ia02_resolve_visible_name(name: str, scopes: list, facts: dict,
                               node: ast.AST, parents: dict,
                               ) -> tuple[bool, str | None]:
    alias = None
    for index, scope in enumerate(scopes):
        scope_fact = facts[id(scope)]
        if name in scope_fact.global_names:
            module_fact = facts[id(scopes[-1])]
            if name in module_fact.bound:
                return True, None
            return False, module_fact.aliases.get(name) or alias
        if name in scope_fact.nonlocal_names:
            continue
        if _ia02_skip_class_scope(name, scopes, index, node, parents):
            continue
        if name in scope_fact.bound:
            return True, None
        if alias is None and name in scope_fact.aliases:
            alias = scope_fact.aliases[name]
    return False, alias
_SCOPE_GRAPH_ATTR = "_jwsgj_coding_scope_graph"
def _ia02_merge_global_bindings(tree: ast.AST, facts: dict) -> None:
    module_fact = facts.get(id(tree))
    if module_fact is None:
        return
    for scope in walk_nodes(tree):
        if scope is tree or not isinstance(
                scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                        ast.Lambda, ast.ClassDef)):
            continue
        scope_fact = facts[id(scope)]
        if not scope_fact.global_names:
            continue
        assigned = _IA02ScopeState(set())
        deleted: set[str] = set()
        for node in _ia02_iter_own_nodes(scope):
            assigned.consume(node)
            if (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Del)
                    and node.id in scope_fact.global_names):
                deleted.add(node.id)
        rebound = (assigned.bound & scope_fact.global_names) - deleted
        module_fact.bound.update(rebound)
        module_fact.builtin_names.update(
            assigned.builtin_names & rebound)

def _ia02_scope_graph(tree: Any) -> tuple[dict, dict]:
    cached = getattr(tree, _SCOPE_GRAPH_ATTR, None)
    if cached is not None:
        return cached
    facts = {id(scope): _ia02_scope_facts(scope)
             for scope in walk_nodes(tree)
             if isinstance(scope, _IA02_SCOPE_TYPES)}
    _ia02_merge_global_bindings(tree, facts)
    graph = (_shared_parent_map(tree), facts)
    try:
        setattr(tree, _SCOPE_GRAPH_ATTR, graph)
    except AttributeError as _e:
        _log.debug("_ia02_scope_graph 缓存挂载降级: %s", _e)
    return graph
def _ia02_alias_issue(node: ast.Name, source: Any, filepath: Any,
                      parents: dict, facts: dict) -> Any:
    bound, alias = _ia02_resolve_visible_name(
        node.id, _ia02_scope_chain(node, parents), facts, node, parents)
    if bound or alias is None:
        return None
    return _finding(
        "IA-02", "P1", "imports", filepath, node.lineno,
        _FindingText(
            title=f"import alias mismatch: used '{node.id}' but imported as '{alias}'",
            description=(
                f"代码使用了 '{node.id}' 但导入语句为 'import {node.id} as {alias}'."
                "应统一使用别名,或修改导入为不带别名."
            ),
            code_snippet=extract_code_lines(source, node.lineno),
            suggestion=f"根因: import alias mismatch: used '{node.id}' but imported as '{alias}'。该问题属于内部API类别。\n修复策略: 统一使用别名 '{alias}' 或修改导入为 'import {node.id}'.\n参考标准: PEP 8 / encapsulation",
            rule_ref="CS-101"),
        col_offset=node.col_offset)
def check_IA02(tree: Any, source: Any, filepath: Any) -> Any:
    if tree is None:
        return []
    if finding_scan_exempt(filepath):
        return []
    parents, facts = _ia02_scope_graph(tree)
    issues = []
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)):
            continue
        if node.id in _BUILTIN_NAMES:
            continue
        issue = _ia02_alias_issue(node, source, filepath, parents, facts)
        if issue is not None:
            issues.append(issue)
    return apply_rule_suppress(issues, source, 'IA-02')
def _is_protocol_base(base: Any) -> bool:
    if isinstance(base, ast.Subscript):
        return _is_protocol_base(base.value)
    if isinstance(base, ast.Name):
        return base.id == 'Protocol'
    if isinstance(base, ast.Attribute):
        return base.attr == 'Protocol'
    return False
def _is_protocol_class(cls: ast.ClassDef) -> bool:
    if any(_is_protocol_base(b) for b in cls.bases):
        return True
    return any(kw.arg == 'metaclass' and _is_protocol_base(kw.value)
               for kw in cls.keywords)
def _protocol_stub_methods(tree: Any) -> set[int]:
    method_ids: set[int] = set()
    for cls in walk_nodes(tree):
        if not isinstance(cls, ast.ClassDef) or not _is_protocol_class(cls):
            continue
        for member in cls.body:
            if isinstance(member, (ast.FunctionDef, ast.AsyncFunctionDef)):
                method_ids.add(id(member))
    return method_ids
def _is_numeric_zero(val: Any) -> bool:
    return (isinstance(val, (int, float, complex))
            and not isinstance(val, bool)
            and val == 0)
def _is_signed_zero_literal(value: Any) -> bool:
    return (isinstance(value, ast.UnaryOp)
            and isinstance(value.op, (ast.USub, ast.UAdd))
            and isinstance(value.operand, ast.Constant)
            and _is_numeric_zero(value.operand.value))
def _ia03_constant_is_empty(val: Any) -> bool:
    if val is None:
        return True
    if isinstance(val, (str, bytes)):
        return not val
    return _is_numeric_zero(val)
def _is_empty_container_literal(value: Any) -> bool:
    if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        return not value.elts
    return isinstance(value, ast.Dict) and not value.keys
def _ia03_return_value_is_empty(value: Any) -> bool:
    if value is None:
        return True
    if isinstance(value, ast.Constant):
        return _ia03_constant_is_empty(value.value)
    if _is_signed_zero_literal(value):
        return True
    return _is_empty_container_literal(value)
def _ia03_strip_docstring(body: list) -> list:
    if body and is_docstring_stmt(body[0]):
        return body[1:]
    return body
def _ia03_is_shell_body(body: list) -> bool:
    body = _ia03_strip_docstring(body)
    if not body:
        return True
    if len(body) != 1:
        return False
    only_stmt = body[0]
    if isinstance(only_stmt, ast.Pass):
        return True
    if isinstance(only_stmt, ast.Expr) and isinstance(only_stmt.value, ast.Constant):
        return True
    if isinstance(only_stmt, ast.Return):
        return _ia03_return_value_is_empty(only_stmt.value)
    return False
_IA03_DECLARATION_ONLY_DECORATORS = frozenset({'abstractmethod', 'overload'})
def _ia03_is_declaration_only(node: Any, protocol_stubs: set[int]) -> bool:
    if node.name.startswith('__') and node.name.endswith('__'):
        return True
    for dec in node.decorator_list:
        if isinstance(dec, ast.Name):
            name = dec.id
        elif isinstance(dec, ast.Attribute):
            name = dec.attr
        else:
            continue
        if name in _IA03_DECLARATION_ONLY_DECORATORS:
            return True
    return id(node) in protocol_stubs
def check_IA03(tree: Any, source: Any, filepath: Any) -> Any:
    if tree is None: return []
    if finding_scan_exempt(filepath):
        return []
    issues = []
    protocol_stubs = _protocol_stub_methods(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if _ia03_is_declaration_only(node, protocol_stubs):
            continue
        if _ia03_is_shell_body(node.body):
            issues.append(_finding(
                "IA-03", "P2", "imports", filepath, node.lineno,
                _FindingText(
                    title=f"empty/stub function: {node.name}()",
                    description=(
                        f"函数 '{node.name}()' 体为空或仅返回空值."
                        "空壳函数可能表示功能尚未实现或实现被意外移除."
                    ),
                    code_snippet=extract_code_lines(source, node.lineno, context=3),
                    suggestion=f"根因: empty/stub function: {node.name}()。该问题属于内部API类别。\n修复策略: 补充 '{node.name}()' 的实现,或添加 TODO 标记说明为何为空壳.\n参考标准: PEP 8 / encapsulation",
                    rule_ref="CS-103"),
                col_offset=node.col_offset))
    return apply_rule_suppress(issues, source, 'IA-03')
class _CC01ConstCondForm(NamedTuple):
    severity: str
    title: str
    description: str
    suggestion: str
_CC01_WHILE_DEAD = _CC01ConstCondForm(
    severity="P0",
    title="while条件始终为False(死代码，永不执行)",
    description="while {shown}: 永远不会执行循环体,这是一个死代码.",
    suggestion='根因: 代码中存在冗余或无效内容, 影响可维护性。该问题属于代码质量类别。\n修复策略: 检查条件是否应为变量,或直接删除死代码\n参考标准: PEP 8 / pylint / SonarQube',
)
_CC01_IF_DEAD = _CC01ConstCondForm(
    severity="P2",
    title="if条件始终为{shown}(死代码)",
    description="if {shown}: 条件永远为假,if体永远不会执行.可能是调试残留或逻辑错误.",
    suggestion='根因: 代码中存在冗余或无效内容, 影响可维护性。该问题属于代码质量类别。\n修复策略: 检查条件或删除死代码\n参考标准: PEP 8 / pylint / SonarQube',
)
_CC01_IF_REDUNDANT = _CC01ConstCondForm(
    severity="P2",
    title="if条件始终为{shown}(多余条件)",
    description="if {shown}: 条件永远为真,if语句是多余的.可能是调试残留或条件变量被错误替换为常量.",
    suggestion='根因: 代码中存在冗余或无效内容, 影响可维护性。该问题属于代码质量类别。\n修复策略: 删除多余的if条件,直接执行if体\n参考标准: PEP 8 / pylint / SonarQube',
)
def _cc01_issue(filepath: Any, line: int, col: int, source_lines: Any,
                form: _CC01ConstCondForm, shown: str) -> dict:
    return {
        "rule_id": "CC-01",
        "severity": form.severity,
        "dimension": "correctness",
        "file": filepath,
        "line": line,
        "col_offset": col,
        "title": form.title.format(shown=shown),
        "description": form.description.format(shown=shown),
        "code_snippet": extract_code_lines(source_lines, line),
        "suggestion": form.suggestion,
        "rule_ref": "SonarQube constant-condition",
    }
def _const_test_truthiness(test: Any) -> tuple[bool, bool]:
    if isinstance(test, ast.Constant):
        return True, bool(test.value)
    if isinstance(test, ast.UnaryOp):
        return _const_unary_truthiness(test)
    if isinstance(test, (ast.Tuple, ast.List, ast.Set)):
        if any(isinstance(e, ast.Starred) for e in test.elts):
            return False, False
        return True, bool(test.elts)
    if isinstance(test, ast.Dict):
        if any(k is None for k in test.keys):
            return False, False
        return True, bool(test.keys)
    return False, False
def _const_unary_truthiness(test: ast.UnaryOp) -> tuple[bool, bool]:
    if isinstance(test.op, ast.Not):
        known, truthy = _const_test_truthiness(test.operand)
        return (known, not truthy) if known else (False, False)
    operand = test.operand
    if not (isinstance(operand, ast.Constant)
            and isinstance(operand.value, (int, float, complex))
            and not isinstance(operand.value, bool)):
        return False, False
    if isinstance(test.op, ast.Invert):
        if not isinstance(operand.value, int):
            return False, False
        return True, bool(~operand.value)
    if isinstance(test.op, (ast.USub, ast.UAdd)):
        return True, bool(operand.value)
    return False, False
def check_CC01(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if tree is None: return []
    if finding_scan_exempt(filepath):
        return []
    issues = []
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.If, ast.While)):
            continue
        known, truthy = _const_test_truthiness(node.test)
        if not known:
            continue
        shown = ast.unparse(node.test)
        if isinstance(node, ast.While):
            if truthy:
                continue
            form = _CC01_WHILE_DEAD
        else:
            form = _CC01_IF_REDUNDANT if truthy else _CC01_IF_DEAD
        issues.append(_cc01_issue(
            filepath, node.lineno, node.col_offset, source_lines, form, shown))
    return apply_rule_suppress(issues, source_lines, 'CC-01')
_AW03_PATH_RECEIVER_RE = re.compile(r'(path|file|dir|module|root|base)', re.IGNORECASE)
_AW03_NODE_RECEIVER_RE = re.compile(
    r'(^|[._])(nodes?|stmts?|exprs?|toks?|asts?)([._\[]|$)', re.IGNORECASE)
_AW03_RECEIVER_PATTERN = (
    r'[A-Za-z_][A-Za-z0-9_]*'
    r'(?:\.[A-Za-z_][A-Za-z0-9_]*|\[[^\]\r\n]+\])*'
)
_AW03_PARENT_ARG_RE = re.compile(r"\s*['\"]parent['\"]")
def _aw03_exempt(receiver: str, ctx: str) -> bool:
    if receiver and _AW03_NODE_RECEIVER_RE.search(receiver):
        return False
    if receiver and _AW03_PATH_RECEIVER_RE.search(receiver):
        return True
    lowered = ctx.lower()
    return not ('ast' in lowered or 'node' in lowered)
def _aw03_finding(filepath: Any, source: Any, ln: int, title: str,
                  suggestion: str) -> DiagnoseFinding:
    return _finding(
        "AW-03", "P0", "ast_safety", filepath, ln,
        _FindingText(
            title=title,
            description="Python标准ast节点无parent属性,hasattr(node,'parent')永远False→逻辑退化恒True.",
            code_snippet=extract_code_lines(source, ln),
            suggestion=suggestion, rule_ref="CS-106"))
def check_AW03(tree: Any, source: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    src = normalize_rule_source(source)
    if not src: return issues
    code_src = _code_only_source(src)
    for m in re.finditer(
            rf'\b({_AW03_RECEIVER_PATTERN})\.parent\b', code_src):
        _recv = m.group(1)
        if not _AW03_NODE_RECEIVER_RE.search(_recv):
            continue
        ln = line_num_fast(code_src, m.start())
        issues.append(_aw03_finding(
            filepath, source, ln,
            "AST node.parent used (no such attribute)",
            '根因: Python标准ast节点无parent属性,hasattr(node,\'parent\')永远False→逻辑退化。该问题属于AST操作类别。\n修复策略: 使用NodeVisitor.generic_visit维护parent栈或asttokens库.\n参考标准: ast模块文档 / NodeVisitor模式'))
    for m in re.finditer(
            rf'\b(?:hasattr|getattr)\s*\(\s*({_AW03_RECEIVER_PATTERN})\s*,',
            code_src):
        if not _AW03_PARENT_ARG_RE.match(src, m.end()):
            continue
        ln = line_num_fast(code_src, m.start())
        ctx = code_src[max(0,m.start()-50):m.start()+50]
        if _aw03_exempt(m.group(1), ctx):
            continue
        issues.append(_aw03_finding(
            filepath, source, ln,
            "AST node.parent probed via hasattr/getattr (always False)",
            '根因: Python标准ast节点无parent属性,hasattr/getattr探测恒False/None。该问题属于AST操作类别。\n修复策略: 使用NodeVisitor.generic_visit维护parent栈或asttokens库.\n参考标准: ast模块文档 / NodeVisitor模式'))
    return apply_rule_suppress(issues, source, 'AW-03')
def check_AW04(tree: Any, source: Any, filepath: Any) -> Any:
    if tree is None: return []
    if finding_scan_exempt(filepath):
        return []
    issues = []
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)): continue
        if not node.body: continue
        if node.body[0].lineno == node.lineno:
            issues.append(_finding(
                "AW-04", "P2", "ast_safety", filepath, node.lineno,
                _FindingText(
                    title=f"single-line function: {node.name}()",
                    description="body[0]与def同行(单行函数),插入语句前需检查lineno关系.",
                    code_snippet=extract_code_lines(source, node.lineno, context=1),
                    suggestion='根因: body[0]与def同行(单行函数),插入语句前需检查lineno关系。该问题属于AST操作类别。\n修复策略: 插入代码前检查 body[0].lineno > func.lineno.\n参考标准: ast模块文档 / NodeVisitor模式',
                    rule_ref="CS-125"),
                col_offset=node.col_offset))
    return apply_rule_suppress(issues, source, 'AW-04')
def check_AW05(tree: Any, source: Any, filepath: Any) -> Any:
    if tree is None: return []
    if finding_scan_exempt(filepath):
        return []
    issues = []
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ImportFrom):
            continue
        mod_name = node.module or ''
        if not (mod_name.startswith('_') and not mod_name.startswith('__')):
            continue
        for alias in node.names:
            if alias.name == '*':
                issues.append(_finding(
                    "AW-05", "P0", "ast_safety", filepath, node.lineno,
                    _FindingText(
                        title=f"star import from private module: {mod_name}",
                        description=(f"from {mod_name} import * 属私有模块星号导入: "
                                     "私有模块不受公开API稳定性约束, 且其未定义"
                                     "__all__时 import * 会跳过模块内 _ 前缀名称"
                                     "(下划线符号可能一无所获, 导入面静默残缺)."),
                        code_snippet=extract_code_lines(source, node.lineno),
                        suggestion=('根因: 私有模块(_前缀)星号导入——模块未定义__all__时 '
                                    'import * 不导入 _ 前缀名称, 下划线符号可能'
                                    '全部无法导入, 导入面静默残缺。'
                                    '该问题属于AST操作类别。\n'
                                    '修复策略: 替换为显式import列表或添加__all__定义.\n'
                                    '参考标准: ast模块文档 / NodeVisitor模式'),
                        rule_ref="CS-108"),
                    col_offset=node.col_offset))
    return apply_rule_suppress(issues, source, 'AW-05')
def _is_simple_assert_test(test: ast.AST) -> bool:
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _is_simple_assert_test(test.operand)
    if isinstance(test, ast.Compare):
        return all(isinstance(operand, (ast.Constant, ast.Name))
                   for operand in (test.left, *test.comparators))
    return isinstance(test, (ast.Constant, ast.Name))
def _is_main_guard_comparison(test: ast.AST) -> bool:
    return (isinstance(test, ast.Compare) and len(test.comparators) == 1
            and isinstance(test.ops[0], (ast.Eq, ast.Is)))
def _main_guard_operand_pairs(test: ast.AST) -> list[tuple[ast.AST, ast.AST]]:
    if _is_main_guard_comparison(test):
        return [(test.left, test.comparators[0])]
    if not (isinstance(test, ast.BoolOp)
            and isinstance(test.op, ast.And)):
        return []
    return [
        (v.left, v.comparators[0])
        for v in test.values
        if _is_main_guard_comparison(v)
    ]
def _is_main_guard_pair(left: ast.AST, right: ast.AST) -> bool:
    if isinstance(left, ast.Name) and left.id == "__name__":
        return isinstance(right, ast.Constant) and right.value == "__main__"
    return (isinstance(right, ast.Name) and right.id == "__name__"
            and isinstance(left, ast.Constant) and left.value == "__main__")
def _assert_lines_under(node: ast.AST) -> set[int]:
    lines: set[int] = set()
    stack = list(getattr(node, 'body', ()))
    while stack:
        child = stack.pop()
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda)):
            continue
        if isinstance(child, ast.Assert):
            lines.add(child.lineno)
        stack.extend(ast.iter_child_nodes(child))
    return lines
def _collect_main_guard_assert_lines(tree: ast.AST) -> set[int]:
    lines: set[int] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.If):
            continue
        if any(_is_main_guard_pair(left, right)
               for left, right in _main_guard_operand_pairs(node.test)):
            lines |= _assert_lines_under(node)
    return lines
def _assert_exempt(node: ast.Assert, self_test_lines: set[int]) -> bool:
    return is_invariant_assert(node) or node.lineno in self_test_lines
def _iter_reportable_asserts(tree: Any, filepath: Any, *,
                             business: bool | None = None):
    if tree is None or finding_scan_exempt(filepath):
        return
    self_test_lines = _collect_main_guard_assert_lines(tree)
    for node in walk_nodes(tree):
        if (not isinstance(node, ast.Assert)
                or _assert_exempt(node, self_test_lines)):
            continue
        if business is not None and _cq_is_business_assert(node) is not business:
            continue
        yield node
def check_AS06(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    _log.debug("规则入口 check_AS06 执行")
    issues = []
    for node in _iter_reportable_asserts(tree, filepath):
        if not _is_simple_assert_test(node.test):
            issues.append(
                {
                    "rule_id": "AS-06",
                    "severity": "P1",
                    "dimension": "defensive",
                    "file": filepath,
                    "line": node.lineno,
                    "col_offset": node.col_offset,
                    "title": "assert包含复杂逻辑, 在-O优化模式下会被跳过",
                    "description": (
                        "assert 语句在 -O 优化模式下被完全移除, 复杂条件"
                        "（调用/布尔链/属性访问）不宜用于业务校验."
                    ),
                    "message": "assert包含复杂逻辑, 在-O优化模式下会被跳过",
                    "code_snippet": extract_code_lines(source_lines, node.lineno),
                    "suggestion": "根因: 代码缺少前置条件验证, 可能导致运行时错误。该问题属于代码结构类别。\n修复策略: 将业务逻辑断言改为显式的if检查并抛出异常\n参考标准: PEP 8 / pylint / SonarQube",
                    "rule_ref": "Bandit B101/Pylint W0129",
                }
            )
    return apply_rule_suppress(issues, source_lines, 'AS-06')
def check_AS07(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    _log.debug("规则入口 check_AS07 执行")
    issues = []
    for node in _iter_reportable_asserts(tree, filepath):
        if not _is_simple_assert_test(node.test):
            continue
        line = node.lineno
        msg = ""
        if node.msg and isinstance(node.msg, ast.Constant):
            msg = str(node.msg.value)
        desc_suffix = ""
        if isinstance(node.test, ast.Name):
            desc_suffix = "(纯真值检查,缺少具体验证条件)"
        issues.append(
            {
                "rule_id": "AS-07",
                "severity": "P3",
                "dimension": "defensive",
                "file": filepath,
                "line": line,
                "col_offset": node.col_offset,
                "title": "assert用于非测试代码的数据验证",
                "description": (
                    f"assert语句在-O优化模式下会被完全移除,不适合用于数据验证或业务逻辑检查{desc_suffix}."
                    f"若用于外部输入验证才需改用显式检查;内部不变量验证可忽略."
                    + (f" 消息: {msg}" if msg else "")
                ),
                "code_snippet": extract_code_lines(source_lines, line),
                "suggestion": "根因: assert 用于内部不变量验证是合法模式(可忽略);仅当确需对用户/外部输入做运行时校验时才考虑替换为 if not condition: raise ValueError(...)",
                "rule_ref": "Effective Python / Python assert陷阱",
            }
        )
    return apply_rule_suppress(issues, source_lines, 'AS-07')
_CQ_LONG_MSG_THRESHOLD = 20
def _cq_is_business_assert(node: Any) -> bool:
    return (node.msg is not None
            and isinstance(node.msg, ast.Constant)
            and isinstance(node.msg.value, str)
            and len(node.msg.value) > _CQ_LONG_MSG_THRESHOLD)
def _cq_assert_rule(
    tree: Any, source_lines: Any, filepath: Any, *,
    rule_id: str, severity: str, business: bool,
    description: str, suggestion: str,
) -> list[DiagnoseFinding]:
    issues = [
        DiagnoseFinding(
            id=rule_id, severity=severity, dimension="quality",
            file=filepath, line=node.lineno,
            description=description, suggestion=suggestion)
        for node in _iter_reportable_asserts(
            tree, filepath, business=business)
    ]
    return apply_rule_suppress(issues, source_lines, rule_id)
def check_CQ02(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    return _cq_assert_rule(
        tree, source_lines, filepath, rule_id="CQ-02", severity="P1",
        business=True,
        description="assert用于业务逻辑(非测试代码)",
        suggestion=(
            "根因: 使用assert进行运行时校验, 在python -O模式下校验会被移除。\n"
            "修复策略:\n"
            "1. 替换为if+raise(首选):\n"
            "   if not condition: raise ValueError('descriptive message')\n"
            "2. 使用Pydantic运行时校验: @validator\n"
            "3. 使用typeguard: @typechecked\n"
            "4. 保留assert仅用于开发期不变量检查\n"
            "参考: CWE-617 / Bandit B101"
        ))
_NON_LITERAL_KEY = object()
def _literal_key_value(node: Any) -> Any:
    if isinstance(node, ast.Constant):
        return node.value
    if isinstance(node, ast.UnaryOp):
        return _literal_unary_value(node)
    if isinstance(node, ast.Tuple):
        if any(isinstance(element, ast.Starred) for element in node.elts):
            return _NON_LITERAL_KEY
        values = tuple(_literal_key_value(element) for element in node.elts)
        if any(value is _NON_LITERAL_KEY for value in values):
            return _NON_LITERAL_KEY
        return values
    return _NON_LITERAL_KEY
def _literal_unary_value(node: ast.UnaryOp) -> Any:
    inner = _literal_key_value(node.operand)
    if inner is _NON_LITERAL_KEY:
        return _NON_LITERAL_KEY
    if isinstance(node.op, ast.Not):
        return not inner
    if not isinstance(inner, (int, float, complex)):
        return _NON_LITERAL_KEY
    if isinstance(node.op, ast.USub):
        return -inner
    if isinstance(node.op, ast.UAdd):
        return +inner
    if isinstance(node.op, ast.Invert) and isinstance(inner, int):
        return ~inner
    return _NON_LITERAL_KEY
def _cq03_duplicate_keys(node: ast.Dict) -> list[tuple[ast.AST, Any]]:
    seen: set = set()
    reported: set = set()
    duplicates: list[tuple[ast.AST, Any]] = []
    for key in node.keys:
        if key is None:
            continue
        value = _literal_key_value(key)
        if value is _NON_LITERAL_KEY:
            continue
        try:
            hash(value)
        except TypeError:
            _log.debug("[CQ-03] dict key 不可哈希，跳过重复键比对: %r", value)
            continue
        if value in seen:
            if value not in reported:
                reported.add(value)
                duplicates.append((key, value))
            continue
        seen.add(value)
    return duplicates
def check_CQ03(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Dict):
            continue
        for key, value in _cq03_duplicate_keys(node):
            issues.append(DiagnoseFinding(
                id="CQ-03", severity="P1", dimension="quality",
                file=filepath, line=key.lineno,
                description=f"重复字典键: {value!r} — 后值将静默覆盖前值",
                suggestion=("根因: 字典中存在重复键, 后面的值会覆盖前面的值。该问题属于代码质量类别。\n"
                            f"修复策略: 移除或重命名重复的字典键 {value!r}\n参考标准: Pylint W0109 / flake8 F601"),
            ))
    return apply_rule_suppress(issues, source_lines, 'CQ-03')
def check_CQ05(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    return _cq_assert_rule(
        tree, source_lines, filepath, rule_id="CQ-05", severity="P2",
        business=False,
        description="assert在非测试代码中(生产环境被优化掉)",
        suggestion='根因: assert在非测试代码中(生产环境被优化掉)。该问题属于代码质量类别。\n修复策略: 使用显式if+raise替代assert\n参考标准: PEP 8 / pylint / flake8')
def _cq06_default_arg(test: Any) -> Any:
    if len(test.args) >= 2:
        return test.args[1]
    return next(
        (kw.value for kw in test.keywords if kw.arg == "default"),
        None,
    )
def check_CQ06(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.If, ast.While)):
            continue
        test = node.test
        if not (isinstance(test, ast.Call)
                and isinstance(test.func, ast.Attribute)
                and test.func.attr == "get"):
            continue
        default = _cq06_default_arg(test)
        if default is None:
            continue
        known, truthy = _const_test_truthiness(default)
        if known and truthy:
            issues.append(DiagnoseFinding(
                id="CQ-06", severity="P2", dimension="quality",
                file=filepath, line=test.lineno,
                description="dict.get()默认值为truthy值, 键缺失时条件为真",
                suggestion='根因: dict.get()的默认值为truthy值, 键缺失时会意外进入真值分支。该问题属于代码质量类别。\n修复策略: 检查默认值是否符合缺失键分支语义, 或改用 in 判断\n参考标准: PEP 8'
            ))
    return apply_rule_suppress(issues, source_lines, 'CQ-06')
def _cq07_binding_kind(name: str, node: ast.AST) -> str | None:
    if (isinstance(node, ast.Name) and node.id == name
            and isinstance(node.ctx, ast.Del)):
        return "delete"
    probe = _IA02ScopeState(set())
    probe.consume(node)
    if name not in probe.bound:
        return None
    return "builtin" if name in probe.builtin_names else "custom"
def _cq07_direct_statement_index(scope: ast.AST, node: ast.AST,
                                 parents: dict) -> int | None:
    child = node
    parent = parents.get(child)
    while parent is not None and parent is not scope:
        child = parent
        parent = parents.get(child)
    if parent is not scope:
        return None
    return next((index for index, statement in enumerate(scope.body)
                 if statement is child), None)
def _cq07_unreachable_binding(scope: ast.AST, node: ast.AST,
                              parents: dict) -> bool:
    child = node
    parent = parents.get(child)
    while parent is not None and parent is not scope:
        if isinstance(parent, (ast.If, ast.While)):
            known, truthy = _const_test_truthiness(parent.test)
            if known:
                if isinstance(parent, ast.If):
                    if ((child in parent.body and not truthy)
                            or (child in parent.orelse and truthy)):
                        return True
                elif child in parent.body and not truthy:
                    return True
        child = parent
        parent = parents.get(child)
    return False
def _cq07_ordered_builtin(name: str, scopes: list, index: int,
                          node: ast.AST, parents: dict,
                          allow_unbound: bool) -> bool | None:
    scope = scopes[index]
    if not isinstance(scope, (ast.Module, ast.ClassDef)):
        return None
    if any(not isinstance(inner, (ast.Module, ast.ClassDef))
           for inner in scopes[:index]):
        return None
    reference = (node.lineno, node.col_offset)
    events = []
    for candidate in _ia02_iter_own_nodes(scope):
        kind = _cq07_binding_kind(name, candidate)
        if kind is None:
            continue
        position = ((candidate.end_lineno, candidate.end_col_offset)
                    if isinstance(candidate, (ast.FunctionDef,
                                              ast.AsyncFunctionDef, ast.ClassDef))
                    else (candidate.lineno, candidate.col_offset))
        if (position <= reference
                and not _cq07_unreachable_binding(scope, candidate, parents)):
            events.append((position, kind, candidate))
    if not events:
        return allow_unbound
    _position, kind, binding = max(events, key=lambda event: event[0])
    if kind != "delete":
        return kind == "builtin"
    binding_statement = binding
    while not isinstance(binding_statement, ast.stmt):
        binding_statement = parents.get(binding_statement)
        if binding_statement is None:
            return None
    binding_index = next(
        (index for index, statement in enumerate(scope.body)
         if statement is binding_statement), None)
    reference_index = _cq07_direct_statement_index(scope, node, parents)
    if (binding_index is not None and reference_index is not None
            and binding_index < reference_index):
        return allow_unbound
    return None
def _cq07_visible_builtin(name: str, scopes: list, facts: dict,
                          node: ast.AST, parents: dict, *,
                          allow_unbound: bool = True) -> bool:
    for index, scope in enumerate(scopes):
        scope_fact = facts[id(scope)]
        if name in scope_fact.global_names:
            module_fact = facts[id(scopes[-1])]
            if name in module_fact.bound:
                ordered = _cq07_ordered_builtin(
                    name, scopes, len(scopes) - 1, node, parents, allow_unbound)
                if ordered is not None:
                    return ordered
                return name in module_fact.builtin_names
            return allow_unbound
        if name in scope_fact.nonlocal_names:
            continue
        if _ia02_skip_class_scope(name, scopes, index, node, parents):
            continue
        if name in scope_fact.bound:
            ordered = _cq07_ordered_builtin(
                name, scopes, index, node, parents, allow_unbound)
            if ordered is not None:
                return ordered
            return name in scope_fact.builtin_names
    return allow_unbound
def _cq07_is_ctor_call(value: Any, parents: dict, facts: dict) -> bool:
    if not (isinstance(value, ast.Call)
            and isinstance(value.func, ast.Name)):
        return False
    func = value.func
    return _cq07_visible_builtin(
        func.id, _ia02_scope_chain(func, parents), facts, func, parents,
        allow_unbound=func.id in _MUTABLE_BUILTIN_NAMES)
def _cq07_finding(line: int, description: str, suggestion: str,
                  filepath: Any) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="CQ-07", severity="P2", dimension="quality",
        file=filepath, line=line,
        description=description, suggestion=suggestion,
    )
def check_CQ07(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    parents, facts = _ia02_scope_graph(tree)
    for node in walk_nodes(tree):
        if isinstance(node, ast.Assign) and len(node.targets) >= 2:
            if _cq07_is_ctor_call(node.value, parents, facts):
                func = node.value.func
                issues.append(_cq07_finding(
                    node.lineno,
                    f"多赋值链共享{func.id}引用",
                    f'根因: 多赋值链共享{func.id}引用。该问题属于代码质量类别。\n'
                    f'修复策略: 分别创建: a = {func.id}(); b = {func.id}()\n'
                    f'参考标准: PEP 8 / pylint / flake8',
                    filepath))
            elif isinstance(node.value, (ast.List, ast.Dict, ast.Set)):
                issues.append(_cq07_finding(
                    node.lineno, "多赋值链共享可变对象引用",
                    "根因: 多个变量引用同一可变对象, 修改其中一个会影响所有引用方。\n"
                    "修复策略:\n"
                    "1. 分别创建独立对象(首选): a = [1,2]; b = [1,2] 而非 b = a\n"
                    "2. 使用copy.copy()浅拷贝: b = copy.copy(a)\n"
                    "3. 使用copy.deepcopy()深拷贝(嵌套结构): b = copy.deepcopy(a)\n"
                    "4. 使用不可变类型: 替代list用tuple, 替代dict用MappingProxyType\n"
                    "参考: CWE-915 / Python copy模块文档",
                    filepath))
    return apply_rule_suppress(issues, source_lines, 'CQ-07')
for _text_detector in (check_AI02, check_AI03, check_all_AI, check_AW03):
    _text_detector._jwsgj_requires_tree = False
def wiring_declarations() -> dict:
    return {
        "catalogs": {
            "rule_bindings": {
                'AI02': check_AI02, 'AI03': check_AI03,
                'AS06': check_AS06, 'AS07': check_AS07,
                'AW03': check_AW03, 'AW04': check_AW04, 'AW05': check_AW05,
                'CC01': check_CC01,
                'CQ02': check_CQ02, 'CQ03': check_CQ03, 'CQ05': check_CQ05,
                'CQ06': check_CQ06, 'CQ07': check_CQ07,
                'IA01': check_IA01, 'IA02': check_IA02, 'IA03': check_IA03,
            },
            "early_channels": {"AI": (30, check_all_AI, True)},
        },
    }

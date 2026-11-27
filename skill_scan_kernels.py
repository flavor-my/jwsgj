from __future__ import annotations

import ast
import bisect
import copy
import logging
import os
import re
import time
from collections.abc import Iterable, Iterator
from dataclasses import dataclass
from pathlib import Path
from typing import Any, ClassVar, NamedTuple

from jwsgj.diag_shared_ast_nodes import (
    _type_checking_guard_node_polarities,
    build_parent_map,
    collect_import_bindings,
    is_docstring_stmt,
    is_mutable_default,
    is_placeholder_stmt,
    is_shell_true_keyword,
    iter_evaluation_scope_chain,
    type_checking_body_node_ids,
)
from jwsgj.diag_shared_ast_views import (
    call_scope_map,
    collect_api_function_nodes,
    collect_lexical_scope_table,
    scope_node_bound_names,
    tree_nodes,
)
from jwsgj.diag_shared_source_core import (
    byte_col_to_char_col,
    line_start_offset,
    parse_cached,
    parse_py_file,
    read_source,
)
from jwsgj.diag_shared_source_scan import (
    comment_only_spans,
    inline_suppressed_at,
    is_masked_offset,
    is_suppressed,
    parse_suppressions,
    py_string_row_spans,
    py_string_token_offsets,
    scan_masked_spans,
    string_comment_spans,
)
from jwsgj.diag_types_vocab import (
    RULE_MISSING_ANNOTATIONS,
    Severity,
)
from jwsgj.log_config import (
    degraded_section,
    log_swallowed,
    mark_section_degraded,
    perf_trace,
    write_audit,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    coerce_skill_dir,
    iter_py_files,
)
from jwsgj.skill_audit_rules import (
    DANGEROUS_COMMANDS,
    NETWORK_CALL_TARGETS,
    REMOTE_SCRIPT_PATTERNS,
    SCRIPT_SCAN_SUFFIXES,
    SECRET_LEAK_VERDICT,
    SecurityReport,
    Verdict,
    docstring_rows_from_nodes,
    frontmatter_block,
    is_comment_line,
    is_test_scan_target,
    iter_leak_candidate_files,
    iter_network_calls_no_timeout,
    iter_scan_scope_files,
    iter_secret_hits,
    line_no,
    mask_secret,
    new_location_issue,
    non_py_comment_spans,
    read_asset_text,
)
from jwsgj.skill_audit_rules import (
    LEAK_SCAN_SUFFIXES as _SHARED_LEAK_SCAN_SUFFIXES,
)

_log = logging.getLogger(__name__)
__all__ = [
    'DANGEROUS_FUNCTIONS',
    'SECURITY_DANGEROUS_PATTERNS',
    'SENSITIVE_PATTERNS',
    'SkillSecurityScanner',
    'check_dependency_declaration',
    'check_path_safety',
    'path_within',
    'scan_dangerous_calls',
    'scan_document_assets',
    'scan_file_security_patterns',
    'scan_python_quality_file',
    'scan_python_security_file',
    'scan_security_issues',
]
_log.info("skill_scan_kernels 已加载: %d 项导出", len(__all__))
_PLACEHOLDER_VALUE_WORDS: frozenset[str] = frozenset({
    "none", "null", "changeme", "your_key", "xxx",
    "todo", "placeholder", "example", "test", "demo",
    "sample", "env", "os.environ", "getenv",
    "hardcoded_secret", "password", "passwd", "pwd",
    "secret", "token", "api_key", "apikey", "secret_key",
    "redacted", "masked", "dummy", "faker", "foobar",
})
_PLACEHOLDER_VALUE_RE = re.compile(
    r"(?<![A-Za-z0-9])(?:" + "|".join(
        re.escape(w) for w in sorted(
            _PLACEHOLDER_VALUE_WORDS, key=len, reverse=True)
    ) + r")(?![A-Za-z0-9])")
_ENV_PLACEHOLDER_RE = re.compile(r"\$\{[^{}\r\n]+\}")
_FULL_PLACEHOLDER_RE = re.compile(r"(?:\{[^{}\r\n]+\}|<[^<>\r\n]+>)")
_PRINTF_PLACEHOLDER_RE = re.compile(r"%[sd](?![A-Za-z])")
def _is_structured_secret_placeholder(value: str) -> bool:
    return bool(
        _ENV_PLACEHOLDER_RE.search(value)
        or _FULL_PLACEHOLDER_RE.fullmatch(value)
        or _PRINTF_PLACEHOLDER_RE.search(value)
        or "***" in value)
_NAME_SEPARATORS_RE = re.compile(r"[_\-\s]+")
def _compact_name(name: str) -> str:
    return _NAME_SEPARATORS_RE.sub("", name.lower())
def _sensitive_name_pattern(name: str) -> str:
    parts = [p for p in _NAME_SEPARATORS_RE.split(name.lower()) if p]
    return (r"(?<![A-Za-z0-9])"
            + r"[_\-\s]?".join(re.escape(p) for p in parts)
            + r"(?![A-Za-z0-9])")
def _is_test_scan_file(path: Path, root: Path) -> bool:
    rel = os.path.relpath(str(path), str(root)).replace('\\', '/')
    return is_test_scan_target(path, root, rel)
class SkillSecurityScanner:
    INJECTION_PATTERNS: ClassVar[list] = [
        "ignore previous instructions",
        "ignore all previous",
        "disregard the above",
        "system prompt:",
        "you are now",
        "new instructions:",
        "forget everything",
        "override system",
        "act as if",
        "pretend you are",
        "忽略之前的指令", "忽略以上所有指令",
        "无视之前的所有指令", "覆盖系统提示",
    ]
    SENSITIVE_NAMES: ClassVar[list] = [
        "api_key", "apikey", "password", "passwd", "pwd",
        "secret", "secret_key", "token", "private_key", "access_key",
        "client_secret",
    ]
    PATH_TRAVERSAL_PATTERNS: ClassVar[list] = ["../", "..\\", "/etc/", "/root/", "/home/"]  # jwsgj:suppress SS-02 — 检测规则表，非执行面
    _TRAVERSAL_GUARDS: ClassVar[dict] = {
        "../": r'(?<![\w.])\.\./',  # jwsgj:suppress SS-02 — 检测规则表，非执行面
        "..\\": r'(?<![\w.])\.\.\\',  # jwsgj:suppress SS-02 — 检测规则表，非执行面
    }
    SCRIPT_SCAN_SUFFIXES: ClassVar[set] = set(SCRIPT_SCAN_SUFFIXES)
    LEAK_SCAN_SUFFIXES: ClassVar[frozenset] = _SHARED_LEAK_SCAN_SUFFIXES
    def __init__(self, cache=None):
        self._findings: list[dict] = []
        self._cache = cache
    def _snapshot(self, predicate=None) -> list[dict]:
        return [dict(f) for f in self._findings
                if predicate is None or predicate(f)]
    def _cache_read(self, method_name: str, path, expected_type: type):
        cache = self._cache
        getter = getattr(cache, method_name, None) if cache is not None else None
        if getter is None:
            return None
        try:
            value = getter(str(path))
        except Exception as _e:  # noqa: BLE001
            log_swallowed(
                __name__, _e,
                context=(f'SkillSecurityScanner.{method_name}:'
                         f'{type(_e).__name__}'))
            return None
        if value is None:
            return None
        if not isinstance(value, expected_type):
            _type_exc = TypeError(f'{method_name} 返回 {type(value).__name__}')
            log_swallowed(
                __name__, _type_exc,
                context=(f'SkillSecurityScanner.{method_name}:'
                         f'{type(_type_exc).__name__}'))
            return None
        return value
    def _record(self, rule_id: str, severity: str, file_ref, line: int,
                message: str, suggestion: str) -> None:
        self._findings.append({
            "rule_id": rule_id,
            "severity": severity,
            "file": str(file_ref),
            "line": line,
            "message": message,
            "suggestion": suggestion,
        })
    def scan_skill(self, skill_dir: str | Path) -> list[dict]:
        _t0 = time.monotonic()
        self._findings = []
        _raw = coerce_skill_dir(skill_dir)
        skill_path = Path(_raw) if _raw.strip() else None
        if skill_path is None or not skill_path.is_dir():
            _where = _raw.strip() or repr(skill_dir)
            raise FileNotFoundError(f'技能扫描目录不存在: {_where}')
        self._scan_skill_md_injection(skill_path)
        self._scan_script_path_traversal(skill_path)
        self._scan_sensitive_info_leak(skill_path)
        self._write_audit_entries()
        self._trace_duration((time.monotonic() - _t0) * 1000)
        return self._snapshot()
    def _write_audit_entries(self) -> None:
        if not self._findings:
            return
        try:
            for f in self._findings:
                write_audit("skill_security_finding",
                            rule_id=f.get("rule_id", ""),
                            severity=f.get("severity", ""),
                            file=f.get("file", ""),
                            line=f.get("line", 0),
                            message=f.get("message", "")[:200])
        except Exception:  # noqa: BLE001
            _log.debug("write_audit failed for skill security findings",
                       exc_info=True)
    def _trace_duration(self, duration_ms: float) -> None:
        try:
            perf_trace("skill_security_scan", round(duration_ms, 2),
                       findings_count=len(self._findings))
        except Exception:  # noqa: BLE001
            _log.debug("perf_trace failed for skill_security_scan",
                       exc_info=True)
    @staticmethod
    def _iter_pattern_matches(line: str, patterns):
        for pattern in patterns:
            guard = SkillSecurityScanner._TRAVERSAL_GUARDS.get(pattern)
            if guard is not None:
                for match in re.finditer(guard, line):
                    yield pattern, match.start()
                continue
            step = max(len(pattern), 1)
            pos = line.find(pattern)
            while pos >= 0:
                yield pattern, pos
                pos = line.find(pattern, pos + step)
    def _scan_skill_md_injection(self, skill_path: Path) -> None:
        md_file = skill_path / "SKILL.md"
        if not md_file.is_file():
            return
        try:
            text = read_asset_text(md_file)
        except (OSError, UnicodeDecodeError) as _e:
            _log.warning("_scan_skill_md_injection: SKILL.md不可读: %s", _e)
            mark_section_degraded('技能安全文档读取')
            return
        self._scan_pattern_lines(
            text.split("\n"), self.INJECTION_PATTERNS,
            rule_id="SS-01", severity="P0", file_ref=md_file,
            prefix="SKILL.md提示注入风险",
            suggestion="移除可能被解释为系统指令的文本", lower=True)
    def _scan_script_path_traversal(self, skill_path: Path) -> None:
        for script_file in sorted(
                iter_scan_scope_files(skill_path, self.SCRIPT_SCAN_SUFFIXES)):
            if _is_test_scan_file(script_file, skill_path):
                continue
            text = self._read_script_text(script_file)
            if text is None:
                continue
            _is_py = script_file.suffix.lower() == '.py'
            self._scan_pattern_lines(
                text.split("\n"), self.PATH_TRAVERSAL_PATTERNS,
                rule_id="SS-02", severity="P1", file_ref=script_file,
                prefix="脚本路径穿越风险",
                suggestion="使用 pathlib.Path 和 resolve() 防止路径穿越",
                skip_comments=True, content=text,
                suppress_spans=(self._string_spans(text) if _is_py else []),
                comment_spans=(comment_only_spans(text) if _is_py else None),
                guard_spans=(_traversal_guard_offsets(text)
                             if _is_py else []),
                skip_rows=(self._docstring_line_spans(text)
                           if _is_py else frozenset()))
    def _scan_pattern_lines(self, lines, patterns, *, rule_id: str,
                            severity: str, file_ref, prefix: str,
                            suggestion: str, lower: bool = False,
                            skip_comments: bool = False,
                            content: str = "", suppress_spans=None,
                            skip_rows: frozenset = frozenset(),
                            guard_spans=None, comment_spans=None) -> None:
        offset = 0
        for i, line in enumerate(lines, 1):
            line_start = offset
            offset += len(line) + 1
            if skip_comments and is_comment_line(line):
                continue
            if i in skip_rows:
                continue
            hit = None
            for pattern, pos in self._iter_pattern_matches(
                    line.lower() if lower else line, patterns):
                if _in_string_or_comment(comment_spans, i, pos):
                    continue
                if guard_spans and is_masked_offset(
                        guard_spans, line_start + pos):
                    _log.info(
                        '[SUPPRESSED-GUARD] %s 路径守卫语义（比较/前后缀判定）: '
                        '%s:%d %s', rule_id, file_ref, i, pattern)
                    continue
                if content and inline_suppressed_at(
                        content, line_start + pos, rule_id, suppress_spans):
                    _log.info(
                        '[SUPPRESSED-INLINE] %s 行内抑制: %s:%d %s',
                        rule_id, file_ref, i, pattern)
                    continue
                hit = (pattern, pos)
                break
            if hit is None:
                continue
            pattern, _pos = hit
            self._record(rule_id, severity, file_ref, i,
                         prefix + ": 检测到 '" + pattern + "'", suggestion)
    @staticmethod
    def _string_spans(text: str):
        try:
            return py_string_token_offsets(text)
        except (ValueError, SyntaxError) as _swallowed_exc:
            log_swallowed(
                __name__, _swallowed_exc,
                context=('SkillSecurityScanner._string_spans:'
                         f'{type(_swallowed_exc).__name__}'))
            return None
    def _read_script_text(self, script_file: Path) -> str | None:
        _is_py = script_file.suffix.lower() == '.py'
        if _is_py:
            cached = self._cache_read('get_source', script_file, str)
            if cached is not None:
                return cached
        try:
            return _read_scan_text(script_file, _is_py)
        except (OSError, UnicodeDecodeError) as _e:
            _log.warning(
                "_scan_script_path_traversal: 跳过不可读文件 %s: %s",
                script_file, _e)
            mark_section_degraded('技能安全脚本读取')
            return None
    @staticmethod
    def _docstring_line_spans_from_tree(tree) -> frozenset:
        return frozenset(docstring_rows_from_nodes(tree_nodes(tree)))
    @classmethod
    def _docstring_line_spans(cls, source: str) -> frozenset:
        try:
            tree = parse_cached(source)
        except (SyntaxError, ValueError, RecursionError, MemoryError) as _e:
            log_swallowed(
                __name__, _e,
                context=f'SkillSecurityScanner._docstring_line_spans:{type(_e).__name__}')
            return frozenset()
        return cls._docstring_line_spans_from_tree(tree)
    @staticmethod
    def _match_in_string_literal(line: str, i: int, match_start: int,
                                  row_spans, file_ref, name: str,
                                  match_end: int | None = None) -> bool:
        if row_spans is None:
            _before = line[:match_start]
            _quotes = ((_before.count('"') - _before.count('\\"'))
                       + (_before.count("'") - _before.count("\\'")))
            return _quotes % 2 == 1
        limit = len(line) if match_end is None else match_end
        for cs, ce in row_spans.get(i, ()):
            if cs <= match_start and limit <= ce:
                _log.info(
                    "[SUPPRESSED-FIXTURE] SS-03 夹具抑制(留CV复核): "
                    "file=%s line=%d name=%s", file_ref, i, name)
                return True
        return False
    @staticmethod
    def _sensitive_assignment(line: str, name: str, *,
                              allow_bare: bool = True):
        _pat = _sensitive_name_pattern(name)
        assign = re.search(
            _pat + r"\s*(?::[^=\n]+)?=\s*"
            r"(?P<assign_quote>['\"])"
            r"(?P<value>(?:\\.|(?!(?P=assign_quote))[^\r\n]){4,})"
            r"(?P=assign_quote)",
            line, re.IGNORECASE)
        if assign is not None:
            return assign
        quoted = re.search(
            r"['\"]" + _pat + r"['\"]\s*:\s*"
            r"(?P<quoted_quote>['\"])"
            r"(?P<value>(?:\\.|(?!(?P=quoted_quote))[^\r\n]){8,})"
            r"(?P=quoted_quote)",
            line, re.IGNORECASE)
        if quoted is not None or not allow_bare:
            return quoted
        return re.search(
            r"(?<![\w'\"])" + _pat + r"\s*[:=]\s*['\"]?"
            r"(?P<value>[^\s'\"]{8,})['\"]?\s*(?:#.*)?$",
            line, re.IGNORECASE)
    def _is_placeholder_value(self, match, line: str, i: int, file_ref,
                              name: str, row_spans) -> bool:
        if file_ref.suffix.lower() == '.py' and self._match_in_string_literal(
                line, i, match.start(), row_spans, file_ref, name,
                match.end()):
            return True
        value = match.group("value").strip().lower()
        if not value:
            return True
        if _PLACEHOLDER_VALUE_RE.search(value):
            return True
        if value.isalpha() and len(value) < 8:
            return True
        return _is_structured_secret_placeholder(value)
    def _scan_line_sensitive_names(self, line, i, f,
                                    row_spans, *, content,
                                    line_start, string_spans, comment_spans):
        line_compact = _compact_name(line)
        _allow_bare = Path(f).suffix.lower() != '.py'
        for name in self.SENSITIVE_NAMES:
            if _compact_name(name) not in line_compact:
                continue
            match = self._sensitive_assignment(
                line, name, allow_bare=_allow_bare)
            if match is None:
                continue
            if _in_string_or_comment(comment_spans, i, match.start()):
                continue
            if self._is_placeholder_value(match, line, i, f, name, row_spans):
                continue
            if content and inline_suppressed_at(
                    content, line_start + match.start(), "SS-03",
                    string_spans):
                _log.info(
                    "[SUPPRESSED-INLINE] SS-03 行内抑制: %s:%d %s",
                    f, i, name)
                continue
            self._record("SS-03", "P0", f, i,
                         "敏感信息泄露: 检测到 " + name + " 硬编码",
                         "使用环境变量或密钥管理服务")
            break
    def _leak_read_text(self, f, is_py: bool):
        if is_py:
            text = self._cache_read('get_source', f, str)
            if text is not None:
                return text
        return _read_scan_text(Path(f), is_py)
    def _leak_doc_lines(self, f, text: str, is_py: bool):
        if not is_py:
            return frozenset()
        _tree = self._cache_read('get_ast', f, ast.AST)
        return (self._docstring_line_spans_from_tree(_tree)
                if _tree is not None
                else self._docstring_line_spans(text))
    def _scan_file_leak_lines(self, f, lines, doc_lines, row_spans,
                              *, content, string_spans, comment_spans) -> None:
        offset = 0
        for i, line in enumerate(lines, 1):
            line_start = offset
            offset += len(line) + 1
            if is_comment_line(line) or i in doc_lines:
                continue
            self._scan_line_sensitive_names(
                line, i, f, row_spans, content=content,
                line_start=line_start, string_spans=string_spans,
                comment_spans=comment_spans)
    def _scan_sensitive_info_leak(self, skill_path):
        for f in iter_leak_candidate_files(
                skill_path, self.LEAK_SCAN_SUFFIXES):
            if _is_test_scan_file(f, skill_path):
                continue
            _is_py = f.suffix.lower() == ".py"
            try:
                text = self._leak_read_text(f, _is_py)
            except (OSError, UnicodeDecodeError) as _e:
                _log.warning("_scan_sensitive_info_leak: 跳过不可读文件 %s: %s", f, _e)
                mark_section_degraded('技能安全凭据读取')
                continue
            doc_lines = self._leak_doc_lines(f, text, _is_py)
            row_spans = (py_string_row_spans(text) if _is_py else None)
            string_spans = self._string_spans(text) if _is_py else None
            self._scan_file_leak_lines(
                f, text.split("\n"), doc_lines, row_spans,
                content=text, string_spans=string_spans,
                comment_spans=(comment_only_spans(text) if _is_py else None))
    def has_blocking_issues(self) -> bool:
        return any(f.get("severity") == "P0" for f in self._findings)
_NETWORK_CALL_PATTERN = '|'.join(
    re.escape(name) for name in sorted(NETWORK_CALL_TARGETS))
_NETWORK_CALL_HEAD = rf'(?<![.\w])(?:{_NETWORK_CALL_PATTERN})\s*\('
_NETWORK_TIMEOUT_PATTERNS = [
    _NETWORK_CALL_HEAD + r'(?![^)\n]*timeout)[^)\n]*\)',
    _NETWORK_CALL_HEAD + r'[^)\n]*timeout\s*=\s*None',
]
SENSITIVE_PATTERNS = {
    '硬编码密钥': {
        'patterns': [
            ('(?<![A-Za-z0-9])(?:api[_-]?key|apikey|private[_-]?key'
             '|access[_-]?key|secret[_-]?key|secret|password|token|auth)'
             '(?![A-Za-z0-9])'
             '\\s*(?::[^=\\n]+)?["\\\']?\\s*[:=]\\s*'
             '(?P<secret_quote>["\\\'])'
             '(?P<secret_value>(?:\\\\.|(?!(?P=secret_quote))[^\\r\\n]){8,})'
             '(?P=secret_quote)'),
        ],
        'severity': Severity.CRITICAL,
        'recommendation': "使用环境变量替代硬编码密钥: os.environ.get('KEY_NAME')",
    },
    '路径穿越风险': {
        'patterns': [
            r'(?<![.\w])os\.path\.join\s*\(\s*[^,)]*user[^,)]*input',
            '(?<![\\w.])(?:\\.\\./)+',
            '(?<![\\w.])(?:\\.\\.\\\\)+',
        ],
        'severity': Severity.HIGH,
        'recommendation': '使用 os.path.realpath() 验证路径在允许范围内',
    },
    '危险系统调用': {
        'patterns': [
            r'(?<![.\w])os\.(?:system|popen)\s*\(',
            (r'(?<![.\w])subprocess\.(?:call|run|Popen|check_call|check_output)'
             r'\s*\([^)]*shell\s*=\s*True'),
            r'(?<![.\w])eval\s*\(',
            r'(?<![.\w])exec\s*\(',
        ],
        'severity': Severity.CRITICAL,
        'recommendation': '使用 subprocess.run([...], shell=False) 或避免 eval/exec',
    },
    '不安全的反序列化': {
        'patterns': [
            r'(?<![.\w])pickle\.(?:load|loads)\s*\(',
            r'(?<![.\w])yaml\.load\s*\((?![^)\n]*SafeLoader)[^)\n]*\)',
        ],
        'severity': Severity.HIGH,
        'recommendation': '使用 yaml.safe_load() 或避免 pickle 反序列化',
    },
    '网络请求无超时': {
        'patterns': _NETWORK_TIMEOUT_PATTERNS,
        'severity': Severity.MEDIUM,
        'recommendation': '所有网络请求添加 timeout 参数: requests.get(url, timeout=30)',
    },
    '文件操作无异常处理': {
        'patterns': [
            r'(?<![A-Za-z0-9_])open\s*\(.*?\)\s*\.(?:read|write)',
        ],
        'severity': Severity.LOW,
        'recommendation': '使用 with 语句或 try/except 包裹文件操作',
    },
}
def _is_fully_masked(mask, start: int, end: int) -> bool:
    return any(s <= start and end <= e for s, e in mask)
_TEXT_EVIDENCE_CATEGORIES = frozenset({'路径穿越风险'})
_TRAVERSAL_TEXT_RE = re.compile(r"\.\.[/\\]")
_TRAVERSAL_GUARD_METHODS = frozenset({'startswith', 'endswith'})
def _string_constant_row_spans(
        node: ast.Constant, lines: list[str]) -> dict[int, list[tuple[int, int]]]:
    srow = getattr(node, "lineno", 0)
    erow = getattr(node, "end_lineno", srow) or srow
    if not (1 <= srow <= len(lines)):
        return {}
    scol = byte_col_to_char_col(lines[srow - 1], node.col_offset)
    if erow == srow:
        ecol = byte_col_to_char_col(
            lines[srow - 1], node.end_col_offset or node.col_offset)
        return {srow: [(scol, max(scol, ecol))]}
    rows: dict[int, list[tuple[int, int]]] = {srow: [(scol, 1 << 30)]}
    for row in range(srow + 1, min(erow, len(lines))):
        rows[row] = [(0, 1 << 30)]
    if 1 <= erow <= len(lines):
        ecol = byte_col_to_char_col(
            lines[erow - 1], node.end_col_offset or 0)
        rows[erow] = [(0, max(0, ecol))]
    return rows
def _is_traversal_guard_call(node: ast.AST) -> bool:
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in _TRAVERSAL_GUARD_METHODS)
def _traversal_guard_offsets(content: str) -> list[tuple[int, int]]:
    if not _TRAVERSAL_TEXT_RE.search(content):
        return []
    tree = _parse_ast_or_none(content)
    if tree is None:
        return []
    parents = build_parent_map(tree)
    lines = content.split("\n")
    line_starts = [0]
    for _m in re.finditer("\n", content):
        line_starts.append(_m.end())
    guard_rows: dict[int, list[tuple[int, int]]] = {}
    def _add_guard(node: ast.Constant) -> None:
        for row, spans in _string_constant_row_spans(node, lines).items():
            guard_rows.setdefault(row, []).extend(spans)
    for node in tree_nodes(tree):
        if not (isinstance(node, ast.Constant)
                and isinstance(node.value, str)):
            continue
        if not _TRAVERSAL_TEXT_RE.search(node.value):
            continue
        parent = parents.get(id(node))
        grand = parents.get(id(parent)) if parent is not None else None
        if isinstance(parent, ast.Compare):
            _add_guard(node)
            continue
        if isinstance(parent, ast.Call):
            if node in parent.args and _is_traversal_guard_call(parent):
                _add_guard(node)
            continue
        if isinstance(parent, (ast.Tuple, ast.List, ast.Set, ast.Dict)):
            if (isinstance(grand, ast.Call) and parent in grand.args
                    and _is_traversal_guard_call(grand)):
                _add_guard(node)
                continue
            if (isinstance(grand, (ast.Assign, ast.AnnAssign))
                    and getattr(grand, "value", None) is parent
                    and isinstance(
                        parents.get(id(grand)), (ast.Module, ast.ClassDef))):
                _add_guard(node)
    return sorted(_absolute_span_offsets(guard_rows, line_starts))
def _absolute_span_offsets(row_spans, line_starts: list[int]) -> list[tuple[int, int]]:
    offsets: list[tuple[int, int]] = []
    for row, spans in (row_spans or {}).items():
        if not 1 <= row <= len(line_starts):
            continue
        base = line_starts[row - 1]
        row_limit = line_starts[row] if row < len(line_starts) else None
        for start, end in spans:
            absolute_end = base + end
            if row_limit is not None:
                absolute_end = min(absolute_end, row_limit)
            offsets.append((base + start, absolute_end))
    return offsets
def _text_evidence_mask(
        content: str, *, mask_all_strings: bool = True,
) -> list[tuple[int, int]] | None:
    comment_spans = comment_only_spans(content)
    if comment_spans is None:
        return None
    line_starts = [0]
    for _m in re.finditer("\n", content):
        line_starts.append(_m.end())
    mask = _absolute_span_offsets(comment_spans, line_starts)
    tree = _parse_ast_or_none(content)
    lines = content.split("\n")
    mask.extend(_absolute_span_offsets(
        _docstring_spans(lines, tree), line_starts))
    mask.extend(_traversal_guard_offsets(content))
    mask.extend(_absolute_span_offsets(
        _rule_table_string_spans(tree, lines), line_starts))
    mask.extend(_absolute_span_offsets(
        _rule_catalog_dict_spans(tree, lines), line_starts))
    if mask_all_strings:
        mask.extend(_absolute_span_offsets(
            _string_literal_spans(tree, lines), line_starts))
    return mask


def _string_literal_spans(
        tree: ast.Module | None, lines: list[str],
) -> dict[int, list[tuple[int, int]]]:
    """掩码全部字符串常量的字符区间。

    危险模式检测针对的是**代码**：``os.system(...)``、``eval(...)`` 这类
    调用写在字符串里时只是文档或规则描述（例如规则知识库里的示例代码）。
    把字符串内容整体掩码，可以一次性消掉「规则库与文档示例自己报自己」的
    成批误报，真实调用点仍落在代码区，不受影响。
    """
    spans: dict[int, list[tuple[int, int]]] = {}
    if tree is None:
        return spans
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Constant)
                and isinstance(node.value, str)):
            continue
        for row, row_spans in _string_constant_row_spans(node, lines).items():
            spans.setdefault(row, []).extend(row_spans)
    return spans


_RULE_ID_KEY_RE = re.compile(r'^[A-Z][A-Z0-9]{0,5}[-_]?\d{1,4}[A-Z]?$')


def _rule_catalog_dict_spans(
        tree: ast.Module | None, lines: list[str],
) -> dict[int, list[tuple[int, int]]]:
    """掩码「规则编号 → 描述」字典里的字符串值。

    ``{"B605": "避免 os.system()，使用 subprocess.run()"}`` 这类知识库把
    危险模式当作文档描述存起来；扫描器会把描述文本当成真实调用，造成
    「规则库自己报自己」的成批误报。只认键形如规则编号的字典（含至少 2
    个字符串键且占多数），避免影响普通的短字典。
    """
    spans: dict[int, list[tuple[int, int]]] = {}
    if tree is None:
        return spans
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Dict):
            continue
        string_keys = [key for key in node.keys
                       if isinstance(key, ast.Constant)
                       and isinstance(key.value, str)]
        if len(string_keys) < 2 or len(string_keys) * 2 < len(node.keys):
            continue
        if not all(_RULE_ID_KEY_RE.match(key.value)
                   for key in string_keys):
            continue
        for value in node.values:
            for sub in walk_nodes(value):
                if not (isinstance(sub, ast.Constant)
                        and isinstance(sub.value, str)):
                    continue
                for row, row_spans in _string_constant_row_spans(
                        sub, lines).items():
                    spans.setdefault(row, []).extend(row_spans)
    return spans
# 规则表命名约定：模块级常量集合里存的字符串是**检测模式定义**，不是被执行的
# 命令/被访问的路径。例如 ``DANGEROUS_COMMANDS = {"rm -rf", "chmod 777"}``
# 或 ``DANGEROUS_NETWORK = [(r'curl\\s+.*\\|\\s*(ba)?sh', '...')]``——扫文本
# 时会把模式本身当成命中，产生 100% 误报（实测 8/8 危险命令、1/1 敏感路径
# 均落在规则表里）。代码引用库（``make_code_ref`` 的示例代码块）同理。
_RULE_TABLE_NAME_RE = re.compile(
    r'(?:PATTERNS?|BLACKLIST|WHITELIST|RULES?|COMMANDS?|NETWORK|PRIVILEGE'
    r'|SECRETS?|SINKS?|DANGER[A-Z_]*|FORBIDDEN|BANNED'
    r'|SENSITIVE_?PATHS?|_REFS?)$',
    re.IGNORECASE)
def _rule_table_string_spans(
        tree: ast.Module | None, lines: list[str],
) -> dict[int, list[tuple[int, int]]]:
    spans: dict[int, list[tuple[int, int]]] = {}
    if tree is None:
        return spans
    # 规则表既可能是模块级常量，也可能封装在 ``_xxx_descriptions()`` 之类
    # 的构建函数里；只扫 ``tree.body`` 会把这部分模式定义当成真实命令，
    # 把规则目录自己报成危险调用。
    for node in walk_nodes(tree):
        if isinstance(node, ast.Assign):
            targets, value = node.targets, node.value
        elif isinstance(node, ast.AnnAssign):
            targets, value = [node.target], node.value
        else:
            continue
        if value is None:
            continue
        names = [t.id for t in targets if isinstance(t, ast.Name)]
        if not any(_RULE_TABLE_NAME_RE.search(name) for name in names):
            continue
        for sub in walk_nodes(value):
            if not (isinstance(sub, ast.Constant)
                    and isinstance(sub.value, str)):
                continue
            for row, row_spans in _string_constant_row_spans(
                    sub, lines).items():
                spans.setdefault(row, []).extend(row_spans)
    return spans
def _iter_unmasked_matches(patterns, content: str, mask, category: str,
                           string_spans, shadowed_heads=None):
    line_starts = None
    for pattern in patterns:
        for match in re.finditer(pattern, content, re.IGNORECASE):
            if _definition_site_at(content, match.start()):
                continue
            if (is_masked_offset(mask, match.start())
                    and _is_fully_masked(
                        mask, match.start(), match.end())):
                continue
            if shadowed_heads:
                if line_starts is None:
                    line_starts = [0]
                    line_starts.extend(
                        found.end() for found in re.finditer("\n", content))
                row = bisect.bisect_right(line_starts, match.start())
                col = match.start() - line_starts[row - 1]
                head = _match_head_name(match.group())
                if head and head in (
                        shadowed_heads.get((row, col)) or ()):
                    continue
            if category and inline_suppressed_at(
                    content, match.start(), category, string_spans):
                continue
            yield match
_DANGEROUS_COMMAND_VERDICT = Verdict(
    Severity.CRITICAL, '供应链安全-危险命令',
    '使用 subprocess.run([...], shell=False) 替代')
_REMOTE_SCRIPT_VERDICT_PY = Verdict(
    Severity.HIGH, '供应链安全-远程脚本', '下载后先做 SHA256 校验')
_REMOTE_SCRIPT_VERDICT_OTHER = Verdict(
    Severity.MEDIUM, '供应链安全-远程脚本', '下载后先做 SHA256 校验')
_SENSITIVE_VERDICTS = {
    _category: Verdict(_config['severity'], _category,
                        _config['recommendation'])
    for _category, _config in SENSITIVE_PATTERNS.items()
}
_SECRET_CATEGORY_WORDS = frozenset({
    'security', 'credential', 'credentials', 'secret', 'secrets', 'password',
    'passwords', 'token', 'tokens', 'auth', 'apikey', 'api-key', 'private',
    'default', 'example', 'sample', 'dummy', 'placeholder', 'changeme',
    'hardcoded', 'unknown', 'none', 'null', 'true', 'false'})
def _hardcoded_secret_is_placeholder(match) -> bool:
    value = match.group('secret_value').strip().lower()
    if _PLACEHOLDER_VALUE_RE.search(value) or value in _SECRET_CATEGORY_WORDS:
        return True
    return len(value) < 10 and value.isalpha()
_SENSITIVE_VALUE_FILTERS = {'硬编码密钥': _hardcoded_secret_is_placeholder}
def _emit_issue(report: SecurityReport, verdict: Verdict,
                rel_path: str, line_num: int, desc_tail: str) -> None:
    _loc = f'{rel_path}:{line_num}'
    _emit_location_issue(report, verdict, _loc, f'在 {_loc} {desc_tail}')
def _emit_location_issue(report: SecurityReport, verdict: Verdict,
                         location: str, description: str) -> None:
    report.issues.append(new_location_issue(verdict, location, description))
def _symlink_target(link: Path) -> Path:
    try:
        raw = os.readlink(str(link))
    except OSError as _e:
        log_swallowed(__name__, _e, context='_symlink_target:OSError')
        return link.resolve()
    return (Path(raw) if os.path.isabs(raw) else link.parent / raw).resolve()
class _FileScanView(NamedTuple):
    content: str
    mask: list
    rel_path: str
    is_py: bool
    secret_tokens: list | None
    text_mask: list
    shadowed_heads: dict
    tree: ast.Module | None
def _scan_masked_patterns(patterns, verdict: Verdict, view: _FileScanView,
                          report: SecurityReport, describe,
                          value_filter=None, *,
                          text_evidence: bool = False) -> None:
    mask = view.text_mask if text_evidence else view.mask
    seen_lines: set[int] = set()
    for match in _iter_unmasked_matches(
            patterns, view.content, mask, verdict.category,
            view.secret_tokens, view.shadowed_heads):
        if value_filter is not None and value_filter(match):
            continue
        line_num = line_no(view.content, match.start())
        if line_num in seen_lines:
            continue
        seen_lines.add(line_num)
        _emit_issue(report, verdict, view.rel_path, line_num, describe(match))
def _dangerous_call_lines(call: ast.Call) -> tuple[int, ...]:
    lines = [call.lineno]
    for kw in call.keywords:
        if kw.arg == 'shell':
            lines.append(kw.value.lineno)
            continue
        if kw.arg is not None or not isinstance(kw.value, ast.Dict):
            continue
        for key, value in zip(kw.value.keys, kw.value.values):
            if isinstance(key, ast.Constant) and key.value == 'shell':
                lines.extend((kw.value.lineno, key.lineno, value.lineno))
    return tuple(dict.fromkeys(lines))
def _scan_ast_dangerous_calls(view: _FileScanView,
                                    report: SecurityReport) -> None:
    verdict = _SENSITIVE_VERDICTS['危险系统调用']
    seen_lines: set[int] = set()
    for call, _func_name, _display in _iter_public_ast_dangers(view.tree):
        if call.lineno in seen_lines:
            continue
        suppressed_line = next((
            line for line in _dangerous_call_lines(call)
            if inline_suppressed_at(
                view.content, line_start_offset(view.content, line),
                verdict.category, view.secret_tokens)), None)
        if suppressed_line is not None:
            _log.info(
                '[SUPPRESSED-INLINE] 危险系统调用行内抑制: %s:%d',
                view.rel_path, suppressed_line)
            continue
        seen_lines.add(call.lineno)
        _emit_issue(report, verdict, view.rel_path, call.lineno,
                    '发现 危险系统调用')
def _scan_sensitive_categories(view: _FileScanView,
                               report: SecurityReport) -> None:
    for category, config in SENSITIVE_PATTERNS.items():
        if view.is_py and category == '网络请求无超时':
            continue
        if (view.is_py and category == '危险系统调用'
                and view.tree is not None):
            _scan_ast_dangerous_calls(view, report)
            continue
        _scan_masked_patterns(
            config['patterns'], _SENSITIVE_VERDICTS[category], view, report,
            lambda _m, _cat=category: f'发现 {_cat}',
            value_filter=_SENSITIVE_VALUE_FILTERS.get(category),
            text_evidence=category in _TEXT_EVIDENCE_CATEGORIES)
def _scan_network_timeouts(view: _FileScanView,
                           report: SecurityReport) -> None:
    if not view.is_py:
        return
    config = SENSITIVE_PATTERNS['网络请求无超时']
    verdict = _SENSITIVE_VERDICTS['网络请求无超时']
    tree = _runtime_security_tree(_parse_ast_or_none(view.content))
    if tree is None:
        _scan_masked_patterns(
            config['patterns'], verdict, view, report,
            lambda _m: '发现 网络请求无超时')
        return
    seen_lines: set[int] = set()
    for call, dotted in iter_network_calls_no_timeout(tree):
        if call.lineno in seen_lines:
            continue
        seen_lines.add(call.lineno)
        if inline_suppressed_at(
                view.content, line_start_offset(view.content, call.lineno),
                verdict.category, view.secret_tokens):
            _log.info(
                '[SUPPRESSED-INLINE] 网络请求无超时行内抑制: %s:%d %s',
                view.rel_path, call.lineno, dotted)
            continue
        _emit_issue(report, verdict, view.rel_path, call.lineno,
                    f'发现 网络请求无超时: {dotted}()')
def _scan_secret_patterns(view: _FileScanView,
                          report: SecurityReport) -> None:
    seen: set[tuple[int, int]] = set()
    for match in iter_secret_hits(view.content, view.rel_path,
                                   view.secret_tokens):
        key = (match.start(), match.end())
        if key in seen:
            continue
        seen.add(key)
        if match.start():
            prev = view.content[match.start() - 1]
            if prev.isascii() and prev.isalnum():
                continue
        _emit_issue(report, SECRET_LEAK_VERDICT, view.rel_path,
                    line_no(view.content, match.start()),
                    f'可能包含泄露的凭据: {mask_secret(match.group())}')
def _scan_remote_scripts(view: _FileScanView,
                         report: SecurityReport) -> None:
    _verdict = (_REMOTE_SCRIPT_VERDICT_PY if view.is_py
                else _REMOTE_SCRIPT_VERDICT_OTHER)
    _scan_masked_patterns(
        REMOTE_SCRIPT_PATTERNS, _verdict, view, report,
        lambda m: f'下载/执行远程脚本: {m.group()[:60]}',
        text_evidence=True)
def _read_scan_text(path: Path, is_py: bool) -> str:
    if is_py:
        source = read_source(str(path))
        if source is not None:
            return source
    return read_asset_text(path, "utf-8-sig")
def scan_file_security_patterns(file_path: Path, report: SecurityReport) -> None:
    _raw = coerce_skill_dir(file_path)
    if not _raw.strip():
        raise FileNotFoundError(f'安全扫描文件不存在: {file_path!r}')
    file_path = Path(_raw)
    _is_py = file_path.suffix.lower() == '.py'
    content = _read_scan_text(file_path, _is_py)
    try:
        rel_path = str(file_path.relative_to(report.skill_path))
    except ValueError as _e:
        log_swallowed(__name__, _e, context='scan_file_security_patterns:ValueError')
        rel_path = str(file_path)
    _mask = (scan_masked_spans(content, True) if _is_py
             else non_py_comment_spans(content))
    _text_mask = _mask
    if _is_py:
        _resolved = _text_evidence_mask(content)
        if _resolved is not None:
            _text_mask = _resolved
    _tree = (_runtime_security_tree(_parse_ast_or_none(content))
             if _is_py else None)
    _view = _FileScanView(
        content=content,
        mask=_mask,
        rel_path=rel_path,
        is_py=_is_py,
        secret_tokens=(py_string_token_offsets(content) if _is_py else None),
        text_mask=_text_mask,
        shadowed_heads=(_shadowed_call_heads(_tree, content)
                        if _tree is not None else {}),
        tree=_tree)
    _scan_sensitive_categories(_view, report)
    _scan_network_timeouts(_view, report)
    _scan_masked_patterns(
        DANGEROUS_COMMANDS, _DANGEROUS_COMMAND_VERDICT, _view, report,
        lambda m: f'包含危险命令: {m.group()[:60]}', text_evidence=True)
    _scan_secret_patterns(_view, report)
    _scan_remote_scripts(_view, report)
def check_dependency_declaration(skill_dir: Path, report: SecurityReport) -> None:
    _raw = coerce_skill_dir(skill_dir)
    if not _raw.strip():
        return
    skill_dir = Path(_raw)
    skill_md = skill_dir / 'SKILL.md'
    if not skill_md.is_file():
        return
    content = read_asset_text(skill_md)
    _fm_block = frontmatter_block(content)
    has_deps = _fm_block is not None and bool(
        re.search(r'^dependencies:', _fm_block, re.MULTILINE))
    has_scripts = any(
        not _is_test_scan_file(path, skill_dir)
        for path in iter_scan_scope_files(skill_dir, SCRIPT_SCAN_SUFFIXES))
    if not has_deps and has_scripts:
        _emit_location_issue(
            report,
            Verdict(Severity.INFO, '依赖声明',
                     '在 SKILL.md frontmatter 中声明 dependencies'),
            'SKILL.md', '存在脚本文件但未声明依赖')
def path_within(child: str, parent: str) -> bool:
    if not child or not parent:
        return False
    _c = os.path.normcase(os.path.normpath(child))
    _p = os.path.normcase(os.path.normpath(parent))
    _prefix = _p if _p.endswith(os.sep) else _p + os.sep
    return _c == _p or _c.startswith(_prefix)
def _symlink_escape(link: Path, boundary: Path) -> Path | None:
    target = _symlink_target(link)
    return None if path_within(str(target), str(boundary)) else target
def check_path_safety(skill_dir: Path, report: SecurityReport) -> None:
    _raw = coerce_skill_dir(skill_dir)
    if not _raw.strip():
        return
    skill_dir = Path(_raw)
    if skill_dir.is_symlink():
        _escaped = _symlink_escape(skill_dir, skill_dir.parent.resolve())
        if _escaped is not None:
            _emit_location_issue(
                report,
                Verdict(Severity.HIGH, '路径安全',
                         '确保技能目录不是指向外部的符号链接'),
                str(skill_dir),
                '技能目录是符号链接且指向可能不安全的位置: '
                + str(_escaped))
    _skill_resolved = skill_dir.resolve()
    for item in skill_dir.rglob('*'):
        if not item.is_symlink():
            continue
        _escaped = _symlink_escape(item, _skill_resolved)
        if _escaped is not None:
            _emit_location_issue(
                report,
                Verdict(Severity.HIGH, '路径安全',
                         '移除指向技能目录外的符号链接'),
                str(item),
                '符号链接逃逸: ' + str(item) + ' -> ' + str(_escaped))
_DOC_SUFFIXES: frozenset = frozenset({'.md', '.txt', '.yaml', '.yml'})
def _scan_doc_file(path: Path, report: SecurityReport) -> None:
    try:
        scan_file_security_patterns(path, report)
    except (OSError, UnicodeDecodeError) as _e:
        _log.warning('安全检查: 文件不可读 - %s: %s', path, _e)
        mark_section_degraded('文档扫描文件跳过')
_DOC_SCAN_TREES: tuple[tuple[str, frozenset], ...] = (
    ('references', _DOC_SUFFIXES),
)
def _sec_docs_scan_tree(tree_dir: Path, suffixes: frozenset,
                        report: SecurityReport,
                        *, production_only: bool = False) -> None:
    for asset in iter_scan_scope_files(tree_dir, suffixes):
        if production_only and _is_test_scan_file(asset, tree_dir):
            continue
        _scan_doc_file(asset, report)
def _sec_docs_dep_and_path(sp: Path, report: SecurityReport) -> None:
    try:
        check_dependency_declaration(sp, report)
    except (OSError, UnicodeDecodeError) as _e:
        _log.warning('安全检查: SKILL.md 不可读 - %s: %s',
                     sp / 'SKILL.md', _e)
        mark_section_degraded('依赖检查跳过')
    try:
        check_path_safety(sp, report)
    except (OSError, RuntimeError) as _e:
        _log.warning('路径安全检查异常 - %s: %s', sp, _e)
        mark_section_degraded('路径安全')
def scan_document_assets(sp: Path, report: SecurityReport) -> None:
    _raw = coerce_skill_dir(sp)
    sp = Path(_raw)
    if not _raw.strip() or not sp.is_dir():
        raise FileNotFoundError(
            f'文档安全扫描目录不存在: {_raw.strip() or repr(sp)}')
    with degraded_section('文档扫描'):
        skill_md = sp / 'SKILL.md'
        if skill_md.is_file():
            _scan_doc_file(skill_md, report)
        _sec_docs_scan_tree(sp, SCRIPT_SCAN_SUFFIXES, report,
                            production_only=True)
        for dirname, suffixes in _DOC_SCAN_TREES:
            tree_dir = sp / dirname
            if tree_dir.is_dir():
                _sec_docs_scan_tree(tree_dir, suffixes, report)
    _sec_docs_dep_and_path(sp, report)
_DANGEROUS_API_REGISTRY = (
    (r"(?<!\.)\beval\s*\(", "eval()", "basic"),
    (r"(?<!\.)\bexec\s*\(", "exec()", "basic"),
    (r"(?<!\.)\bos\.system\s*\(", "os.system()", "basic"),
    (r"(?<!\.)\bos\.popen\s*\(", "os.popen()", "basic"),
    (r"(?<!\.)\b__import__\s*\(", "__import__()", "unconditional"),
    (r"(?<!\.)\bsubprocess\.call\s*\(", "subprocess.call()", "shell"),
    (r"(?<!\.)\bsubprocess\.run\s*\(", "subprocess.run()", "shell"),
    (r"(?<!\.)\bsubprocess\.getoutput\s*\(",
     "subprocess.getoutput()", "unconditional"),
    (r"(?<!\.)\bsubprocess\.getstatusoutput\s*\(",
     "subprocess.getstatusoutput()", "unconditional"),
)
DANGEROUS_FUNCTIONS = [
    (regex, display)
    for regex, display, kind in _DANGEROUS_API_REGISTRY
    if kind == "basic"
]
_SHELL_TRUE_RULE = "shell=True"
SECURITY_DANGEROUS_PATTERNS = [
    (regex, display)
    for regex, display, kind in _DANGEROUS_API_REGISTRY
    if kind != "shell"
] + [(r"shell\s*=\s*True", _SHELL_TRUE_RULE)]
def _in_string_or_comment(spans: Any, row: int, col: int) -> bool:
    if spans is None:
        return False
    return any(start <= col < end for start, end in spans.get(row, ()))
_SUBPROCESS_CALL_RE = re.compile(r"(?<![\w.])subprocess\.\w+\s*\(")
_SUBPROCESS_FAMILY = frozenset({
    "call", "run", "Popen", "check_call", "check_output",
    "getoutput", "getstatusoutput",
})
_ALIAS_DISPLAY_BY_QUALIFIED: dict[str, str] = {
    "eval": "eval()", "builtins.eval": "eval()",
    "exec": "exec()", "builtins.exec": "exec()",
    "__import__": "__import__()",
    "builtins.__import__": "__import__()",
    "os.system": "os.system()", "os.popen": "os.popen()",
}
def _type_checking_only_node_ids(tree: ast.AST) -> set[int]:
    ids = type_checking_body_node_ids(tree)
    guard_polarities = _type_checking_guard_node_polarities(tree)
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.If)
                and guard_polarities.get(id(node)) is True):
            continue
        for stmt in node.orelse:
            ids.update(id(sub) for sub in walk_nodes(stmt))
    return ids
def _runtime_import_bindings(content: str, tree: ast.AST | None):
    if tree is None:
        return collect_import_bindings(content, None)
    type_checking_only = _type_checking_only_node_ids(tree)
    if not type_checking_only:
        return collect_import_bindings(content, tree)
    imports = [
        node for node in walk_nodes(tree)
        if (isinstance(node, (ast.Import, ast.ImportFrom))
            and id(node) not in type_checking_only)
    ]
    wrapper = ast.Module(body=imports, type_ignores=[])
    return collect_import_bindings("", wrapper)
def _dangerous_alias_displays(content: str,
                             tree: ast.AST | None) -> dict[str, str]:
    module_aliases, from_imports, star_modules = (
        _runtime_import_bindings(content, tree))
    displays: dict[str, str] = {}
    for local, qualified in from_imports.items():
        display = _ALIAS_DISPLAY_BY_QUALIFIED.get(qualified)
        if display is not None:
            displays[local] = display
            continue
        module, _sep, func = qualified.rpartition(".")
        if module == "subprocess" and func in _SUBPROCESS_FAMILY:
            displays[local] = f"subprocess.{func}()"
    for alias, module in module_aliases.items():
        if module == "subprocess":
            for func in _SUBPROCESS_FAMILY:
                displays[f"{alias}.{func}"] = f"subprocess.{func}()"
        elif module == "os":
            for func in ("system", "popen"):
                displays[f"{alias}.{func}"] = f"os.{func}()"
        elif module == "builtins":
            for func in ("eval", "exec", "__import__"):
                displays[f"{alias}.{func}"] = f"{func}()"
    for module in star_modules:
        if module == "subprocess":
            for func in _SUBPROCESS_FAMILY:
                displays.setdefault(func, f"subprocess.{func}()")
        elif module == "os":
            for func in ("system", "popen"):
                displays.setdefault(func, f"os.{func}()")
    return displays
def _alias_patterns(
        displays: dict[str, str], allowed_displays: set[str],
) -> list[tuple[str, str]]:
    return [
        (r"(?<![.\w])" + _dotted_name_pattern(local) + r"\s*\(", display)
        for local, display in displays.items()
        if display in allowed_displays
    ]
def _subprocess_alias_regexes(
        displays: dict[str, str]) -> list[re.Pattern] | None:
    names = ["subprocess\\.[A-Za-z_][A-Za-z0-9_]*"]
    names.extend(
        _dotted_name_pattern(local) for local, display in displays.items()
        if display.startswith("subprocess."))
    if len(names) == 1:
        return None
    return [re.compile(r"(?<![\w.])(?:" + "|".join(names) + r")\s*\(")]
_SHELL_LITERAL_PATTERN = (
    r"(?:[-+]?(?:True|False)|None|[-+]?\d+(?:\.\d+)?(?:[eE][-+]?\d+)?"
    r"|[rbuRBU]{0,2}(?:'(?:[^'\\]|\\.)*'|\"(?:[^\"\\]|\\.)*\"))"
)
_SHELL_KWARG_RE = re.compile(
    r"(?<![\w.])shell\s*=\s*[(\s]*"
    r"(?P<literal>" + _SHELL_LITERAL_PATTERN + r")"
    r"(?=\s*[,)#]|\s*$)")
def _static_shell_value_truthy(value: ast.AST) -> bool:
    if is_shell_true_keyword(ast.keyword(arg="shell", value=value)):
        return True
    if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        return any(not isinstance(item, ast.Starred) for item in value.elts)
    if isinstance(value, ast.Dict):
        return any(key is not None for key in value.keys)
    return False
def _shell_keyword_truthy(kw: ast.keyword) -> bool:
    if kw.arg == "shell":
        return _static_shell_value_truthy(kw.value)
    if kw.arg is not None or not isinstance(kw.value, ast.Dict):
        return False
    for key, value in reversed(list(zip(kw.value.keys, kw.value.values))):
        if key is None or not isinstance(key, ast.Constant):
            return False
        if key.value == "shell":
            return _static_shell_value_truthy(value)
    return False
def _shell_literal_truthy(literal: str) -> bool:
    try:
        value = ast.parse(literal, mode="eval").body
    except (ValueError, SyntaxError, TypeError, MemoryError, RecursionError):  # jwsgj:silent-ok 非字面量即预期分支
        return False
    return _static_shell_value_truthy(value)
def _span_intervals(spans: Any, line_starts: list[int]) -> list[tuple[int, int]]:
    intervals: list[tuple[int, int]] = []
    for row, ranges in (spans or {}).items():
        if not 1 <= row <= len(line_starts):
            continue
        base = line_starts[row - 1]
        intervals.extend((base + start, base + end) for start, end in ranges)
    intervals.sort()
    return intervals
def _shell_true_hits(content: str, spans: Any, line_starts: list[int],
                     call_regexes: list[re.Pattern] | None = None,
                     shadowed_heads: dict[tuple[int, int], set[str]] | None = None
                     ) -> list[tuple[int, str]]:
    intervals = _span_intervals(spans, line_starts)
    hits: list[tuple[int, str]] = []
    for call_re in (call_regexes or (_SUBPROCESS_CALL_RE,)):
        hits.extend(_shell_true_matches(
            content, call_re, spans, intervals, line_starts,
            shadowed_heads or {}))
    return hits
def _shell_true_matches(content: str, call_re: re.Pattern, spans: Any,
                        intervals: list[tuple[int, int]],
                        line_starts: list[int],
                        shadowed_heads: dict[tuple[int, int], set[str]]
                        ) -> list[tuple[int, str]]:
    hits: list[tuple[int, str]] = []
    total = len(content)
    for call in call_re.finditer(content):
        call_li = bisect.bisect_right(line_starts, call.start()) - 1
        call_col = call.start() - line_starts[call_li]
        if _in_string_or_comment(spans, call_li + 1, call_col):
            continue
        head = _match_head_name(call.group())
        if head and head in (
                shadowed_heads.get((call_li + 1, call_col)) or ()):
            continue
        pos = call.end()
        depth = 1
        cursor = bisect.bisect_right(intervals, (pos, float("inf")))
        if cursor:
            span_start, span_end = intervals[cursor - 1]
            if span_start <= pos < span_end:
                pos = span_end
        while pos < total and depth > 0:
            while cursor < len(intervals) and intervals[cursor][1] <= pos:
                cursor += 1
            if cursor < len(intervals) and intervals[cursor][0] <= pos:
                pos = intervals[cursor][1]
                continue
            if depth == 1:
                kwarg = _SHELL_KWARG_RE.match(content, pos)
                if kwarg and _shell_literal_truthy(kwarg.group('literal')):
                    li = bisect.bisect_right(line_starts, pos) - 1
                    hits.append((li + 1, _SHELL_TRUE_RULE))
                    pos = kwarg.end()
                    continue
            char = content[pos]
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
            pos += 1
    return hits
def _scan_file_security_hits(
        content: str,
        patterns: Iterable[tuple[str, str]],
        subprocess_regexes: list[re.Pattern] | None = None,
        shadowed_heads: dict[tuple[int, int], set[str]] | None = None,
) -> list[tuple[int, str]]:
    hits: list[tuple[int, str]] = []
    spans = string_comment_spans(content)
    line_starts = [0]
    for _m in re.finditer('\n', content):
        line_starts.append(_m.end())
    for pattern, func_name in patterns:
        if func_name == _SHELL_TRUE_RULE:
            hits.extend(_shell_true_hits(
                content, spans, line_starts, subprocess_regexes,
                shadowed_heads))
            continue
        for match in re.finditer(pattern, content):
            if _definition_site_at(content, match.start()):
                continue
            li = bisect.bisect_right(line_starts, match.start()) - 1
            col = match.start() - line_starts[li]
            if _in_string_or_comment(spans, li + 1, col):
                continue
            head = _match_head_name(match.group())
            if head and head in (
                    (shadowed_heads or {}).get((li + 1, col)) or ()):
                continue
            hits.append((li + 1, func_name))
    return hits
def _scan_content_security_hits(
        content: str,
        patterns: Iterable[tuple[str, str]],
) -> list[tuple[int, str]]:
    patterns = tuple(patterns)
    tree = _runtime_security_tree(_parse_ast_or_none(content))
    alias_displays = (
        _dangerous_alias_displays(content, tree) if tree is not None else {})
    shadowed_heads = (
        _shadowed_call_heads(tree, content) if tree is not None else {})
    hits = (
        _scan_file_security_hits(
            content, patterns, _subprocess_alias_regexes(alias_displays),
            shadowed_heads)
        + _scan_file_security_hits(
            content,
            _alias_patterns(
                alias_displays, {display for _regex, display in patterns}),
            shadowed_heads=shadowed_heads)
    )
    return list(dict.fromkeys(hits))
def scan_dangerous_calls(
        content: str,
        *,
        basic_only: bool = False,
) -> list[str]:
    tree = _runtime_security_tree(_parse_ast_or_none(content))
    if tree is not None:
        allowed = ({display for _regex, display in DANGEROUS_FUNCTIONS}
                   if basic_only else None)
        hits: list[str] = []
        for _call, _func_name, display in _iter_public_ast_dangers(tree):
            if allowed is not None and display not in allowed:
                continue
            if display not in hits:
                hits.append(display)
        return hits
    patterns = (DANGEROUS_FUNCTIONS if basic_only
                else SECURITY_DANGEROUS_PATTERNS)
    hits = []
    for _line_no, func_name in sorted(
            _scan_content_security_hits(content, patterns),
            key=lambda hit: hit[0]):
        if func_name not in hits:
            hits.append(func_name)
    return hits
def _iter_security_scan_files(skill_dir: str) -> Iterator[str]:
    root = Path(skill_dir)
    for fpath in sorted(iter_py_files(skill_dir)):
        if not _is_test_scan_file(Path(fpath), root):
            yield fpath
_NOQA_SUPPRESS_RE = re.compile(
    r"#\s*noqa(?![A-Za-z0-9_])(?::\s*[A-Za-z0-9_, \t]+)?",
    re.IGNORECASE)
def _line_suppressed_by_noqa(lines: list[str], row: int,
                             comment_spans) -> bool:
    if not 0 < row <= len(lines):
        return False
    match = _NOQA_SUPPRESS_RE.search(lines[row - 1])
    if match is None:
        return False
    return any(start <= match.start() < end
               for start, end in (comment_spans or {}).get(row, ()))
def _scan_py_file_security(fpath: str, skill_dir: str) -> list[str]:
    content = read_source(fpath)
    if content is None:
        _log.warning("scan_security_issues: 源码不可读，记入安全扫描错误: %s", fpath)
        relpath = os.path.relpath(fpath, skill_dir)
        return [f"安全扫描错误: 源码不可读: {relpath}"]
    relpath = os.path.relpath(fpath, skill_dir)
    lines = content.splitlines()
    comment_spans = comment_only_spans(content)
    tree = _runtime_security_tree(_parse_ast_or_none(content))
    if tree is not None:
        issues = []
        for call, _func_name, display in _iter_public_ast_dangers(tree):
            if any(_line_suppressed_by_noqa(lines, row, comment_spans)
                   for row in _dangerous_call_lines(call)):
                continue
            issues.append(
                f"安全风险: {relpath}:{call.lineno} 含 '{display}'")
        return issues
    return [f"安全风险: {relpath}:{row} 含 '{func_name}'"
            for row, func_name in _scan_content_security_hits(
                content, SECURITY_DANGEROUS_PATTERNS)
            if not _line_suppressed_by_noqa(lines, row, comment_spans)]
def scan_security_issues(skill_dir: str) -> list[str]:
    root = coerce_skill_dir(skill_dir)
    if not root.strip() or not os.path.isdir(root):
        raise FileNotFoundError(
            f'安全扫描目录不存在: {root.strip() or repr(skill_dir)}')
    issues = []
    for fpath in _iter_security_scan_files(root):
        issues.extend(_scan_py_file_security(fpath, root))
    return issues
class _SpanTables(NamedTuple):
    merged: dict[int, list[tuple[int, int]]] | None
    comments: dict[int, list[tuple[int, int]]] | None
    docstrings: dict[int, list[tuple[int, int]]]
class _DangerForm(NamedTuple):
    category: str
    module: str
    func: str
    tail: str
    desc: str
    code_only: bool
    anchor_in_code: bool = False
    token: str = ""
    token_in_code: bool = True
class _DerivedPattern(NamedTuple):
    category: str
    regex: re.Pattern
    desc: str
    code_only: bool
    anchor_in_code: bool = False
    head_regex: re.Pattern | None = None
    token_regex: re.Pattern | None = None
    token_in_code: bool = True
class _ScanContext(NamedTuple):
    fname: str
    suppressions: dict
    tables: _SpanTables
    patterns: list[_DerivedPattern]
    lines: list[str]
    line_starts: list[int]
    guards: list[tuple[int, int]]
    shadowed_heads: dict[tuple[int, int], set[str]]
    tree: ast.Module | None
def _span_end(row_spans: Iterable[tuple[int, int]], col: int) -> int | None:
    for start, end in row_spans:
        if start <= col < end:
            return end
    return None
def _span_contains(row_spans: Iterable[tuple[int, int]], col: int) -> bool:
    return _span_end(row_spans, col) is not None
def _hit_in_code(row: int, col: int, spans: dict[int, list[tuple[int, int]]] | None) -> bool:
    if spans is None:
        return True
    return not _span_contains(spans.get(row, ()), col)
def _hit_in_comment(row: int, col: int,
                    comment_spans: dict[int, list[tuple[int, int]]] | None) -> bool:
    if comment_spans is None:
        return False
    return _span_contains(comment_spans.get(row, ()), col)
def _call_head_name(node: ast.Call) -> str:
    func = node.func
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        return func.value.id
    return ''
def _scope_nodes(scope) -> Iterator[ast.AST]:
    body = getattr(scope, "body", None)
    if not isinstance(body, list):
        return
    stack = list(body)
    while stack:
        node = stack.pop()
        yield node
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda)):
            continue
        stack.extend(ast.iter_child_nodes(node))
def _scope_import_nodes(scope) -> list:
    imports = (node for node in _scope_nodes(scope)
               if isinstance(node, (ast.Import, ast.ImportFrom)))
    return sorted(imports, key=lambda n: (n.lineno, n.col_offset))
def _node_position(node: ast.AST, parents) -> tuple[int, int]:
    current = node
    while current is not None:
        lineno = getattr(current, 'lineno', None)
        if lineno is not None:
            return lineno, getattr(current, 'col_offset', 0)
        current = parents.get(id(current))
    return 0, 0
def _scope_binding_may_precede_call(scope, name: str, call: ast.Call,
                                    parents) -> bool:
    call_pos = _node_position(call, parents)
    for node in _scope_nodes(scope):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            continue
        if name not in scope_node_bound_names(node):
            continue
        if _node_position(node, parents) < call_pos:
            return True
    return False
def _security_call_head_is_shadowed(node: ast.Call, table, scopes,
                                    parents) -> bool:
    func = node.func
    if isinstance(func, ast.Name):
        name = func.id
    elif isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        name = func.value.id
    else:
        return False
    scope = scopes.get(id(node))
    direct = scope
    while scope is not None:
        if ((not (isinstance(scope, ast.ClassDef) and scope is not direct)
                and name in table.shadow_bound.get(scope, frozenset()))
                and (not isinstance(scope, (ast.Module, ast.ClassDef))
                     or _scope_binding_may_precede_call(
                         scope, name, node, parents))):
            return True
        scope = table.parent.get(scope)
    return False
def _call_import_bindings(call: ast.Call, parents,
                          type_checking_only=frozenset()):
    module_aliases, from_imports, star_modules = {}, {}, set()
    scopes = list(reversed(iter_evaluation_scope_chain(call, parents)))
    for index, scope in enumerate(scopes):
        for node in _scope_import_nodes(scope):
            if id(node) in type_checking_only:
                continue
            if (index == len(scopes) - 1
                    and (node.lineno, node.col_offset)
                    >= (call.lineno, call.col_offset)):
                continue
            wrapper = ast.Module(body=[node], type_ignores=[])
            modules, imported, stars = collect_import_bindings("", wrapper)
            module_aliases.update(modules)
            from_imports.update(imported)
            star_modules.update(stars)
    return module_aliases, from_imports, star_modules
def _import_target_names(local_name: str, bindings) -> set[str]:
    module_aliases, from_imports, star_modules = bindings
    if "." in local_name:
        root, rest = local_name.split(".", 1)
        module = module_aliases.get(root)
        return {f"{module}.{rest}"} if module else set()
    if local_name in from_imports:
        return {from_imports[local_name]}
    return {f"{module}.{local_name}" for module in star_modules}
def _shadow_key(node: ast.AST, lines: list[str]) -> tuple[int, int]:
    lineno = node.lineno
    col = node.col_offset
    if 1 <= lineno <= len(lines):
        col = byte_col_to_char_col(lines[lineno - 1], col)
    return (lineno, col)
def _shadowed_call_heads(tree: ast.Module | None, content: str
                         ) -> dict[tuple[int, int], set[str]]:
    if tree is None:
        return {}
    lines = content.split('\n')
    shadow = collect_lexical_scope_table(tree)
    scopes = call_scope_map(shadow)
    heads: dict[tuple[int, int], set[str]] = {}
    parents = build_parent_map(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        if not _security_call_head_is_shadowed(
                node, shadow, scopes, parents):
            continue
        name = _call_head_name(node)
        if name:
            heads.setdefault(_shadow_key(node, lines), set()).add(name)
    alias_displays = _dangerous_alias_displays("", tree)
    if not alias_displays:
        return heads
    global_bindings = _runtime_import_bindings("", tree)
    type_checking_only = _type_checking_only_node_ids(tree)
    expected = {local: _import_target_names(local, global_bindings)
                for local in alias_displays}
    candidate_heads = {local.split(".", 1)[0] for local in alias_displays}
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        head = _call_head_name(node)
        if head not in candidate_heads:
            continue
        visible = _call_import_bindings(
            node, parents, type_checking_only)
        for local in alias_displays:
            if local.split(".", 1)[0] != head:
                continue
            targets = _import_target_names(local, visible)
            if expected[local] and not expected[local] & targets:
                heads.setdefault(_shadow_key(node, lines), set()).add(head)
    return heads
def _match_head_name(text: str) -> str:
    return re.split(r'[.(]', text, maxsplit=1)[0].strip()
def _parse_ast_or_none(content: str) -> ast.Module | None:
    try:
        return parse_cached(content)
    except (SyntaxError, ValueError, RecursionError, MemoryError) as _e:
        log_swallowed(
            __name__, _e,
            context=f'_parse_ast_or_none:{type(_e).__name__}')
        return None
class _StaticallyUnreachableBranchPruner(ast.NodeTransformer):
    def __init__(self, type_checking_polarities: dict[int, bool]):
        self._type_checking_polarities = type_checking_polarities

    def _visit_live_statements(self, statements) -> list:
        visited: list = []
        for statement in statements:
            result = self.visit(statement)
            if result is None:
                continue
            if isinstance(result, list):
                visited.extend(result)
            else:
                visited.append(result)
        return visited
    def visit_If(self, node):
        if isinstance(node.test, ast.Constant):
            live = node.body if bool(node.test.value) else node.orelse
            return self._visit_live_statements(live)
        polarity = self._type_checking_polarities.get(id(node))
        if polarity is not None:
            live = node.body if polarity else node.orelse
            return self._visit_live_statements(live)
        return self.generic_visit(node)
    def visit_While(self, node):
        if not isinstance(node.test, ast.Constant):
            return self.generic_visit(node)
        if not bool(node.test.value):
            return self._visit_live_statements(node.orelse)
        node.body = self._visit_live_statements(node.body)
        node.orelse = []
        return node
def _runtime_security_tree(tree: ast.Module | None) -> ast.Module | None:
    if tree is None:
        return None
    has_constant_branch = any(
        isinstance(node, (ast.If, ast.While))
        and isinstance(node.test, ast.Constant)
        for node in walk_nodes(tree))
    type_checking_polarities = _type_checking_guard_node_polarities(tree)
    if not has_constant_branch and not type_checking_polarities:
        return tree
    projected = copy.deepcopy(tree)
    projected_polarities = {
        id(projected_node): type_checking_polarities[id(original_node)]
        for original_node, projected_node in zip(
            tuple(ast.walk(tree)), tuple(ast.walk(projected)), strict=True)
        if id(original_node) in type_checking_polarities
    }
    return _StaticallyUnreachableBranchPruner(projected_polarities).visit(projected)
def _docstring_spans(lines: list[str],
                     tree: ast.Module | None) -> dict[int, list[tuple[int, int]]]:
    if tree is None:
        return {}
    spans: dict[int, list[tuple[int, int]]] = {}
    for node in walk_nodes(tree):
        tok = _docstring_first_const(node)
        if tok is None:
            continue
        _expand_docstring_rows(tok, lines, spans)
    return spans
_DOCSTRING_HOSTS = (ast.Module, ast.ClassDef,
                    ast.FunctionDef, ast.AsyncFunctionDef)
def _docstring_first_const(node: ast.AST) -> ast.Constant | None:
    if not isinstance(node, _DOCSTRING_HOSTS):
        return None
    body = getattr(node, "body", None)
    if not body or not is_docstring_stmt(body[0]):
        return None
    return body[0].value
def _expand_docstring_rows(tok: ast.Constant, lines: list[str],
                           spans: dict[int, list[tuple[int, int]]]) -> None:
    srow, scol_b = tok.lineno, tok.col_offset
    erow, ecol_b = tok.end_lineno, tok.end_col_offset
    for r in range(srow, erow + 1):
        if not (1 <= r <= len(lines)):
            continue
        cs = byte_col_to_char_col(lines[r - 1], scol_b) if r == srow else 0
        ce = byte_col_to_char_col(lines[r - 1], ecol_b) if r == erow else (1 << 30)
        spans.setdefault(r, []).append((cs, ce))
def _match_exempted(phys_line: int, phys_col: int, match: re.Match,
                     seg_offsets: list[tuple[int, int]],
                     tables: _SpanTables,
                     code_only: bool,
                     anchor_in_code: bool = False) -> bool:
    if code_only:
        if not _hit_in_code(phys_line, phys_col, tables.merged):
            return True
        end_line, end_col = _resolve_position(seg_offsets, match.end() - 1)
        if _hit_in_comment(end_line, end_col, tables.comments):
            return True
        return bool(anchor_in_code) and not _hit_in_code(
            end_line, end_col, tables.merged)
    return (_hit_in_comment(phys_line, phys_col, tables.comments)
            or _span_contains(
                tables.docstrings.get(phys_line, ()), phys_col))
_DEF_SITE_RE = re.compile(r"\b(?:def|class)\s+$")
def _definition_site_at(text: str, pos: int) -> bool:
    line_start = text.rfind("\n", 0, pos) + 1
    return bool(_DEF_SITE_RE.search(text, line_start, pos))
def _call_close_index(logical: str, start: int,
                      seg_offsets: list[tuple[int, int]],
                      tables: _SpanTables) -> int:
    depth = 1
    i = start
    while i < len(logical):
        row, col = _resolve_position(seg_offsets, i)
        if not _hit_in_code(row, col, tables.merged):
            i += 1
            continue
        if _hit_in_comment(row, col, tables.comments):
            i += 1
            continue
        ch = logical[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return len(logical)
def _argument_depth(logical: str, start: int, pos: int,
                    seg_offsets: list[tuple[int, int]],
                    tables: _SpanTables) -> int:
    depth = 1
    i = start
    while i < pos:
        row, col = _resolve_position(seg_offsets, i)
        if (_hit_in_code(row, col, tables.merged)
                and not _hit_in_comment(row, col, tables.comments)):
            ch = logical[i]
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
        i += 1
    return depth
def _first_code_token_line(token_regex: re.Pattern, logical: str,
                           start: int, end: int,
                           seg_offsets: list[tuple[int, int]],
                           tables: _SpanTables,
                           token_in_code: bool = True) -> int | None:
    for tok in token_regex.finditer(logical, start, end):
        literal = tok.groupdict().get("literal")
        if literal is not None and not _shell_literal_truthy(literal):
            continue
        token_pos = tok.start() if literal is not None else tok.end() - 1
        row, col = _resolve_position(seg_offsets, token_pos)
        if token_in_code:
            if not _hit_in_code(row, col, tables.merged):
                continue
            if _argument_depth(
                    logical, start, tok.start(), seg_offsets, tables) != 1:
                continue
        if _hit_in_comment(row, col, tables.comments):
            continue
        if _span_contains(tables.docstrings.get(row, ()), col):
            continue
        return row
    return None
def _resolve_position(seg_offsets: list[tuple[int, int]], abs_col: int) -> tuple[int, int]:
    phys_line = seg_offsets[0][1]
    seg_start = 0
    for off, lineno in seg_offsets:
        if off <= abs_col:
            seg_start, phys_line = off, lineno
        else:
            break
    return phys_line, abs_col - seg_start
def _logical_lines_passthrough(lines: list[str]):
    for i, line in enumerate(lines, 1):
        if line.lstrip().startswith('#'):
            continue
        yield i, line, [(0, i)]
def _depth_scan_line(line: str, row_spans, depth: int) -> int:
    col = 0
    while col < len(line):
        hit = _span_end(row_spans, col)
        if hit is not None:
            col = hit
            continue
        ch = line[col]
        if ch in '([{':
            depth += 1
        elif ch in ')]}':
            depth = max(depth - 1, 0)
        col += 1
    return depth
def _dotted_name_pattern(local_name: str) -> str:
    return r"\s*\.\s*".join(re.escape(part) for part in local_name.split("."))
def _line_has_continuation(joined: str, row_spans) -> bool:
    return bool(joined.endswith('\\')
                and not _span_contains(row_spans, len(joined) - 1))
def _logical_text(line: str, cont: bool) -> str:
    if not cont:
        return line
    return line.rstrip()[:-1]
def _logical_lines(lines: list[str], spans: dict[int, list[tuple[int, int]]] | None):
    if spans is None:
        yield from _logical_lines_passthrough(lines)
        return
    segs: list[tuple[int, int]] = []
    buf: list[str] = []
    offset = 0
    depth = 0
    start = 1
    prev_cont = False
    for lineno, line in enumerate(lines, 1):
        if not buf:
            start = lineno
            segs = []
            offset = 0
            prev_cont = False
        row_spans = spans.get(lineno, ())
        cont = _line_has_continuation(line.rstrip(), row_spans)
        if buf and not prev_cont:
            buf.append(' ')
            offset += 1
        segs.append((offset, lineno))
        text = _logical_text(line, cont)
        buf.append(text)
        offset += len(text)
        depth = _depth_scan_line(line, row_spans, depth)
        prev_cont = cont
        if depth == 0 and not cont:
            yield start, ''.join(buf), list(segs)
            buf = []
    if buf:
        yield start, ''.join(buf), list(segs)
_CALL_TAIL = r"\s*\("
_SHELL_TRUE_TAIL = r"\s*\(.*?shell\s*="
_HTTP_PLAINTEXT_TAIL = r"\s*\(.*?http://"
_PASSWORD_TAIL = r"\s*\(.*?(?i:password)"  # jwsgj:suppress RL-01 CF-02 SE-03 E1-HARDCODED-CRED E1-hardcoded_secret hardcoded_secret — 审计认可：password 检测模式正则常量，非硬编码凭据
_TAIL_TOKENS = {
    _SHELL_TRUE_TAIL: (_SHELL_KWARG_RE.pattern, True),
    _HTTP_PLAINTEXT_TAIL: (r"http://", False),
    _PASSWORD_TAIL: (r"(?i:password)", False),
}
GATE_DANGEROUS_CALL_FORMS: dict[str, list[tuple[str, str, str, bool]]] = {
    "code_execution": [
        ("builtins.eval", _CALL_TAIL, "eval execution", True),
        ("builtins.exec", _CALL_TAIL, "exec execution", True),
        ("builtins.__import__", _CALL_TAIL, "Dynamic import", True),
        ("os.system", _CALL_TAIL, "System command execution", True),
        ("os.popen", _CALL_TAIL, "System command execution", True),
        ("subprocess.call", _SHELL_TRUE_TAIL, "Shell=True execution", True),
        ("subprocess.run", _SHELL_TRUE_TAIL, "Shell=True execution", True),
        ("subprocess.Popen", _SHELL_TRUE_TAIL, "Shell=True execution", True),
        ("subprocess.check_call", _SHELL_TRUE_TAIL, "Shell=True execution", True),
        ("subprocess.check_output", _SHELL_TRUE_TAIL, "Shell=True execution", True),
        ("subprocess.getoutput", _CALL_TAIL, "Implicit shell execution", True),
        ("subprocess.getstatusoutput", _CALL_TAIL, "Implicit shell execution", True),
    ],
    "network": [
        ("requests.post", _HTTP_PLAINTEXT_TAIL, "HTTP plaintext", True),
        ("requests.put", _HTTP_PLAINTEXT_TAIL, "HTTP plaintext", True),
        ("requests.patch", _HTTP_PLAINTEXT_TAIL, "HTTP plaintext", True),
        ("socket.send", _PASSWORD_TAIL, "Password over network", True),
        ("socket.sendto", _PASSWORD_TAIL, "Password over network", True),
        ("socket.sendall", _PASSWORD_TAIL, "Password over network", True),
    ],
    "file_operations": [
        ("os.remove", _CALL_TAIL, "File deletion", True),
        ("os.unlink", _CALL_TAIL, "File deletion", True),
        ("os.rmdir", _CALL_TAIL, "File deletion", True),
        ("shutil.rmtree", _CALL_TAIL, "Recursive deletion", True),
    ],
}
_GATE_CODE_ANCHOR_FORMS: frozenset[str] = frozenset({
    "subprocess.call", "subprocess.run", "subprocess.Popen",
    "subprocess.check_call", "subprocess.check_output",
})
GATE_DANGEROUS_TEXT_PATTERNS: dict[str, list[tuple[str, str, bool]]] = {
    "code_execution": [
        (r"(?<![.\w])eval\s*\(", "eval execution", True),
        (r"(?<![.\w])exec\s*\(", "exec execution", True),
        (r"(?<![.\w])__import__\s*\(", "Dynamic import", True),
    ],
    "file_operations": [
        (r"(?:\.\.[/\\])+", "Path traversal", False),
    ],
}
def _rebind(form: _DangerForm, local_name: str) -> _DerivedPattern:
    prefix = r"(?<![.\w])" + _dotted_name_pattern(local_name)
    token = form.token or ""
    return _DerivedPattern(
        form.category,
        re.compile(prefix + form.tail),
        form.desc, form.code_only, form.anchor_in_code,
        re.compile(prefix + r"\s*\(") if token else None,
        re.compile(token) if token else None,
        form.token_in_code)
def _derive_file_patterns(content: str,
                          tree: ast.Module | None
                          ) -> list[_DerivedPattern]:
    module_aliases, from_imports, star_modules = (
        _runtime_import_bindings(content, tree))
    index = _build_danger_index()
    patterns = _dp_all_channels(
        index, module_aliases, from_imports, star_modules)
    if tree is not None:
        return [form for form in patterns
                if form.category not in {'code_execution', 'network'}
                and (form.category != 'file_operations' or not form.code_only)]
    return patterns
def _dp_all_channels(index: dict[str, _DangerForm],
                     module_aliases: dict[str, str],
                     from_imports: dict[str, str],
                     star_modules: set[str]) -> list[_DerivedPattern]:
    forms = [_rebind(form, f"{form.module}.{form.func}")
             for form in index.values()]
    forms.extend(
        _DerivedPattern(category, re.compile(pattern), desc, code_only)
        for category, patterns in GATE_DANGEROUS_TEXT_PATTERNS.items()
        for pattern, desc, code_only in patterns)
    for local, qualified in from_imports.items():
        form = index.get(qualified)
        if form is not None:
            forms.append(_rebind(form, local))
    for module in star_modules:
        forms.extend(_rebind(form, form.func)
                     for form in index.values() if form.module == module)
    for alias, module in module_aliases.items():
        forms.extend(_rebind(form, f"{alias}.{form.func}")
                     for form in index.values() if form.module == module)
    derived: list[_DerivedPattern] = []
    seen: set[tuple[str, str]] = set()
    for form in forms:
        key = (form.category, form.regex.pattern)
        if key in seen:
            continue
        seen.add(key)
        derived.append(form)
    return derived
def _build_danger_index() -> dict[str, _DangerForm]:
    index: dict[str, _DangerForm] = {}
    for category, forms in GATE_DANGEROUS_CALL_FORMS.items():
        for qualified, tail, desc, code_only in forms:
            module, _, func = qualified.rpartition(".")
            token, token_in_code = _TAIL_TOKENS.get(tail, ("", True))
            index[qualified] = _DangerForm(
                category, module, func, tail, desc, code_only,
                qualified in _GATE_CODE_ANCHOR_FORMS,
                token, token_in_code)
    return index
def _prepare_scan_context(fpath: str) -> _ScanContext:
    content = read_source(fpath)
    if content is None:
        _log.warning("scan_python_security_file: 源码不可读: %s", fpath)
        raise OSError(f"scan_python_security_file: 源码不可读: {fpath}")
    try:
        suppressions = parse_suppressions(content)
    except Exception as e:  # noqa: BLE001 — 解析失败置空降级
        _log.warning("[Pipeline] 抑制配置解析失败,置空: %s", e)
        suppressions = {}
    lines = content.split("\n")
    line_starts = [0]
    line_starts.extend(
        found.end() for found in re.finditer("\n", content))
    tree = _parse_ast_or_none(content)
    runtime_tree = _runtime_security_tree(tree)
    tables = _SpanTables(
        merged=string_comment_spans(content),
        comments=comment_only_spans(content),
        docstrings=_docstring_spans(lines, tree),
    )
    return _ScanContext(
        fname=os.path.basename(fpath),
        suppressions=suppressions,
        tables=tables,
        patterns=_derive_file_patterns(content, runtime_tree),
        lines=lines,
        line_starts=line_starts,
        guards=_traversal_guard_offsets(content),
        shadowed_heads=_shadowed_call_heads(runtime_tree, content),
        tree=runtime_tree,
    )
def _head_is_shadowed(form: _DerivedPattern, hit_text: str,
                      phys_line: int, phys_col: int,
                      ctx: _ScanContext) -> bool:
    if not form.code_only:
        return False
    names = ctx.shadowed_heads.get((phys_line, phys_col))
    if not names:
        return False
    return _match_head_name(hit_text) in names
def _hits_in_logical_line(logical: str,
                          seg_offsets: list[tuple[int, int]],
                          ctx: _ScanContext) -> list[str]:
    hits: list[str] = []
    for form in ctx.patterns:
        if form.token_regex is not None:
            hits.extend(_hits_for_tail_form(
                form, logical, seg_offsets, ctx))
            continue
        for match in form.regex.finditer(logical):
            if _definition_site_at(logical, match.start()):
                continue
            phys_line, phys_col = _resolve_position(
                seg_offsets, match.start())
            if _match_exempted(
                    phys_line, phys_col, match, seg_offsets, ctx.tables,
                    form.code_only, form.anchor_in_code):
                continue
            if _head_is_shadowed(
                    form, match.group(), phys_line, phys_col, ctx):
                continue
            if (ctx.guards and 1 <= phys_line <= len(ctx.line_starts)
                    and is_masked_offset(
                        ctx.guards,
                        ctx.line_starts[phys_line - 1] + phys_col)):
                _log.info(
                    '[SUPPRESSED-GUARD] %s 路径守卫语义: %s:%d %s',
                    form.category, ctx.fname, phys_line, match.group())
                continue
            if is_suppressed(ctx.suppressions, phys_line, form.category):
                continue
            hits.append(
                f"{form.category}: {form.desc} in {ctx.fname}:{phys_line}")
    return hits
def _hits_for_tail_form(form: _DerivedPattern, logical: str,
                        seg_offsets: list[tuple[int, int]],
                        ctx: _ScanContext) -> list[str]:
    hits: list[str] = []
    for head in form.head_regex.finditer(logical):
        if _definition_site_at(logical, head.start()):
            continue
        head_line, head_col = _resolve_position(seg_offsets, head.start())
        if not _hit_in_code(head_line, head_col, ctx.tables.merged):
            continue
        close = _call_close_index(
            logical, head.end(), seg_offsets, ctx.tables)
        token_line = _first_code_token_line(
            form.token_regex, logical, head.end(), close,
            seg_offsets, ctx.tables, form.token_in_code)
        if token_line is None:
            continue
        if _head_is_shadowed(
                form, head.group(), head_line, head_col, ctx):
            continue
        if is_suppressed(ctx.suppressions, head_line, form.category):
            continue
        if is_suppressed(ctx.suppressions, token_line, form.category):
            continue
        hits.append(
            f"{form.category}: {form.desc} in {ctx.fname}:{head_line}")
    return hits
def scan_python_security_file(fpath: str) -> list[str]:
    ctx = _prepare_scan_context(fpath)
    issues: list[str] = []
    if ctx.tree is not None:
        index = _build_danger_index()
        for call, func_name, _display in _iter_public_ast_dangers(ctx.tree):
            canonical = (f'builtins.{func_name}'
                         if func_name in {'eval', 'exec', '__import__'}
                         else func_name)
            form = index[canonical]
            suppressed_lines = set(_dangerous_call_lines(call))
            if any(is_suppressed(ctx.suppressions, line, form.category)
                   for line in suppressed_lines):
                continue
            issues.append(
                f'{form.category}: {form.desc} in {ctx.fname}:{call.lineno}')
        for call, form, token_lines in _iter_gate_non_code_ast_calls(
                ctx.tree, index):
            suppressed_lines = {call.lineno, *token_lines}
            if any(is_suppressed(ctx.suppressions, line, form.category)
                   for line in suppressed_lines):
                continue
            issues.append(
                f'{form.category}: {form.desc} in {ctx.fname}:{call.lineno}')
    for _start, logical, seg_offsets in _logical_lines(
            ctx.lines, ctx.tables.merged):
        issues.extend(
            _hits_in_logical_line(logical, seg_offsets, ctx))
    issues.sort(key=lambda issue: int(issue.rsplit(':', 1)[1]))
    return list(dict.fromkeys(issues))
def _gate_resolve_call_names(node: ast.Call, module_aliases: dict[str, str],
                        from_imports: dict[str, str],
                        star_modules: set[str]) -> list[str]:
    func = node.func
    if isinstance(func, ast.Name):
        mapped = from_imports.get(func.id)
        if mapped is not None:
            return [mapped]
        return [func.id] + [f"{module}.{func.id}"
                            for module in sorted(star_modules)]
    if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        base = func.value.id
        return [f"{module_aliases.get(base, base)}.{func.attr}"]
    return []
@dataclass
class _GateCollectors:
    issues: list
    warnings: list
    metrics: dict[str, int]
GATE_UNCONDITIONAL_DANGEROUS_CALLS: frozenset[str] = frozenset({
    "eval", "exec", "builtins.eval", "builtins.exec",
    "__import__", "builtins.__import__",
    "os.system", "os.popen",
    "subprocess.getoutput", "subprocess.getstatusoutput",
})
GATE_SUBPROCESS_SHELL_FAMILY: frozenset[str] = frozenset({
    "subprocess.call", "subprocess.run", "subprocess.Popen",
    "subprocess.check_call", "subprocess.check_output",
})
def _gate_check_ast_antipatterns(tree: ast.AST, py_file: str,
                            collectors: _GateCollectors) -> None:
    for node in walk_nodes(tree):
        if isinstance(node, ast.ExceptHandler):
            _gate_flag_exception_antipatterns(node, py_file, collectors)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda)):
            _gate_flag_mutable_defaults(node, py_file, collectors)
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            _gate_flag_star_imports(node, py_file, collectors)
def _gate_flag_exception_antipatterns(node: ast.ExceptHandler, py_file: str,
                                 collectors: _GateCollectors) -> None:
    if node.type is None:
        collectors.issues.append(
            f"Anti-pattern: {os.path.basename(py_file)}:{node.lineno} bare except"
        )
        collectors.metrics["bare_excepts"] += 1
        collectors.metrics["anti_patterns"] += 1
    if len(node.body) == 1 and is_placeholder_stmt(node.body[0]):
        placeholder = ("pass" if isinstance(node.body[0], ast.Pass)
                       else "ellipsis")
        collectors.warnings.append(
            f"Exception: {os.path.basename(py_file)}:{node.lineno} "
            f"swallowed with {placeholder}"
        )
def _gate_flag_mutable_defaults(node: ast.FunctionDef | ast.AsyncFunctionDef
                           | ast.Lambda, py_file: str,
                           collectors: _GateCollectors) -> None:
    _fname = getattr(node, "name", "<lambda>")
    for default in [
        *node.args.defaults,
        *(d for d in node.args.kw_defaults if d is not None),
    ]:
        if is_mutable_default(default):
            collectors.issues.append(
                f"Anti-pattern: {os.path.basename(py_file)}:{node.lineno} "
                f"mutable default in {_fname}()"
            )
            collectors.metrics["anti_patterns"] += 1
def _gate_flag_star_imports(node: ast.Import | ast.ImportFrom, py_file: str,
                      collectors: _GateCollectors) -> None:
    for alias in node.names:
        if alias.name == "*":
            collectors.warnings.append(
                f"Anti-pattern: {os.path.basename(py_file)}:{node.lineno} star import"
            )
            collectors.metrics["anti_patterns"] += 1
def _iter_gate_resolved_calls(
        tree: ast.AST) -> Iterator[tuple[ast.Call, list[str]]]:
    parents = build_parent_map(tree)
    shadow = collect_lexical_scope_table(tree)
    scopes = call_scope_map(shadow)
    type_checking_only = _type_checking_only_node_ids(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        if _security_call_head_is_shadowed(
                node, shadow, scopes, parents):
            continue
        module_aliases, from_imports, star_modules = _call_import_bindings(
            node, parents, type_checking_only)
        func_names = _gate_resolve_call_names(
            node, module_aliases, from_imports, star_modules)
        yield node, func_names
def _iter_gate_dangerous_calls(
        tree: ast.AST) -> Iterator[tuple[ast.Call, str]]:
    for node, func_names in _iter_gate_resolved_calls(tree):
        shell_true = any(_shell_keyword_truthy(kw)
                         for kw in node.keywords)
        func_name = next(
            (name for name in func_names
             if name in GATE_UNCONDITIONAL_DANGEROUS_CALLS
             or (name in GATE_SUBPROCESS_SHELL_FAMILY
                 and shell_true)), None)
        if func_name is not None:
            yield node, func_name
def _gate_form_token_lines(call: ast.Call,
                           form: _DangerForm) -> set[int]:
    roots = (call,)
    if form.token == 'http://':
        if call.args:
            roots = (call.args[0],)
        else:
            roots = tuple(
                kw.value for kw in call.keywords if kw.arg == 'url')
            roots += tuple(
                value
                for kw in call.keywords
                if kw.arg is None and isinstance(kw.value, ast.Dict)
                for key, value in zip(kw.value.keys, kw.value.values)
                if isinstance(key, ast.Constant) and key.value == 'url'
            )
    token_regex = re.compile(form.token)
    lines: set[int] = set()
    for root in roots:
        for node in walk_nodes(root):
            text = None
            if isinstance(node, ast.Constant) and isinstance(
                    node.value, (str, bytes)):
                text = (node.value if isinstance(node.value, str)
                        else repr(node.value))
            elif isinstance(node, ast.Name):
                text = node.id
            elif isinstance(node, ast.Attribute):
                text = node.attr
            elif isinstance(node, ast.keyword):
                text = node.arg
            if text and token_regex.search(text):
                lines.add(getattr(node, 'lineno', call.lineno))
    return lines
def _iter_gate_non_code_ast_calls(
        tree: ast.AST, index: dict[str, _DangerForm],
) -> Iterator[tuple[ast.Call, _DangerForm, set[int]]]:
    for call, func_names in _iter_gate_resolved_calls(tree):
        func_name = next(
            (name for name in func_names
             if name in index and index[name].category != 'code_execution'),
            None)
        if func_name is None:
            continue
        form = index[func_name]
        token_lines = ({call.lineno} if not form.token
                       else _gate_form_token_lines(call, form))
        if not token_lines:
            continue
        yield call, form, token_lines
def _ast_danger_display(func_name: str) -> str | None:
    if func_name in GATE_SUBPROCESS_SHELL_FAMILY:
        return _SHELL_TRUE_RULE
    if func_name in {'eval', 'exec', '__import__'}:
        return f'{func_name}()'
    display = _ALIAS_DISPLAY_BY_QUALIFIED.get(func_name)
    if display is not None:
        return display
    if func_name in {
            'subprocess.getoutput', 'subprocess.getstatusoutput'}:
        return f'{func_name}()'
    return None
def _iter_public_ast_dangers(
        tree: ast.AST | None) -> Iterator[tuple[ast.Call, str, str]]:
    if tree is None:
        return
    dangerous = sorted(
        _iter_gate_dangerous_calls(tree),
        key=lambda item: (item[0].lineno, item[0].col_offset))
    for call, func_name in dangerous:
        display = _ast_danger_display(func_name)
        if display is not None:
            yield call, func_name, display
def _gate_check_dangerous_calls(tree: ast.AST, py_file: str,
                           collectors: _GateCollectors) -> None:
    for node, func_name in _iter_gate_dangerous_calls(tree):
        collectors.issues.append(
            f"Security: {os.path.basename(py_file)}:{node.lineno} "
            f"{func_name}() usage"
        )
        collectors.metrics["dangerous_calls"] += 1
def _gate_check_return_annotations(tree: ast.Module, py_file: str,
                              collectors: _GateCollectors) -> None:
    for node, _is_method in collect_api_function_nodes(tree):
        if not node.name.startswith("_") and node.returns is None:
            collectors.metrics[RULE_MISSING_ANNOTATIONS] += 1
            if collectors.metrics[RULE_MISSING_ANNOTATIONS] <= 5:
                collectors.warnings.append(
                    f"Type annotation: {os.path.basename(py_file)}:{node.lineno} "
                    f"{node.name}() missing return type"
                )
def scan_python_quality_file(fpath: str) -> tuple[list, list, dict[str, int]] | None:
    source, tree = parse_py_file(fpath, quiet=True)
    if source is None or tree is None:
        return None
    collectors = _GateCollectors(
        issues=[],
        warnings=[],
        metrics={
            "anti_patterns": 0,
            "bare_excepts": 0,
            RULE_MISSING_ANNOTATIONS: 0,
            "dangerous_calls": 0,
        },
    )
    _gate_check_ast_antipatterns(tree, fpath, collectors)
    _gate_check_dangerous_calls(
        _runtime_security_tree(tree), fpath, collectors)
    _gate_check_return_annotations(tree, fpath, collectors)
    return collectors.issues, collectors.warnings, collectors.metrics

from __future__ import annotations

import ast
import configparser
import json
import logging
import math
import os
import re
from collections.abc import Iterator
from dataclasses import asdict, dataclass, field
from difflib import SequenceMatcher
from pathlib import Path
from typing import Any, NamedTuple, Self
from urllib.parse import urlparse

try:
    import tomllib as _tomllib
except ImportError:  # pragma: no cover - 3.10 环境  # jwsgj:silent-ok 可选依赖降级：3.10 环境无 tomllib，按不可用返回
    _tomllib = None
from jwsgj.build_safe_orchestration import safe_delivery_check
from jwsgj.build_text_document import (
    scan_fence_state,
    strip_fenced_blocks,
)
from jwsgj.build_text_frontmatter import (
    extract_description,
    load_frontmatter,
    parse_frontmatter,
)
from jwsgj.diag_shared_ast_nodes import (
    _is_outer_comprehension_iter,
    build_parent_map,
    is_none_literal,
    is_shell_true_keyword,
    iter_arg_nodes,
    iter_evaluation_scope_chain,
)
from jwsgj.diag_shared_ast_views import (
    tree_nodes,
)
from jwsgj.diag_shared_source_core import (
    byte_col_to_char_col,
    parse_cached,
    read_source_strict,
    read_source_with_fingerprint,
)
from jwsgj.diag_shared_source_scan import (
    comment_only_spans,
    inline_suppressed_at,
    is_masked_offset,
    py_string_token_offsets,
    string_token_body,
)
from jwsgj.diag_types_normalize import strip_bom
from jwsgj.diag_types_vocab import (
    DESC_MAX,
    PARSE_DEGRADE_EXC,
    SKILL_MD_LINE_LIMIT,
    Severity,
)
from jwsgj.log_config import (
    degraded_section,
    log_swallowed,
    mark_section_degraded,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    GENERIC_SCAN_IGNORE_DIRS_LOWER,
    PY_SUFFIXES,
    SCAN_COLLECT_PRUNE_DIRS_LOWER,
    coerce_skill_dir,
    is_runtime_temp_path,
    is_test_file_path,
    is_test_scan_asset,
    prune_scan_dirnames,
)
from jwsgj.shared_cache import (
    SharedCache,
    get_warmed_cache,
    require_warmed,
)

_log = logging.getLogger(__name__)
__all__ = [
    'DANGEROUS_COMMANDS',
    'DOC_ROLE_MANIFEST',
    'DOC_ROLE_NONE',
    'DOC_ROLE_README',
    'DOC_ROLE_SKILL',
    'LEAK_SCAN_SUFFIXES',
    'NETWORK_CALL_TARGETS',
    'P_SEVERITY_MAP',
    'REMOTE_SCRIPT_PATTERNS',
    'SCRIPT_SCAN_SUFFIXES',
    'SECRET_LEAK_VERDICT',
    'SECRET_PATTERNS',
    'TARGET_KIND_NONE',
    'TARGET_KIND_PROJECT',
    'TARGET_KIND_SKILL',
    'SecurityFinding',
    'SecurityFindingDeduplicator',
    'SecurityIssue',
    'SecurityReport',
    'SupplyChainReport',
    'TargetDocument',
    'Verdict',
    'acquire_scan_cache',
    'cached_scan_ast',
    'cached_scan_source',
    'check_dangerous_commands',
    'check_remote_scripts',
    'check_secret_leaks',
    'check_sensitive_paths',
    'check_skill_packaging_quality',
    'check_supply_chain',
    'check_supply_chain_hardening',
    'check_third_party_skill',
    'collect_delivery_issues',
    'count_dangerous_call_risks',
    'deduplicate_security_findings',
    'docstring_rows_from_nodes',
    'file_compiles_strict',
    'format_supply_chain_report',
    'frontmatter_block',
    'is_backup_or_temp_file',
    'is_codetext_fixture_at',
    'is_comment_line',
    'is_placeholder_secret_value',
    'is_test_scan_target',
    'iter_leak_candidate_files',
    'iter_markdown_lines',
    'iter_network_calls_no_timeout',
    'iter_scan_scope_files',
    'iter_secret_hits',
    'join_issue_location',
    'line_no',
    'mask_secret',
    'new_location_issue',
    'non_py_comment_spans',
    'normalize_issue_line',
    'normalize_issue_severity',
    'normalize_issue_suggestion',
    'read_asset_text',
    'read_scan_source_tree',
    'resolve_target_document',
    'split_issue_location',
    'timeout_value_effective',
]
_log.info("skill_audit_rules 已加载: %d 项导出", len(__all__))
def _docstring_row_range(node) -> range | None:
    body = getattr(node, "body", None)
    if not body or not isinstance(body[0], ast.Expr):
        return None
    value = body[0].value
    if not (isinstance(value, ast.Constant) and isinstance(value.value, str)):
        return None
    first = body[0]
    return range(first.lineno, (first.end_lineno or first.lineno) + 1)
def docstring_rows_from_nodes(nodes) -> set:
    rows: set = set()
    for node in nodes:
        if not isinstance(node, (ast.Module, ast.ClassDef,
                                 ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        node_rows = _docstring_row_range(node)
        if node_rows is not None:
            rows.update(node_rows)
    return rows
def is_backup_or_temp_file(path: Path) -> bool:
    return (path.name.startswith('.tmp_')
            or any(s.lower() == '.bak' for s in path.suffixes))
def _rel_project_path(f: Path, root: Path) -> str:
    try:
        return Path(f).relative_to(root).as_posix()
    except ValueError as _e:
        log_swallowed(__name__, _e, context='_rel_project_path:ValueError')
        return os.path.abspath(str(f)).replace('\\', '/')
def iter_scan_scope_files(root: Any, suffixes: frozenset = PY_SUFFIXES):
    root = Path(root)
    accepted = {str(suffix).lower() for suffix in suffixes}
    skip_dirs = (SCAN_COLLECT_PRUNE_DIRS_LOWER
                 if (root / "SKILL.md").is_file()
                 else GENERIC_SCAN_IGNORE_DIRS_LOWER)
    for current, dirnames, filenames in os.walk(root):
        prune_scan_dirnames(dirnames, skip_dirs)
        dirnames.sort()
        for filename in sorted(filenames):
            f = Path(current) / filename
            if not f.is_file():
                continue
            if (f.suffix.lower() not in accepted
                    and f.name.lower() not in accepted):
                continue
            if is_runtime_temp_path(str(f)):
                continue
            yield f
def cached_scan_source(fpath: str, cache) -> str | None:
    if cache is not None:
        try:
            return cache.get_source(fpath)
        except Exception:  # noqa: BLE001
            _log.debug('供应链缓存源码读取失败，回退直读: %s', fpath, exc_info=True)
    return None
def _parse_scan_source(src: str, *, context: str):
    try:
        return parse_cached(src.removeprefix('\ufeff'))
    except PARSE_DEGRADE_EXC as _e:
        log_swallowed(__name__, _e, context=f'{context}:{type(_e).__name__}')
        return None
def cached_scan_ast(fpath: str, src: str, cache):
    if cache is not None:
        try:
            _t = cache.get_ast(fpath)
            if _t is not None:
                return _t
        except Exception:  # noqa: BLE001
            _log.debug('供应链缓存 AST 读取失败，回退解析: %s', fpath, exc_info=True)
    return _parse_scan_source(src, context='cached_scan_ast')
DANGEROUS_COMMANDS = [
    'rm\\s+-rf\\s+/',
    'curl\\s+.*\\|\\s*(?:ba)?sh\\b',
    'wget\\s+.*-O\\s+.*\\|\\s*(?:ba)?sh\\b',
    'chmod\\s+777',
    'chown\\s+-R\\s+root',
    'mkfs\\.',
    'dd\\s+if=',
    '>\\s*/dev/sda',
    'format\\s+[CF]:',
]
REMOTE_SCRIPT_PATTERNS = [
    '(?:curl|wget)\\s+(?:https?://|ftp://)[^\\s|]*\\.sh\\b',
    'pip\\s+install\\s+(?:https?://|git\\+)',
    'npm\\s+install\\s+(?:https?://|git\\+)',
    'source\\s+<(?:curl|wget)',
]
SECRET_PATTERNS = [
    # 前导边界：task-/disk-/risk- 等 <字母>sk-<32位字母数字> 标识符不得被当作密钥
    '(?<![A-Za-z0-9])sk-[a-zA-Z0-9]{32,}',
    '(?:ghp|gho|ghu|ghs|ghr)_[a-zA-Z0-9]{36,}',
    'AKIA[0-9A-Z]{16}',
    '(?:eyJ[a-zA-Z0-9_-]{10,}\\.[a-zA-Z0-9_-]{10,}\\.[a-zA-Z0-9_-]{10,})',
    '(?i)aws_secret_access_key\\s*[=:]\\s*(?:["\\\'][A-Za-z0-9/+=]{40}["\\\']|[A-Za-z0-9/+=]{40}(?![A-Za-z0-9/+=]))',
    'AIza[0-9A-Za-z_\\-]{35}',
    'xox[baprs]-[0-9A-Za-z-]{10,}',
    '-----BEGIN (?:RSA |EC |DSA |OPENSSH )?PRIVATE KEY-----',
    '(?i)(?:secret|password|token|api_key|apikey)\\s*[=:]\\s*(?:["\\\'][A-Za-z0-9+/=]{32,}["\\\']|[A-Za-z0-9+/=]{32,})',
]
_SECRET_PLACEHOLDER_KEYWORDS = frozenset({
    'test', 'example', 'placeholder', 'dummy', 'fake', 'sample',
    'mock', 'your_', 'xxx', 'yyy', 'zzz', 'changeme', 'todo',
    'replace', 'insert', 'demo', '1234567890', 'abcdefgh',
    '0123456789',
})
def is_placeholder_secret_value(value: str) -> bool:
    if not value or len(value) < 8:
        return True
    val_lower = value.lower()
    for kw in _SECRET_PLACEHOLDER_KEYWORDS:
        if re.search(rf'(?<![a-z]){re.escape(kw)}', val_lower):
            return True
    return val_lower.strip('0') == ''
P_SEVERITY_MAP = {'P0': Severity.CRITICAL, 'P1': Severity.HIGH,
              'P2': Severity.MEDIUM, 'P3': Severity.LOW}
def _first_truthy(*values, default=''):
    for value in values:
        if value:
            return value
    return default
def mask_secret(value: str) -> str:
    if len(value) <= 8:
        return '****'
    return value[:4] + '****' + value[-4:]
_CODETEXT_ASSIGN_PAT = re.compile(r"[:=]\s*['\"]")
_CODETEXT_LINE_ESCAPE_PAT = re.compile(r"\\n")
def _is_codetext_fixture_token(raw: str,
                               is_text_segment: bool) -> bool:
    body = string_token_body(raw, is_text_segment=is_text_segment)
    if _CODETEXT_ASSIGN_PAT.search(body):
        return True
    return bool(_CODETEXT_LINE_ESCAPE_PAT.search(body)
                and ("=" in body or "(" in body))
def is_codetext_fixture_at(pos: int, secret_toks) -> bool:
    if not secret_toks:
        return False
    return any(
        s <= pos < e
        and _is_codetext_fixture_token(raw, is_text_segment=is_text)
        for s, e, raw, is_text in secret_toks)
def normalize_issue_line(value) -> int:
    if isinstance(value, int) and not isinstance(value, bool) and value > 0:
        return value
    return 0
_P_TO_SEVERITY: dict[str, Severity] = dict(P_SEVERITY_MAP)
_P_TO_SEVERITY['P4'] = Severity.INFO
_SEVERITY_BY_NAME: dict[str, Severity] = {
    _sev.name: _sev for _sev in Severity}
def normalize_issue_severity(value) -> Severity:
    if isinstance(value, Severity):
        return value
    if isinstance(value, str):
        level = value.strip().upper()
        if level in _SEVERITY_BY_NAME:
            return _SEVERITY_BY_NAME[level]
        if level in _P_TO_SEVERITY:
            return _P_TO_SEVERITY[level]
    return Severity.MEDIUM
def normalize_issue_suggestion(value) -> str:
    return value if isinstance(value, str) else ''
def join_issue_location(file: str, line: int) -> str:
    if (isinstance(line, int) and not isinstance(line, bool)
            and line > 0):
        return f'{file}:{line}'
    return file
def split_issue_location(loc: str) -> tuple[str, int]:
    m = re.search(r':(\d+)$', loc)
    if m:
        return loc[:m.start()], int(m.group(1))
    return loc, 0
def acquire_scan_cache(skill_dir, cache=None, *,
                       who: str = "安全审计") -> SharedCache:
    if cache is None:
        return get_warmed_cache(str(skill_dir))
    return require_warmed(cache, who)
def read_scan_source_tree(py_file: Path, cache) -> tuple[str, object | None]:
    if cache is not None:
        try:
            _src = cache.get_source(str(py_file))
        except Exception:  # noqa: BLE001
            _log.debug('安全审计缓存源码读取失败，回退直读: %s', py_file, exc_info=True)
            _src = None
        if _src is not None:
            try:
                return _src, cache.get_ast(str(py_file))
            except Exception:  # noqa: BLE001
                _log.debug('缓存 AST 读取失败，树回退 None: %s', py_file, exc_info=True)
                return _src, None
    _text = read_source_with_fingerprint(str(py_file))[0]
    if _text is None:
        raise OSError(f'源码不可读: {py_file}')
    return _text, None
_DEFAULT_SEVERITY_LABEL = 'P2'
_SEVERITY_RANK = {'P0': 0, 'P1': 1, 'P2': 2, 'P3': 3, 'P4': 4}
_SEVERITY_NAME_RANK: dict[str, int] = {
    _sev.name: _SEVERITY_RANK[_p]
    for _p, _sev in _P_TO_SEVERITY.items()}
@dataclass
class SecurityFinding:
    rule_id: str = ''
    severity: str = _DEFAULT_SEVERITY_LABEL
    file: str = ''
    line: int = 0
    message: str = ''
    suggestion: str = ''
    code_snippet: str = ''
    def __post_init__(self) -> None:
        for name in ('rule_id', 'file', 'message', 'suggestion',
                     'code_snippet'):
            if not isinstance(getattr(self, name), str):
                setattr(self, name, '')
        if not isinstance(self.severity, str) or not self.severity:
            self.severity = _DEFAULT_SEVERITY_LABEL
        self.line = normalize_issue_line(self.line)
    @property
    def severity_rank(self) -> int:
        level = self.severity.strip().upper()
        if level in _SEVERITY_RANK:
            return _SEVERITY_RANK[level]
        return _SEVERITY_NAME_RANK.get(level, 5)
class SecurityFindingDeduplicator:
    SIMILARITY_THRESHOLD = 0.75
    def __init__(self) -> None:
        self._findings: list[SecurityFinding] = []
        self._dedup_stats: dict = {'total': 0, 'duplicates': 0, 'retained': 0}
    @staticmethod
    def _coerce_finding(f) -> SecurityFinding | None:
        if isinstance(f, SecurityFinding):
            return f
        if not isinstance(f, dict):
            return None
        return SecurityFinding(
            rule_id=_first_truthy(f.get('rule_id')),
            severity=_first_truthy(
                f.get('severity'), default=_DEFAULT_SEVERITY_LABEL),
            file=_first_truthy(f.get('file'), f.get('filepath')),
            line=normalize_issue_line(f.get('line')),
            message=_first_truthy(f.get('message'), f.get('title')),
            suggestion=_first_truthy(f.get('suggestion')),
            code_snippet=_first_truthy(f.get('code_snippet')))
    def add_findings(self: Self, findings: list) -> Self:
        for f in findings:
            _c = self._coerce_finding(f)
            if _c is not None:
                self._findings.append(_c)
        return self
    def deduplicate(self: Self) -> list[SecurityFinding]:
        self._dedup_stats['total'] = len(self._findings)
        if not self._findings:
            self._dedup_stats['duplicates'] = 0
            self._dedup_stats['retained'] = 0
            return []
        groups: dict[tuple, list[int]] = {}
        for i, f in enumerate(self._findings):
            groups.setdefault((f.rule_id, f.file, f.line), []).append(i)
        retained_indices = set()
        duplicates_count = 0
        for indices in groups.values():
            if len(indices) == 1:
                retained_indices.add(indices[0])
                continue
            _retained, _dup_n = self._dedup_group(indices)
            retained_indices.update(_retained)
            duplicates_count += _dup_n
        result = [self._findings[i] for i in sorted(retained_indices)]
        self._dedup_stats['duplicates'] = duplicates_count
        self._dedup_stats['retained'] = len(result)
        return result
    def _similar(self: Self, msg_a: str, msg_b: str) -> bool:
        return SequenceMatcher(None, msg_a, msg_b).ratio() >= self.SIMILARITY_THRESHOLD
    def _absorb_cluster(self: Self, indices: list[int], pos: int,
                        visited: set) -> tuple[int, int]:
        best_idx = indices[pos]
        visited.add(best_idx)
        best_rank = self._findings[best_idx].severity_rank
        cluster_msg = self._findings[best_idx].message
        dup_n = 0
        for other in indices[pos + 1:]:
            if other in visited or not self._similar(
                    cluster_msg, self._findings[other].message):
                continue
            visited.add(other)
            dup_n += 1
            other_rank = self._findings[other].severity_rank
            if other_rank < best_rank:
                best_idx, best_rank = other, other_rank
        return best_idx, dup_n
    def _dedup_group(self: Self, indices: list[int]) -> tuple[list[int], int]:
        visited: set = set()
        retained: list[int] = []
        dup_n = 0
        for pos in range(len(indices)):
            if indices[pos] in visited:
                continue
            best_idx, cluster_dup = self._absorb_cluster(indices, pos, visited)
            retained.append(best_idx)
            dup_n += cluster_dup
        return retained, dup_n
    def deduplicate_as_dicts(self: Self) -> list[dict]:
        return [asdict(f) for f in self.deduplicate()]
    @property
    def stats(self: Self) -> dict:
        return dict(self._dedup_stats)
def deduplicate_security_findings(findings: list) -> list[dict]:
    dedup = SecurityFindingDeduplicator()
    dedup.add_findings(findings)
    return dedup.deduplicate_as_dicts()
@dataclass
class SecurityIssue:
    severity: Severity
    category: str
    description: str
    location: str
    recommendation: str
@dataclass
class SecurityReport:
    skill_name: str = ''
    skill_path: str = ''
    issues: list[SecurityIssue] = field(default_factory=list)
    risk_level: str = 'low'
    passed: bool = True
_DIM_PACKAGING = "skill_packaging"
_DIM_SUPPLY_CHAIN = "supply_chain"
def _finding(rule_id: str, severity: str, filepath, line: int,
             message: str, suggestion: str, dimension: str) -> dict:
    return {"rule_id": rule_id, "severity": severity, "dimension": dimension,
            "file": str(filepath), "line": line,
            "message": message, "suggestion": suggestion}
def _summarize_findings(findings: list) -> dict:
    by_rule: dict = {}
    for f in findings:
        by_rule[f["rule_id"]] = by_rule.get(f["rule_id"], 0) + 1
    return {"total": len(findings), "by_rule": by_rule}
def _error_envelope(message: str) -> dict:
    return {"status": "error", "data": {"findings": []}, "message": message}
def _resolve_public_dir(skill_dir, not_dir_label: str) -> tuple[Path, dict | None]:
    normalized = coerce_skill_dir(skill_dir)
    if not normalized:
        return Path(), _error_envelope(f"目录不存在: {skill_dir}")
    sp = Path(normalized)
    if not sp.exists():
        return sp, _error_envelope(f"目录不存在: {normalized}")
    if not sp.is_dir():
        return sp, _error_envelope(f"{not_dir_label}: {normalized}")
    return sp, None
def _ok_envelope(findings: list, label: str) -> dict:
    summary = _summarize_findings(findings)
    by_rule = ', '.join(
        f'{k}x{v}' for k, v in sorted(summary["by_rule"].items())) or '无'
    return {
        "status": "ok",
        "data": {"findings": findings, "summary": summary},
        "message": f"{label}: {summary['total']} 项发现 ({by_rule})",
    }
def _record_scan_error(scan_errors: list[str] | None, message: str) -> None:
    if scan_errors is not None:
        scan_errors.append(message)
def _scan_envelope(findings: list, label: str,
                   scan_errors: list[str]) -> dict:
    result = _ok_envelope(findings, label)
    if not scan_errors:
        return result
    detail = '; '.join(dict.fromkeys(scan_errors))
    result['status'] = 'error'
    result['data']['scan_errors'] = list(scan_errors)
    result['error'] = detail
    result['message'] = f'{label}: 扫描不完整: {detail}'
    return result
_SC07_GOTCHA_PAT = re.compile(
    r'^#{2,6}[^\n]*(?:Gotchas|陷阱|踩坑|常见错误|⚠️|警告)',
    re.IGNORECASE | re.MULTILINE)
def _sc07_doc_gotchas(content: str, filepath: str) -> list:
    issues = []
    if len(content.splitlines()) > 100 and not _SC07_GOTCHA_PAT.search(
            strip_fenced_blocks(content)):
        issues.append(_finding(
            "SC-07", "P1", filepath, 1,
            ("SC-07: 大型 SKILL.md 缺少 Gotchas(陷阱)章节."
             "Gotchas 是技能中价值最高的内容,可一次性避免反复踩坑."),
            "添加 ## Gotchas 章节, 列出 Agent 容易犯的具体错误与规避方法", dimension=_DIM_PACKAGING))
    return issues
def _sc02_skill_md_size(content: str, filepath: str) -> list:
    issues = []
    total_lines = len(content.splitlines())
    if total_lines > SKILL_MD_LINE_LIMIT:
        issues.append(_finding(
            "SC-02", "P1", filepath, 1,
            (f"SC-02: SKILL.md 主体{total_lines}行,超过渐进式披露的指令层限制"
             f"({SKILL_MD_LINE_LIMIT}行/5000 token).长内容应移至 references/ 目录按需加载."),
            "将详细内容(API 详细说明/示例代码/高级用法)移至 references/ 按需加载", dimension=_DIM_PACKAGING))
    return issues
def _is_frontmatter_delim_line(line: str) -> bool:
    return line.rstrip(' \t\r') == '---'
def frontmatter_block(content: str) -> str | None:
    content = strip_bom(content)
    lines = content.split('\n')
    if not _is_frontmatter_delim_line(lines[0]):
        return None
    for idx in range(1, len(lines)):
        if _is_frontmatter_delim_line(lines[idx]):
            block = '\n' + '\n'.join(lines[1:idx])
            return block + '\n' if idx > 1 else block
    return None
def _quoted_scalar_end(value: str, quote: str) -> int | None:
    i = 1
    while i < len(value):
        ch = value[i]
        if quote == '"' and ch == '\\':
            i += 2
            continue
        if ch == quote:
            if quote == "'" and i + 1 < len(value) and value[i + 1] == "'":
                i += 2
                continue
            return i
        i += 1
    return None
def _frontmatter_scalar_value(raw: str) -> str:
    value = raw.strip()
    quote = value[:1]
    if quote in ("'", '"'):
        end = _quoted_scalar_end(value, quote)
        inner = value[1:end] if end is not None else value[1:]
        if quote == '"':
            try:
                return json.loads('"' + inner + '"')
            except (TypeError, ValueError) as exc:
                log_swallowed(
                    __name__, exc,
                    context='_frontmatter_scalar_value:'
                            f'{type(exc).__name__}')
                return inner
        return inner.replace("''", "'")
    comment = re.search(r'\s#', value)
    if comment:
        value = value[:comment.start()].rstrip()
    return value
def _frontmatter_field_match(block: str, field: str):
    return re.search(rf'^{re.escape(field)}:[ \t]*(.*)$', block, re.MULTILINE)
def _sc03_boundary_issue(content: str, filepath: str) -> list:
    if not _is_frontmatter_delim_line(
            strip_bom(content).split('\n', 1)[0]):
        return [_finding(
            "SC-03", "P0", filepath, 1,
            ("SC-03: SKILL.md 缺少 frontmatter 起始 --- 分隔符,"
             "manage_skills upload 报 missing frontmatter 错误."),
            "在文件首行添加 --- 分隔符", dimension=_DIM_PACKAGING)]
    return [_finding(
        "SC-03", "P0", filepath, 1,
        "SC-03: SKILL.md frontmatter 缺少闭合 --- 分隔符.",
        "在 frontmatter 结束处添加 --- 分隔符", dimension=_DIM_PACKAGING)]
def _sc03_metadata_issue(frontmatter: str, filepath: str) -> list:
    metadata_match = re.search(r"^metadata:[ \t]*", frontmatter, re.MULTILINE)
    if not metadata_match:
        return []
    metadata_raw = frontmatter[metadata_match.end():]
    try:
        metadata_value, metadata_end = _JSON_DECODER.raw_decode(metadata_raw)
    except (ValueError, RecursionError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_sc03_metadata_issue:{type(_e).__name__}')
    else:
        same_line_tail = metadata_raw[metadata_end:].split("\n", 1)[0]
        tail_is_comment = re.match(r"^[ \t]+#", same_line_tail) is not None
        if (isinstance(metadata_value, dict)
                and (not same_line_tail.strip() or tail_is_comment)):
            return []
    return [_finding(
        "SC-03", "P0", filepath,
        line_no(frontmatter, metadata_match.start()),
        (f"SC-03: frontmatter metadata 字段不是合法 JSON inline."
         f"原始: {metadata_raw[:100]}"),
        ("metadata 后用 JSON inline 格式: "
         "metadata: {\"k\": \"v\"}, "
         "不用嵌套 YAML 列表/未双引号字符串"), dimension=_DIM_PACKAGING)]
def _sc03_frontmatter_format(content: str, filepath: str) -> list:
    frontmatter = frontmatter_block(content)
    if frontmatter is None:
        return _sc03_boundary_issue(content, filepath)
    return _sc03_metadata_issue(frontmatter, filepath)
def _sc04_name_field(content: str, filepath: str) -> list:
    issues = []
    _fm = frontmatter_block(content)
    if _fm is None:
        return issues
    m = _frontmatter_field_match(_fm, 'name')
    if not m:
        return issues
    name_val = _frontmatter_scalar_value(m.group(1))
    if not name_val:
        return issues
    row_no = line_no(_fm, m.start())
    if " " in name_val:
        issues.append(_finding(
            "SC-04", "P1", filepath, row_no,
            (f"SC-04: SKILL.md name 字段 '{name_val}' 包含空格."
             "manage_skills 报 SkillInvalidName."),
            "用连字符替代空格, 例如 my-skill", dimension=_DIM_PACKAGING))
    if re.search(r"[\u4e00-\u9fff]", name_val):
        issues.append(_finding(
            "SC-04", "P1", filepath, row_no,
            (f"SC-04: SKILL.md name 字段 '{name_val}' 含中文."
             "manage_skills 的 names 参数不支持中文, 须用纯 ASCII 别名."),
            "使用纯 ASCII 名称, 如 my-skill", dimension=_DIM_PACKAGING))
    return issues
_JSON_DECODER = json.JSONDecoder()
_BLOCK_SCALAR_MARKERS = ("|", "|-", "|+", ">", ">-", ">+")
def _block_scalar_indent(line: str) -> int | None:
    if not line.strip():
        return None
    return len(line) - len(line.lstrip())
def _trim_trailing_blank(lines: list[str]) -> list[str]:
    for end in range(len(lines), 0, -1):
        if lines[end - 1]:
            return lines[:end]
    return []
def _collect_block_scalar(tail: str) -> str:
    content = _trim_trailing_blank(_block_scalar_lines(tail))
    return "\n".join(ln.strip() for ln in content if ln.strip())
def _block_scalar_lines(tail: str) -> list[str]:
    lines = tail.split("\n")
    start = _first_content_index(lines)
    if start is None:
        return []
    base_indent = _block_scalar_indent(lines[start])
    if base_indent == 0:
        return []
    block: list[str] = []
    for ln in lines[start:]:
        indent = _block_scalar_indent(ln)
        if indent is None:
            block.append("")
            continue
        if indent < base_indent:
            break
        block.append(ln)
    return block
def _first_content_index(lines: list[str]) -> int | None:
    for idx, line in enumerate(lines):
        if line.strip():
            return idx
    return None
def _parse_frontmatter_description(content: str) -> tuple[str, int]:
    m = _frontmatter_field_match(content, 'description')
    if not m:
        return "", 0
    row_no = line_no(content, m.start())
    val = _frontmatter_scalar_value(m.group(1))
    if val in _BLOCK_SCALAR_MARKERS:
        val = _collect_block_scalar(content[m.end():])
    return val, row_no
def _sc05_description_length(content: str, filepath: str) -> list:
    issues = []
    _fm = frontmatter_block(content)
    if _fm is None:
        return issues
    desc, row_no = _parse_frontmatter_description(_fm)
    if not desc:
        return issues
    if len(desc) < 30:
        issues.append(_finding(
            "SC-05", "P1", filepath, row_no,
            f"SC-05: SKILL.md description 长度{len(desc)}字符 < 30 字符,信息量不足.",
            "description 应说明:(1)技能做什么 (2)何时触发 (3)使用场景. "
            "简短但具体的描述有助于 Agent 准确判断是否触发.", dimension=_DIM_PACKAGING))
    if len(desc) > DESC_MAX:
        issues.append(_finding(
            "SC-05", "P2", filepath, row_no,
            (f"SC-05: SKILL.md description 长度{len(desc)}字符 > {DESC_MAX} 字符,超出"
             "可发现性引擎硬上限(DESC_MAX),影响多技能同时加载的上下文效率."),
            f"精简 description 至 {DESC_MAX} 字符以内, 详细内容放正文", dimension=_DIM_PACKAGING))
    return issues
def _skill_md_findings(
        sp: Path, scan_errors: list[str] | None = None) -> list[dict]:
    skill_md = sp / "SKILL.md"
    if not skill_md.is_file():
        return []
    try:
        content = read_asset_text(skill_md)
    except OSError as e:
        _log.warning("SC-02~SC-07 读取失败 %s: %s", skill_md, e)
        mark_section_degraded('技能包装文档读取')
        _record_scan_error(scan_errors, f'SKILL.md 读取失败: {e}')
        return []
    return [
        *_sc02_skill_md_size(content, "SKILL.md"),
        *_sc03_frontmatter_format(content, "SKILL.md"),
        *_sc04_name_field(content, "SKILL.md"),
        *_sc05_description_length(content, "SKILL.md"),
        *_sc07_doc_gotchas(content, "SKILL.md"),
    ]
def check_skill_packaging_quality(skill_dir: str) -> dict:
    sp, err = _resolve_public_dir(skill_dir, "目标不是目录")
    if err is not None:
        return err
    scan_errors: list[str] = []
    findings: list = _skill_md_findings(sp, scan_errors)
    return _scan_envelope(findings, "技能包装质量检测", scan_errors)
_OFFICIAL_PYPI_HOSTS = ("pypi.org", "pypi.python.org", "files.pythonhosted.org")
def _host_is_official(url: str) -> bool:
    candidate = url if "://" in url else "//" + url
    host = urlparse(candidate).hostname or ""
    if not host:
        return False
    return any(host == o or host.endswith("." + o)
               for o in _OFFICIAL_PYPI_HOSTS)
_PIP_BIN = r'pip(?:3(?:\.\d+)?)?'
_PIP_INSTALL_CMD_PAT = re.compile(  # jwsgj:suppress SE-30 — 模式常量已实测压测(200/1000/4000字符)最坏<0.2ms，无灾难性回溯
    _PIP_BIN + r'\s+install\s+'
    r'(?:'
    r'--(?:index-url|extra-index-url|find-links|trusted-host|'
    r'editable|requirement|constraint|target|prefix|src)\b'
    r'(?:\s*=\s*|\s+)(?:"[^"]*"|\'[^\']*\'|\S+)(?:\s+|$)'
    r'|(?-i:-(?:i|e|r|c|t|f))(?:\s*=\s*|\s*)(?:"[^"]*"|\'[^\']*\'|\S+)(?:\s+|$)'
    r'|(?-i:-(?!(?:i|e|r|c|t|f)(?:\s|=|$))[A-Za-z][\w-]*(?:=\S+)?\s+)'
    r'|--(?!(?:index-url|extra-index-url|find-links|trusted-host|editable|'
    r'requirement|constraint|target|prefix|src)\b)[A-Za-z][\w-]*(?:=\S+)?\s+'
    r')*'
    r'(?!-)(\S+)', re.IGNORECASE)
_PIP_INSTALL_PREFIX_PAT = re.compile(
    _PIP_BIN + r'\s+install\b(?=\s)', re.IGNORECASE)
_PIP_INSTALL_OPERAND_PAT = re.compile(
    _PIP_BIN + r'\s+install\s+(\S+)(?:\s+(\S+))?', re.IGNORECASE)
_PIP_INDEX_URL_PAT = re.compile(
    _PIP_BIN + r'\s+install\s+(?:(?!\n).)*?--(?:index-url|extra-index-url)(?:\s*=\s*|\s+)(\S+)',
    re.IGNORECASE | re.DOTALL)
_PIP_INDEX_URL_SHORT_PAT = re.compile(
    _PIP_BIN + r'\s+install\s+(?:(?!\n).)*?(?<=\s)(?-i:-i)(?:\s*=\s*|\s+|)'
    r'((?:https?|ftp)://\S+|(?:[A-Za-z0-9-]+\.)+[A-Za-z]{2,}(?:[/?#:]\S*)?)',
    re.IGNORECASE | re.DOTALL)
_PIP_CONF_INDEX_PAT = re.compile(
    r'^[ \t]*(?:index-url|extra-index-url)[ \t]*=[ \t]*(\S+)',
    re.IGNORECASE | re.MULTILINE)
_PIP_TRUSTED_HOST_PAT = re.compile(
    r'--trusted-host(?:\s*=\s*|\s+)(\S+)', re.IGNORECASE)
_PIP_CONF_TRUSTED_HOST_PAT = re.compile(
    r'^[ \t]*trusted-host[ \t]*=[ \t]*(\S+)',
    re.IGNORECASE | re.MULTILINE)
_SUBPROCESS_METHODS = frozenset(("run", "call", "Popen", "check_call", "check_output",
                                 "getoutput", "getstatusoutput"))
_OS_EXEC_NAMES = frozenset({"system", "popen"})
_EXEC_SINK_TARGETS: frozenset = frozenset(
    {f'subprocess.{name}' for name in _SUBPROCESS_METHODS}
    | {f'os.{name}' for name in _OS_EXEC_NAMES}
    | {'builtins.eval', 'builtins.exec'})
_EXEC_SINK_ATTRS: frozenset = frozenset(
    {*_SUBPROCESS_METHODS, *_OS_EXEC_NAMES, 'eval', 'exec'})
def _constant_text(value) -> str | None:
    if isinstance(value, ast.Constant) and isinstance(value.value, str):
        return value.value
    if isinstance(value, ast.JoinedStr):
        return "".join(v.value for v in value.values
                       if isinstance(v, ast.Constant) and isinstance(v.value, str))
    if isinstance(value, (ast.List, ast.Tuple)):
        parts = [_constant_text(element) for element in value.elts]
        return " ".join("" if part is None else part for part in parts)
    if isinstance(value, ast.BinOp):
        if isinstance(value.op, ast.Add):
            left = _constant_text(value.left)
            right = _constant_text(value.right)
            if left is None or right is None:
                return right if left is None else left
            return left + right
        if isinstance(value.op, ast.Mod):
            return _constant_text(value.left)
    return None
_EXEC_COMMAND_KEYWORDS = ('args', 'command', 'source')
def _exec_command_arg(node: ast.Call) -> ast.expr | None:
    if node.args:
        return node.args[0]
    for kw in node.keywords:
        if kw.arg in _EXEC_COMMAND_KEYWORDS:
            return kw.value
    return None
def _iter_expression_values(value, call, parents, resolving):
    if isinstance(value, ast.IfExp):
        yield from _iter_expression_values(
            value.body, call, parents, resolving)
        yield from _iter_expression_values(
            value.orelse, call, parents, resolving)
        return
    if isinstance(value, ast.Name) and parents is not None:
        if value.id in resolving:
            return
        values = _literal_binding_values(call, parents, value.id)
        if values:
            resolving = resolving | {value.id}
            for candidate in values:
                yield from _iter_expression_values(
                    candidate, call, parents, resolving)
            return
    yield value
def _constant_texts(value, call, parents) -> Iterator[str]:
    for candidate in _iter_expression_values(
            value, call, parents, frozenset()):
        text = _constant_text(candidate)
        if text:
            yield text
def _exec_command_texts(call: _ExecutionCall) -> Iterator[str]:
    node = call.node
    arg = _exec_command_arg(node)
    if arg is None:
        return
    texts = list(_constant_texts(arg, call.node, call.parents))
    yield from dict.fromkeys(texts)
def _iter_executed_pattern_matches(tree, patterns, flags=0):
    calls = _execution_call_contexts(tree, tree_nodes(tree))
    seen_texts: set[tuple[int, str]] = set()
    for call in calls:
        for text in _exec_command_texts(call):
            key = (id(call.node), text)
            if key in seen_texts:
                continue
            seen_texts.add(key)
            for pattern in patterns:
                for match in re.finditer(pattern, text, flags):
                    yield pattern, call, match
def _sc06_executed_texts(nodes, tree, call_contexts) -> dict[str, int]:
    executed: dict[str, int] = {}
    calls = _resolve_execution_calls(tree, nodes, call_contexts)
    for call in calls:
        for text in _exec_command_texts(call):
            executed.setdefault(text, call.node.lineno)
    return executed
def _py_sc06_context(source: str, tree, nodes, call_contexts):
    toks = py_string_token_offsets(source)
    if toks is None:
        return None
    doc_rows = docstring_rows_from_nodes(nodes)
    executed = _sc06_executed_texts(
        nodes, tree, call_contexts=call_contexts)
    return {"tokens": toks, "doc_rows": doc_rows, "executed": executed}
def _token_span_at(toks, offset):
    for span in toks:
        if span[0] <= offset < span[1]:
            return span
    return None
def _texts_related(body: str, executed: str) -> bool:
    return (executed == body
            or (len(executed) >= 12 and executed in body)
            or (len(body) >= 12 and body in executed))
def _sc06_is_inert_string(source, m, toks, doc_rows, executed) -> bool:
    span = _token_span_at(toks, m.start())
    if span is None:
        return False
    if source.count("\n", 0, m.start()) + 1 in doc_rows:
        # 文档字符串不会作为命令执行；命中其中的 pip 配置只是文档示例。
        return True
    body = string_token_body(span[2], is_text_segment=span[3])
    return not any(_texts_related(body, ev) for ev in executed)
_SC06_SOURCE_PATTERNS = (
    (_PIP_INDEX_URL_PAT, "pip install使用非官方源", True),
    (_PIP_INDEX_URL_SHORT_PAT, "pip install使用非官方源", True),
    (_PIP_CONF_INDEX_PAT, "pip配置使用非官方源", True),
    (_PIP_TRUSTED_HOST_PAT, "pip使用--trusted-host", False),
)
def _sc06_issue(kind: str, url: str, filepath: str, line: int) -> dict:
    return _finding(
        "SC-06", "P1", filepath, line, f"{kind}: {url}",
        "使用官方源 https://pypi.org/simple；避免 --trusted-host，用 CA 证书验证", dimension=_DIM_SUPPLY_CHAIN)
def _sc06_scan_source(source: str, filepath: str, comment_spans, toks,
                     doc_rows, executed) -> tuple[list, set]:
    issues: list = []
    source_hits: set[tuple[str, str]] = set()
    for pat, kind, official_host_allowed in _SC06_SOURCE_PATTERNS:
        for m in pat.finditer(source):
            if is_masked_offset(comment_spans, m.start()):
                continue
            url = m.group(1).strip("\"'")
            if not url or (official_host_allowed and _host_is_official(url)):
                continue
            if (toks is not None
                    and _sc06_is_inert_string(
                        source, m, toks, doc_rows, executed)):
                _log.info(
                    "[SUPPRESSED-FIXTURE] SC-06 夹具抑制(留CV复核): "
                    "file=%s kind=%s url=%s", filepath, kind, url[:60])
                continue
            match_line = line_no(source, m.start())
            if match_line not in doc_rows:
                source_hits.add((kind, url))
            issues.append(_sc06_issue(
                kind, url, filepath, match_line))
    return issues, source_hits
def _sc06_scan_executed(filepath: str, executed,
                       source_hits: set) -> list:
    issues: list = []
    for text, exec_line in executed.items():
        for pat, kind, official_host_allowed in _SC06_SOURCE_PATTERNS:
            for m in pat.finditer(text):
                url = m.group(1).strip("\"'")
                if not url or (official_host_allowed and _host_is_official(url)):
                    continue
                if (kind, url) in source_hits:
                    continue
                issues.append(_sc06_issue(kind, url, filepath, exec_line))
    return issues
def _sc06_non_official_index(source: str, filepath: str, context) -> list:
    _ctx = context or {}
    _toks = _ctx.get("tokens")
    _doc_rows = _ctx.get("doc_rows") or set()
    _executed = _ctx.get("executed") or {}
    issues, source_hits = _sc06_scan_source(
        source, filepath, _comment_span_offsets(source), _toks,
        _doc_rows, _executed)
    issues.extend(_sc06_scan_executed(filepath, _executed, source_hits))
    return issues
_PIP_CONFIG_NAMES = frozenset({'pip.conf', 'pip.ini'})
_SC06_PIP_CONFIG_PATTERNS = (
    (_PIP_CONF_INDEX_PAT, 'pip配置使用非官方源', True),
    (_PIP_CONF_TRUSTED_HOST_PAT, 'pip使用--trusted-host', False),
)
def _sc06_pip_config_issues(
        sp: Path, scan_errors: list[str] | None = None) -> list:
    issues: list = []
    for cfg in iter_scan_scope_files(sp, frozenset({'.conf', '.ini'})):
        if cfg.name.lower() not in _PIP_CONFIG_NAMES:
            continue
        rel = _rel_project_path(cfg, sp)
        if is_test_scan_target(cfg, sp, rel):
            continue
        try:
            content = read_asset_text(cfg)
        except (OSError, UnicodeDecodeError) as _e:
            _log.warning('SC-06 pip 配置读取失败 %s: %s', cfg, _e)
            mark_section_degraded('供应链加固pip配置读取')
            _record_scan_error(scan_errors, f'{cfg.name} 读取失败: {_e}')
            continue
        _mask = non_py_comment_spans(content)
        for pat, kind, official_host_allowed in _SC06_PIP_CONFIG_PATTERNS:
            for m in pat.finditer(content):
                if is_masked_offset(_mask, m.start()):
                    continue
                url = m.group(1).strip("\"'")
                if not url or (official_host_allowed and _host_is_official(url)):
                    continue
                issues.append(_sc06_issue(
                    kind, url, rel, line_no(content, m.start())))
    return issues
_SC01_BLOCKING_METHODS = ("run", "call", "check_call", "check_output")
_SC01_SINK_TARGETS = frozenset(
    f'subprocess.{name}' for name in _SC01_BLOCKING_METHODS)
_OS_EXEC_TARGETS = frozenset(f'os.{name}' for name in _OS_EXEC_NAMES)
_BUILTIN_EXEC_NAMES = frozenset({'eval', 'exec'})
def timeout_value_effective(node: ast.AST) -> bool:
    if is_none_literal(node):
        return False
    literal = isinstance(node, ast.Constant)
    value = node.value if literal else None
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
        operand = node.operand
        if isinstance(operand, ast.Constant):
            literal = True
            if isinstance(operand.value, bool):
                return False
            if isinstance(operand.value, (int, float)):
                value = (-operand.value if isinstance(node.op, ast.USub)
                         else operand.value)
    if isinstance(value, bool):
        return False
    if isinstance(value, int):
        return value > 0
    if isinstance(value, float):
        return math.isfinite(value) and value > 0
    return not literal
def _timeout_value_effective_at_call(value, call, parents) -> bool:
    return all(
        timeout_value_effective(candidate)
        for candidate in _iter_expression_values(
            value, call, parents, frozenset()))
@dataclass(frozen=True)
class _ExecutionCall:
    node: ast.Call
    dotted: str
    parents: dict
    @property
    def short(self) -> str:
        return self.dotted.rsplit('.', 1)[-1]
def _execution_call_contexts(tree, nodes) -> list[_ExecutionCall]:
    resolved = nodes
    parents = build_parent_map(tree)
    contexts: list[_ExecutionCall] = []
    for call, dotted in _iter_resolved_target_calls(
            tree, _EXEC_SINK_TARGETS, _EXEC_SINK_ATTRS,
            builtin_names=_BUILTIN_EXEC_NAMES, nodes=resolved, parents=parents):
        if dotted not in _EXEC_SINK_TARGETS:
            continue
        contexts.append(_ExecutionCall(
            node=call, dotted=dotted, parents=parents))
    return contexts
def _resolve_execution_calls(tree, nodes, call_contexts):
    return (_execution_call_contexts(tree, nodes)
            if call_contexts is None else call_contexts)
def _sc01_subprocess_no_timeout(tree, filepath: str, nodes,
                                call_contexts) -> list:
    issues = []
    calls = _resolve_execution_calls(tree, nodes, call_contexts)
    for call in calls:
        if call.dotted not in _SC01_SINK_TARGETS:
            continue
        if any(kw.arg == "timeout" and _timeout_value_effective_at_call(
                kw.value, call.node, call.parents)
               for kw in call.node.keywords):
            continue
        issues.append(_finding(
            "SC-01", "P2", filepath, call.node.lineno,
            f"{call.short}() 未指定 timeout 参数，子进程卡死将无限阻塞（挂起风险）",
            "添加超时参数并在 TimeoutExpired 分支中降级: subprocess.run(cmd, timeout=30)", dimension=_DIM_SUPPLY_CHAIN))
    return issues
def _sc08_static_text(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant):
        return isinstance(node.value, str)
    if isinstance(node, ast.JoinedStr):
        return all(isinstance(v, ast.Constant) and isinstance(v.value, str)
                   for v in node.values)
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Mod)):
        right = node.right
        if isinstance(right, ast.Tuple):
            return (_sc08_static_text(node.left)
                    and all(_sc08_static_text(e) for e in right.elts))
        return _sc08_static_text(node.left) and _sc08_static_text(right)
    return False
def _sc08_first_arg_dynamic(arg) -> bool:
    if isinstance(arg, (ast.List, ast.Tuple)):
        return any(_sc08_first_arg_dynamic(e) for e in arg.elts)
    if _sc08_static_text(arg):
        return False
    if isinstance(arg, ast.IfExp):
        return (_sc08_first_arg_dynamic(arg.body)
                or _sc08_first_arg_dynamic(arg.orelse))
    if isinstance(arg, (ast.NamedExpr, ast.Starred)):
        return _sc08_first_arg_dynamic(arg.value)
    if isinstance(arg, (ast.Await, ast.Yield, ast.YieldFrom)):
        return True
    return isinstance(
        arg, (ast.JoinedStr, ast.Name, ast.Call, ast.Attribute,
              ast.Subscript, ast.BinOp))
def _sc08_shell_keyword_truthy(kw) -> bool:
    """识别 ``shell=True``，包括 ``**{'shell': True}`` 字典展开形式。"""
    if kw.arg == "shell":
        return is_shell_true_keyword(kw)
    if kw.arg is not None or not isinstance(kw.value, ast.Dict):
        return False
    for key, value in reversed(list(zip(
            kw.value.keys, kw.value.values, strict=True))):
        if key is None or not isinstance(key, ast.Constant):
            return False
        if key.value == "shell":
            return is_shell_true_keyword(
                ast.keyword(arg="shell", value=value))
    return False
def _sc08_shell_injection(tree, filepath: str, nodes,
                          call_contexts) -> list:
    issues = []
    calls = _resolve_execution_calls(tree, nodes, call_contexts)
    for call in calls:
        implicit_shell = call.dotted in _OS_EXEC_TARGETS
        if not implicit_shell and not any(
                _sc08_shell_keyword_truthy(kw)
                for kw in call.node.keywords):
            continue
        command_arg = _exec_command_arg(call.node)
        if command_arg is not None and _sc08_first_arg_dynamic(command_arg):
            issues.append(_finding(
                "SC-08", "P1", filepath, call.node.lineno,
                f"{call.short}() 使用隐式/显式 shell 且命令包含动态构造（命令注入风险）",
                "避免 shell 执行动态命令，使用参数列表传递: subprocess.run(['cmd', arg1])", dimension=_DIM_SUPPLY_CHAIN))
    return issues
def _pip_install_target(text: str) -> str | None:
    if not _PIP_INSTALL_PREFIX_PAT.search(text):
        return None
    m = _PIP_INSTALL_CMD_PAT.search(text)
    if m:
        return m.group(1)
    op = _PIP_INSTALL_OPERAND_PAT.search(text)
    return " ".join(t for t in op.groups() if t) if op else "?"
def _sc09_declared_manifest_operand(call) -> bool:
    """命令的任一绑定候选含星号展开时返回 True。

    该标记只表示存在声明式依赖分支；调用方仍须报告其他候选中的字面量包。
    """
    node = getattr(call, 'node', None)
    if node is None:
        return False
    command_arg = _exec_command_arg(node)
    if command_arg is None:
        return False
    candidates = _iter_expression_values(
        command_arg, node, getattr(call, 'parents', None), frozenset())
    return any(
        isinstance(candidate, (ast.List, ast.Tuple))
        and any(isinstance(elt, ast.Starred) for elt in candidate.elts)
        for candidate in candidates
    )
def _sc09_declared_manifest_option(pkg: str) -> bool:
    """``-r/--requirement``/``-c/--constraint`` 属声明式依赖管理，不是运行时装包。"""
    if not pkg:
        return False
    first = pkg.split()[0]
    return first in {"-r", "--requirement", "-c", "--constraint"}
def _sc09_runtime_pip_install(tree, filepath: str, nodes,
                              call_contexts) -> list:
    issues = []
    calls = _resolve_execution_calls(tree, nodes, call_contexts)
    for call in calls:
        has_declared_operand = _sc09_declared_manifest_operand(call)
        for text in _exec_command_texts(call):
            pkg = _pip_install_target(text)
            if (pkg is None or _sc09_declared_manifest_option(pkg)
                    or (has_declared_operand and pkg
                        and (pkg == "?" or pkg.startswith("-")))):
                continue
            issues.append(_finding(
                "SC-09", "P1", filepath, call.node.lineno,
                f"检测到运行时 pip install ({pkg})，存在包幻觉/供应链投毒风险",
                "移除运行时 pip install，改用 requirements.txt + 哈希锁定管理依赖", dimension=_DIM_SUPPLY_CHAIN))
            break
    return issues
_REQ_DEP_NAME_PAT = re.compile(r'^([A-Za-z0-9_][A-Za-z0-9_.-]*)(?:[><=!~]+\s*\S+)?')
_REQ_URL_DEP_PAT = re.compile(r'^(?:(?:git|hg|svn|bzr)\+)?(?:https?|ftp|file)://')
def _merge_continuation_lines(content: str) -> list[str]:
    logical_lines: list[str] = []
    pending = ""
    for raw_line in content.split("\n"):
        if raw_line.rstrip().endswith("\\"):
            pending += raw_line.rstrip()[:-1] + " "
            continue
        logical_lines.append(pending + raw_line)
        pending = ""
    if pending:
        logical_lines.append(pending)
    return logical_lines
def _is_url_dependency(line: str) -> bool:
    if _REQ_URL_DEP_PAT.match(line):
        return True
    _, sep, target = line.partition(" @ ")
    return bool(sep) and bool(_REQ_URL_DEP_PAT.match(target.lstrip()))
def _count_dep_and_hash_lines(logical_lines: list[str]) -> tuple[int, int]:
    dep_lines = 0
    hash_lines = 0
    for line in logical_lines:
        stripped = line.strip()
        if not stripped or stripped.startswith(("#", "-")):
            continue
        executable = re.split(r"\s+#", stripped, maxsplit=1)[0].rstrip()
        if _is_url_dependency(executable):
            continue
        if not _REQ_DEP_NAME_PAT.match(executable):
            continue
        dep_lines += 1
        hash_lines += 1 if "--hash=" in executable else 0
    return dep_lines, hash_lines
def _sc10_counts_issue(rel: str, dep_lines: int, hash_lines: int):
    if dep_lines <= 0:
        return None
    if hash_lines == 0:
        return _finding(
            "SC-10", "P2", rel, 1,
            f"requirements 文件有 {dep_lines} 个依赖但未使用 --hash 锁定，存在包替换风险",
            "为每个依赖添加 --hash=sha256:...，或用 pip-compile --generate-hashes 生成锁文件", dimension=_DIM_SUPPLY_CHAIN)
    if hash_lines < dep_lines:
        return _finding(
            "SC-10", "P2", rel, 1,
            f"requirements 文件 {dep_lines} 个依赖中仅 {hash_lines} 个有哈希校验",
            "补齐缺失依赖的 --hash=sha256 校验，启用 pip install --require-hashes", dimension=_DIM_SUPPLY_CHAIN)
    return None
def _sc10_requirements_hash(
        skill_dir: str | Path, scan_errors: list[str] | None = None) -> list:
    issues = []
    root = Path(skill_dir)
    for req in sorted(root.glob("requirements*.txt")):
        rel = _rel_project_path(req, root)
        try:
            content = req.read_text(encoding="utf-8", errors="replace")
        except OSError as e:
            _log.warning("SC-10 读取失败 %s: %s", rel, e)
            mark_section_degraded('供应链加固依赖锁定读取')
            _record_scan_error(scan_errors, f'{rel} 读取失败: {e}')
            continue
        if "SC-10" in content and "设计性豁免" in content:
            continue
        dep_lines, hash_lines = _count_dep_and_hash_lines(
            _merge_continuation_lines(content))
        issue = _sc10_counts_issue(rel, dep_lines, hash_lines)
        if issue is not None:
            issues.append(issue)
    return issues
def is_test_scan_target(fpath: Path, skill_path: Path, rel: str) -> bool:
    return (is_test_scan_asset(fpath, skill_path)
            or is_test_file_path(rel))
def _scan_py_file(fpath: Path, skill_path: Path, cache,
                  scan_errors: list[str] | None = None) -> list:
    rel = _rel_project_path(fpath, skill_path)
    if is_test_scan_target(fpath, skill_path, rel):
        _log.debug("[SCOPE-SKIP] 供应链加固跳过测试资产: %s", rel)
        return []
    try:
        content, tree = read_scan_source_tree(fpath, cache)
    except OSError as e:
        _log.warning("供应链加固扫描跳过不可读文件: %s: %s", fpath, e)
        mark_section_degraded('供应链加固源码读取')
        _record_scan_error(scan_errors, f'{fpath.name} 读取失败: {e}')
        return []
    if tree is None:
        tree = cached_scan_ast(str(fpath), content, None)
    if tree is None:
        _log.debug("SC-01/08/09 跳过语法错误文件 %s", rel)
        mark_section_degraded('供应链加固语法解析')
        _record_scan_error(scan_errors, f'{rel} 语法错误，AST 安全规则未完整执行')
        return _sc06_non_official_index(content, rel, context=None)
    nodes = tree_nodes(tree)
    call_contexts = _execution_call_contexts(tree, nodes)
    return [
        *_sc06_non_official_index(
            content, rel,
            context=_py_sc06_context(
                content, tree, nodes=nodes, call_contexts=call_contexts)),
        *_sc01_subprocess_no_timeout(
            tree, rel, nodes=nodes, call_contexts=call_contexts),
        *_sc08_shell_injection(
            tree, rel, nodes=nodes, call_contexts=call_contexts),
        *_sc09_runtime_pip_install(
            tree, rel, nodes=nodes, call_contexts=call_contexts),
    ]
def check_supply_chain_hardening(skill_dir: str, cache: SharedCache | None = None) -> dict:
    sp, err = _resolve_public_dir(skill_dir, "路径不是目录")
    if err is not None:
        return err
    findings: list = []
    scan_errors: list[str] = []
    for fpath in iter_scan_scope_files(sp):
        findings.extend(_scan_py_file(fpath, sp, cache, scan_errors))
    findings.extend(_sc06_pip_config_issues(sp, scan_errors))
    findings.extend(_sc10_requirements_hash(sp, scan_errors))
    return _scan_envelope(findings, "供应链加固检测", scan_errors)
_COMMENT_PREFIXES = ("#", "//")
def iter_leak_candidate_files(sp: Path, suffixes: frozenset):
    for f in sorted(iter_scan_scope_files(sp, suffixes)):
        if not is_backup_or_temp_file(f):
            yield f
SCRIPT_SCAN_SUFFIXES: frozenset = frozenset({
    '.py', '.sh', '.bash', '.ps1', '.js', '.ts', '.rb', '.pl',
})
def is_comment_line(line: str) -> bool:
    return line.strip().startswith(_COMMENT_PREFIXES)
def _non_py_comment_start(line: str) -> int:
    quote = ''
    escaped = False
    for index, char in enumerate(line):
        if quote:
            if escaped:
                escaped = False
            elif char == '\\':
                escaped = True
            elif char == quote:
                quote = ''
            continue
        if char in ('"', "'", '`'):
            quote = char
            continue
        previous = line[index - 1] if index else ''
        if char == '#' and (index == 0 or previous.isspace()):
            return index
        if (line.startswith('//', index)
                and (index == 0 or previous != ':')):
            return index
    return -1
def non_py_comment_spans(content: str) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    offset = 0
    for line in content.split('\n'):
        start = _non_py_comment_start(line)
        if start >= 0:
            spans.append((offset + start, offset + len(line)))
        offset += len(line) + 1
    return spans
def read_asset_text(path: Path, fallback_encoding: str = "utf-8") -> str:
    if path.suffix.lower() == ".py":
        text = read_source_with_fingerprint(str(path))[0]
        if text is not None:
            return text
    encodings = ["utf-8-sig"]
    for encoding in (fallback_encoding, "gb18030"):
        if encoding and encoding.lower() not in {
                item.lower() for item in encodings}:
            encodings.append(encoding)
    for encoding in encodings:
        try:
            return path.read_text(encoding=encoding)
        except UnicodeDecodeError:
            continue
    return path.read_text(encoding="utf-8", errors="replace")
TARGET_KIND_SKILL = "skill"
TARGET_KIND_PROJECT = "project"
TARGET_KIND_NONE = "none"
DOC_ROLE_SKILL = "skill_doc"
DOC_ROLE_README = "readme"
DOC_ROLE_MANIFEST = "manifest"
DOC_ROLE_NONE = "none"
_PROJECT_MANIFEST_NAMES = ("pyproject.toml", "setup.cfg", "setup.py")
_PROJECT_README_NAMES = ("README.md", "README.rst", "README.txt", "README")
_MARKDOWN_NOISE_RE = re.compile(r"[*_`>#]+")
_README_NOISE_RE = re.compile(r"^\[!\[|^!\[|<img\b|^---$")
_MARKDOWN_HEADING_RE = re.compile(r"^[ ]{0,3}#{1,6}[ \t]+(.+?)[ \t]*#*[ \t]*$")
_SETUP_PY_FIELD_RE = re.compile(
    r"\b(name|version|description)\s*=\s*['\"]([^'\"]+)['\"]")
@dataclass(frozen=True)
class TargetDocument:
    kind: str = TARGET_KIND_NONE
    doc_role: str = DOC_ROLE_NONE
    path: Path | None = None
    name: str = ""
    description: str = ""
    version: str = ""
    text: str = ""
    read_failed: bool = False
def _read_target_text(path: Path) -> tuple[str, bool]:
    try:
        return read_asset_text(path), False
    except (OSError, UnicodeDecodeError) as exc:
        _log.debug("[Health] 目标文档读取失败 %s: %s", path, exc)
        return "", True
def _first_existing(sp: Path, names: tuple[str, ...]) -> Path | None:
    for name in names:
        candidate = sp / name
        try:
            if candidate.is_file():
                return candidate
        except OSError as exc:
            _log.debug("[Health] 目标文件探测失败 %s: %s", candidate, exc)
    return None
def _has_python_sources(sp: Path) -> bool:
    try:
        return next(iter_scan_scope_files(sp), None) is not None
    except OSError as exc:
        _log.debug("[Health] 项目源码探测失败 %s: %s", sp, exc)
    return False
def _skill_document_fields(text: str) -> tuple[str, str, str]:
    if not text.strip():
        return "", "", ""
    fm_text, _body = parse_frontmatter(text)
    frontmatter, reason, detail = load_frontmatter(fm_text)
    if reason == "parse_error":
        _log.debug("[Health] frontmatter 解析失败，按无元数据处理: %s", detail)
    data = frontmatter if isinstance(frontmatter, dict) else {}
    def _field(key: str) -> str:
        value = data.get(key)
        return value.strip() if isinstance(value, str) else ""
    try:
        description = extract_description(text).strip()
    except Exception as exc:  # noqa: BLE001 — 描述提取失败降级空描述
        _log.debug("[Health] 描述提取失败，降级空描述: %s", exc, exc_info=True)
        description = ""
    return _field("name"), description, _field("version")
def _toml_table_fields(text: str, section: str) -> dict[str, str]:
    if _tomllib is not None:
        try:
            data = _tomllib.loads(text)
        except (ValueError, TypeError) as exc:
            _log.debug("[Health] TOML 解析失败，走文本回退: %s", exc)
        else:
            table: Any = data
            for part in section.split("."):
                table = table.get(part) if isinstance(table, dict) else None
            if not isinstance(table, dict):
                return {}
            return {key: value.strip()
                    for key, value in table.items()
                    if isinstance(value, str) and value.strip()}
    fields: dict[str, str] = {}
    active = False
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("[") and stripped.endswith("]"):
            active = stripped[1:-1].strip() == section
            continue
        if not active or stripped.startswith("#") or "=" not in stripped:
            continue
        key, _sep, raw = stripped.partition("=")
        raw = raw.strip()
        if raw[:1] in ("'", '"'):
            end = raw.find(raw[0], 1)
            if end > 0:
                fields.setdefault(key.strip(), raw[1:end])
    return fields
def _setup_cfg_fields(text: str) -> dict[str, str]:
    parser = configparser.RawConfigParser()
    try:
        parser.read_string(text)
    except configparser.Error as exc:
        _log.debug("[Health] setup.cfg 解析失败: %s", exc)
        return {}
    if not parser.has_section("metadata"):
        return {}
    fields: dict[str, str] = {}
    for key in ("name", "version", "description"):
        if parser.has_option("metadata", key):
            value = parser.get("metadata", key).strip()
            if value:
                fields[key] = value
    return fields
def _project_manifest_fields(manifest: Path | None) -> dict[str, str]:
    if manifest is None:
        return {}
    text, failed = _read_target_text(manifest)
    if failed:
        return {}
    name = manifest.name.lower()
    if name == "pyproject.toml":
        merged: dict[str, str] = {}
        for section in ("tool.poetry", "project"):
            merged.update(_toml_table_fields(text, section))
        return merged
    if name == "setup.cfg":
        return _setup_cfg_fields(text)
    return dict(_SETUP_PY_FIELD_RE.findall(text))
def iter_markdown_lines(text: str) -> Iterator[tuple[str, str]]:
    in_fence = False
    fence_char = ""
    fence_len = 0
    for raw in text.splitlines():
        in_fence, fence_char, fence_len, line_kind = scan_fence_state(
            in_fence, fence_char, fence_len, raw)
        if line_kind or in_fence:
            continue
        line = raw.strip()
        heading = _MARKDOWN_HEADING_RE.match(line)
        if heading:
            yield "heading", _MARKDOWN_NOISE_RE.sub("", heading.group(1)).strip()
        elif not line:
            yield "blank", ""
        else:
            yield "text", line
def _readme_summary(text: str) -> tuple[str, str]:
    title = ""
    paragraph: list[str] = []
    for kind, value in iter_markdown_lines(text):
        if kind == "heading":
            if not title:
                title = value
            if paragraph:
                break
            continue
        if kind == "blank":
            if paragraph:
                break
            continue
        if _README_NOISE_RE.match(value):
            continue
        paragraph.append(_MARKDOWN_NOISE_RE.sub("", value).strip())
    return title, " ".join(part for part in paragraph if part).strip()
def resolve_target_document(target_dir: Any) -> TargetDocument:
    try:
        raw = (os.fspath(target_dir)
               if isinstance(target_dir, (os.PathLike, bytes))
               else str(target_dir or ""))
        if isinstance(raw, bytes):
            raw = os.fsdecode(raw)
    except TypeError:
        return TargetDocument()
    if not raw.strip():
        return TargetDocument()
    sp = Path(raw.strip())
    fallback_name = (sp.name if sp.name not in ('', '.', '..')
                     else Path(os.path.abspath(sp)).name)
    try:
        if not sp.is_dir():
            return TargetDocument(name=fallback_name)
    except OSError as exc:
        _log.debug("[Health] 目标目录不可访问 %s: %s", sp, exc)
        return TargetDocument(name=fallback_name)
    skill_md = sp / "SKILL.md"
    try:
        has_skill_doc = skill_md.is_file()
    except OSError:
        has_skill_doc = False
    if has_skill_doc:
        text, failed = _read_target_text(skill_md)
        name, description, version = _skill_document_fields(text)
        return TargetDocument(
            kind=TARGET_KIND_SKILL, doc_role=DOC_ROLE_SKILL,
            path=skill_md, name=name or fallback_name,
            description=description, version=version, text=text,
            read_failed=failed)
    manifests = []
    for manifest_name in _PROJECT_MANIFEST_NAMES:
        candidate = _first_existing(sp, (manifest_name,))
        if candidate is not None:
            manifests.append(candidate)
    manifest = manifests[0] if manifests else None
    readme = _first_existing(sp, _PROJECT_README_NAMES)
    fields: dict[str, str] = {}
    for candidate in reversed(manifests):
        fields.update(_project_manifest_fields(candidate))
    readme_text, readme_failed = ("", False)
    if readme is not None:
        readme_text, readme_failed = _read_target_text(readme)
    _title, summary = _readme_summary(readme_text)
    description = fields.get("description") or summary
    name = fields.get("name") or fallback_name
    version = fields.get("version", "")
    if readme is not None:
        doc_path, role = readme, DOC_ROLE_README
        text, failed = readme_text, readme_failed
    elif manifest is not None:
        doc_path, role = manifest, DOC_ROLE_MANIFEST
        text, failed = _read_target_text(manifest)
    else:
        doc_path, role, text, failed = None, DOC_ROLE_NONE, "", False
    kind = TARGET_KIND_PROJECT if (doc_path is not None
                                    or _has_python_sources(sp)) else TARGET_KIND_NONE
    return TargetDocument(
        kind=kind, doc_role=role, path=doc_path, name=name,
        description=description, version=version, text=text,
        read_failed=failed)
def line_no(content: str, pos: int) -> int:
    return content.count('\n', 0, pos) + 1
class Verdict(NamedTuple):
    severity: Severity
    category: str
    recommendation: str
SECRET_LEAK_VERDICT = Verdict(
    Severity.CRITICAL, '供应链安全-Secret泄露',
    '使用环境变量或密钥管理服务')
def new_location_issue(verdict: Verdict, location: str,
                        description: str) -> SecurityIssue:
    return SecurityIssue(
        severity=verdict.severity, category=verdict.category,
        description=description, location=location,
        recommendation=verdict.recommendation)
_SECRET_SUPPRESS_CATEGORIES = ('供应链安全-Secret泄露', 'SS-03')
def _secret_inline_suppressed(content: str, pos: int, secret_tokens) -> bool:
    return any(inline_suppressed_at(content, pos, category, secret_tokens)
               for category in _SECRET_SUPPRESS_CATEGORIES)
def iter_secret_hits(content: str, rel_path: str, secret_tokens):
    for pattern in SECRET_PATTERNS:
        for match in re.finditer(pattern, content):
            value = match.group()
            if is_placeholder_secret_value(value):
                continue
            if _secret_inline_suppressed(
                    content, match.start(), secret_tokens):
                _log.info('[SUPPRESSED-INLINE] Secret泄露行内抑制: file=%s val=%s',
                          rel_path, mask_secret(value))
                continue
            if is_codetext_fixture_at(match.start(), secret_tokens):
                _log.info(
                    '[SUPPRESSED-FIXTURE] Secret泄露夹具抑制(留CV复核): '
                    'file=%s pat_prefix=%s val=%s',
                    rel_path, pattern[:24], mask_secret(value))
                continue
            yield match
_SENSITIVE_PATHS = [
    '/etc/passwd', '/etc/shadow', '/etc/ssh/', '~/.ssh/', '~/.gnupg/',  # jwsgj:suppress SS-02,供应链安全-敏感路径 — 检测规则表，非执行面
    '~/.aws/', 'C:\\Windows\\System32\\config\\', '~/.bash_history',  # jwsgj:suppress 供应链安全-敏感路径 — 检测规则表，非执行面
    '~/.zsh_history', '/var/log/', '/proc/', '/sys/',  # jwsgj:suppress 供应链安全-敏感路径 — 检测规则表，非执行面
]
_SC_SUBPROCESS_SHELL_FUNCS = frozenset({
    'subprocess.call', 'subprocess.run', 'subprocess.Popen',
    'subprocess.check_call', 'subprocess.check_output',
})
_SC_DANGEROUS_IMPORT_FUNCS = frozenset({
    'os.system', 'os.popen', 'builtins.eval', 'builtins.exec',
}) | _SC_SUBPROCESS_SHELL_FUNCS
def _match_patterns_in_content(fpath: Path, base: Path, content: str,
                               patterns: list, severity: Severity,
                               category: str, desc_template: str,
                               recommendation: str) -> list:
    issues = []
    for pattern in patterns:
        for match in re.finditer(pattern, content, re.IGNORECASE):
            issues.append(_pattern_match_issue(
                fpath, base, content, match, severity, category,
                desc_template, recommendation))
    return issues
def _pattern_match_issue(fpath: Path, base: Path, content: str, match,
                         severity: Severity, category: str,
                         desc_template: str, recommendation: str,
                         match_line: int | None = None) -> SecurityIssue:
    rel = _rel_project_path(fpath, base)
    line_num = (line_no(content, match.start())
                if match_line is None else match_line)
    return SecurityIssue(
        severity=severity, category=category,
        description=desc_template.format(
            file=fpath.name, line=line_num, match=match.group()[:60]),
        location=f'{rel}:{line_num}',
        recommendation=recommendation)
def _scan_file_for_patterns(fpath: Path, base: Path, patterns: list,
                            severity: Severity, category: str,
                            desc_template: str, recommendation: str,
                            scan_errors: list[str] | None = None) -> list:
    try:
        content = read_asset_text(fpath)
    except (OSError, UnicodeDecodeError) as exc:
        _log.warning('[Security] 文件不可读，跳过扫描 %s: %s', fpath, exc)
        mark_section_degraded('供应链安全文档读取')
        _record_scan_error(scan_errors, f'{fpath.name} 读取失败: {exc}')
        return []
    return _match_patterns_in_content(
        fpath, base, content, patterns, severity, category,
        desc_template, recommendation)
def _read_script_source(script: Path, cache=None,
                        scope: str = '安全检查') -> str | None:
    if script.suffix.lower() == '.py':
        content = cached_scan_source(str(script), cache)
        if content is None:
            content = read_source_with_fingerprint(str(script))[0]
    else:
        try:
            content = read_asset_text(script)
        except (OSError, UnicodeDecodeError) as _e:
            _log.warning('%s: 跳过不可读文件 %s: %s', scope, script, _e)
            mark_section_degraded(f'{scope}脚本读取')
            return None
    if content is None:
        _log.warning('%s: 跳过不可读文件: %s', scope, script)
        mark_section_degraded(f'{scope}脚本读取')
    return content
def _iter_script_sources(
        sp: Path, cache, scan_errors: list[str] | None = None):
    _skipped = 0
    for script in iter_scan_scope_files(sp, SCRIPT_SCAN_SUFFIXES):
        if is_test_scan_target(script, sp, _rel_project_path(script, sp)):
            _skipped += 1
            continue
        content = _read_script_source(script, cache)
        if content is None:
            _record_scan_error(scan_errors, f'{script.name} 读取失败，脚本规则未执行')
            continue
        yield script, content
    if _skipped:
        _log.info('[SCOPE-SKIP] 供应链启发式跳过测试资产 %d 个: %s',
                  _skipped, sp)
def _comment_span_offsets(content: str) -> list[tuple[int, int]]:
    row_spans = comment_only_spans(content)
    if row_spans is None:
        return non_py_comment_spans(content)
    if not row_spans:
        return []
    line_starts: list[int] = []
    offset = 0
    for line in content.split('\n'):
        line_starts.append(offset)
        offset += len(line) + 1
    spans: list[tuple[int, int]] = []
    for row, items in row_spans.items():
        if not 1 <= row <= len(line_starts):
            continue
        base = line_starts[row - 1]
        spans.extend((base + start, base + end) for start, end in items)
    return spans
class _MaskedScanSpec(NamedTuple):
    severity: Severity
    category: str
    desc_template: str
    recommendation: str
    flags: int = 0
    first_per_pattern: bool = False
    scan_executed: bool = False
    # 敏感路径的证据就在字符串字面量里；默认掩码全部字符串会让 Python 文件
    # 的 open('/etc/passwd') 完全漏报，仅危险命令等代码执行类规则需要全掩。
    mask_all_strings: bool = True
def _python_docstring_rows(content: str) -> frozenset:
    tree = _parse_scan_source(content, context='_scan_masked_scripts')
    if tree is None:
        return frozenset()
    return frozenset(docstring_rows_from_nodes(tree_nodes(tree)))
def _scan_masked_scripts(sp: Path, cache, patterns: list,
                         spec: _MaskedScanSpec,
                         scan_errors: list[str] | None = None) -> list:
    issues = []
    for script, content in _iter_script_sources(sp, cache, scan_errors):
        _is_py = script.suffix.lower() == '.py'
        # 掩码口径必须与 ``skill_scan_kernels`` 的文本证据通道保持一致
        # （注释 + 文档字符串 + 路径守卫 + 规则表字面量）。此前本通道只掩注释，
        # 同一份规则表（``COMMAND_BLACKLIST`` / ``SENSITIVE_PATHS``）在两条
        # 扫描通道里得出相反结论：内核通道豁免、本通道报 P0 阻断。
        if _is_py:
            # 函数内导入：skill_scan_kernels 反向从本模块导入 SecurityReport
            # 等类型，顶部导入会构成硬环。
            from jwsgj.skill_scan_kernels import (
                _text_evidence_mask as _resolve_text_evidence_mask,
            )
            _mask = (_resolve_text_evidence_mask(
                         content, mask_all_strings=spec.mask_all_strings)
                     or _comment_span_offsets(content))
        else:
            _mask = non_py_comment_spans(content)
        _str_spans = (py_string_token_offsets(content)
                      if _is_py else ())
        _doc_rows = (_python_docstring_rows(content)
                     if _is_py else frozenset())
        handled_raw_matches: dict[tuple[str, str], list[int]] = {}
        for pattern in patterns:
            for match in re.finditer(pattern, content, spec.flags):
                if is_masked_offset(_mask, match.start()):
                    continue
                if _doc_rows and line_no(content, match.start()) in _doc_rows:
                    _log.info(
                        '[SUPPRESSED-FIXTURE] %s 文档字符串示例抑制: %s:%d',
                        spec.category, script, line_no(content, match.start()))
                    continue
                if inline_suppressed_at(content, match.start(), spec.category,
                                         _str_spans):
                    handled_raw_matches.setdefault(
                        (pattern, match.group()), []).append(match.start())
                    continue
                issues.append(_pattern_match_issue(
                    script, sp, content, match, spec.severity, spec.category,
                    spec.desc_template, spec.recommendation))
                handled_raw_matches.setdefault(
                    (pattern, match.group()), []).append(match.start())
                if spec.first_per_pattern:
                    break
        if not spec.scan_executed or not _is_py:
            continue
        tree = cached_scan_ast(str(script), content, cache)
        if tree is None:
            mark_section_degraded('供应链脚本语法解析')
            _record_scan_error(
                scan_errors, f'{script.name} 语法错误，执行语义规则未完整执行')
            continue
        lines = content.split('\n')
        line_starts = [0]
        line_starts.extend(m.end() for m in re.finditer(r'\n', content))
        for pattern, call, match in _iter_executed_pattern_matches(
                tree, patterns, spec.flags):
            call_pos = line_starts[call.node.lineno - 1] + byte_col_to_char_col(
                lines[call.node.lineno - 1], call.node.col_offset)
            call_end = line_starts[call.node.end_lineno - 1] + byte_col_to_char_col(
                lines[call.node.end_lineno - 1], call.node.end_col_offset)
            raw_positions = handled_raw_matches.get(
                (pattern, match.group()), ())
            if any(call_pos <= raw_pos < call_end
                   for raw_pos in raw_positions):
                continue
            if inline_suppressed_at(content, call_pos, spec.category,
                                     _str_spans):
                continue
            issues.append(_pattern_match_issue(
                script, sp, content, match, spec.severity, spec.category,
                spec.desc_template, spec.recommendation,
                match_line=call.node.lineno))
    return issues
def _quickcheck_root(skill_dir, label: str) -> Path | None:
    normalized = coerce_skill_dir(skill_dir)
    sp = Path(normalized) if normalized else None
    if sp is not None and sp.is_dir():
        return sp
    _log.warning('供应链快查-%s: 扫描目录不存在或不是目录，保守判不通过: %s',
                 label, skill_dir)
    return None
def _masked_channel_issues(skill_dir, label: str, patterns: list,
                           spec: _MaskedScanSpec,
                           cache: SharedCache | None = None,
                           scan_errors: list[str] | None = None
                           ) -> tuple[Path | None, list]:
    sp = _quickcheck_root(skill_dir, label)
    if sp is None:
        return None, []
    return sp, _scan_masked_scripts(
        sp, cache, patterns, spec, scan_errors)
def check_sensitive_paths(
        skill_dir: str, cache: SharedCache | None=None, *,
        _scan_errors: list[str] | None = None) -> tuple[bool, list]:
    scan_errors: list[str] = []
    sp, issues = _masked_channel_issues(
        skill_dir, '敏感路径', [re.escape(p) for p in _SENSITIVE_PATHS],
        _MaskedScanSpec(
            severity=Severity.HIGH, category='供应链安全-敏感路径',
            desc_template='脚本 {file}:{line} 引用了敏感路径: {match}',
            recommendation='如需访问用户目录，使用 os.path.expanduser() 并做权限校验',
            first_per_pattern=True, mask_all_strings=False),
        cache, scan_errors=scan_errors)
    if _scan_errors is not None:
        _scan_errors.extend(scan_errors)
    return (sp is not None and not issues and not scan_errors, issues)
def check_dangerous_commands(
        skill_dir: str, cache: SharedCache | None=None, *,
        _scan_errors: list[str] | None = None) -> tuple[bool, list]:
    scan_errors: list[str] = []
    sp, issues = _masked_channel_issues(
        skill_dir, '危险命令', DANGEROUS_COMMANDS,
        _MaskedScanSpec(
            severity=Severity.CRITICAL, category='供应链安全-危险命令',
            desc_template='脚本 {file}:{line} 包含危险命令: {match}',
            recommendation='使用 subprocess.run([...], shell=False) 替代，或添加沙箱隔离',
            flags=re.IGNORECASE, scan_executed=True), cache,
        scan_errors=scan_errors)
    if _scan_errors is not None:
        _scan_errors.extend(scan_errors)
    return (sp is not None and not issues and not scan_errors, issues)
def check_remote_scripts(
        skill_dir: str, cache: SharedCache | None=None, *,
        _scan_errors: list[str] | None = None) -> tuple[bool, list]:
    scan_errors: list[str] = []
    sp, issues = _masked_channel_issues(
        skill_dir, '远程脚本', REMOTE_SCRIPT_PATTERNS,
        _MaskedScanSpec(
            severity=Severity.HIGH, category='供应链安全-远程脚本',
            desc_template='脚本 {file}:{line} 下载并执行远程脚本',
            recommendation='下载后先做 SHA256 校验，或使用官方包管理器',
            scan_executed=True), cache, scan_errors=scan_errors)
    if sp is None:
        return (False, [])
    skill_md = sp / 'SKILL.md'
    if skill_md.is_file():
        md_issues = _scan_file_for_patterns(
            skill_md, sp, REMOTE_SCRIPT_PATTERNS, Severity.MEDIUM,
            '供应链安全-远程脚本',
            '在 {file}:{line} 提到远程脚本执行: {match}',
            '在 SKILL.md 中添加安全警告和校验步骤', scan_errors=scan_errors)
        issues.extend(md_issues)
    if _scan_errors is not None:
        _scan_errors.extend(scan_errors)
    return (not issues and not scan_errors, issues)
LEAK_SCAN_SUFFIXES: frozenset = frozenset(
    set(SCRIPT_SCAN_SUFFIXES)
    | {'.md', '.txt', '.yaml', '.yml', '.json', '.toml', '.ini',
       '.cfg', '.conf', '.env'})
def _emit_secret_issues(content: str, rel: str, secret_toks,
                        issues: list) -> None:
    for match in iter_secret_hits(content, rel, secret_toks):
        _line = line_no(content, match.start())
        issues.append(new_location_issue(
            SECRET_LEAK_VERDICT, f'{rel}:{_line}',
            f'在 {rel}:{_line} 可能包含泄露的凭据: '
            f'{mask_secret(match.group())}'))
def check_secret_leaks(
        skill_dir: str, cache: SharedCache | None=None, *,
        _scan_errors: list[str] | None = None) -> tuple[bool, list]:
    sp = _quickcheck_root(skill_dir, 'Secret泄露')
    if sp is None:
        return (False, [])
    issues = []
    scan_errors: list[str] = []
    for f in iter_leak_candidate_files(sp, LEAK_SCAN_SUFFIXES):
        _rel = _rel_project_path(f, sp)
        _is_env_file = f.name.lower().endswith('.env')
        _skip = (is_test_file_path(_rel) if _is_env_file
                 else is_test_scan_target(f, sp, _rel))
        if _skip:
            _log.debug('[SCOPE-SKIP] Secret泄露跳过测试资产: %s', f)
            continue
        content = _read_script_source(f, cache, scope='check_secret_leaks')
        if content is None:
            _record_scan_error(scan_errors, f'{f.name} 读取失败，Secret 规则未执行')
            continue
        _secret_toks = (py_string_token_offsets(content)
                        if f.suffix.lower() == '.py' else ())
        _emit_secret_issues(content, _rel, _secret_toks, issues)
    if _scan_errors is not None:
        _scan_errors.extend(scan_errors)
    return (not issues and not scan_errors, issues)
@dataclass
class SupplyChainReport:
    skill_name: str = ""
    skill_path: str = ""
    passed: bool = True
    sensitive_path_access: list = field(default_factory=list)
    dangerous_commands: list = field(default_factory=list)
    remote_scripts: list = field(default_factory=list)
    network_calls: list = field(default_factory=list)
    secret_leaks: list = field(default_factory=list)
    total_issues: int = 0
    risk_level: str = "low"
    scan_errors: list[str] = field(default_factory=list)
    def all_issues(self) -> list:
        return (self.sensitive_path_access + self.dangerous_commands
                + self.remote_scripts + self.network_calls
                + self.secret_leaks)
def _scan_scripts_for_danger(
        target_dir, scan_errors: list[str] | None = None) -> str | None:
    target_dir = Path(target_dir)
    if not target_dir.is_dir():
        return None
    for pf in iter_scan_scope_files(target_dir, SCRIPT_SCAN_SUFFIXES):
        if is_test_scan_target(
                pf, target_dir, _rel_project_path(pf, target_dir)):
            continue
        sc = _read_script_source(pf, scope='第三方技能危险扫描')
        if sc is None:
            _record_scan_error(scan_errors, f'{pf.name} 读取失败，危险扫描未执行')
            continue
        if pf.suffix.lower() != '.py':
            _mask = non_py_comment_spans(sc)
            if any(
                    not is_masked_offset(_mask, m.start())
                    for pattern in DANGEROUS_COMMANDS
                    for m in re.finditer(pattern, sc, re.IGNORECASE)):
                return pf.name
            continue
        tree = cached_scan_ast(str(pf), sc, None)
        if tree is None:
            mark_section_degraded('第三方技能语法解析')
            _record_scan_error(scan_errors, f'{pf.name} 语法错误，危险调用检查未执行')
            continue
        if (any(count_dangerous_call_risks(tree))
                or any(_iter_executed_pattern_matches(
                    tree, DANGEROUS_COMMANDS, re.IGNORECASE))):
            return pf.name
    return None
def check_third_party_skill(skill_dir: str) -> tuple[bool, str]:
    normalized = coerce_skill_dir(skill_dir)
    sp = Path(normalized) if normalized else None
    if sp is None or not sp.is_dir():
        return (False, '目录不存在')
    skill_md = sp / 'SKILL.md'
    if not skill_md.is_file():
        return (False, '缺少 SKILL.md')
    try:
        content = read_asset_text(skill_md)
    except (OSError, UnicodeDecodeError) as e:
        _log.error('check_third_party_skill failed: %s', e, exc_info=True)
        return (False, f'检查失败: {e}')
    has_source = bool(re.search(
        r'\bsources?\b|\bauthors?\b|来源|作者', content, re.IGNORECASE))
    scan_errors: list[str] = []
    dangerous_script = _scan_scripts_for_danger(sp, scan_errors)
    if scan_errors:
        return (False, '安全检查不完整: ' + '; '.join(scan_errors))
    if dangerous_script:
        return (False, f'脚本 {dangerous_script} 包含危险调用')
    provenance_note = '' if has_source else '（未声明来源/作者，溯源信息不足）'
    return (True, '通过基本安全检查' + provenance_note)
NETWORK_CALL_TARGETS = frozenset({
    'requests.get', 'requests.post', 'requests.put',
    'requests.delete', 'requests.head', 'requests.patch', 'requests.request',
    'httpx.get', 'httpx.post', 'httpx.put',
    'httpx.delete', 'httpx.head', 'httpx.patch', 'httpx.request',
    'aiohttp.request', 'aiohttp.ClientSession.request',
    'urllib.request.urlopen', 'urllib.request.urlretrieve'})
_SC_POSITIONAL_TIMEOUT_SLOTS: dict[str, int] = {
    'urllib.request.urlopen': 2,
}
def _register_star_bindings(module: str, targets,
                            bare_bindings: dict[str, str | None]) -> None:
    prefix = f'{module}.'
    for target in sorted(targets):
        if not target.startswith(prefix):
            continue
        leaf = target[len(prefix):]
        if leaf and '.' not in leaf:
            bare_bindings.setdefault(leaf, target)
def _register_from_import(node: ast.ImportFrom,
                          bare_bindings: dict[str, str | None],
                          module_aliases: dict[str, str | None],
                          targets) -> None:
    if node.level or not node.module:
        for alias in node.names:
            if alias.name != '*':
                bare_bindings[alias.asname or alias.name] = None
        return
    for alias in node.names:
        if alias.name == '*':
            _register_star_bindings(node.module, targets, bare_bindings)
            continue
        qualified, is_module_prefix = _classify_import_alias(
            node.module, alias.name, targets)
        bound_name = alias.asname or alias.name
        if qualified is None:
            bare_bindings[bound_name] = None
            continue
        target = module_aliases if is_module_prefix else bare_bindings
        target[bound_name] = qualified
def _classify_import_alias(module: str, name: str,
                           targets) -> tuple[str | None, bool]:
    qualified = f'{module}.{name}'
    if qualified in targets:
        return qualified, False
    if any(w.startswith(qualified + '.') for w in targets):
        return qualified, True
    return None, False
def _register_module_import(node: ast.Import,
                            module_aliases: dict[str, str | None]) -> None:
    for alias in node.names:
        if alias.asname:
            module_aliases[alias.asname] = alias.name
        else:
            root = alias.name.split('.')[0]
            module_aliases[root] = root
_COMPREHENSION_NODES = (ast.ListComp, ast.SetComp, ast.DictComp,
                         ast.GeneratorExp)
_FUNCTION_SCOPE_NODES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
_PATTERN_BINDING_NODES = (ast.MatchAs, ast.MatchStar, ast.MatchMapping)
def _iter_walrus_targets(scope) -> Iterator[ast.Name]:
    stack = list(ast.iter_child_nodes(scope))
    while stack:
        current = stack.pop()
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef, ast.Lambda)):
            continue
        if isinstance(current, ast.NamedExpr):
            if isinstance(current.target, ast.Name):
                yield current.target
            stack.append(current.value)
            continue
        stack.extend(ast.iter_child_nodes(current))
def _iter_scope_binding_nodes(scope) -> list:
    body = getattr(scope, 'body', None)
    if isinstance(scope, ast.Lambda) and body is not None:
        body = [body]
    if not isinstance(body, list):
        return []
    out: list = []
    stack = list(body)
    while stack:
        current = stack.pop()
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef)):
            out.append(current)
            continue
        if isinstance(current, ast.Lambda):
            continue
        if isinstance(current, _COMPREHENSION_NODES):
            out.extend(_iter_walrus_targets(current))
            continue
        if (isinstance(current, (ast.Import, ast.ImportFrom,
                                 ast.ExceptHandler))
                or (isinstance(current, ast.Name)
                    and isinstance(current.ctx, (ast.Store, ast.Del)))
                or (isinstance(current, _PATTERN_BINDING_NODES)
                    and _pattern_node_name(current))):
            out.append(current)
        stack.extend(ast.iter_child_nodes(current))
    return out
def _binding_position(node, parents) -> tuple[int, int]:
    statement = node
    while (statement is not None
           and not isinstance(statement, (ast.stmt, ast.NamedExpr))):
        statement = parents.get(id(statement))
    statement = statement or node
    line = (getattr(statement, 'end_lineno', None)
            or getattr(statement, 'lineno', 0))
    column = (getattr(statement, 'end_col_offset', None)
              or getattr(statement, 'col_offset', 0))
    return line, column
def _scope_parameter_names(scope) -> list[str]:
    if not isinstance(scope, _FUNCTION_SCOPE_NODES):
        return []
    return [arg.arg for arg in iter_arg_nodes(scope.args)]
def _scope_global_names(scope, *, global_only: bool = False) -> set[str]:
    if not isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef)):
        return set()
    names: set[str] = set()
    stack = list(getattr(scope, 'body', None) or [])
    while stack:
        current = stack.pop()
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef, ast.Lambda)):
            continue
        if (isinstance(current, ast.Global)
                or (not global_only and isinstance(current, ast.Nonlocal))):
            names.update(current.names)
            continue
        stack.extend(ast.iter_child_nodes(current))
    return names
def _pattern_node_name(node) -> str:
    if isinstance(node, ast.MatchMapping):
        return node.rest or ''
    return getattr(node, 'name', '') or ''
def _binding_names(node) -> set[str]:
    if isinstance(node, ast.Import):
        return {(alias.asname or alias.name.split('.')[0])
                for alias in node.names}
    if isinstance(node, ast.ImportFrom):
        return {(alias.asname or alias.name)
                for alias in node.names if alias.name != '*'}
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef)):
        return {node.name}
    if isinstance(node, ast.ExceptHandler):
        return {node.name} if node.name else set()
    if isinstance(node, ast.Name):
        return {node.id}
    if isinstance(node, _PATTERN_BINDING_NODES):
        name = _pattern_node_name(node)
        return {name} if name else set()
    return set()
def _shadow_binding(name: str, bare_bindings: dict,
                    module_aliases: dict) -> None:
    bare_bindings[name] = None
    module_aliases[name] = None
def _merge_import_bindings(bare_bindings: dict, module_aliases: dict,
                           new_bare: dict, new_aliases: dict) -> None:
    for name, value in new_bare.items():
        bare_bindings[name] = value
        module_aliases.pop(name, None)
    for name, value in new_aliases.items():
        module_aliases[name] = value
        bare_bindings.pop(name, None)
def _scope_bindings_at_call(scope, call, parents, targets,
                            immediate: bool) -> tuple[dict, dict]:
    bare_bindings: dict[str, str | None] = {}
    module_aliases: dict[str, str | None] = {}
    for name in _scope_parameter_names(scope):
        _shadow_binding(name, bare_bindings, module_aliases)
    call_position = (call.lineno, call.col_offset)
    positioned = [(_binding_position(node, parents), node)
                  for node in _iter_scope_binding_nodes(scope)]
    positioned.sort(key=lambda item: item[0])
    is_function = isinstance(scope, _FUNCTION_SCOPE_NODES)
    global_names = _scope_global_names(scope)
    for position, node in positioned:
        if immediate and position >= call_position:
            if is_function:
                for name in _binding_names(node) - global_names:
                    _shadow_binding(name, bare_bindings, module_aliases)
            continue
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            new_bare, new_aliases = _net_import_bindings([node], targets)
            _merge_import_bindings(
                bare_bindings, module_aliases, new_bare, new_aliases)
        else:
            for name in _binding_names(node):
                _shadow_binding(name, bare_bindings, module_aliases)
    return bare_bindings, module_aliases
def _target_names(target) -> set[str]:
    if target is None:
        return set()
    return {node.id for node in walk_nodes(target) if isinstance(node, ast.Name)}
def _pattern_names(pattern) -> set[str]:
    return {name for node in walk_nodes(pattern)
            if isinstance(node, _PATTERN_BINDING_NODES)
            for name in [_pattern_node_name(node)] if name}
def _statement_scope(node, parents):
    current = parents.get(id(node))
    while current is not None and not isinstance(
            current, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda,
                      ast.ClassDef, ast.Module)):
        current = parents.get(id(current))
    return current
def _contextual_binding_names(call, parents) -> set[str]:
    names: set[str] = set()
    visible_scopes = {
        id(scope) for scope in iter_evaluation_scope_chain(call, parents)}
    current = parents.get(id(call))
    child = call
    below = None
    while current is not None:
        bound: set[str] = set()
        if isinstance(current, _COMPREHENSION_NODES):
            if not _is_outer_comprehension_iter(current, child, below):
                for generator in current.generators:
                    names.update(_target_names(generator.target))
        elif (isinstance(current, (ast.For, ast.AsyncFor))
              and child in current.body):
            bound = _target_names(current.target)
        elif (isinstance(current, (ast.With, ast.AsyncWith))
              and child in current.body):
            for item in current.items:
                bound.update(_target_names(item.optional_vars))
        elif (isinstance(current, ast.ExceptHandler)
              and child in current.body and current.name):
            bound.add(current.name)
        elif isinstance(current, ast.match_case):
            bound = _pattern_names(current.pattern)
        if bound:
            scope = _statement_scope(current, parents)
            if id(scope) in visible_scopes:
                names.update(bound)
        below = child
        child = current
        current = parents.get(id(current))
    return names
def _call_scope_bindings(call, parents,
                         targets: frozenset) -> tuple[dict, dict]:
    bare_bindings: dict[str, str | None] = {}
    module_aliases: dict[str, str | None] = {}
    module_binding_state: tuple[dict, dict] = ({}, {})
    scopes = list(reversed(iter_evaluation_scope_chain(call, parents)))
    for index, scope in enumerate(scopes):
        if not isinstance(scope, ast.Module):
            module_bare, module_alias = module_binding_state
            for name in _scope_global_names(scope, global_only=True):
                bare_bindings.pop(name, None)
                module_aliases.pop(name, None)
                if name in module_bare:
                    bare_bindings[name] = module_bare[name]
                if name in module_alias:
                    module_aliases[name] = module_alias[name]
        local_bare, local_aliases = _scope_bindings_at_call(
            scope, call, parents, targets,
            immediate=index == len(scopes) - 1)
        _merge_import_bindings(
            bare_bindings, module_aliases, local_bare, local_aliases)
        if isinstance(scope, ast.Module):
            module_binding_state = (dict(bare_bindings), dict(module_aliases))
    for name in _contextual_binding_names(call, parents):
        _shadow_binding(name, bare_bindings, module_aliases)
    return bare_bindings, module_aliases
def _net_import_bindings(nodes, targets: frozenset) -> tuple[dict, dict]:
    bare_bindings: dict[str, str | None] = {}
    module_aliases: dict[str, str | None] = {}
    for _imp in nodes:
        if isinstance(_imp, ast.ImportFrom):
            _register_from_import(_imp, bare_bindings, module_aliases, targets)
        elif isinstance(_imp, ast.Import):
            _register_module_import(_imp, module_aliases)
    return bare_bindings, module_aliases
class _ConditionalBindingEvent(NamedTuple):
    position: tuple[int, int]
    control: tuple[tuple[int, str], ...]
    kind: str
    value: Any = None
def _is_try_statement(node) -> bool:
    return isinstance(node, ast.Try) or node.__class__.__name__ == 'TryStar'
def _loop_has_own_break(loop) -> bool:
    stack = list(loop.body)
    while stack:
        current = stack.pop()
        if isinstance(current, ast.Break):
            return True
        if isinstance(current, (ast.For, ast.AsyncFor, ast.While,
                                ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef, ast.Lambda)):
            continue
        stack.extend(ast.iter_child_nodes(current))
    return False
def _boolop_operand_is_conditional(node, child) -> bool:
    # 用显式定位代替「for + break + else: return」：后者依赖隐式控制流，
    # 任何增量重构都可能把 index 留在未绑定状态。
    index = next(
        (position for position, value in enumerate(node.values)
         if value is child), None)
    if index is None or index == 0:
        return False
    for previous in node.values[:index]:
        if not isinstance(previous, ast.Constant):
            return True
        truth = bool(previous.value)
        if ((isinstance(node.op, ast.And) and not truth)
                or (isinstance(node.op, ast.Or) and truth)):
            return True
    return False
def _binding_control_path(node, scope, parents) -> tuple[tuple[int, str], ...]:
    path: list[tuple[int, str]] = []
    child = node
    below = None
    current = parents.get(id(node))
    while current is not None and current is not scope:
        branch = None
        if isinstance(current, ast.If):
            if child in current.body:
                branch = 'body'
            elif child in current.orelse:
                branch = 'else'
        elif isinstance(current, ast.IfExp):
            if child is current.body:
                branch = 'body'
            elif child is current.orelse:
                branch = 'else'
        elif (isinstance(current, ast.BoolOp)
              and _boolop_operand_is_conditional(current, child)):
            branch = 'short-circuit'
        elif (isinstance(current, _COMPREHENSION_NODES)
              and not _is_outer_comprehension_iter(current, child, below)):
            branch = 'body'
        elif isinstance(current, (ast.For, ast.AsyncFor, ast.While)):
            if child in current.body:
                branch = 'body'
            elif child in current.orelse and _loop_has_own_break(current):
                branch = 'else'
        elif _is_try_statement(current):
            if child in current.handlers:
                branch = f'handler-{current.handlers.index(child)}'
            elif ((child in current.body or child in current.orelse)
                  and current.handlers):
                branch = 'body'
        elif isinstance(current, ast.Match) and child in current.cases:
            branch = f'case-{current.cases.index(child)}'
        if branch is not None:
            path.append((id(current), branch))
        below = child
        child = current
        current = parents.get(id(current))
    path.reverse()
    return tuple(path)
def _loop_target_owner(node, parents):
    current = parents.get(id(node))
    while current is not None and not isinstance(current, ast.stmt):
        current = parents.get(id(current))
    if not isinstance(current, (ast.For, ast.AsyncFor)):
        return None
    return current if any(node is item for item in walk_nodes(current.target)) else None
def _control_paths_compatible(left, right) -> bool:
    for (left_id, left_branch), (right_id, right_branch) in zip(left, right):
        if left_id == right_id and left_branch != right_branch:
            return False
    return True
def _is_control_prefix(prefix, path) -> bool:
    return len(prefix) <= len(path) and path[:len(prefix)] == prefix
def _match_has_irrefutable_last_case(node) -> bool:
    if not node.cases or node.cases[-1].guard is not None:
        return False
    pattern = node.cases[-1].pattern
    return isinstance(pattern, ast.MatchAs) and pattern.pattern is None
def _conditional_branch_options(node) -> tuple[str, ...]:
    if isinstance(node, (ast.If, ast.IfExp, ast.For, ast.AsyncFor, ast.While)):
        return 'body', 'else'
    if _is_try_statement(node):
        if node.handlers:
            return ('body', *(f'handler-{index}'
                              for index in range(len(node.handlers))))
        return ()
    if isinstance(node, ast.Match):
        cases = tuple(f'case-{index}' for index in range(len(node.cases)))
        return cases if _match_has_irrefutable_last_case(node) else (*cases, 'missing')
    return ()
def _conditional_coverage(events, prefix, nodes_by_id) -> bool:
    if any(event.control == prefix for event in events):
        return True
    depth = len(prefix)
    groups: dict[int, list[_ConditionalBindingEvent]] = {}
    for event in events:
        if (len(event.control) > depth
                and event.control[:depth] == prefix):
            node_id = event.control[depth][0]
            groups.setdefault(node_id, []).append(event)
    for node_id, group in groups.items():
        options = _conditional_branch_options(nodes_by_id.get(node_id))
        if not options:
            continue
        if all(_conditional_coverage(
                group, (*prefix, (node_id, branch)), nodes_by_id)
                for branch in options):
            return True
    return False
def _common_control_prefix(left, right):
    length = 0
    for left_item, right_item in zip(left, right):
        if left_item != right_item:
            break
        length += 1
    return left[:length]
def _binding_event_covered(event, later, nodes_by_id) -> bool:
    relevant = [candidate for candidate in later
                if _control_paths_compatible(event.control, candidate.control)]
    if any(_is_control_prefix(candidate.control, event.control)
           for candidate in relevant):
        return True
    nested = [candidate for candidate in relevant
              if _is_control_prefix(event.control, candidate.control)]
    if _conditional_coverage(nested, event.control, nodes_by_id):
        return True
    sequential_prefixes = {
        _common_control_prefix(event.control, candidate.control)
        for candidate in relevant
        if not _is_control_prefix(event.control, candidate.control)}
    return any(
        _conditional_coverage(relevant, prefix, nodes_by_id)
        for prefix in sequential_prefixes)
def _literal_assignment_value(node, parents):
    if not isinstance(node, ast.Name):
        return None
    parent = parents.get(id(node))
    if (isinstance(parent, ast.Assign)
            and any(node is target for target in parent.targets)):
        return parent.value
    if isinstance(parent, ast.AnnAssign) and node is parent.target:
        return parent.value
    if isinstance(parent, ast.NamedExpr) and node is parent.target:
        return parent.value
    return None
def _local_conditional_events(scope, name, targets, parents,
                              literal_values: bool = False
                              ) -> list[_ConditionalBindingEvent]:
    events: list[_ConditionalBindingEvent] = []
    for node in _iter_scope_binding_nodes(scope):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            if literal_values:
                has_star = (isinstance(node, ast.ImportFrom)
                            and any(alias.name == '*' for alias in node.names))
                if name not in _binding_names(node) and not has_star:
                    continue
                kind, value = 'shadow', None
            else:
                bare, aliases = _net_import_bindings([node], targets)
                if name in bare:
                    kind, value = 'bare', bare[name]
                elif name in aliases:
                    kind, value = 'alias', aliases[name]
                else:
                    continue
        else:
            if name not in _binding_names(node):
                continue
            if literal_values:
                value = _literal_assignment_value(node, parents)
                parent = parents.get(id(node))
                if (value is None and isinstance(parent, ast.AnnAssign)
                        and parent.value is None and node is parent.target):
                    continue
                kind = 'value' if value is not None else 'shadow'
            else:
                kind, value = 'shadow', None
        control = _binding_control_path(node, scope, parents)
        loop = _loop_target_owner(node, parents)
        if loop is not None:
            control = (*_binding_control_path(loop, scope, parents),
                       (id(loop), 'body'))
        events.append(_ConditionalBindingEvent(
            _binding_position(node, parents), control, kind, value))
    return events
def _surviving_binding_choices(events, nodes_by_id) -> set[tuple[str, str | None]]:
    choices: set[tuple[str, str | None]] = set()
    for index, event in enumerate(events):
        later = [candidate for candidate in events[index + 1:]
                 if candidate.position > event.position]
        if not _binding_event_covered(event, later, nodes_by_id):
            choices.add((event.kind, event.value))
    return choices
def _scope_conditional_choices(scope, call, parents, targets, immediate,
                               name, incoming, literal_values: bool = False
                               ) -> set[tuple[str, Any]]:
    events = [_ConditionalBindingEvent((-2, -2), (), kind, value)
              for kind, value in sorted(
                  incoming, key=lambda item: (
                      item[0], item[1] if isinstance(item[1], str) else ''))]
    local = _local_conditional_events(
        scope, name, targets, parents, literal_values=literal_values)
    has_local_binding = bool(local) or (
        literal_values and any(
            name in _binding_names(node)
            for node in _iter_scope_binding_nodes(scope)))
    is_function = isinstance(scope, _FUNCTION_SCOPE_NODES)
    if (is_function and name not in _scope_global_names(scope)
            and (has_local_binding or name in _scope_parameter_names(scope))):
        events.append(_ConditionalBindingEvent((-1, -1), (), 'shadow'))
    events.extend(local)
    events.sort(key=lambda event: event.position)
    call_position = (call.lineno, call.col_offset)
    call_control = _binding_control_path(call, scope, parents)
    nodes_by_id = {id(scope): scope}
    nodes_by_id.update({id(node): node for node in parents.values()})
    eligible = []
    for event in events:
        if not _control_paths_compatible(event.control, call_control):
            continue
        common = _common_control_prefix(event.control, call_control)
        comprehension_path = any(
            isinstance(nodes_by_id.get(node_id), _COMPREHENSION_NODES)
            for node_id, _branch in common)
        if ((immediate or comprehension_path)
                and event.position >= call_position):
            continue
        eligible.append(event._replace(control=event.control[len(common):]))
    return _surviving_binding_choices(eligible, nodes_by_id)
def _call_conditional_choices(call, parents, targets, name,
                              literal_values: bool = False):
    scopes = list(reversed(iter_evaluation_scope_chain(call, parents)))
    choices: set[tuple[str, Any]] = {('missing', None)}
    module_choices = set(choices)
    for index, scope in enumerate(scopes):
        if (not isinstance(scope, ast.Module)
                and name in _scope_global_names(scope, global_only=True)):
            choices = set(module_choices)
        choices = _scope_conditional_choices(
            scope, call, parents, targets,
            immediate=index == len(scopes) - 1,
            name=name, incoming=choices, literal_values=literal_values)
        if isinstance(scope, ast.Module):
            module_choices = set(choices)
    if name in _contextual_binding_names(call, parents):
        return {('shadow', None)}
    return choices
def _literal_binding_values(call, parents, name) -> list:
    choices = _call_conditional_choices(
        call, parents, frozenset(), name, literal_values=True)
    values = [value for kind, value in choices
              if kind == 'value' and value is not None]
    return sorted(
        values,
        key=lambda value: (
            getattr(value, 'lineno', 0), getattr(value, 'col_offset', 0),
            getattr(value, 'end_lineno', 0), getattr(value, 'end_col_offset', 0)))
def _attribute_call_parts(call: ast.Call) -> tuple[str, list[str]]:
    parts: list[str] = []
    node = call.func
    while isinstance(node, ast.Attribute):
        parts.append(node.attr)
        node = node.value
    if not isinstance(node, ast.Name):
        return '', []
    parts.append(node.id)
    parts.reverse()
    return node.id, parts
def _reachable_dotted_call_names(call, parents, targets, builtin_names):
    if isinstance(call.func, ast.Attribute):
        name, parts = _attribute_call_parts(call)
        if not name:
            return
        choices = _call_conditional_choices(call, parents, targets, name)
        for kind, value in sorted(
            choices, key=lambda item: (item[0], item[1] or '')):
            if kind == 'shadow' or (kind in {'bare', 'alias'} and value is None):
                continue
            root = value if kind == 'alias' else name
            yield '.'.join([root, *parts[1:]])
        return
    if not isinstance(call.func, ast.Name):
        return
    name = call.func.id
    choices = _call_conditional_choices(call, parents, targets, name)
    for kind, value in sorted(
            choices, key=lambda item: (item[0], item[1] or '')):
        if kind == 'bare' and value is not None:
            yield value
        elif kind == 'missing' and name in builtin_names:
            yield f'builtins.{name}'
def _resolve_dotted_call_name(call: ast.Call, module_aliases: dict,
                              bare_bindings: dict) -> str | None:
    if isinstance(call.func, ast.Attribute):
        dotted_parts: list[str] = []
        node = call.func
        while isinstance(node, ast.Attribute):
            dotted_parts.append(node.attr)
            node = node.value
        if isinstance(node, ast.Name):
            if node.id in module_aliases:
                root = module_aliases[node.id]
                if root is None:
                    return None
            elif bare_bindings.get(node.id, node.id) is None:
                return None
            else:
                root = node.id
            dotted_parts.append(root)
            return '.'.join(reversed(dotted_parts))
        return None
    if isinstance(call.func, ast.Name) and call.func.id in bare_bindings:
        return bare_bindings[call.func.id]
    return None
_DANGEROUS_CALL_ATTRS = frozenset({'eval', 'exec', 'system', 'popen'}) | frozenset(
    name.rsplit('.', 1)[-1] for name in _SC_SUBPROCESS_SHELL_FUNCS)
def _call_candidate_names(nodes, targets, initial_names) -> set[str]:
    names = set(initial_names)
    for node in nodes:
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            bare, _aliases = _net_import_bindings([node], targets)
            names.update(name for name, value in bare.items()
                         if value is not None)
    return names
def _imported_module_roots(nodes, targets) -> set[str]:
    roots: set[str] = set()
    for node in nodes:
        if not isinstance(node, (ast.Import, ast.ImportFrom)):
            continue
        _bare, aliases = _net_import_bindings([node], targets)
        roots.update(name for name, value in aliases.items()
                     if value is not None)
    return roots
def _attr_root_name(func: ast.Attribute) -> str:
    node: ast.expr = func.value
    while isinstance(node, ast.Attribute):
        node = node.value
    return node.id if isinstance(node, ast.Name) else ''
def _is_call_candidate(node, names: set[str], attrs,
                       roots) -> bool:
    func = getattr(node, 'func', None)
    if isinstance(func, ast.Name):
        return func.id in names
    if isinstance(func, ast.Attribute):
        if func.attr not in attrs:
            return False
        return not roots or _attr_root_name(func) in roots
    return False
def _iter_resolved_target_calls(tree, targets, candidate_attrs, *,
                                builtin_names=frozenset(), nodes=None,
                                parents=None):
    parents = build_parent_map(tree) if parents is None else parents
    nodes = tree_nodes(tree) if nodes is None else nodes
    candidate_names = _call_candidate_names(nodes, targets, builtin_names)
    roots = _imported_module_roots(nodes, targets) | {
        target.split('.')[0] for target in targets}
    for node in nodes:
        if not isinstance(node, ast.Call):
            continue
        if not _is_call_candidate(node, candidate_names, candidate_attrs,
                                  roots):
            continue
        bare, aliases = _call_scope_bindings(node, parents, targets)
        dotted = _resolve_dotted_call_name(node, aliases, bare)
        if (dotted is None and isinstance(node.func, ast.Name)
                and node.func.id in builtin_names
                and node.func.id not in bare
                and node.func.id not in aliases):
            dotted = f'builtins.{node.func.id}'
        yield node, dotted
        seen = {dotted}
        for reachable in _reachable_dotted_call_names(
                node, parents, targets, builtin_names):
            if reachable in targets and reachable not in seen:
                seen.add(reachable)
                yield node, reachable
def count_dangerous_call_risks(tree) -> tuple[int, int, int]:
    eval_count = exec_count = shell_count = 0
    for node, dotted in _iter_resolved_target_calls(
            tree, _SC_DANGEROUS_IMPORT_FUNCS, _DANGEROUS_CALL_ATTRS,
            builtin_names=frozenset({'eval', 'exec'})):
        if dotted == 'builtins.eval':
            eval_count += 1
        elif dotted == 'builtins.exec':
            exec_count += 1
        elif (dotted in ('os.system', 'os.popen')
              or (dotted in _SC_SUBPROCESS_SHELL_FUNCS
                  and any(is_shell_true_keyword(kw)
                          for kw in node.keywords))):
            shell_count += 1
    return eval_count, exec_count, shell_count
def _has_net_timeout(call: ast.Call, dotted: str, parents=None) -> bool:
    if any(kw.arg == 'timeout' and _timeout_value_effective_at_call(
            kw.value, call, parents) for kw in call.keywords):
        return True
    slot = _SC_POSITIONAL_TIMEOUT_SLOTS.get(dotted)
    return (slot is not None and len(call.args) > slot
            and _timeout_value_effective_at_call(
                call.args[slot], call, parents))
_NET_CALL_ATTRS = frozenset(
    name.rsplit('.', 1)[-1] for name in NETWORK_CALL_TARGETS)
def iter_network_calls_no_timeout(
        tree: ast.AST) -> Iterator[tuple[ast.Call, str]]:
    parents = build_parent_map(tree)
    for call, dotted in _iter_resolved_target_calls(
            tree, NETWORK_CALL_TARGETS, _NET_CALL_ATTRS, parents=parents):
        if dotted not in NETWORK_CALL_TARGETS:
            continue
        if _has_net_timeout(call, dotted, parents):
            continue
        yield call, dotted
def _scan_net_calls_no_timeout(tree, rel_path: str) -> list:
    out: list = []
    for _call, _dotted in iter_network_calls_no_timeout(tree):
        out.append(SecurityIssue(
            severity=Severity.HIGH, category='供应链安全-网络调用',
            description=f'文件 {rel_path}:{_call.lineno} 存在网络调用: {_dotted}()（未设置 timeout）',
            location=f'{rel_path}:{_call.lineno}',
            recommendation='为网络调用添加 timeout 参数并校验响应，或使用官方包管理器'))
    return out
def _append_net_issues(report: SupplyChainReport, skill_dir: str,
                      cache, scan_errors: list[str] | None = None) -> None:
    base = Path(skill_dir)
    for fpath in iter_scan_scope_files(skill_dir):
        if is_test_scan_target(fpath, base, _rel_project_path(fpath, base)):
            _log.debug('[SCOPE-SKIP] 网络调用检测跳过测试资产: %s', fpath)
            continue
        try:
            src, _tree = read_scan_source_tree(fpath, cache)
        except OSError as e:
            _log.warning('check_supply_chain: 跳过不可读文件: %s: %s', fpath, e)
            mark_section_degraded('供应链网络调用源码读取')
            _record_scan_error(scan_errors, f'{fpath.name} 读取失败，网络规则未执行')
            continue
        rel_path = _rel_project_path(fpath, base)
        if _tree is None:
            _tree = cached_scan_ast(str(fpath), src, None)
        if _tree is None:
            _log.debug('check_supply_chain: 跳过语法错误文件 %s（AST 网络调用检测）',
                       rel_path)
            mark_section_degraded('供应链网络调用语法解析')
            _record_scan_error(scan_errors, f'{rel_path} 语法错误，网络规则未执行')
            continue
        report.network_calls.extend(
            _scan_net_calls_no_timeout(_tree, rel_path))
def _classify_risk(issues: list) -> str:
    severities = {issue.severity for issue in issues}
    for severity, level in ((Severity.CRITICAL, 'critical'),
                            (Severity.HIGH, 'high'),
                            (Severity.MEDIUM, 'medium')):
        if severity in severities:
            return level
    return 'low'
def check_supply_chain(skill_dir: str, cache: SharedCache | None=None) -> SupplyChainReport:
    normalized = coerce_skill_dir(skill_dir)
    report = SupplyChainReport(
        skill_name=(os.path.basename(os.path.abspath(normalized))
                    if normalized else ''),
        skill_path=normalized,
    )
    if not normalized or not Path(normalized).is_dir():
        report.passed = False
        report.risk_level = 'unknown'
        return report
    def _run_channel(label, invoke):
        error_count_before = len(report.scan_errors)
        result = invoke()
        if (not result[0] and not result[1]
                and len(report.scan_errors) == error_count_before):
            _record_scan_error(
                report.scan_errors, f'{label}通道未完成且未返回具体问题')
        return result
    sensitive_result = _run_channel(
        '敏感路径', lambda: check_sensitive_paths(
            normalized, cache=cache, _scan_errors=report.scan_errors))
    dangerous_result = _run_channel(
        '危险命令', lambda: check_dangerous_commands(
            normalized, cache=cache, _scan_errors=report.scan_errors))
    secret_result = _run_channel(
        'Secret泄露', lambda: check_secret_leaks(
            normalized, cache=cache, _scan_errors=report.scan_errors))
    remote_result = _run_channel(
        '远程脚本', lambda: check_remote_scripts(
            normalized, cache=cache, _scan_errors=report.scan_errors))
    report.sensitive_path_access = sensitive_result[1]
    report.dangerous_commands = dangerous_result[1]
    report.secret_leaks = secret_result[1]
    report.remote_scripts = remote_result[1]
    _append_net_issues(report, normalized, cache, report.scan_errors)
    all_issues = report.all_issues()
    report.total_issues = len(all_issues)
    report.passed = report.total_issues == 0 and not report.scan_errors
    report.risk_level = ('unknown' if report.scan_errors
                         else _classify_risk(all_issues))
    return report
def format_supply_chain_report(report: SupplyChainReport) -> str:
    lines = [
        '=' * 60,
        f'供应链安全诊断: {report.skill_name}',
        '=' * 60,
        f'路径: {report.skill_path}',
        f"通过: {'是' if report.passed else '否'}",
        f'风险等级: {report.risk_level.upper()}',
        f'问题总数: {report.total_issues}',
        '',
    ]
    if report.scan_errors:
        lines.extend(['--- 扫描不完整 ---',
                      *(f'  - {error}' for error in report.scan_errors), ''])
    sections = [
        ('敏感路径访问', report.sensitive_path_access),
        ('危险命令', report.dangerous_commands),
        ('远程脚本', report.remote_scripts),
        ('网络调用无超时', report.network_calls),
        ('Secret泄露', report.secret_leaks),
    ]
    for title, issues in sections:
        if issues:
            lines.append(f'--- {title} ({len(issues)}个) ---')
            for issue in issues[:5]:
                lines.append(f'  [{issue.severity.value}] {issue.description[:70]}')
                lines.append(f'    建议: {issue.recommendation[:70]}')
            lines.append('')
    lines.append('=' * 60)
    return '\n'.join(lines)
def file_compiles_strict(fp) -> bool:
    try:
        compile(read_source_strict(str(fp)), str(fp), 'exec')
        return True
    except (OSError, SyntaxError, LookupError, UnicodeDecodeError,
            ValueError, MemoryError, RecursionError) as _e:
        log_swallowed(
            __name__, _e,
            context=f'file_compiles_strict:{type(_e).__name__}')
        return False
_OPS_LEVEL_SEVERITY = {'block': Severity.CRITICAL, 'error': Severity.HIGH}
def _coerce_count(value, fallback: int = 0) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        return fallback
    return value
def _g3_detail_file(detail) -> str:
    fp, sep, _ = str(detail).partition(': ')
    return fp.strip() if sep else ''
def _g3_detail_files(details) -> list[str]:
    files: list[str] = []
    for detail in details or []:
        fp = _g3_detail_file(detail)
        if fp and fp not in files:
            files.append(fp)
    return files
def _g3_terminal_recheck(details: list) -> tuple[bool, list[str]]:
    files = _g3_detail_files(details)
    if not files:
        return False, []
    if any(not _g3_detail_file(detail) for detail in details):
        return False, []
    still_bad = [fp for fp in files if not file_compiles_strict(fp)]
    return (False, still_bad) if still_bad else (True, files)
def _ops_details_norm(_details_raw) -> list:
    if isinstance(_details_raw, (list, tuple)):
        return list(_details_raw)
    if isinstance(_details_raw, str) and _details_raw.strip():
        return [_details_raw]
    return []
def _ops_level_severity(level) -> Severity:
    if isinstance(level, str):
        return _OPS_LEVEL_SEVERITY.get(level, Severity.MEDIUM)
    return Severity.MEDIUM
def _ops_details_digest(details: list) -> str:
    if not details:
        return ''
    text = '; '.join(str(_d) for _d in details[:3])
    if len(details) > 3:
        text += '; ...等' + str(len(details)) + '项'
    return text
def _ops_g3_verdict(guard_name: str, level, details: list) -> tuple[bool, list]:
    if guard_name != 'G3' or level != 'block' or not details:
        return False, []
    healed, files = _g3_terminal_recheck(details)
    return (healed, files) if healed else (False, files)
def _ops_location(sp: Path, guard_name: str, details: list,
                  transient: bool, failing: list[str]) -> str:
    if guard_name == 'G3' and details and not transient:
        if failing:
            return failing[0]
        return _g3_detail_file(details[0]) or str(sp)
    return str(sp)
def _ops_issue_message(_message: str, _transient: bool, _failing: list,
                       _details) -> str:
    if _transient:
        _message = (_message + '（终态复验已通过：' + ', '.join(_failing)
                    + '，判定为诊断窗口内并行写入瞬态，非终态问题）')
    elif _failing:
        _message = _message + '（终态复验仍失败：' + ', '.join(_failing) + '）'
    _detail_txt = _ops_details_digest(_details)
    if _detail_txt:
        _message = _message + ' | 明细: ' + _detail_txt
    return _message
def _ops_issue_from_detail(sp: Path, _issue_detail,
                           report: SecurityReport) -> bool:
    if not isinstance(_issue_detail, dict):
        _log.warning('collect_delivery_issues: 跳过撕裂 issue 条目: %r',
                     _issue_detail)
        mark_section_degraded('安全操作条目跳过')
        return False
    _guard_name = (normalize_issue_suggestion(_issue_detail.get('guard', 'unknown'))
                   or 'unknown')
    _level = _issue_detail.get('level', 'warn')
    _message = normalize_issue_suggestion(_issue_detail.get('message', ''))
    _details = _ops_details_norm(_issue_detail.get('details'))
    _sev = _ops_level_severity(_level)
    _transient, _failing = _ops_g3_verdict(_guard_name, _level, _details)
    _loc = _ops_location(
        sp, _guard_name, _details, _transient, _failing)
    if _transient:
        _sev = Severity.MEDIUM
    _message = _ops_issue_message(_message, _transient, _failing, _details)
    report.issues.append(SecurityIssue(
        severity=_sev, category='安全操作-' + _guard_name,
        description=_guard_name + ': ' + _message, location=_loc,
        recommendation='修复守卫 ' + _guard_name + ' 检测到的问题'))
    return _transient
def _ops_block_issue(sp: Path, ops_result,
                     _transient_g3_count: int) -> SecurityIssue:
    _raw_blockers = ops_result.get('blockers')
    _n_blockers = _coerce_count(
        _raw_blockers, _coerce_count(ops_result.get('failed'), 0))
    _blockers_is_count = (isinstance(_raw_blockers, int)
                          and not isinstance(_raw_blockers, bool))
    if (_transient_g3_count > 0 and _blockers_is_count
            and _transient_g3_count >= _n_blockers):
        return SecurityIssue(
            severity=Severity.MEDIUM, category='安全操作-交付阻断',
            description='安全操作阻断级问题经终态复验判定为并行写入瞬态'
                        '（G3 语法错误已自愈），无终态阻断', location=str(sp),
            recommendation='无需修复；若持续出现请检查并行写入进程的写入原子性')
    return SecurityIssue(
        severity=Severity.CRITICAL, category='安全操作-交付阻断',
        description='安全操作检测到阻断级问题: ' + str(_n_blockers) + ' 项',
        location=str(sp),
        recommendation='修复安全操作检测到的阻断项后重新审计')
def collect_delivery_issues(sp: Path, report, cache=None) -> None:
    with degraded_section('安全操作'):
        ops_result = safe_delivery_check(target_path=str(sp), cache=cache)
        _transient_g3_count = 0
        for _issue_detail in (ops_result.get('issues') or []):
            if _ops_issue_from_detail(sp, _issue_detail, report):
                _transient_g3_count += 1
        if ops_result.get('blocked'):
            report.issues.append(
                _ops_block_issue(sp, ops_result, _transient_g3_count))

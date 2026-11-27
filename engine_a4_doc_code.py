from __future__ import annotations

import ast
import builtins as _builtins_mod
import hashlib
import keyword
import logging
import os
import re
from dataclasses import dataclass, field
from functools import lru_cache
from itertools import chain
from typing import Any, ClassVar, NamedTuple

from jwsgj.build_text_document import (
    ENTRY_DOC_NAME,
    iter_fence_state,
    resolve_entry_document,
)
from jwsgj.build_text_frontmatter import locate_frontmatter_body_start
from jwsgj.diag_shared_ast_nodes import (
    _prune_non_import_time_branches,
    iter_unpack_target_names,
)
from jwsgj.diag_shared_source_core import read_source
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    RUNTIME_DIR_NAME,
    is_backup_like_dir,
    is_diagnosis_out_of_scope,
    is_scan_py_name,
    prune_ignore_dirs,
)
from jwsgj.shared_cache import CacheNotWarmedError
from jwsgj.skill_profile import detect_layout

__all__ = [
    'CodeExport',
    'ConsistencyFinding',
    'DocCodeConsistencyAnalyzer',
    'DocEntry',
    'PackageExportScanner',
    'RuleIdRegistry',
    'attr_call_on_pkg_host',
    'attr_on_bare_func_host',
    'extract_all_info',
    'find_close_triple',
    'find_open_triple',
    'from_import_module',
    'init_has_dynamic_export',
    'is_plain_import',
    'is_standalone_call_ctx',
    'is_try_statement',
    'merge_import_continuations',
    'prune_scan_dirs',
    'strip_line_comment',
    'strip_string_literals',
]
logger = logging.getLogger(__name__)
logger.info(
    "engine_a4_doc_code A14 文档-代码一致性引擎已加载: %d 项导出", len(__all__))
_IMPORT_WORD_RE = re.compile(r"\bimport\b")
_INLINE_SPAN_RE = re.compile(r"`([^`]+)`")
_INLINE_NAME_RE = re.compile(
    r"^(?:[A-Za-z_]\w*\.)*([A-Za-z_]\w*)(?:\(.*\))?$")
_INLINE_CALL_RE = re.compile(r"(?<![\w.])([A-Za-z_]\w*)\s*\(")
_REGEX_CACHE_MAXSIZE = 512
def _inline_claim_names(span: str) -> list[str]:
    text = span.strip()
    whole = _INLINE_NAME_RE.match(text)
    if whole:
        return [whole.group(1)]
    return [call.group(1) for call in _INLINE_CALL_RE.finditer(text)]
_BARE_API_ASSIGN_RE = re.compile(r"^(\w+)\s*=\s*([a-zA-Z_]\w*)$")
_CALL_API_ASSIGN_RE = re.compile(r"^(\w+)\s*=\s*([A-Za-z_]\w*)\s*\(")
_DEF_LINE_RE = re.compile(r"^(?:async\s+)?def\s+([A-Za-z_]\w*)\s*\(")
_CLASS_LINE_RE = re.compile(r"^class\s+([A-Za-z_]\w*)")
_BUILTIN_FUNC_NAMES = frozenset(
    n for n in dir(_builtins_mod) if not n.startswith("_"))
_STDLIB_FUNC_NAMES = frozenset({
    "deepcopy",
    "getcwd", "chdir", "mkdir", "makedirs", "rmtree", "remove", "unlink",
    "rename", "isdir", "isfile", "islink", "isabs", "abspath", "basename",
    "dirname", "splitext", "normpath", "realpath", "relpath", "exists",
    "lexists", "expanduser", "expandvars", "walk",
    "sleep",
    "dumps", "loads",
    "urlopen", "quote", "unquote", "urlparse", "parse_qs",
    "sha256", "md5", "b64encode", "b64decode",
})
_FROM_IMPORT_TAIL_RE = re.compile(
    r"^from\s+[\w.]+\s+import\s+(.+)$"
)
_IMPORT_TAIL_RE = re.compile(r"^import\s+(.+)$")
_BOX_DRAWING_CHARS = "─│┌┐└┘├┤┬┴┼═║┆┊┈┉"
_FROM_IMPORT_LINE_RE = re.compile(
    r"^from\s+([\w.]+)\s+import\s+[\w(*\s,\\]"
)
_PLAIN_IMPORT_LINE_RE = re.compile(
    r"^import\s+[\w.,\s\\]+"
)
def from_import_module(line: str) -> str | None:
    match = _FROM_IMPORT_LINE_RE.match(line)
    return match.group(1) if match else None
def is_plain_import(line: str) -> bool:
    return bool(_PLAIN_IMPORT_LINE_RE.match(line))
def _skip_quoted(line: str, i: int) -> tuple[int, bool]:
    trip = line[i:i + 3]
    if trip in ('"""', "'''"):
        close = find_close_triple(line, trip, i + 3)
        if close == -1:
            return len(line), True
        return close + 3, False
    return _skip_single_quoted(line, i), False
def strip_line_comment(line: str) -> str:
    i, n = 0, len(line)
    while i < n:
        ch = line[i]
        if ch in ("'", '"'):
            i, _unclosed = _skip_quoted(line, i)
            if _unclosed:
                return line
            continue
        if ch == "#":
            return line[:i]
        i += 1
    return line
def _skip_single_quoted(line: str, start: int) -> int:
    quote = line[start]
    i, n = start + 1, len(line)
    while i < n and line[i] != quote:
        if line[i] == "\\":
            i += 1
        i += 1
    return min(i + 1, n)
def strip_string_literals(line: str) -> str:
    i, n = 0, len(line)
    out: list[str] = []
    while i < n:
        ch = line[i]
        if ch == "\\":
            out.append(line[i:i + 2])
            i += 2
            continue
        if ch in ("'", '"'):
            end, _unclosed = _skip_quoted(line, i)
            out.append(" " * (end - i))
            i = end
            continue
        out.append(ch)
        i += 1
    return "".join(out)
def _claim_scan_text(context: str) -> str | None:
    if any(ch in context for ch in _BOX_DRAWING_CHARS):
        return None
    return strip_string_literals(strip_line_comment(context))
_FSTRING_START_RE = re.compile(
    r"(?i)(?<![A-Za-z0-9_])(?:fr|rf|f)['\"]")
_FSTRING_PARSE_EXC = (SyntaxError, ValueError, RecursionError, MemoryError)
def _fstring_expression_sources(code: str) -> list[str]:
    """提取 f-string 中真正执行的表达式，不把普通字符串当代码。"""
    if _FSTRING_START_RE.search(code) is None:
        return []
    try:
        tree = ast.parse(code)
        return [ast.unparse(node.value) for node in walk_nodes(tree)
                if isinstance(node, ast.FormattedValue)]
    except _FSTRING_PARSE_EXC as exc:
        logger.debug("f-string 补充解析失败，沿用常规文本扫描: %s: %s",
                     type(exc).__name__, exc)
        return []
def _iter_code_statements(line: str):
    scan_text = strip_string_literals(strip_line_comment(line))
    start = 0
    for index, char in enumerate(scan_text):
        if char != ";":
            continue
        statement = line[start:index].strip()
        if statement:
            yield statement
        start = index + 1
    statement = line[start:].strip()
    if statement:
        yield statement
@lru_cache(maxsize=_REGEX_CACHE_MAXSIZE)
def _standalone_call_re(name: str) -> re.Pattern:
    return re.compile(r"(?<![\w.])" + re.escape(name) + r"\s*\(")
def is_standalone_call_ctx(context: str, name: str) -> bool:
    code_ctx = _claim_scan_text(context)
    if code_ctx is None:
        return False
    return bool(_standalone_call_re(name).search(code_ctx))
def _code_paren_delta(line: str) -> int:
    ctx = strip_string_literals(strip_line_comment(line))
    return ctx.count("(") - ctx.count(")")
def _import_seg_state(stripped: str) -> tuple[str, int, bool]:
    code_seg = strip_line_comment(stripped).strip()
    return (code_seg.rstrip("\\").strip(),
            _code_paren_delta(code_seg),
            code_seg.endswith("\\"))
class _ImportLineBuffer:
    _MAX_PENDING = 100
    def __init__(self):
        self._pending: list[str] = []
        self._pending_no = 0
        self._depth = 0
        self._cont = False
    def push(self, line_no: int, line: str) -> list[tuple[int, str]]:
        if not self._pending:
            return self._open(line_no, line)
        return self._absorb(line_no, line)
    def _open(self, line_no: int, line: str) -> list[tuple[int, str]]:
        stripped = line.strip()
        if not self._is_import_start(stripped):
            return [(line_no, line)]
        seg_first, depth, cont = _import_seg_state(stripped)
        if depth <= 0 and not cont:
            return [(line_no, stripped)]
        self._pending, self._pending_no = [seg_first], line_no
        self._depth, self._cont = depth, cont
        return []
    def _absorb(self, line_no: int, line: str) -> list[tuple[int, str]]:
        stripped = line.strip()
        if len(self._pending) >= self._MAX_PENDING:
            return self.finish() + [(line_no, line)]
        if stripped.startswith("#"):
            return []
        seg, seg_delta, cont = _import_seg_state(stripped)
        self._pending.append(seg)
        self._depth += seg_delta
        self._cont = cont
        if self._depth <= 0 and not cont:
            return self.finish()
        return []
    def finish(self) -> list[tuple[int, str]]:
        if not self._pending:
            return []
        merged = [(self._pending_no, " ".join(self._pending))]
        self._pending, self._pending_no = [], 0
        self._depth, self._cont = 0, False
        return merged
    @staticmethod
    def _is_import_start(stripped: str) -> bool:
        return from_import_module(stripped) is not None or is_plain_import(stripped)
def merge_import_continuations(
        code_block_lines: list[tuple[int, str]]) -> list[tuple[int, str]]:
    buffer = _ImportLineBuffer()
    logical: list[tuple[int, str]] = []
    in_triple = ""
    for line_no, line in code_block_lines:
        if in_triple:
            close = find_close_triple(line, in_triple)
            if close == -1:
                logical.append((line_no, line))
                continue
            logical.append((line_no, line[:close + 3]))
            line = line[close + 3:].lstrip(" ;")
            in_triple = ""
            if not line:
                continue
        logical.extend(buffer.push(line_no, line))
        in_triple = find_open_triple(line)
    logical.extend(buffer.finish())
    return logical
def find_close_triple(line: str, trip: str, start: int = 0) -> int:
    i, n = start, len(line)
    while i < n:
        if line[i] == "\\":
            i += 2
            continue
        if line[i:i + 3] == trip:
            return i
        i += 1
    return -1
def find_open_triple(line: str) -> str:
    i, n = 0, len(line)
    while i < n:
        ch = line[i]
        if ch == "\\":
            i += 2
            continue
        if ch == "#":
            return ""
        if ch in ("'", '"'):
            end, _unclosed = _skip_quoted(line, i)
            if _unclosed:
                return line[i:i + 3]
            i = end
            continue
        i += 1
    return ""
_FUNCTION_EXPORT_TYPES = frozenset({"function", "async_function"})
_CALLABLE_EXPORT_TYPES = _FUNCTION_EXPORT_TYPES | {"class"}
_ENTRY_MODULE_REL = "__init__.py"
_COMMON_OBJ_METHODS = frozenset({
    "get", "keys", "values", "items", "pop", "popitem", "update",
    "setdefault", "copy", "clear", "fromkeys",
    "append", "extend", "insert", "remove", "sort", "reverse",
    "index", "count",
    "split", "rsplit", "splitlines", "join", "strip", "lstrip", "rstrip",
    "format", "encode", "decode", "startswith", "endswith", "replace",
    "lower", "upper", "title", "capitalize", "casefold", "find", "rfind",
    "isdigit", "isalpha", "isalnum", "isspace",
    "isupper", "islower", "zfill", "ljust", "rjust", "center",
    "add", "discard", "union", "intersection", "difference",
    "symmetric_difference", "issubset", "issuperset",
    "read", "write", "readline", "readlines", "writelines", "seek",
    "tell", "flush", "close", "fileno", "readable", "writable",
    "truncate", "__enter__", "__exit__",
    "search", "match", "fullmatch", "findall", "finditer", "sub",
    "subn", "group", "groups", "groupdict", "span", "start", "end",
    "dumps", "loads",
})
@lru_cache(maxsize=_REGEX_CACHE_MAXSIZE)
def _host_attr_re(name: str) -> re.Pattern:
    return re.compile(r"(?<![\w.])(\w+)\." + re.escape(name) + r"\s*\(")
def _iter_host_attr_mentions(name: str, entries: list[DocEntry]):
    pat = _host_attr_re(name)
    for e in entries:
        ctx = _claim_scan_text(e.context)
        if ctx is None:
            continue
        for match in pat.finditer(ctx):
            yield match.group(1)
def _public_names(code_exports: list,
                  export_types: tuple[str, ...] | None = None) -> set:
    return {e.name for e in code_exports
            if e.is_public and (export_types is None
                                or e.export_type in export_types)}
def _host_api_for_form(var: str, form: str,
                       assign_hosts: dict,
                       public_apis: set) -> str | None:
    host = assign_hosts.get(var)
    if not host or host[0] != form or host[1] not in public_apis:
        return None
    return host[1]
def _iter_host_apis(name: str, entries: list[DocEntry],
                    assign_hosts: dict, form: str,
                    public_apis: set):
    for var in _iter_host_attr_mentions(name, entries):
        api = _host_api_for_form(var, form, assign_hosts, public_apis)
        if api is not None:
            yield api
def attr_on_bare_func_host(
    name: str,
    entries: list[DocEntry],
    assign_hosts: dict[str, tuple[str, str] | None],
    class_method_names: set[str],
    code_exports: list[CodeExport],
) -> bool:
    if not assign_hosts:
        return False
    public_funcs = _public_names(code_exports, _FUNCTION_EXPORT_TYPES)
    public_classes = _public_names(code_exports, ("class",))
    for api in _iter_host_apis(
            name, entries, assign_hosts, "bare",
            public_funcs | public_classes):
        if _bare_host_upgrades(name, api, public_funcs, public_classes,
                               class_method_names):
            return True
    return False
def _bare_host_upgrades(name: str, api: str, public_funcs: set,
                        public_classes: set,
                        class_method_names: set) -> bool:
    if api in public_funcs:
        return True
    return (api in public_classes
            and name not in class_method_names
            and name not in _COMMON_OBJ_METHODS)
def attr_call_on_pkg_host(
    name: str,
    entries: list[DocEntry],
    assign_hosts: dict[str, tuple[str, str] | None],
    class_method_names: set[str],
    code_exports: list[CodeExport],
) -> bool:
    if not assign_hosts:
        return False
    if name in class_method_names or name in _COMMON_OBJ_METHODS:
        return False
    public_names = _public_names(code_exports)
    return next(
        iter(_iter_host_apis(
            name, entries, assign_hosts, "call", public_names)),
        None,
    ) is not None
_RULE_ID_NAME_RE = re.compile(
    r"^(?:[A-Z]{1,6}\d{1,3}|[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)+)$")
_RULE_ID_COLLECT_RE = re.compile(
    r"['\"]([A-Z]+\d{1,3}"
    r"|[A-Z][A-Z0-9]*(?:-(?=[A-Z0-9])[A-Z0-9]+)+)['\"]")
_HYPHEN_COMPOUND_RE = re.compile(
    r"\b([A-Za-z][A-Za-z0-9_]*(?:-(?=[A-Za-z0-9_])[A-Za-z0-9_]+)+)\b")
_EXTERNAL_NS_PREFIXES = frozenset({
    "CVE", "CWE", "BANDIT", "OWASP", "PYSEC", "GHSA",
    "UTF", "ASCII", "MD", "SHA", "BASE", "HTML", "HTTP", "JSON",
    "XML", "YAML", "TOML", "CSV", "AES", "RSA", "HMAC", "TLS",
    "PEP", "IEEE", "ISO",
})
def _iter_scannable_python_files(skill_dir: str):
    for root, dirs, files in os.walk(skill_dir):
        dirs[:] = sorted(prune_scan_dirs(dirs, skill_dir))
        for fn in sorted(files):
            if not is_scan_py_name(fn):
                continue
            filepath = os.path.join(root, fn)
            if not is_diagnosis_out_of_scope(filepath, skill_dir):
                yield filepath
def _iter_registry_sources(skill_dir: str, get_source):
    for filepath in _iter_scannable_python_files(skill_dir):
        src = get_source(filepath)
        if src is not None:
            yield filepath, os.path.relpath(filepath, skill_dir), src
def _register_tokens_in(src: str, rel: str, registered: set,
                        evidence: dict) -> None:
    for m in _RULE_ID_COLLECT_RE.finditer(src):
        tok = m.group(1)
        if tok not in registered:
            registered.add(tok)
            if len(evidence) < 4096:
                evidence[tok] = rel
def _build_family_index(registered: set) -> dict:
    families: dict = {}
    for tok in registered:
        fam = re.match(r"^[A-Z]+", tok)
        if fam and fam.group(0) not in _EXTERNAL_NS_PREFIXES:
            families[fam.group(0)] = families.get(fam.group(0), 0) + 1
    return families
def _registered_compound(name: str, entries, registered: set) -> str | None:
    for e in entries:
        for compound in _HYPHEN_COMPOUND_RE.findall(e.context):
            if name in compound.split("-") and compound in registered:
                return compound
    return None
def _ghost_compound(name: str, entries, registered: set,
                    families: dict) -> str | None:
    for e in entries:
        for compound in _HYPHEN_COMPOUND_RE.findall(e.context):
            if name not in compound.split("-") or compound in registered:
                continue
            fam = re.match(r"^[A-Z]+", compound)
            if fam and families.get(fam.group(0), 0) > 0:
                return compound
    return None
class RuleIdRegistry:
    def __init__(self, skill_dir: str, get_source):
        self._skill_dir = skill_dir
        self._get_source = get_source
        self.registered: set[str] | None = None
        self.families: dict[str, int] = {}
        self.evidence: dict[str, str] = {}
        self.stripped: list[dict] = []
        self.ghosts: list[dict] = []
    def _collect(self) -> None:
        registered: set[str] = set()
        evidence: dict[str, str] = {}
        for _fp, rel, src in _iter_registry_sources(
                self._skill_dir, self._get_source):
            _register_tokens_in(src, rel, registered, evidence)
        families = _build_family_index(registered)
        self.registered = registered
        self.evidence = evidence
        self.families = families
    def verdict(self, name: str, entries: list[DocEntry]) -> tuple[str, str]:
        if self.registered is None:
            self._collect()
        if not self.registered:
            return "none", ""
        if name in self.registered:
            return "registered", name
        compound = _registered_compound(name, entries, self.registered)
        if compound is not None:
            return "registered", compound
        if _ghost_compound(name, entries, self.registered,
                           self.families) is not None:
            return "ghost_family", ""
        if _RULE_ID_NAME_RE.match(name):
            fam = re.match(r"^[A-Z]+", name)
            if fam and self.families.get(fam.group(0), 0) > 0:
                return "ghost_family", ""
        return "none", ""
    def disposition(self) -> dict:
        return {
            "registered_stripped": list(self.stripped),
            "ghost_elevated": list(self.ghosts),
        }
@dataclass
class DocEntry:
    name: str
    entry_type: str
    declared_in: str
    line_in_doc: int
    context: str
@dataclass
class ConsistencyFinding:
    rule_id: str
    severity: str
    confidence: float
    message: str
    file: str
    line: int
    extra: dict = field(default_factory=dict)
class _OrphanVerdict(NamedTuple):
    confidence: float
    elevated_by_host: bool
    elevated_kind: str
    elevated_by_rid: bool
def _as_alias_parts(seg: str) -> tuple[str, str] | None:
    _as_parts = re.split(r"\s+as\s+", seg)
    if (len(_as_parts) == 2
            and _as_parts[0].strip()
            and _as_parts[1].strip()):
        return _as_parts[0].strip(), _as_parts[1].strip()
    return None
def _import_name_tail(stripped: str, pattern: re.Pattern) -> str:
    _tm = pattern.match(strip_line_comment(stripped))
    _tail = _tm.group(1).strip() if _tm else ""
    if _tail.startswith("("):
        _tail = _tail.strip("()")
    return _tail
def _pattern_match_names(match) -> list[str]:
    if isinstance(match, str):
        return [n.strip() for n in match.split(",")]
    return [m.strip() for m in match if m.strip()]
def _is_extractable_doc_name(name, local_def_names,
                             seen_in_line, skip_names) -> bool:
    return bool(name and name[0].isalpha()
                and name not in skip_names
                and name not in local_def_names
                and not keyword.iskeyword(name)
                and len(name) > 2
                and name not in seen_in_line)
def _module_segments_in_scope(segs: list[str], base_dir: str) -> bool:
    if not segs:
        return True
    dirs = segs[:-1]
    if len(prune_scan_dirs(list(dirs), base_dir)) != len(dirs):
        return False
    return not is_diagnosis_out_of_scope(
        os.path.join(os.path.abspath(base_dir), *dirs, segs[-1] + ".py"),
        base_dir)
def _string_domain_pass(stripped: str,
                        in_triple: str) -> tuple[str | None, str]:
    while True:
        if in_triple:
            close = find_close_triple(stripped, in_triple)
            if close == -1:
                return None, in_triple
            in_triple = ""
            stripped = stripped[close + 3:].lstrip(" ;").strip()
            if not stripped:
                return None, ""
            continue
        if not stripped.startswith(("#", '"', "'")):
            return stripped, ""
        trip = stripped[:3] if stripped[:3] in ('"""', "'''") else ""
        if not trip:
            if stripped[0] in ('"', "'"):
                end = _skip_single_quoted(stripped, 0)
                stripped = stripped[end:].lstrip(" ;").strip()
                if not stripped:
                    return None, ""
                continue
            return None, ""
        close = find_close_triple(stripped, trip, 3)
        if close == -1:
            return None, trip
        stripped = stripped[close + 3:].lstrip(" ;").strip()
        if not stripped:
            return None, ""
def _ledger_entry(name: str, entries: list,
                        *, with_first: bool = False) -> dict:
    entry = {
        "name": name,
        "mentions": len(entries),
        "lines": [e.line_in_doc for e in entries],
        "contexts": [e.context[:100] for e in entries[:5]],
    }
    if with_first:
        entry["line"] = entries[0].line_in_doc
        entry["context"] = entries[0].context[:100]
    return entry
def _doc_coverage_names(doc_entries, assign_hosts) -> set[str]:
    names = {e.name for e in doc_entries}
    for rec in assign_hosts.values():
        if rec is not None:
            names.add(rec[1])
    return names
def _orphan_in_import_ctx(name: str, entries: list) -> bool:
    for e in entries:
        _code_ctx = _claim_scan_text(e.context)
        if _code_ctx is None:
            continue
        if (_IMPORT_WORD_RE.search(_code_ctx)
                and re.search(r"(?<![\w.])" + re.escape(name) + r"\b",
                              _code_ctx)):
            return True
    return False
def _from_import_claims_name(name: str, context: str) -> bool:
    if from_import_module(context) is None:
        return False
    tail = _import_name_tail(context, _FROM_IMPORT_TAIL_RE).split(";", 1)[0]
    for raw_segment in tail.split(","):
        segment = raw_segment.strip()
        alias = _as_alias_parts(segment)
        source = alias[0] if alias is not None else segment
        if source.strip() == name:
            return True
    return False
def _orphan_base_confidence(name, entries, rid_verdict, assign_hosts,
                            class_method_names, code_exports):
    if any(is_standalone_call_ctx(e.context, e.name) for e in entries):
        return _OrphanVerdict(0.6, False, "", False)
    if attr_on_bare_func_host(
            name, entries, assign_hosts,
            class_method_names, code_exports):
        return _OrphanVerdict(0.6, True, "bare_func_host_attr", False)
    if attr_call_on_pkg_host(
            name, entries, assign_hosts,
            class_method_names, code_exports):
        return _OrphanVerdict(0.6, True, "pkg_host_attr_method", False)
    if rid_verdict == "ghost_family":
        return _OrphanVerdict(0.6, False, "", True)
    return _OrphanVerdict(0.4, False, "", False)
def _api_face_names(code_exports, callable_types: set, *,
                    entry_only: bool,
                    callable_imports: set[str]) -> set[str]:
    api_face_names: set[str] = set()
    for e in code_exports:
        if not e.is_public:
            continue
        if entry_only and e.defined_in != _ENTRY_MODULE_REL:
            continue
        if (e.export_type in callable_types
                or (e.defined_in == _ENTRY_MODULE_REL
                    and e.name in callable_imports)):
            api_face_names.add(e.name)
    return api_face_names
def _export_index(code_exports) -> dict[str, list[CodeExport]]:
    exports_by_name: dict[str, list[CodeExport]] = {}
    for e in code_exports:
        exports_by_name.setdefault(e.name, []).append(e)
    return exports_by_name
class _DocClaimExtractor:
    def __init__(self, skill_dir, scanner, skip_names, ident_patterns):
        self.skill_dir = skill_dir
        self._scanner = scanner
        self._skip_names = skip_names
        self._patterns = ident_patterns
        self.doc_entries: list[DocEntry] = []
        self.doc_source_status: str = "ok"
        self.doc_name: str = ENTRY_DOC_NAME
        self.assign_hosts: dict[str, tuple[str, str] | None] = {}
        self.local_defs: set[str] = set()
        self.out_of_scope_imports: set[str] = set()
        self.has_star_import = False
    def reset(self) -> None:
        self.doc_entries.clear()
        self.assign_hosts.clear()
        self.local_defs.clear()
        self.out_of_scope_imports.clear()
        self.has_star_import = False
        self.doc_source_status = "ok"
        self.doc_name = ENTRY_DOC_NAME
    def _read_skill_md_lines(self) -> list[str] | None:
        md_path = resolve_entry_document(self.skill_dir)
        if md_path is None:
            self.doc_source_status = "missing"
            return None
        self.doc_name = md_path.name
        text = read_source(str(md_path))
        if text is None:
            self.doc_source_status = "read_error"
            logger.warning("DocClaimExtractor.parse: 入口文档读取失败，降级空文档 %s",
                           md_path)
            return None
        return text.split("\n")
    def _register_inline_mentions(self, line_no: int, line: str,
                                  stripped: str) -> None:
        _seen: set[str] = set()
        for name in chain.from_iterable(
                _inline_claim_names(span) for span in _INLINE_SPAN_RE.findall(line)):
            if name in _seen:
                continue
            if _is_extractable_doc_name(
                    name, frozenset(), frozenset(), self._skip_names()):
                _seen.add(name)
                self.doc_entries.append(DocEntry(
                    name=name,
                    entry_type="inline_mention",
                    declared_in=self.doc_name,
                    line_in_doc=line_no,
                    context=stripped,
                ))
    def parse(self) -> str:
        lines = self._read_skill_md_lines()
        if lines is None:
            return self.doc_source_status
        in_code_block = False
        code_block_lines: list[tuple[int, str]] = []
        self._scanner.refresh_pkg_identity()
        body_start = locate_frontmatter_body_start(lines)
        for line_no, (line, line_in_fence) in enumerate(
                iter_fence_state(lines[body_start:]), body_start + 1):
            if line_in_fence:
                if not in_code_block:
                    in_code_block = True
                    code_block_lines = []
                else:
                    code_block_lines.append((line_no, line))
                continue
            if in_code_block:
                in_code_block = False
                self.extract_from_code_block(code_block_lines)
                code_block_lines = []
                continue
            self._register_inline_mentions(line_no, line, line.strip())
        if in_code_block and code_block_lines:
            self.extract_from_code_block(code_block_lines)
        return self.doc_source_status
    def _register_assign_host(self, var: str, form: str, api: str) -> None:
        if var not in self.assign_hosts:
            self.assign_hosts[var] = (form, api)
            return
        cur = self.assign_hosts[var]
        if cur is None:
            return
        if cur[1] != api:
            self.assign_hosts[var] = None
        else:
            self.assign_hosts[var] = (form, api)
    def _register_out_of_scope_names(self, stripped: str) -> None:
        _tail = _import_name_tail(stripped, _FROM_IMPORT_TAIL_RE)
        for _seg in _tail.split(","):
            _seg = _seg.strip()
            if not _seg:
                continue
            _as = _as_alias_parts(_seg)
            for _n in (_as if _as is not None else (_seg,)):
                if _n.isidentifier():
                    self.out_of_scope_imports.add(_n)
    def _resolve_as_alias(self, name: str) -> str:
        _as = _as_alias_parts(name)
        if _as is not None:
            _orig_n, _alias_n = _as
            self._register_assign_host(_alias_n, "bare", _orig_n)
            return _orig_n
        return name
    def module_belongs_to_pkg(self, module: str) -> bool:
        if module.startswith("."):
            leading = len(module) - len(module.lstrip("."))
            if leading >= 2:
                return False
            segs = [s for s in module.split(".") if s]
        else:
            parts = module.split(".")
            first = parts[0]
            if first != self._scanner.pkg_name and first not in self._scanner.local_modules:
                return False
            segs = parts[1:] if first == self._scanner.pkg_name else parts
        return _module_segments_in_scope(segs, self._scanner.package_root)
    def _register_line_local_defs(self, stripped: str,
                                  line_no: int) -> set[str]:
        _host_line = strip_line_comment(stripped).strip()
        _bare_match = _BARE_API_ASSIGN_RE.match(_host_line)
        if _bare_match is not None:
            self._register_assign_host(
                _bare_match.group(1), "bare", _bare_match.group(2))
        else:
            _call_match = _CALL_API_ASSIGN_RE.match(_host_line)
            if _call_match is not None:
                self._register_assign_host(
                    _call_match.group(1), "call", _call_match.group(2))
        _local_def_names: set[str] = set()
        for _m in (_DEF_LINE_RE.match(stripped),
                   _CLASS_LINE_RE.match(stripped)):
            if _m:
                _dn = _m.group(1)
                _local_def_names.add(_dn)
                self.local_defs.add(_dn)
                self.doc_entries.append(DocEntry(
                    name=_dn,
                    entry_type="inline_mention",
                    declared_in=self.doc_name,
                    line_in_doc=line_no,
                    context=stripped,
                ))
        return _local_def_names
    def _handle_line_imports(self, stripped: str) -> bool:
        _from_mod = from_import_module(stripped)
        if _from_mod is not None:
            tail = _import_name_tail(stripped, _FROM_IMPORT_TAIL_RE)
            star_import = any(
                segment.strip() == "*" for segment in tail.split(","))
            if star_import:
                self.has_star_import = True
            if not self.module_belongs_to_pkg(_from_mod):
                self._register_out_of_scope_names(stripped)
                return True
            return star_import
        if not is_plain_import(stripped):
            return False
        _tail = _import_name_tail(stripped, _IMPORT_TAIL_RE)
        for _seg in _tail.split(","):
            _as = _as_alias_parts(_seg.strip())
            if _as is not None:
                self._register_assign_host(_as[1], "bare", _as[0])
        return True
    def _extract_line_names(self, stripped: str, line_no: int,
                            local_def_names: set[str]) -> None:
        _seen_in_line: set[str] = set()
        scan_text = _claim_scan_text(stripped)
        if scan_text is None:
            return
        scan_texts = [scan_text]
        for expression in _fstring_expression_sources(stripped):
            expression_text = _claim_scan_text(expression)
            if expression_text is not None:
                scan_texts.append(expression_text)
        for scan_text in scan_texts:
            for pattern in self._patterns():
                matches = pattern.findall(scan_text)
                for match in matches:
                    for _raw_name in _pattern_match_names(match):
                        _alias = _as_alias_parts(_raw_name)
                        name = self._resolve_as_alias(_raw_name)
                        if _is_extractable_doc_name(
                                name, local_def_names, _seen_in_line,
                                self._skip_names()):
                            _seen_in_line.add(name)
                            self.doc_entries.append(DocEntry(
                                name=name,
                                entry_type="unknown",
                                declared_in=self.doc_name,
                                line_in_doc=line_no,
                                context=stripped,
                            ))
                        if _alias is None:
                            continue
                        _alias_name = _alias[1]
                        if not _is_extractable_doc_name(
                                _alias_name, local_def_names, _seen_in_line,
                                self._skip_names()):
                            continue
                        _seen_in_line.add(_alias_name)
                        self.doc_entries.append(DocEntry(
                            name=_alias_name,
                            entry_type="inline_mention",
                            declared_in=self.doc_name,
                            line_in_doc=line_no,
                            context=stripped,
                        ))
    def extract_from_code_block(self, code_block_lines: list[tuple[int, str]]):
        in_triple = ""
        for line_no, line in merge_import_continuations(code_block_lines):
            in_triple = self._process_block_line(line_no, line, in_triple)
    def _process_block_line(self, line_no: int, line: str,
                            in_triple: str) -> str:
        code, in_triple = _string_domain_pass(line.strip(), in_triple)
        if code is None:
            return in_triple
        for statement in _iter_code_statements(code):
            _local_def_names = self._register_line_local_defs(
                statement, line_no)
            if self._handle_line_imports(statement):
                continue
            self._extract_line_names(statement, line_no, _local_def_names)
        return find_open_triple(code)
class DocCodeConsistencyAnalyzer:
    IDENT_PATTERNS: ClassVar[list[re.Pattern]] = [
        re.compile(r"from\s+[\w.]+\s+import\s+(?:\(?\s*)?([\w,\s]+)"),  # jwsgj:suppress SE-30
        re.compile(r"\bimport\s+([\w,\s]+)"),
        re.compile(r"\b([a-zA-Z_]\w*)\s*\("),
        re.compile(r"\b([A-Z][a-zA-Z0-9_]*)\b"),
    ]
    SMALL_API_FACE_LIMIT = 20
    DOC_COVERAGE_FULL_THRESHOLD = 0.5
    SKIP_NAMES = frozenset({
        "Optional", "List", "Dict", "Set", "Tuple", "Any", "Callable",
        "str", "int", "float", "bool", "bytes", "None",
        "True", "False", "os", "sys", "json", "re", "ast",
        "print", "len", "range", "type", "isinstance",
        "Exception", "ValueError", "TypeError", "KeyError",
        "TODO", "FIXME", "NOTE", "WARNING", "XXX",
    }) | _BUILTIN_FUNC_NAMES | _STDLIB_FUNC_NAMES
    def __init__(self, skill_dir: str, cache: Any = None):
        self.skill_dir = os.path.abspath(skill_dir)
        self._scanner = PackageExportScanner(skill_dir, cache=cache)
        self._doc = _DocClaimExtractor(
            self.skill_dir, self._scanner,
            lambda: self.SKIP_NAMES, lambda: self.IDENT_PATTERNS)
        self._reset_run_state()
    @property
    def doc_entries(self) -> list[DocEntry]:
        return self._doc.doc_entries
    def _reset_run_state(self) -> None:
        self._doc.reset()
        self.doc_source_status: str = "ok"
        self.code_exports: list[CodeExport] = []
        self.findings: list[ConsistencyFinding] = []
        self._binding_evidence: set[str] = set()
        self._all_ghosts: list[str] = []
        self._all_line: int = 0
        self._all_names: set[str] = set()
        self.api_face_total: int = 0
        self.api_face_covered: int = 0
        self.filtered_orphans: list[dict] = []
        self._host_var_stripped: list[dict] = []
        self._local_def_stripped: list[dict] = []
        self._out_of_scope_stripped: list[dict] = []
        self._module_bindings: dict[str, set[str]] = {}
        self._module_imports: dict[str, dict[str, tuple[str, str]]] = {}
        self._module_callables: dict[str, set[str]] = {}
        self._module_dynamic: dict[str, bool] = {}
        self._orphan_entry_overrides: dict[str, list[DocEntry]] = {}
        self._class_method_names: set[str] = set()
        self._rule_ids = RuleIdRegistry(
            self.skill_dir, self._scanner.get_source_for_scan)
        self._orphan_docs: set[str] = set()
        self._undocumented: set[str] = set()
    def analyze(self) -> list[ConsistencyFinding]:
        self._reset_run_state()
        logger.info("[A14] DocCodeConsistencyAnalyzer.analyze 开始: %s", self.skill_dir)
        self.doc_source_status = self._doc.parse()
        self._collect_scan_results()
        self._compare()
        self._generate_findings()
        logger.debug("[A14] 分析完成: %d 文档条目, %d 导出, %d 发现",
                     len(self.doc_entries), len(self.code_exports),
                     len(self.findings))
        return self.findings
    def _collect_scan_results(self) -> None:
        sc = self._scanner
        sc.scan()
        self.code_exports = sc.code_exports
        self._binding_evidence = sc.binding_evidence
        self._all_line = sc.all_line
        self._all_names = sc.all_names
        self._all_ghosts = sc.all_ghosts
        self._class_method_names = sc.class_method_names
        self._module_bindings = {
            os.path.normcase(os.path.normpath(path)): set(names)
            for path, names in sc.module_bindings.items()
        }
        self._module_imports = {
            os.path.normcase(os.path.normpath(path)): dict(imports)
            for path, imports in sc.module_imports.items()
        }
        self._module_callables = {
            os.path.normcase(os.path.normpath(path)): set(names)
            for path, names in sc.module_callables.items()
        }
        self._module_dynamic = {
            os.path.normcase(os.path.normpath(path)): dynamic
            for path, dynamic in sc.module_dynamic.items()
        }
    def _module_import_candidates(
            self, module: str, importer_path: str) -> tuple[str, ...]:
        if module.startswith("."):
            level = len(module) - len(module.lstrip("."))
            base = os.path.dirname(importer_path)
            for _ in range(level - 1):
                if not base:
                    return ()
                base = os.path.dirname(base)
            segs = [s for s in module[level:].split(".") if s]
        else:
            parts = module.split(".")
            if parts[0] == self._scanner.pkg_name:
                segs = parts[1:]
            elif parts[0] in self._scanner.local_modules:
                segs = parts
            else:
                return ()
            base = ""
        if not segs:
            return ((os.path.join(base, _ENTRY_MODULE_REL) if base
                     else _ENTRY_MODULE_REL),)
        prefix = os.path.join(base, *segs)
        module_candidate = prefix + ".py"
        package_candidate = os.path.join(prefix, _ENTRY_MODULE_REL)
        package_path = os.path.join(
            self._scanner.package_root, package_candidate)
        if os.path.isfile(package_path):
            return (package_candidate,)
        module_path = os.path.join(
            self._scanner.package_root, module_candidate)
        if os.path.isfile(module_path):
            return (module_candidate,)
        return module_candidate, package_candidate
    def _module_import_state(
            self, module: str) -> tuple[set[str], bool, bool]:
        candidates = self._module_import_candidates(
            module, _ENTRY_MODULE_REL)
        found = False
        dynamic = False
        bindings: set[str] = set()
        for rel in candidates:
            key = os.path.normcase(os.path.normpath(rel))
            if key not in self._module_bindings:
                continue
            found = True
            bindings |= self._module_bindings[key]
            dynamic |= self._module_dynamic.get(key, False)
        return bindings, found, dynamic
    def _module_import_incomplete(self, module: str) -> bool:
        incomplete = {
            os.path.normcase(os.path.normpath(path))
            for path in self._scanner.incomplete_files
        }
        return any(
            os.path.normcase(os.path.normpath(candidate)) in incomplete
            for candidate in self._module_import_candidates(
                module, _ENTRY_MODULE_REL))

    def _import_resolves_callable(
            self, importer_path: str, module: str, source_name: str) -> bool:
        pending = [(importer_path, module, source_name)]
        seen: set[tuple[str, str]] = set()
        while pending:
            current_importer, current_module, current_name = pending.pop()
            candidates = self._module_import_candidates(
                current_module, current_importer)
            for candidate in candidates:
                key = os.path.normcase(os.path.normpath(candidate))
                binding_key = (key, current_name)
                if binding_key in seen:
                    continue
                seen.add(binding_key)
                if current_name in self._module_callables.get(key, set()):
                    return True
                nested = self._module_imports.get(key, {}).get(current_name)
                if nested is not None:
                    nested_module, nested_name = nested
                    pending.append((key, nested_module, nested_name))
        return False
    def _callable_entry_imports(self) -> set[str]:
        callable_imports: set[str] = set()
        for export in self.code_exports:
            if (export.defined_in != _ENTRY_MODULE_REL
                    or export.export_type != "import"
                    or not export.is_public
                    or export.import_source is None):
                continue
            module, source_name = export.import_source
            if not self._doc.module_belongs_to_pkg(module):
                continue
            if self._import_resolves_callable(
                    export.defined_in, module, source_name):
                callable_imports.add(export.name)
        return callable_imports
    def _package_submodule_exists(self, module: str, name: str) -> bool:
        member_module = (f"{module}{name}" if module.endswith(".")
                         else f"{module}.{name}")
        if not self._doc.module_belongs_to_pkg(member_module):
            return False
        package_dir: str | None = None
        for candidate in self._module_import_candidates(
                module, _ENTRY_MODULE_REL):
            full_path = os.path.join(self._scanner.package_root, candidate)
            if os.path.basename(candidate) == _ENTRY_MODULE_REL:
                if os.path.isfile(full_path):
                    package_dir = os.path.dirname(full_path)
                    break
            elif not os.path.isfile(full_path) and os.path.isdir(full_path[:-3]):
                package_dir = full_path[:-3]
                break
        if package_dir is None:
            return False
        member_file = os.path.join(package_dir, name + ".py")
        if os.path.isfile(member_file):
            return is_scan_py_name(name + ".py")
        member_dir = os.path.join(package_dir, name)
        if not os.path.isdir(member_dir):
            return False
        if not prune_scan_dirs([name], os.path.dirname(member_dir)):
            return False
        return not is_diagnosis_out_of_scope(
            os.path.join(member_dir, _ENTRY_MODULE_REL),
            self._scanner.package_root)
    def _import_claim_verdict(self, name: str, entry: DocEntry) -> str:
        context = strip_line_comment(entry.context).strip()
        module = from_import_module(context)
        if (module is None or not self._doc.module_belongs_to_pkg(module)
                or not _from_import_claims_name(name, context)):
            return ""
        if self._module_import_incomplete(module):
            return "incomplete"
        bindings, found, dynamic = self._module_import_state(module)
        if found and dynamic:
            return "dynamic"
        if name in bindings:
            return "bound"
        if self._package_submodule_exists(module, name):
            return "submodule"
        return "invalid"
    def _unbound_import_entries(self, name: str,
                                entries: list[DocEntry]) -> list[DocEntry]:
        return [entry for entry in entries
                if self._import_claim_verdict(name, entry) == "invalid"]
    def _compare(self):
        code_names = {e.name for e in self.code_exports}
        doc_names = _doc_coverage_names(self.doc_entries, self._doc.assign_hosts)
        strong_doc_names = {
            e.name for e in self.doc_entries
            if e.entry_type != "inline_mention"
        }
        entries_by_name: dict[str, list[DocEntry]] = {}
        for entry in self.doc_entries:
            entries_by_name.setdefault(entry.name, []).append(entry)
        self._orphan_docs = set()
        for name in strong_doc_names:
            entries = entries_by_name.get(name, [])
            invalid = self._unbound_import_entries(name, entries)
            if invalid:
                self._orphan_docs.add(name)
                self._orphan_entry_overrides[name] = invalid
                continue
            if name not in code_names:
                strong_entries = [
                    e for e in entries if e.entry_type != "inline_mention"]
                verdicts = [
                    self._import_claim_verdict(name, e) for e in strong_entries]
                if any(verdict in {"dynamic", "incomplete"}
                       for verdict in verdicts):
                    continue
                if (not strong_entries
                        or not all(verdict in {"bound", "submodule"}
                                   for verdict in verdicts)):
                    self._orphan_docs.add(name)
        self._undocumented = code_names - doc_names
    @property
    def rule_id_disposition(self) -> dict:
        return self._rule_ids.disposition()
    @property
    def host_var_stripped(self) -> list[dict]:
        return list(self._host_var_stripped)
    @property
    def local_def_stripped(self) -> list[dict]:
        return list(self._local_def_stripped)
    @property
    def out_of_scope_import_stripped(self) -> list[dict]:
        return list(self._out_of_scope_stripped)
    def _emit_all_ghost_findings(self) -> None:
        for name in self._all_ghosts:
            self.findings.append(ConsistencyFinding(
                rule_id="DOC-ALL-GHOST",
                severity="P2",
                confidence=0.85,
                message=(
                    f"__all__ 声明 '{name}' 但全包无任何顶级定义"
                    f"（import 该名称将失败）"
                ),
                file="__init__.py",
                line=self._all_line or 0,
                extra={
                    "name": name,
                    "type": "all_ghost",
                },
            ))
    def _process_orphan_doc(self, name: str, entries: list) -> None:
        rid_verdict, rid_evidence = self._rule_ids.verdict(name, entries)
        in_import_ctx = _orphan_in_import_ctx(name, entries)
        if rid_verdict == "registered" and not in_import_ctx:
            self._strip_registered_rid(name, entries, rid_evidence)
            return
        if in_import_ctx:
            verdict = _OrphanVerdict(0.75, False, "", False)
        elif self._strip_by_local_binding(name, entries):
            return
        else:
            verdict = _orphan_base_confidence(
                name, entries, rid_verdict, self._doc.assign_hosts,
                self._class_method_names, self.code_exports)
        if verdict.confidence < 0.5:
            self.filtered_orphans.append(
                _ledger_entry(name, entries, with_first=True))
            return
        self._emit_orphan_finding(name, entries, verdict)
    def _strip_registered_rid(self, name: str, entries: list,
                              rid_evidence: str) -> None:
        self._rule_ids.stripped.append({
            "name": name,
            "registered_as": rid_evidence,
            "evidence_file": self._rule_ids.evidence.get(rid_evidence, ""),
            "mentions": len(entries),
            "lines": [e.line_in_doc for e in entries],
        })
    def _strip_by_local_binding(self, name: str, entries: list) -> bool:
        if self._doc.has_star_import:
            self._out_of_scope_stripped.append(_ledger_entry(name, entries))
            return True
        for known, ledger in (
            (self._doc.assign_hosts, self._host_var_stripped),
            (self._doc.local_defs, self._local_def_stripped),
            (self._doc.out_of_scope_imports, self._out_of_scope_stripped),
        ):
            if name in known:
                ledger.append(_ledger_entry(name, entries))
                return True
        return False
    def _emit_orphan_finding(self, name: str, entries: list,
                             verdict: _OrphanVerdict) -> None:
        line = entries[0].line_in_doc
        _msg = (f"文档声称 '{name}' 存在但代码中未找到定义")
        _extra = {
            "name": name,
            "type": "orphan_doc",
            "context": entries[0].context[:100],
            **({"elevated_by": verdict.elevated_kind}
               if verdict.elevated_by_host else {}),
        }
        if verdict.elevated_by_rid:
            _msg = (f"文档引用规则 ID '{name}' 但全包无注册"
                    f"（同前缀族已注册，疑似幽灵规则号）")
            _extra["elevated_by"] = "rule_id_ghost_family"
            self._rule_ids.ghosts.append(
                _ledger_entry(name, entries))
        self.findings.append(ConsistencyFinding(
            rule_id="DOC-ORPHAN",
            severity="P2",
            confidence=verdict.confidence,
            message=_msg,
            file=self._doc.doc_name,
            line=line,
            extra=_extra,
        ))
    def _emit_missing_for_name(self, name: str, api_face_names: set,
                               exports_by_name: dict) -> None:
        if name not in api_face_names:
            return
        if len(name) < 4:
            return
        src = next((e for e in exports_by_name.get(name, ())
                    if e.is_public
                    and e.export_type in _CALLABLE_EXPORT_TYPES), None)
        if src is None:
            src = next((e for e in exports_by_name.get(name, ())
                        if e.is_public
                        and e.defined_in == _ENTRY_MODULE_REL), None)
        self.findings.append(ConsistencyFinding(
            rule_id="DOC-MISSING",
            severity="P3",
            confidence=0.5,
            message=f"公开导出 '{name}' 未在文档中提及",
            file=src.defined_in if src else "__init__.py",
            line=src.line if src else 0,
            extra={
                "name": name,
                "type": "undocumented",
            },
        ))
    def _emit_doc_missing_findings(self) -> None:
        doc_names = _doc_coverage_names(self.doc_entries, self._doc.assign_hosts)
        exports_by_name = _export_index(self.code_exports)
        entry_only = os.path.isfile(os.path.join(
            self._scanner.package_root, _ENTRY_MODULE_REL))
        callable_imports = (
            self._callable_entry_imports() if entry_only else set())
        api_face_names = _api_face_names(
            self.code_exports, _CALLABLE_EXPORT_TYPES,
            entry_only=entry_only, callable_imports=callable_imports)
        total = len(api_face_names)
        covered = sum(1 for n in api_face_names if n in doc_names)
        self.api_face_total = total
        self.api_face_covered = covered
        selective_docs = (
            total > self.SMALL_API_FACE_LIMIT
            and covered / max(total, 1) < self.DOC_COVERAGE_FULL_THRESHOLD
        )
        names_to_report = () if selective_docs else sorted(self._undocumented)
        for name in names_to_report:
            self._emit_missing_for_name(
                name, api_face_names, exports_by_name)
    def _generate_findings(self):
        self._emit_all_ghost_findings()
        _entries_by_name: dict[str, list[DocEntry]] = {}
        for _e in self.doc_entries:
            _entries_by_name.setdefault(_e.name, []).append(_e)
        for name in sorted(self._orphan_docs):
            entries = self._orphan_entry_overrides.get(
                name, _entries_by_name[name])
            self._process_orphan_doc(name, entries)
        self._emit_doc_missing_findings()
_TRY_TYPES = tuple(
    t for t in (ast.Try, getattr(ast, "TryStar", None)) if t is not None)
def is_try_statement(node) -> bool:
    return isinstance(node, _TRY_TYPES)
@dataclass
class CodeExport:
    name: str
    export_type: str
    defined_in: str
    line: int
    is_public: bool
    import_source: tuple[str, str] | None = None
def prune_scan_dirs(dirs: list[str],
                    root_dir: str | None = None) -> list[str]:
    kept = [d for d in dirs if not is_backup_like_dir(d)]
    prune_ignore_dirs(kept, root_dir)
    return kept
def _merge_all_states(states) -> tuple[set[str], int, bool]:
    states = list(states)
    names = set().union(*(state[0] for state in states))
    lines = [state[1] for state in states if state[1]]
    return names, min(lines, default=0), all(state[2] for state in states)
def _exec_all_body(body: list, state) -> tuple[set[str], int, bool]:
    current = (set(state[0]), state[1], state[2])
    for node in body:
        current = _exec_all_stmt(node, current)
        if _all_stmt_blocks_fallthrough(node):
            break
    return current
def _all_stmt_blocks_fallthrough(node) -> bool:
    if isinstance(node, (ast.Raise, ast.Return, ast.Break, ast.Continue)):
        return True
    return (isinstance(node, ast.If) and bool(node.orelse)
            and _all_body_blocks_fallthrough(node.body)
            and _all_body_blocks_fallthrough(node.orelse))
def _all_body_blocks_fallthrough(body: list) -> bool:
    return any(_all_stmt_blocks_fallthrough(node) for node in body)
def _exec_all_control_stmt(node, state) -> tuple[set[str], int, bool] | None:
    if isinstance(node, ast.If):
        return _merge_all_states((
            _exec_all_body(node.body, state),
            _exec_all_body(node.orelse, state),
        ))
    if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
        body_state = _exec_all_body(node.body, state)
        return _merge_all_states((
            state, body_state,
            _exec_all_body(node.orelse, state),
            _exec_all_body(node.orelse, body_state),
        ))
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return _exec_all_body(node.body, state)
    if isinstance(node, ast.Delete) and "__all__" in set(
            iter_unpack_target_names(node.targets)):
        return set(), node.lineno, True
    if is_try_statement(node):
        body_state = _exec_all_body(node.body, state)
        has_else = bool(node.orelse)
        body_falls_through = not _all_body_blocks_fallthrough(node.body)
        normal_state = (_exec_all_body(node.orelse, body_state) if has_else
                        else body_state)
        states = ([normal_state]
                  if body_falls_through or not node.handlers else [])
        if node.handlers:
            states.append(state)
            handler_state = _merge_all_states((state, body_state))
            states.extend(
                _exec_all_body(h.body, handler_state) for h in node.handlers)
        return _exec_all_body(node.finalbody, _merge_all_states(states))
    if hasattr(ast, "Match") and isinstance(node, ast.Match):
        return _merge_all_states(
            [state]
            + [_exec_all_body(case.body, state) for case in node.cases])
    return None
def _apply_all_augassign(op: ast.operator, names: set[str],
                         seg_names: set[str]) -> set[str] | None:
    if isinstance(op, (ast.Add, ast.BitOr)):
        return names | seg_names
    if isinstance(op, ast.Sub):
        return names - seg_names
    if isinstance(op, ast.BitAnd):
        return names & seg_names
    if isinstance(op, ast.BitXor):
        return names ^ seg_names
    return None
def _all_repeat_factor(node: ast.AST) -> int | None:
    if (isinstance(node, ast.Constant) and isinstance(node.value, int)
            and not isinstance(node.value, bool)):
        return node.value
    if (isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub)
            and isinstance(node.operand, ast.Constant)
            and isinstance(node.operand.value, int)
            and not isinstance(node.operand.value, bool)):
        return -node.operand.value
    return None
def _exec_all_stmt(node, state) -> tuple[set[str], int, bool]:
    control_state = _exec_all_control_stmt(node, state)
    if control_state is not None:
        return control_state
    seg = _all_segment_from_node(node)
    if seg is None:
        return state
    seg_names, seg_ok = seg
    if isinstance(node, (ast.Assign, ast.AnnAssign)):
        if _all_assign_value(node) is None:
            names, lineno, resolved = state
            return names, lineno or node.lineno, False
        return set(seg_names), node.lineno, seg_ok
    if isinstance(node, ast.AugAssign):
        names, lineno, resolved = state
        if isinstance(node.op, ast.Mult):
            factor = _all_repeat_factor(node.value)
            if factor is None:
                return names, lineno or node.lineno, False
            return (set(names) if factor > 0 else set()), node.lineno, resolved
        updated = _apply_all_augassign(node.op, names, seg_names)
        if updated is None:
            return names, lineno or node.lineno, False
        return updated, node.lineno, resolved and seg_ok
    names, lineno, resolved = state
    names |= seg_names
    return names, lineno or node.lineno, resolved and seg_ok
def extract_all_info(tree: ast.Module | None) -> tuple[set[str], int, bool]:
    if tree is None:
        logger.warning("extract_all_info: 解析失败，返回未解析空集合")
        return set(), 0, False
    tree = _prune_non_import_time_branches(tree)
    return _exec_all_body(tree.body, (set(), 0, True))
def _module_sub_bodies(node) -> list | None:
    if isinstance(node, (ast.If, ast.For, ast.AsyncFor, ast.While,
                         ast.With, ast.AsyncWith)) or is_try_statement(node):
        sub_bodies = [node.body,
                      getattr(node, "orelse", []),
                      getattr(node, "finalbody", [])]
        if is_try_statement(node):
            sub_bodies.extend(h.body for h in node.handlers)
    elif hasattr(ast, "Match") and isinstance(node, ast.Match):
        sub_bodies = [c.body for c in node.cases]
    else:
        return None
    return list(chain.from_iterable(sub_bodies))
def _iter_module_level_stmts(body: list):
    for node in body:
        yield node
        subs = _module_sub_bodies(node)
        if subs is not None:
            yield from _iter_module_level_stmts(subs)
def _is_all_name_target(target) -> bool:
    return isinstance(target, ast.Name) and target.id == "__all__"
_ALL_MUTATING_METHODS = frozenset({"extend", "append", "insert"})
_ALL_MEMBERSHIP_PRESERVING_METHODS = frozenset({
    "sort", "reverse", "copy", "count", "index",
})
def _is_all_subscript(target) -> bool:
    return isinstance(target, ast.Subscript) and _is_all_name_target(target.value)
def _all_targets_of(node) -> tuple:
    if isinstance(node, ast.Assign):
        return tuple(node.targets)
    if isinstance(node, (ast.AnnAssign, ast.AugAssign)):
        return (node.target,)
    if isinstance(node, ast.Delete):
        return tuple(node.targets)
    return ()
def _all_unmodeled_mutation(node) -> bool:
    if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
        func = node.value.func
        if (isinstance(func, ast.Attribute)
                and _is_all_name_target(func.value)
                and func.attr not in _ALL_MUTATING_METHODS
                and func.attr not in _ALL_MEMBERSHIP_PRESERVING_METHODS):
            return True
    return any(_is_all_subscript(t) for t in _all_targets_of(node))
def _append_const_segment(arg) -> tuple[set[str], bool] | None:
    if isinstance(arg, ast.Constant):
        if isinstance(arg.value, str):
            return {arg.value}, True
        return set(), True
    return None
def _all_extend_segment(
        node) -> tuple[set[str], bool] | None:
    if not (isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Call)):
        return None
    call = node.value
    func = call.func
    if not (isinstance(func, ast.Attribute)
            and func.attr in _ALL_MUTATING_METHODS
            and _is_all_name_target(func.value)
            and call.args):
        return None
    arg = call.args[0]
    if func.attr == "append":
        seg = _append_const_segment(arg)
        if seg is not None:
            return seg
        if isinstance(arg, (ast.List, ast.Tuple, ast.Set, ast.Dict)):
            return set(), True
        return set(), False
    if func.attr == "insert":
        if len(call.args) < 2:
            return set(), False
        seg = _append_const_segment(call.args[1])
        return seg if seg is not None else (set(), False)
    val = _unwrap_all_value(arg)
    return (val if val is not None else set(), val is not None)
def _all_segment_from_node(node) -> tuple[set[str], bool] | None:
    if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
        func = node.value.func
        if (isinstance(func, ast.Attribute)
                and _is_all_name_target(func.value)
                and func.attr in _ALL_MEMBERSHIP_PRESERVING_METHODS):
            return None
    if not isinstance(node, (ast.AnnAssign, ast.Assign, ast.AugAssign)):
        seg = _all_extend_segment(node)
        if seg is not None:
            return seg
        return (set(), False) if _all_unmodeled_mutation(node) else None
    value = _all_assign_value(node)
    if value is None:
        return (set(), False) if _all_unmodeled_mutation(node) else None
    val = _unwrap_all_value(value)
    return (val if val is not None else set(), val is not None)
_ALL_UNKNOWN_VALUE = object()
def _all_target_value(target, value):
    if _is_all_name_target(target):
        return value
    if not isinstance(target, (ast.Tuple, ast.List)):
        return None
    if not any(_is_all_name_target(part) for part in walk_nodes(target)):
        return None
    if (not isinstance(value, (ast.Tuple, ast.List))
            or len(target.elts) != len(value.elts)
            or any(isinstance(elt, ast.Starred) for elt in target.elts)):
        return _ALL_UNKNOWN_VALUE
    values = [_all_target_value(elt, value_elt)
              for elt, value_elt in zip(target.elts, value.elts)]
    values = [item for item in values if item is not None]
    if not values:
        return None
    first = values[0]
    if all(item is first for item in values[1:]):
        return first
    return _ALL_UNKNOWN_VALUE
def _all_assign_value(node):
    if isinstance(node, ast.AnnAssign):
        targets = () if node.value is None else (node.target,)
    elif isinstance(node, ast.Assign):
        targets = node.targets
    elif isinstance(node, ast.AugAssign):
        targets = (node.target,)
    else:
        return None
    values = [_all_target_value(target, node.value) for target in targets]
    values = [item for item in values if item is not None]
    if not values:
        return None
    first = values[0]
    if all(item is first for item in values[1:]):
        return first
    return _ALL_UNKNOWN_VALUE
def _is_module_namespace_call(node) -> bool:
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id in {"globals", "locals", "vars"}
            and not node.args and not node.keywords)
def _literal_module_namespace_delete(node) -> str | None:
    if not (isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Call)):
        return None
    call = node.value
    func = call.func
    if not (isinstance(func, ast.Attribute)
            and func.attr in {"pop", "__delitem__"}
            and _is_module_namespace_call(func.value)
            and len(call.args) == 1 and not call.keywords):
        return None
    key = call.args[0]
    return key.value if isinstance(key, ast.Constant) and isinstance(
        key.value, str) else None
_NAMESPACE_MUTATING_METHODS = frozenset({
    "update", "setdefault", "__setitem__",
    "pop", "popitem", "clear", "__delitem__",
})
def _has_dynamic_globals_mutation(node) -> bool:
    targets = (() if isinstance(node, ast.AnnAssign) and node.value is None
               else _all_targets_of(node))
    for target in targets:
        if any(isinstance(part, ast.Subscript)
               and _is_module_namespace_call(part.value)
               for part in walk_nodes(target)):
            return True
    if not (isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Call)):
        return False
    func = node.value.func
    return (isinstance(func, ast.Attribute)
            and func.attr in _NAMESPACE_MUTATING_METHODS
            and _is_module_namespace_call(func.value))
def _init_has_star_import(tree: ast.Module | None) -> bool:
    if tree is None:
        return False
    tree = _prune_non_import_time_branches(tree)
    return any(
        isinstance(node, ast.ImportFrom)
        and any(alias.name == "*" for alias in node.names)
        for node in _iter_module_level_stmts(tree.body))
def init_has_dynamic_export(tree: ast.Module | None) -> bool:
    if tree is None:
        return False
    tree = _prune_non_import_time_branches(tree)
    for node in _iter_module_level_stmts(tree.body):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) \
                and node.name == "__getattr__":
            return True
        if _has_dynamic_globals_mutation(node):
            return True
    return _init_has_star_import(tree)
def _unwrap_all_value(node) -> set[str] | None:
    pending = [node]
    result: set[str] = set()
    while pending:
        cur = pending.pop()
        if isinstance(cur, ast.BinOp) and isinstance(cur.op, ast.Mult):
            left_factor = _all_repeat_factor(cur.left)
            right_factor = _all_repeat_factor(cur.right)
            if left_factor is None and right_factor is None:
                return None
            if right_factor is not None:
                sequence, factor = cur.left, right_factor
            else:
                sequence, factor = cur.right, left_factor
            if factor > 0:
                pending.append(sequence)
            continue
        if isinstance(cur, ast.BinOp) and isinstance(cur.op, (ast.Add, ast.BitOr)):
            pending.extend((cur.left, cur.right))
            continue
        while (isinstance(cur, ast.Call) and isinstance(cur.func, ast.Name)
               and cur.func.id in ("sorted", "list", "tuple", "set")
               and len(cur.args) == 1):
            cur = cur.args[0]
        if not isinstance(cur, (ast.List, ast.Tuple, ast.Set)):
            return None
        segment: set[str] = set()
        for elt in cur.elts:
            if not isinstance(elt, ast.Constant):
                return None
            if isinstance(elt.value, str):
                segment.add(elt.value)
        result |= segment
    return result
_FILE_SCAN_MEMO: dict[str, tuple] = {}
_FILE_SCAN_MEMO_MAX = 4096
def _uses_future_annotations(tree) -> bool:
    for node in tree.body:
        if (isinstance(node, ast.ImportFrom)
                and node.module == "__future__"
                and node.level == 0
                and any(alias.name == "annotations" for alias in node.names)):
            return True
    return False
def _push_def_annotations(node, stack) -> None:
    _args = node.args
    for _va in (_args.vararg, _args.kwarg):
        if _va is not None and _va.annotation is not None:
            stack.append(_va.annotation)
    stack.extend(
        _p.annotation
        for _p in (*_args.posonlyargs, *_args.args, *_args.kwonlyargs)
        if _p.annotation is not None)
    if node.returns is not None:
        stack.append(node.returns)
def _defer_function_scope(node, stack, skip_annotations: bool) -> None:
    stack.extend(node.decorator_list)
    _args = node.args
    stack.extend(_args.defaults)
    stack.extend(d for d in _args.kw_defaults if d is not None)
    if not skip_annotations:
        _push_def_annotations(node, stack)
def _defer_class_scope(node, stack, _skip_annotations: bool) -> None:
    stack.extend(node.decorator_list)
    stack.extend(node.bases)
    stack.extend(kw.value for kw in node.keywords if kw.value is not None)
def _defer_lambda_scope(node, stack, _skip_annotations: bool) -> None:
    _args = node.args
    stack.extend(_args.defaults)
    stack.extend(d for d in _args.kw_defaults if d is not None)
def _iter_walrus_expr_events(node, conditional=False):
    if isinstance(node, ast.Lambda):
        roots = []
        _defer_lambda_scope(node, roots, False)
        for root in roots:
            yield from _iter_walrus_expr_events(root, conditional)
        return
    if isinstance(node, ast.NamedExpr):
        yield node, conditional
    if isinstance(node, ast.BoolOp):
        yield from _iter_walrus_expr_events(node.values[0], conditional)
        for value in node.values[1:]:
            yield from _iter_walrus_expr_events(value, True)
        return
    if isinstance(node, ast.IfExp):
        yield from _iter_walrus_expr_events(node.test, conditional)
        yield from _iter_walrus_expr_events(node.body, True)
        yield from _iter_walrus_expr_events(node.orelse, True)
        return
    if isinstance(node, ast.Compare):
        yield from _iter_walrus_expr_events(node.left, conditional)
        for index, comparator in enumerate(node.comparators):
            yield from _iter_walrus_expr_events(
                comparator, conditional if index == 0 else True)
        return
    if isinstance(node, (ast.ListComp, ast.SetComp,
                         ast.DictComp, ast.GeneratorExp)):
        for child in ast.iter_child_nodes(node):
            yield from _iter_walrus_expr_events(child, True)
        return
    for child in ast.iter_child_nodes(node):
        yield from _iter_walrus_expr_events(child, conditional)
def _iter_statement_walrus_events(node, skip_annotations: bool,
                                  conditional=False):
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        roots = []
        _defer_function_scope(node, roots, skip_annotations)
        for root in roots:
            yield from _iter_walrus_expr_events(root, conditional)
        return
    if isinstance(node, ast.ClassDef):
        roots = []
        _defer_class_scope(node, roots, skip_annotations)
        for root in roots:
            yield from _iter_walrus_expr_events(root, conditional)
        return
    if skip_annotations and isinstance(node, ast.AnnAssign):
        if node.value is not None:
            yield from _iter_walrus_expr_events(node.value, conditional)
        return
    if is_try_statement(node):
        for handler in node.handlers:
            if handler.type is not None:
                yield from _iter_walrus_expr_events(handler.type, True)
        return
    if isinstance(node, ast.Assert):
        yield from _iter_walrus_expr_events(node.test, conditional)
        if node.msg is not None:
            yield from _iter_walrus_expr_events(node.msg, True)
        return
    if hasattr(ast, 'Match') and isinstance(node, ast.Match):
        yield from _iter_walrus_expr_events(node.subject, conditional)
        for case in node.cases:
            if case.guard is not None:
                yield from _iter_walrus_expr_events(case.guard, True)
        return
    for child in ast.iter_child_nodes(node):
        if isinstance(child, ast.stmt):
            continue
        if isinstance(child, ast.expr):
            yield from _iter_walrus_expr_events(child, conditional)
        else:
            yield from _iter_statement_walrus_events(
                child, skip_annotations, conditional)
def _collect_statement_walrus_bindings(node, skip_annotations: bool):
    for event, conditional in _iter_statement_walrus_events(
            node, skip_annotations):
        if isinstance(event.target, ast.Name):
            yield event.target.id, event.lineno, conditional
def _flat_names(target) -> list[str]:
    if isinstance(target, ast.Name):
        return [target.id]
    if isinstance(target, (ast.Tuple, ast.List)):
        out: list[str] = []
        for elt in target.elts:
            out.extend(_flat_names(elt))
        return out
    if isinstance(target, ast.Starred):
        return _flat_names(target.value)
    return []
def _match_case_bound_names(pattern) -> set[str]:
    bound: set[str] = set()
    for _pn in walk_nodes(pattern):
        _bound = getattr(_pn, "name", None) or getattr(_pn, "rest", None)
        if isinstance(_bound, str):
            bound.add(_bound)
    return bound
@dataclass
class _TopBindCtx:
    records: list
    evidence: set
    code_exports: list
    rel_path: str
    collect_imports: bool
    imports: dict
    callables: set
    conditional: bool = False
    skip_annotations: bool = False
def _remove_top_export(ctx: _TopBindCtx, name: str) -> None:
    ctx.code_exports[:] = [
        export for export in ctx.code_exports
        if export.defined_in != ctx.rel_path or export.name != name
    ]
    ctx.records[:] = [record for record in ctx.records if record[0] != name]
def _emit_top_bind(ctx: _TopBindCtx, name: str, export_type: str, lineno: int) -> None:
    if not ctx.conditional:
        _remove_top_export(ctx, name)
    ctx.evidence.add(name)
    ctx.code_exports.append(CodeExport(
        name=name,
        export_type=export_type,
        defined_in=ctx.rel_path,
        line=lineno,
        is_public=not name.startswith("_"),
    ))
    ctx.records.append((name, export_type, lineno, False, None))
def _record_statement_walrus(ctx: _TopBindCtx, node) -> None:
    for name, lineno, conditional in _collect_statement_walrus_bindings(
            node, ctx.skip_annotations):
        previous = ctx.conditional
        ctx.conditional = previous or conditional
        try:
            _record_top_bind(ctx, name, "variable", lineno)
        finally:
            ctx.conditional = previous
def _record_top_bind(ctx: _TopBindCtx, name: str, export_type: str, lineno: int) -> None:
    if export_type in _CALLABLE_EXPORT_TYPES:
        ctx.callables.add(name)
    elif not ctx.conditional:
        ctx.callables.discard(name)
    if not ctx.conditional:
        ctx.imports.pop(name, None)
    if name.startswith("_"):
        ctx.evidence.add(name)
    else:
        _emit_top_bind(ctx, name, export_type, lineno)
def _emit_import_binds(ctx: _TopBindCtx, node) -> None:
    is_from_import = isinstance(node, ast.ImportFrom)
    export_type = "import" if is_from_import else "module"
    module = (
        "." * node.level + (node.module or "")
        if is_from_import else ""
    )
    for alias in node.names:
        bound = alias.asname or alias.name.split(".")[0]
        if bound == "*":
            continue
        import_source = (module, alias.name) if is_from_import else None
        if import_source is not None:
            ctx.imports[bound] = import_source
        if not ctx.conditional:
            ctx.callables.discard(bound)
        ctx.evidence.add(bound)
        if not bound.startswith("_"):
            if not ctx.conditional:
                _remove_top_export(ctx, bound)
            if ctx.collect_imports:
                ctx.code_exports.append(CodeExport(
                    name=bound,
                    export_type=export_type,
                    defined_in=ctx.rel_path,
                    line=node.lineno,
                    is_public=True,
                    import_source=import_source,
                ))
            ctx.records.append((
                bound, export_type, node.lineno, True, import_source))
def _bind_function(ctx: _TopBindCtx, node) -> None:
    _record_top_bind(ctx, node.name,
                     "function" if isinstance(node, ast.FunctionDef)
                     else "async_function", node.lineno)
def _bind_class(ctx: _TopBindCtx, node) -> None:
    _record_top_bind(ctx, node.name, "class", node.lineno)
def _bind_assign(ctx: _TopBindCtx, node) -> None:
    for _target in node.targets:
        for _name in _flat_names(_target):
            _record_top_bind(ctx, _name, "variable", node.lineno)
def _bind_annassign(ctx: _TopBindCtx, node) -> None:
    if node.value is not None and isinstance(node.target, ast.Name):
        _record_top_bind(ctx, node.target.id, "variable", node.lineno)
def _delete_top_names(ctx: _TopBindCtx, deleted: set[str]) -> None:
    if not deleted:
        return
    ctx.evidence.difference_update(deleted)
    ctx.callables.difference_update(deleted)
    for name in deleted:
        ctx.imports.pop(name, None)
    ctx.records[:] = [record for record in ctx.records
                      if record[0] not in deleted]
    ctx.code_exports[:] = [
        export for export in ctx.code_exports
        if export.defined_in != ctx.rel_path or export.name not in deleted
    ]
def _delete_top_bind(ctx: _TopBindCtx, node) -> None:
    _delete_top_names(ctx, {
        name
        for target in node.targets
        for name in _flat_names(target)
    })
def _bind_type_alias(ctx: _TopBindCtx, node) -> None:
    _record_top_bind(ctx, node.name.id, "type_alias", node.lineno)
_LEAF_BIND_RULES: tuple = (
    ((ast.FunctionDef, ast.AsyncFunctionDef), _bind_function),
    (ast.ClassDef, _bind_class),
    (ast.Assign, _bind_assign),
    (ast.AnnAssign, _bind_annassign),
    ((ast.Import, ast.ImportFrom), _emit_import_binds),
)
if hasattr(ast, "TypeAlias"):
    _LEAF_BIND_RULES = (*_LEAF_BIND_RULES, (ast.TypeAlias, _bind_type_alias))
def _dispatch_bind_rule(rules: tuple, ctx: _TopBindCtx, node) -> bool:
    for _types, _handler in rules:
        if isinstance(node, _types):
            _handler(ctx, node)
            return True
    return False
def _flow_for(ctx: _TopBindCtx, node) -> None:
    previous = ctx.conditional
    ctx.conditional = True
    try:
        for name in _flat_names(node.target):
            _record_top_bind(ctx, name, "variable", node.lineno)
        _walk_top_body(ctx, node.body, conditional=True)
        _walk_top_body(ctx, node.orelse, conditional=True)
    finally:
        ctx.conditional = previous
def _flow_with(ctx: _TopBindCtx, node) -> None:
    for item in node.items:
        if item.optional_vars is not None:
            for name in _flat_names(item.optional_vars):
                _record_top_bind(ctx, name, "variable", node.lineno)
    _walk_top_body(ctx, node.body, conditional=True)
def _flow_match(ctx: _TopBindCtx, node) -> None:
    previous = ctx.conditional
    ctx.conditional = True
    try:
        for case in node.cases:
            _line = getattr(case.pattern, "lineno", node.lineno)
            for name in sorted(_match_case_bound_names(case.pattern)):
                _record_top_bind(ctx, name, "variable", _line)
            _walk_top_body(ctx, case.body, conditional=True)
    finally:
        ctx.conditional = previous
_FLOW_BIND_RULES: tuple = (
    ((ast.For, ast.AsyncFor), _flow_for),
    ((ast.With, ast.AsyncWith), _flow_with),
)
if hasattr(ast, "Match"):
    _FLOW_BIND_RULES = (*_FLOW_BIND_RULES, (ast.Match, _flow_match))
def _walk_block_children(ctx: _TopBindCtx, node, *,
                         conditional: bool) -> bool:
    if is_try_statement(node):
        for body in (node.body, node.orelse,
                     *(handler.body for handler in node.handlers)):
            _walk_top_body(ctx, body, conditional=True)
        _walk_top_body(ctx, node.finalbody, conditional=conditional)
        return True
    sub_nodes = _module_sub_bodies(node)
    if sub_nodes is None:
        return False
    for sub_node in sub_nodes:
        _walk_top_body(ctx, [sub_node], conditional=True)
    return True
def _walk_top_body(ctx: _TopBindCtx, body: list, *,
                   conditional: bool = False) -> None:
    previous = ctx.conditional
    ctx.conditional = conditional
    try:
        for node in body:
            _record_statement_walrus(ctx, node)
            if isinstance(node, ast.Delete) and not conditional:
                _delete_top_bind(ctx, node)
                continue
            literal_delete = _literal_module_namespace_delete(node)
            if literal_delete is not None and not conditional:
                _delete_top_names(ctx, {literal_delete})
                continue
            if _dispatch_bind_rule(_LEAF_BIND_RULES, ctx, node):
                continue
            if _dispatch_bind_rule(_FLOW_BIND_RULES, ctx, node):
                continue
            _walk_block_children(ctx, node, conditional=conditional)
    finally:
        ctx.conditional = previous
def _collect_class_methods(tree) -> set:
    _cls_methods: set = set()
    for _node in walk_nodes(tree):
        if not isinstance(_node, ast.ClassDef):
            continue
        _stack: list[ast.AST] = list(_node.body)
        while _stack:
            _sub = _stack.pop()
            if isinstance(_sub, (ast.FunctionDef, ast.AsyncFunctionDef)):
                _cls_methods.add(_sub.name)
                continue
            if isinstance(_sub, (ast.ClassDef, ast.Lambda)):
                continue
            _stack.extend(ast.iter_child_nodes(_sub))
    return _cls_methods
def _list_dir_entries(skill_dir: str) -> list[str]:
    try:
        return os.listdir(skill_dir)
    except OSError as _e:
        logger.debug(
            '静默降级[_list_dir_entries:OSError]: %s: %s',
            type(_e).__name__, _e)
        return []
def _collect_top_module_stems(skill_dir: str,
                              entries: list[str]) -> set[str]:
    return {
        fn[:-3] for fn in entries
        if is_scan_py_name(fn) and fn.lower() != "__init__.py"
        and fn[:-3].isidentifier()
        and not is_diagnosis_out_of_scope(
            os.path.join(skill_dir, fn), skill_dir)
    }
def _prune_dir_by_root(name: str, root_dir: str) -> bool:
    probe = [name]
    prune_ignore_dirs(probe, root_dir)
    return not probe
def _collect_subpackage_names(skill_dir: str, entries: list[str]) -> set[str]:
    return {
        fn for fn in entries
        if os.path.isdir(os.path.join(skill_dir, fn))
        and not fn.startswith(".")
        and fn.isidentifier()
        and fn != RUNTIME_DIR_NAME
        and not is_diagnosis_out_of_scope(
            os.path.join(skill_dir, fn, "__init__.py"), skill_dir)
        and not _prune_dir_by_root(fn, skill_dir)
        and not is_backup_like_dir(fn)
    }
def _rel_path_of(filepath: str, dir_prefix: str, skill_dir: str) -> str:
    if filepath.startswith(dir_prefix):
        return filepath[len(dir_prefix):]
    return os.path.relpath(filepath, skill_dir)
def _read_via_cache(cache: Any, getter_name: str, filepath: str):
    if cache is None:
        return None
    try:
        return getattr(cache, getter_name)(filepath)
    except CacheNotWarmedError:
        raise
    except Exception:
        logger.warning("%s: cache 读取失败，回退直读 %s", getter_name,
                       filepath, exc_info=True)
        return None
def _file_content_sha256(filepath: str) -> str | None:
    digest = hashlib.sha256()
    try:
        with open(filepath, "rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError as _e:
        logger.debug('静默降级[PackageExportScanner._file_content_sha256:OSError]: %s: %s',
                     type(_e).__name__, _e)
        return None
    return digest.hexdigest()
def _file_scan_fingerprint(filepath: str) -> tuple:
    _mtime_ns: int | None
    _size: int | None
    try:
        _st = os.stat(filepath)
        _mtime_ns, _size = _st.st_mtime_ns, _st.st_size
    except OSError as _e:
        logger.debug('静默降级[_file_scan_fingerprint:OSError]: %s: %s',
                     type(_e).__name__, _e)
        _mtime_ns = _size = None
    content_sha256 = _file_content_sha256(filepath)
    _hit = _FILE_SCAN_MEMO.get(filepath)
    if (_hit is not None and _mtime_ns is not None
            and content_sha256 is not None and len(_hit) >= 9
            and _hit[0] == _mtime_ns and _hit[1] == _size
            and _hit[8] == content_sha256):
        return _hit, (_mtime_ns, _size, content_sha256)
    return None, (_mtime_ns, _size, content_sha256)
class PackageExportScanner:
    def __init__(self, skill_dir: str, cache: Any = None):
        self.skill_dir = os.path.abspath(skill_dir)
        self.cache = cache
        self.package_root = self.skill_dir
        self._dir_prefix = self.skill_dir + os.sep
        self.refresh_pkg_identity()
        self._reset_scan_state()
    def _reset_scan_state(self) -> None:
        self.incomplete_files: set[str] = set()
        self.code_exports: list[CodeExport] = []
        self.binding_evidence: set[str] = set()
        self.all_ghosts: list[str] = []
        self.all_line: int = 0
        self.all_names: set[str] = set()
        self.class_method_names: set[str] = set()
        self.module_bindings: dict[str, set[str]] = {}
        self.module_imports: dict[str, dict[str, tuple[str, str]]] = {}
        self.module_callables: dict[str, set[str]] = {}
        self.module_dynamic: dict[str, bool] = {}
    def refresh_pkg_identity(self) -> None:
        layout = detect_layout(self.skill_dir)
        self.package_root = os.path.abspath(
            layout.package_root or self.skill_dir)
        self.pkg_name = layout.package_name or os.path.basename(
            self.package_root)
        self._dir_prefix = self.package_root + os.sep
        _entries_ls = _list_dir_entries(self.package_root)
        self.local_modules = (
            _collect_top_module_stems(self.package_root, _entries_ls)
            | _collect_subpackage_names(self.package_root, _entries_ls)
        )
    def _get_ast(self, filepath: str):
        tree = _read_via_cache(self.cache, "get_ast", filepath)
        if tree is not None:
            return tree
        text = read_source(filepath)
        if text is None:
            self._mark_incomplete(filepath)
            return None
        try:
            return ast.parse(text)
        except (SyntaxError, ValueError) as _e:
            self._mark_incomplete(filepath)
            logger.debug('静默降级[PackageExportScanner._get_ast:SyntaxError]: %s: %s', type(_e).__name__, _e)
            return None
        except (RecursionError, MemoryError) as _e:
            self._mark_incomplete(filepath)
            logger.debug('静默降级[PackageExportScanner._get_ast:Resource]: %s: %s', type(_e).__name__, _e)
            return None
    def _mark_incomplete(self, filepath: str) -> None:
        self.incomplete_files.add(
            _rel_path_of(filepath, self._dir_prefix, self.skill_dir))
    def get_source_for_scan(self, filepath: str) -> str | None:
        src = _read_via_cache(self.cache, "get_source", filepath)
        if src is not None:
            return src
        src = read_source(filepath)
        if src is None:
            self._mark_incomplete(filepath)
        return src
    def scan(self) -> None:
        self._reset_scan_state()
        self.refresh_pkg_identity()
        all_names, all_resolved, _init_tree = self._scan_init_file()
        self._scan_package_files()
        self._add_local_module_exports()
        dynamic_guard = (
            self.module_dynamic.get(_ENTRY_MODULE_REL, False)
            or not all_resolved)
        self._apply_all_exports(all_names, dynamic_guard)
    def _scan_init_file(self) -> tuple[set[str], bool, ast.Module | None]:
        init_path = os.path.join(self.package_root, "__init__.py")
        all_names: set[str] = set()
        all_resolved = True
        init_tree: ast.Module | None = None
        if os.path.isfile(init_path):
            init_tree = self._get_ast(init_path)
            self._scan_file_exports(init_path, collect_imports=True,
                                    tree=init_tree)
            all_names, all_line, all_resolved = extract_all_info(init_tree)
            self.all_line = all_line
            self.all_names = all_names
        return all_names, all_resolved, init_tree
    def _scan_package_files(self) -> None:
        init_path = os.path.normcase(
            os.path.join(self.package_root, "__init__.py"))
        for filepath in _iter_scannable_python_files(self.package_root):
            if os.path.normcase(filepath) != init_path:
                self._scan_file_exports(filepath)
    def _add_local_module_exports(self) -> None:
        for _mod in sorted(self.local_modules):
            self.binding_evidence.add(_mod)
            if _mod.startswith("_"):
                continue
            self.code_exports.append(CodeExport(
                name=_mod,
                export_type="module",
                defined_in=(
                    _mod if os.path.isdir(
                        os.path.join(self.package_root, _mod))
                    else f"{_mod}.py"),
                line=0,
                is_public=True,
            ))
    def _apply_all_exports(self, all_names: set, dynamic_guard: bool) -> None:
        if self.incomplete_files:
            logger.info(
                "[A14] %d 个文件扫描不完整，跳过 __all__ 幽灵判定: %s",
                len(self.incomplete_files),
                sorted(self.incomplete_files)[:5])
            self.all_ghosts = []
        elif not dynamic_guard:
            root_bindings = self.module_bindings.get(
                _ENTRY_MODULE_REL, set())
            self.all_ghosts = sorted(
                n for n in all_names
                if n not in root_bindings and n not in self.local_modules
            )
        else:
            self.all_ghosts = []
        ghost_set = set(self.all_ghosts)
        existing_export_names = {e.name for e in self.code_exports}
        for name in sorted(all_names):
            if name in ghost_set:
                continue
            if name not in existing_export_names:
                self.code_exports.append(CodeExport(
                    name=name,
                    export_type="unknown",
                    defined_in="__init__.py",
                    line=0,
                    is_public=not name.startswith("_"),
                ))
    def _replay_file_scan_memo(self, hit, rel_path: str, collect_imports: bool) -> None:
        for name, export_type, lineno, is_import, import_source in hit[2]:
            if is_import and not collect_imports:
                continue
            self.binding_evidence.add(name)
            self.code_exports.append(CodeExport(
                name=name,
                export_type=export_type,
                defined_in=rel_path,
                line=lineno,
                is_public=not name.startswith("_"),
                import_source=import_source,
            ))
        self.binding_evidence.update(hit[3])
        self.module_bindings[rel_path] = set(hit[3])
        self.module_dynamic[rel_path] = hit[5]
        self.module_imports[rel_path] = dict(hit[6])
        self.module_callables[rel_path] = set(hit[7])
        self.class_method_names.update(hit[4])
    def _extract_file_bindings(self, tree, rel_path: str,
                               collect_imports: bool) -> tuple[_TopBindCtx, set]:
        tree = _prune_non_import_time_branches(tree)
        ctx = _TopBindCtx(
            records=[],
            evidence=set(),
            code_exports=self.code_exports,
            rel_path=rel_path,
            collect_imports=collect_imports,
            imports={},
            callables=set(),
            skip_annotations=_uses_future_annotations(tree),
        )
        _walk_top_body(ctx, list(ast.iter_child_nodes(tree)))
        return ctx, _collect_class_methods(tree)
    def _memoize_file_scan(self, filepath: str, fingerprint: tuple,
                           ctx: _TopBindCtx, cls_methods: set,
                           dynamic: bool) -> None:
        mtime_ns, size, content_sha256 = fingerprint
        self.module_bindings[ctx.rel_path] = set(ctx.evidence)
        self.module_dynamic[ctx.rel_path] = dynamic
        self.module_imports[ctx.rel_path] = dict(ctx.imports)
        self.module_callables[ctx.rel_path] = set(ctx.callables)
        self.binding_evidence.update(ctx.evidence)
        if mtime_ns is None or content_sha256 is None:
            return
        if len(_FILE_SCAN_MEMO) >= _FILE_SCAN_MEMO_MAX:
            _FILE_SCAN_MEMO.clear()
        _FILE_SCAN_MEMO[filepath] = (
            mtime_ns, size, tuple(ctx.records), frozenset(ctx.evidence),
            frozenset(cls_methods), dynamic, tuple(ctx.imports.items()),
            frozenset(ctx.callables), content_sha256)
    def _scan_file_exports(self, filepath: str, collect_imports: bool = False,
                           tree=None):
        rel_path = _rel_path_of(filepath, self._dir_prefix, self.skill_dir)
        hit, _fp = _file_scan_fingerprint(filepath)
        if hit is not None:
            self._replay_file_scan_memo(hit, rel_path, collect_imports)
            return
        if tree is None:
            tree = self._get_ast(filepath)
        if tree is None:
            logger.warning("_scan_file_exports: skipped %s (parse failed)", rel_path)
            return
        ctx, _cls_methods = self._extract_file_bindings(
            tree, rel_path, collect_imports)
        self.class_method_names.update(_cls_methods)
        dynamic = init_has_dynamic_export(tree) or '__getattr__' in ctx.evidence
        self._memoize_file_scan(
            filepath, _fp, ctx, _cls_methods, dynamic)

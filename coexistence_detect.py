from __future__ import annotations

import ast
import hashlib
import logging
import math
import os
import re
from collections import defaultdict
from collections.abc import Callable, Iterable, Iterator
from dataclasses import dataclass, field
from functools import cache
from itertools import combinations
from pathlib import Path
from typing import Any, Self

from jwsgj.diag_shared_ast_bindings import import_stmt_binds
from jwsgj.diag_shared_ast_nodes import (
    call_tail_name,
    collect_param_names,
    dotted_name,
    is_docstring_stmt,
    iter_arg_nodes,
    iter_unpack_target_names,
    type_last_name,
)
from jwsgj.diag_shared_ast_surface import module_export_names
from jwsgj.diag_shared_ast_views import (
    parent_map,
    tree_nodes,
)
from jwsgj.diag_shared_source_core import (
    parse_py_source,
    read_source_text,
    resolve_module_name,
)
from jwsgj.diag_shared_source_scan import (
    comment_tokens,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    SCAN_COLLECT_PRUNE_DIRS,
    is_backup_snapshot_dir,
)

__all__ = [
    'COEXISTENCE_STRATEGIES',
    'NOISE_REFS',
    'TRIVIAL_HASHES',
    'UNSPECIFIED_TARGET',
    'CoexistenceItem',
    'CrossFileIndex',
    'DefEntry',
    'ScanContext',
    'body_hash',
    'body_without_docstring',
    'build_cross_file_index',
    'camel_tokens',
    'check_deprecated',
    'check_similarity_pair_valid',
    'collect_calls_from_nodes',
    'collect_referenced_names',
    'detect_conditional_routing',
    'detect_delegation',
    'detect_deprecated_markers',
    'detect_dual_write',
    'detect_import_bridge',
    'detect_migration_markers',
    'detect_partial_delegation',
    'detect_same_name',
    'detect_semantic_similar',
    'detect_shadow_functions',
    'detect_stub_real',
    'determine_old_new',
    'has_new_name_hint',
    'has_old_name_hint',
    'has_strict_new_hint',
    'has_strict_old_hint',
    'is_delegation',
    'is_stub',
    'is_thin_delegate_entry',
    'is_unspecified_target',
    'make_def_entry',
    'name_similarity',
    'name_tokens',
    'run_coexistence_strategies',
    'stmt_hash',
    'version_suffix',
]
_log = logging.getLogger(__name__)
@dataclass
class CoexistenceItem:
    pattern_type: str = ""
    old_name: str = ""
    new_name: str = ""
    old_file: str = ""
    new_file: str = ""
    old_lines: tuple[int, int] = (0, 0)
    new_lines: tuple[int, int] = (0, 0)
    confidence: float = 0.0
    evidence: list[str] = field(default_factory=list)
    suggestion: str = ""
    category: str = "coexistence"
    severity: str = "warning"
    verified: bool = False
    reason: str = ""
UNSPECIFIED_TARGET = "(未指定)"
@dataclass
class DefEntry:
    name: str
    kind: str
    file_path: str
    lineno: int
    end_lineno: int
    is_stub: bool = False
    is_deprecated: bool = False
    deprecated_replacement: str = ""
    body_hash: str = ""
    is_dead: bool = False
    referenced_names: set[str] = field(default_factory=set)
    bases: set[str] = field(default_factory=set)
    parent_class: str = ""
class CrossFileIndex:
    def __init__(self: Self) -> None:
        self.definitions: dict[str, list[DefEntry]] = defaultdict(
            list
        )
        self.all_refs: set[str] = set()
        self.all_defs: set[str] = set()
    def add_definition(self: Self, entry: DefEntry) -> None:
        self.definitions[entry.name].append(entry)
        self.all_defs.add(entry.name)
    def add_reference(self: Self, name: str) -> None:
        self.all_refs.add(name)
    def is_referenced(self: Self, name: str) -> bool:
        return name in self.all_refs
    def get_same_name_defs(self: Self) -> dict[str, list[DefEntry]]:
        return {
            name: entries
            for name, entries in self.definitions.items()
            if len(entries) >= 2
        }
@dataclass
class ScanContext:
    skill_dir: Path
    py_files: list[str] = field(default_factory=list)
    file_sources: dict[str, str] = field(
        default_factory=dict
    )
    file_trees: dict[str, ast.AST] = field(default_factory=dict)
    index: CrossFileIndex = field(default_factory=CrossFileIndex)
    scope_maps: dict[str, tuple[dict[ast.AST, ast.AST],
                                dict[ast.AST, frozenset[str]],
                                dict[str, str]]] = field(
        default_factory=dict, repr=False, compare=False)
_VERSION_SUFFIX_RE = re.compile(r"_v(\d+)$", re.IGNORECASE)
_NEW_VERSION_NUMBER_PATTERN = r"(?:[2-9]|[1-9]\d+)"
_OLD_NAME_PATTERNS = [
    re.compile(r"^old_", re.IGNORECASE),
    re.compile(r"^legacy_", re.IGNORECASE),
    re.compile(r"^deprecated_", re.IGNORECASE),
    re.compile(r"_old$", re.IGNORECASE),
    _VERSION_SUFFIX_RE,
    re.compile(r"^v1_", re.IGNORECASE),
    re.compile(r"_legacy$", re.IGNORECASE),
    re.compile(r"_deprecated$", re.IGNORECASE),
    re.compile(r"_bak$", re.IGNORECASE),
    re.compile(r"_backup$", re.IGNORECASE),
    re.compile(r"_prev$", re.IGNORECASE),
]
_NEW_NAME_PATTERNS = [
    re.compile(r"^new_", re.IGNORECASE),
    re.compile(r"_new$", re.IGNORECASE),
    _VERSION_SUFFIX_RE,
    re.compile(
        rf"^v{_NEW_VERSION_NUMBER_PATTERN}_", re.IGNORECASE),
]
_OLD_MARKER_PAT = (
    r"(?<![a-zA-Z])(?:old|legacy|deprecated|backups?)(?![a-zA-Z])"
    r"|_v1(?![a-zA-Z0-9])|_bak(?![a-zA-Z])|_prev(?![a-zA-Z])"
    r"|(?<![a-zA-Z0-9])v1(?![a-zA-Z0-9])"
)
_OLD_MARKER_RE: re.Pattern = re.compile(_OLD_MARKER_PAT, re.IGNORECASE)
NOISE_REFS = frozenset(
    {
        "self",
        "cls",
        "True",
        "False",
        "None",
        "str",
        "int",
        "float",
        "bool",
        "dict",
        "list",
        "set",
        "tuple",
        "len",
        "range",
        "enumerate",
        "zip",
        "sorted",
        "reversed",
        "isinstance",
        "issubclass",
        "type",
        "id",
        "hash",
        "repr",
        "print",
        "open",
        "super",
        "property",
        "classmethod",
        "Exception",
        "ValueError",
        "TypeError",
        "KeyError",
        "RuntimeError",
        "OSError",
        "ImportError",
        "NotImplementedError",
        "Any",
        "Optional",
        "List",
        "Dict",
        "Set",
        "Tuple",
        "Union",
        "field",
        "asdict",
        "dataclass",
    }
)
_TRIVIAL_BODY_PARTS = (
    "Pass",
    "Return|void",
    "Return|const",
    "Return|expr",
    "",
)
TRIVIAL_HASHES = frozenset(
    hashlib.md5(part.encode(), usedforsecurity=False).hexdigest()[:12]
    for part in _TRIVIAL_BODY_PARTS
)
def body_without_docstring(body: list[ast.stmt]) -> list[ast.stmt]:
    if body and is_docstring_stmt(body[0]):
        return body[1:]
    return body
_EXCLUDED_DIRS: frozenset[str] = frozenset(SCAN_COLLECT_PRUNE_DIRS) | {
    "tests",
    "_versions",
}
_EXCLUDED_FILES: frozenset[str] = frozenset({"conftest.py", "setup.py"})
_EXCLUDED_DIRS_LOWER = frozenset(d.lower() for d in _EXCLUDED_DIRS)
_EXCLUDED_FILES_LOWER = frozenset(f.lower() for f in _EXCLUDED_FILES)
_DEPRECATED_PATTERNS: tuple[re.Pattern[str], ...] = (
    re.compile(
        r"(?:已废弃|已弃用|已过时|已淘汰|不推荐使用).*?(?:请改用|建议使用|推荐使用|改用|迁移到)\s*(\w+)"
    ),
    re.compile(r"(?:已废弃|已弃用|已过时).+?(\w+)"),
    re.compile(r"(?:请改用|建议使用|推荐使用|迁移到)\s*(\w+)"),
    re.compile(r"(?:use|see|prefer)\s+(\w+)\s+instead", re.IGNORECASE),
    re.compile(r"(?:replaced\s+by|superseded\s+by)\s+(\w+)", re.IGNORECASE),
)
_DEPRECATED_ENGLISH_KEYWORD_RE = re.compile(
    r"(?:deprecated|obsolete|outdated|superseded)", re.IGNORECASE)
_DEPRECATED_ACTION_RE = re.compile(
    r"\b(?:use|see|prefer)\s+(\w+)", re.IGNORECASE)
_DEPRECATED_NEGATED_ACTION_RE = re.compile(
    r"(?:\b(?:do|does|did)\s+not|\bdon['’]t|\bnever)\s+$",
    re.IGNORECASE,
)
_DEPRECATED_NEGATED_KEYWORD_RE = re.compile(
    r"(?:\b(?:not|never|non)|\bno\s+longer|\bisn['’]t)[\s-]*$",
    re.IGNORECASE,
)
_DEPRECATED_KEYWORD_RE = re.compile(
    r"(?:deprecated|obsolete|outdated|superseded|已废弃|已弃用|已过时"
    r"|已淘汰|不推荐使用)",
    re.IGNORECASE,
)
_DEPRECATED_STOPWORDS = frozenset(
    {
        "a", "an", "the", "this", "that", "these", "those", "it", "its",
        "for", "to", "of", "in", "on", "at", "and", "or", "is", "are",
        "was", "were", "be", "been", "here", "below", "above", "instead",
        "use", "see", "prefer",
        "docs", "doc", "documentation",
    }
)
_DefNode = ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef
_DEPRECATED_COMMENT_WINDOW = 4
def is_stub(node: _DefNode) -> bool:
    body = body_without_docstring(list(node.body))
    if not body:
        return True
    return len(body) == 1 and _is_single_stmt_stub(body[0])
def _stub_shape_pass(stmt: ast.stmt) -> bool:
    return isinstance(stmt, ast.Pass)
def _stub_shape_notimpl(stmt: ast.stmt) -> bool:
    if not isinstance(stmt, ast.Raise):
        return False
    exc = stmt.exc
    if isinstance(exc, ast.Call):
        exc = exc.func
    return type_last_name(exc) == "NotImplementedError"
def _stub_shape_const_return(stmt: ast.stmt) -> bool:
    return isinstance(stmt, ast.Return) and (
        stmt.value is None or isinstance(stmt.value, ast.Constant))
def _stub_shape_none_expr(stmt: ast.stmt) -> bool:
    return (isinstance(stmt, ast.Expr)
            and isinstance(stmt.value, ast.Constant)
            and stmt.value.value in (None, ...))
_STUB_SHAPES = (_stub_shape_pass, _stub_shape_notimpl,
                _stub_shape_const_return, _stub_shape_none_expr)
def _is_single_stmt_stub(stmt: ast.stmt) -> bool:
    return any(check(stmt) for check in _STUB_SHAPES)
def _collect_deco_text(node: ast.AST) -> str:
    return "".join(
        _deco_text(dec) for dec in getattr(node, "decorator_list", []))
def _deco_text(dec: ast.AST) -> str:
    if isinstance(dec, ast.Call):
        return _deco_call_text(dec)
    name = type_last_name(dec)
    return " " + name if name else ""
def _deco_call_text(dec: ast.Call) -> str:
    func_name = type_last_name(dec.func)
    arg_texts = [
        a.value for a in dec.args
        if isinstance(a, ast.Constant) and isinstance(a.value, str)
    ] + [
        kw.value.value for kw in dec.keywords
        if isinstance(kw.value, ast.Constant)
        and isinstance(kw.value.value, str)
    ]
    return " ".join([" ", func_name, *arg_texts]).rstrip()
def _adjacent_comment_text(lines: list[str], anchor_line: int) -> str:
    texts: list[str] = []
    blank_run = 0
    index = anchor_line - 2
    lower_bound = max(0, anchor_line - 1 - _DEPRECATED_COMMENT_WINDOW)
    while index >= lower_bound:
        text = lines[index].strip()
        if text.startswith("#"):
            texts.append(text.lstrip("#").strip())
            blank_run = 0
        elif not text:
            blank_run += 1
            if blank_run > 1:
                break
        else:
            break
        index -= 1
    return " ".join(reversed(texts))
def _deprecated_action_is_negated(text: str, action_start: int) -> bool:
    return _DEPRECATED_NEGATED_ACTION_RE.search(
        text[:action_start]) is not None
def _positive_keyword_match(
    text: str, pattern: re.Pattern[str]
) -> re.Match[str] | None:
    return next(
        (
            match for match in pattern.finditer(text)
            if _DEPRECATED_NEGATED_KEYWORD_RE.search(
                text[:match.start()]) is None
        ),
        None,
    )
def _deprecated_english_replacement(text: str) -> str:
    keyword = _positive_keyword_match(
        text, _DEPRECATED_ENGLISH_KEYWORD_RE)
    if keyword is None:
        return ""
    for match in _DEPRECATED_ACTION_RE.finditer(text, keyword.end()):
        if _deprecated_action_is_negated(text, match.start()):
            continue
        replacement = _valid_replacement(match.group(1))
        if replacement:
            return replacement
    return ""
def check_deprecated(node: _DefNode, lines: list[str]) -> tuple[bool, str]:
    docstring = ast.get_docstring(node) or ""
    deco_text = _collect_deco_text(node)
    anchor_line = (node.decorator_list[0].lineno
                   if node.decorator_list else node.lineno)
    above_comments = _adjacent_comment_text(lines, anchor_line)
    combined = f"{docstring} {deco_text} {above_comments}"
    if _positive_keyword_match(combined, _DEPRECATED_KEYWORD_RE) is None:
        return False, ""
    for pattern in _DEPRECATED_PATTERNS:
        m = pattern.search(combined)
        if m and not _deprecated_action_is_negated(combined, m.start()):
            replacement = _valid_replacement(m.group(1))
            if replacement:
                return True, replacement
    return True, _deprecated_english_replacement(combined)
_ASCII_IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
def _valid_replacement(candidate: str | None) -> str:
    if (candidate
            and candidate.lower() not in _DEPRECATED_STOPWORDS
            and _ASCII_IDENTIFIER_RE.match(candidate)):
        return candidate
    return ""
_TRY_STMT_TYPES = ((ast.Try, ast.TryStar) if hasattr(ast, "TryStar")
                  else (ast.Try,))
def _return_value_tag(value: ast.expr | None) -> str:
    if value is None:
        return "void"
    if isinstance(value, ast.Constant):
        return "const"
    if isinstance(value, ast.Call):
        return f"call:{call_tail_name(value)}"
    return "expr"
def _expr_tag(value: ast.expr | None) -> str:
    if isinstance(value, ast.Call):
        return f"call:{call_tail_name(value)}"
    return type(value).__name__.lower() if value is not None else "none"
def stmt_hash(stmt: ast.stmt) -> str:
    name = type(stmt).__name__
    if isinstance(stmt, ast.If):
        extra = f"if_{len(stmt.body)}"
        if stmt.orelse:
            extra += f"_else_{len(stmt.orelse)}"
        return f"{name}|{extra}"
    if isinstance(stmt, ast.For):
        return f"{name}|for_{len(stmt.body)}"
    if isinstance(stmt, ast.While):
        return f"{name}|while_{len(stmt.body)}"
    if isinstance(stmt, ast.Return):
        return f"{name}|{_return_value_tag(stmt.value)}"
    if isinstance(stmt, ast.Assign):
        return f"{name}|{_expr_tag(stmt.value)}"
    if isinstance(stmt, ast.Expr):
        return f"{name}|{_expr_tag(stmt.value)}"
    if isinstance(stmt, _TRY_STMT_TYPES):
        return f"{name}|try_{len(stmt.body)}_h{len(stmt.handlers)}"
    return name
def body_hash(node: ast.AST) -> str:
    body = body_without_docstring(list(node.body))
    parts = [stmt_hash(stmt) for stmt in body]
    return hashlib.md5("|".join(parts).encode(), usedforsecurity=False).hexdigest()[:12]
def collect_referenced_names(node: ast.AST) -> set[str]:
    refs: set[str] = set()
    for child in walk_nodes(node):
        if isinstance(child, ast.Name) and isinstance(child.ctx, ast.Load):
            refs.add(child.id)
        elif (isinstance(child, ast.Attribute)
              and isinstance(child.ctx, ast.Load)):
            refs.add(child.attr)
    return refs
def make_def_entry(
    node: _DefNode,
    file_path: str,
    lines: list[str],
    *,
    kind: str = "function",
    parent_class: str = "",
) -> DefEntry:
    is_deprecated, replacement = check_deprecated(node, lines)
    return DefEntry(
        name=node.name,
        kind=kind,
        file_path=file_path,
        lineno=node.lineno,
        end_lineno=node.end_lineno or node.lineno,
        is_stub=is_stub(node),
        is_deprecated=is_deprecated,
        deprecated_replacement=replacement,
        body_hash=body_hash(node),
        referenced_names=collect_referenced_names(node),
        bases=_collect_bases(node) if kind == "class" else set(),
        parent_class=parent_class,
    )
def _collect_bases(node: ast.AST) -> set[str]:
    bases: set[str] = set()
    for base in getattr(node, "bases", ()):
        name = type_last_name(base)
        if name:
            bases.add(name)
    return bases
def _pruned_dir(dirname: str) -> bool:
    return (
        dirname.lower() in _EXCLUDED_DIRS_LOWER
        or dirname.startswith(".")
        or is_backup_snapshot_dir(dirname)
    )
def _indexable_file(fname: str) -> bool:
    return (
        fname.lower().endswith(".py")
        and not fname.startswith(".")
        and fname.lower() not in _EXCLUDED_FILES_LOWER
    )
def _collect_py_files(skill_dir: Path) -> list[str]:
    py_files: list[str] = []
    def _on_walk_error(error: OSError) -> None:
        _log.warning(
            "coexistence_detect:_collect_py_files: 目录遍历失败，索引不完整: %s (%s)",
            getattr(error, "filename", ""),
            error,
        )
    for root, dirs, files in os.walk(skill_dir, onerror=_on_walk_error):
        dirs[:] = [d for d in dirs if not _pruned_dir(d)]
        for fname in files:
            if _indexable_file(fname):
                py_files.append(os.path.join(root, fname))
    return sorted(py_files)
def _qualified_scope(parent_scope: str, name: str) -> str:
    return f"{parent_scope}.{name}" if parent_scope else name
def _iter_defs(node: ast.AST,
               parent_scope: str) -> Iterator[tuple[_DefNode, str]]:
    for child in ast.iter_child_nodes(node):
        if isinstance(
            child, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)
        ):
            yield child, parent_scope
            yield from _iter_defs(
                child, _qualified_scope(parent_scope, child.name))
        else:
            yield from _iter_defs(child, parent_scope)
def _index_one_file(ctx: ScanContext, file_path: str) -> None:
    source = read_source_text(file_path)
    if source is None:
        _log.warning(
            "coexistence_detect:_index_one_file: 源文件读取失败，跳过索引: %s",
            file_path,
        )
        return
    ctx.file_sources[file_path] = source
    tree, parse_error = parse_py_source(source)
    if tree is None:
        _log.warning(
            "coexistence_detect:_index_one_file: 源文件解析失败，跳过索引: %s (%s)",
            file_path,
            parse_error,
        )
        return
    ctx.file_trees[file_path] = tree
    pre_lines = source.split("\n")
    for node, parent_cls in _iter_defs(tree, ""):
        kind = "class" if isinstance(node, ast.ClassDef) else "function"
        entry = make_def_entry(
            node, file_path, pre_lines, kind=kind, parent_class=parent_cls)
        ctx.index.add_definition(entry)
def _dynamic_ref_name(node: ast.Call) -> str | None:
    if not (isinstance(node.func, ast.Name)
            and node.func.id in ("getattr", "hasattr", "setattr", "delattr")):
        return None
    if (len(node.args) >= 2
            and isinstance(node.args[1], ast.Constant)
            and isinstance(node.args[1].value, str)):
        return node.args[1].value
    return None
def _reference_name_of(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name):
        return node.id if isinstance(node.ctx, ast.Load) else None
    if isinstance(node, ast.Attribute):
        return node.attr if isinstance(node.ctx, ast.Load) else None
    if isinstance(node, ast.Call):
        return _dynamic_ref_name(node)
    return None
def _index_references(ctx: ScanContext) -> None:
    for tree in ctx.file_trees.values():
        for node in walk_nodes(tree):
            ref = _reference_name_of(node)
            if ref is not None:
                ctx.index.add_reference(ref)
        for exported in module_export_names(tree):
            ctx.index.add_reference(exported)
def build_cross_file_index(skill_dir: Path | str) -> ScanContext:
    if not skill_dir:
        raise ValueError(f"无效的技能目录: {skill_dir!r}")
    skill_dir = Path(skill_dir)
    if not skill_dir.is_dir():
        raise ValueError(f"无效的技能目录: {skill_dir}")
    ctx = ScanContext(skill_dir=skill_dir)
    ctx.py_files = _collect_py_files(skill_dir)
    for file_path in ctx.py_files:
        _index_one_file(ctx, file_path)
    _index_references(ctx)
    for name, entries in ctx.index.definitions.items():
        for entry in entries:
            if not ctx.index.is_referenced(name):
                entry.is_dead = True
    return ctx
def version_suffix(name: str) -> int | None:
    m = _VERSION_SUFFIX_RE.search(name)
    return int(m.group(1)) if m else None
def has_old_name_hint(name: str) -> bool:
    return any(p.search(name) for p in _OLD_NAME_PATTERNS)
def has_new_name_hint(name: str) -> bool:
    return any(p.search(name) for p in _NEW_NAME_PATTERNS)
def has_strict_old_hint(name: str) -> bool:
    ver = version_suffix(name)
    if ver is not None:
        return ver < 2
    return has_old_name_hint(name)
def has_strict_new_hint(name: str) -> bool:
    ver = version_suffix(name)
    if ver is not None:
        return ver >= 2
    return has_new_name_hint(name)
def _one_sided_signal(
    a: DefEntry, b: DefEntry, predicate: Callable[[DefEntry], bool]
) -> tuple[DefEntry, DefEntry] | None:
    a_flag = predicate(a)
    b_flag = predicate(b)
    if a_flag == b_flag:
        return None
    return (a, b) if a_flag else (b, a)
def _deprecated_signal(a: DefEntry, b: DefEntry) -> tuple[DefEntry, DefEntry] | None:
    return _one_sided_signal(a, b, lambda e: e.is_deprecated)
def _stub_signal(a: DefEntry, b: DefEntry) -> tuple[DefEntry, DefEntry] | None:
    return _one_sided_signal(a, b, lambda e: e.is_stub)
def _dead_signal(a: DefEntry, b: DefEntry) -> tuple[DefEntry, DefEntry] | None:
    return _one_sided_signal(a, b, lambda e: e.is_dead)
def _version_name_signal(a: DefEntry, b: DefEntry) -> tuple[DefEntry, DefEntry] | None:
    a_ver = version_suffix(a.name)
    b_ver = version_suffix(b.name)
    if a_ver is not None and b_ver is not None and a_ver != b_ver:
        return (a, b) if a_ver < b_ver else (b, a)
    return _name_hint_pair(a, b)
def _name_hint_pair(a: DefEntry, b: DefEntry) -> tuple[DefEntry, DefEntry] | None:
    hints = (
        has_strict_old_hint(a.name),
        has_strict_new_hint(a.name),
        has_strict_old_hint(b.name),
        has_strict_new_hint(b.name),
    )
    if hints == (True, False, False, True):
        return a, b
    if hints == (False, True, True, False):
        return b, a
    return None
def _basename_signal(a: DefEntry, b: DefEntry) -> tuple[DefEntry, DefEntry] | None:
    return _one_sided_signal(
        a, b,
        lambda e: bool(_OLD_MARKER_RE.search(os.path.basename(e.file_path))),
    )
def _dead_pair_tiebreak(
    a: DefEntry, b: DefEntry
) -> tuple[DefEntry, DefEntry] | None:
    if not (a.is_dead and b.is_dead) or a.file_path != b.file_path:
        return None
    key_a = (a.file_path, a.lineno)
    key_b = (b.file_path, b.lineno)
    if key_a == key_b:
        return None
    return (a, b) if key_a < key_b else (b, a)
def _same_file_order_signal(
    a: DefEntry, b: DefEntry
) -> tuple[DefEntry, DefEntry] | None:
    if a.file_path != b.file_path or a.lineno == b.lineno:
        return None
    return (a, b) if a.lineno < b.lineno else (b, a)
_OLD_NEW_SIGNALS = (
    _deprecated_signal,
    _stub_signal,
    _version_name_signal,
    _dead_signal,
    _basename_signal,
    _same_file_order_signal,
)
def determine_old_new(
    entry_a: DefEntry, entry_b: DefEntry
) -> tuple[DefEntry | None, DefEntry | None]:
    for signal in _OLD_NEW_SIGNALS:
        pair = signal(entry_a, entry_b)
        if pair is not None:
            return pair
    return None, None
_NEW_MODULE_PATTERNS: re.Pattern = re.compile(
    rf"(?<![a-zA-Z])new(?![a-zA-Z])"
    rf"|_v{_NEW_VERSION_NUMBER_PATTERN}(?![a-zA-Z0-9])"
    rf"|(?<![a-zA-Z0-9])v{_NEW_VERSION_NUMBER_PATTERN}(?![a-zA-Z0-9])"
    r"|_next(?![a-zA-Z])|_refactored(?![a-zA-Z])",
    re.IGNORECASE,
)
_FEATURE_KW: re.Pattern = re.compile(
    r"(feature(?:s)?(?![a-z])|enable|use_new|use_ng|toggle|experiment|"
    r"switch|beta|v2_ready|new_impl|new_pipeline|"
    r"next_gen|ff_|flags?(?![a-z]))",
    re.IGNORECASE,
)
_MIGRATION_TAGS: re.Pattern = re.compile(
    r"(?:#|//)\s*(TODO|FIXME|HACK|XXX|DEPRECATED|NOTE|WARN|TEMP|WORKAROUND)"
    r"(?:\s*[\(\[][^\)\]]{0,64}[\)\]])?\s*[:\-]?\s*"
    r"(migrat\w*|remov\w*|replac\w*|legac\w*|old(?![a-z])|deprecat\w*|"
    r"temporar\w*|bridg\w*|compat\w*|backward|new(?![a-z])|"
    r"v2(?![a-z0-9])|_new(?![a-z])|_v2(?![a-z0-9])|next(?![a-z0-9])|"
    r"ng(?![a-z])|cleanup|obsolet\w*|dead(?![a-z])|unused|refactor\w*|"
    r"switch\w*|upgrad\w*)",
    re.IGNORECASE,
)
_MIGRATION_REF_PAT: re.Pattern = re.compile(
    rf"(?<![\w])(\w+\.v{_NEW_VERSION_NUMBER_PATTERN}\w*"
    rf"|\w+_v{_NEW_VERSION_NUMBER_PATTERN}\w*"
    rf"|\w+V{_NEW_VERSION_NUMBER_PATTERN}\w*"
    r"|\w+\.new(?:_\w+)?|\w+_new(?:_\w+)?"
    r"|\w+_next(?:_\w+)?|\w+_ng(?:_\w+)?"
    r"|\w+_refactored(?:_\w+)?|\w+_revised(?:_\w+)?"
    rf"|v{_NEW_VERSION_NUMBER_PATTERN}_\w+"
    r"|new_\w+)"
    r"(?![\w])",
    re.IGNORECASE,
)
_OLD_IMPL_FN: re.Pattern = re.compile(
    r"(?<![a-zA-Z])(?:old|legacy|deprecated)(?![a-zA-Z])"
    r"|_v1(?![a-zA-Z0-9])|(?-i:V1)$"
    r"|(?<![a-zA-Z0-9])v1(?![a-zA-Z0-9])",
    re.IGNORECASE,
)
_NEW_IMPL_FN: re.Pattern = re.compile(
    r"(?<![a-zA-Z])new(?![a-zA-Z])"
    rf"|_v{_NEW_VERSION_NUMBER_PATTERN}(?![a-zA-Z0-9])"
    rf"|(?-i:V{_NEW_VERSION_NUMBER_PATTERN})$"
    rf"|(?<![a-zA-Z0-9])v{_NEW_VERSION_NUMBER_PATTERN}(?![a-zA-Z0-9])"
    r"|_ng(?![a-zA-Z])|_next(?![a-zA-Z])",
    re.IGNORECASE,
)
_DEFERRED_SCOPE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef)
_OWN_SCOPE_DEFERRED_TYPES = (*_DEFERRED_SCOPE_TYPES, ast.Lambda)
def _arg_annotations(args: ast.arguments) -> list[ast.AST]:
    return [
        arg.annotation
        for arg in iter_arg_nodes(args)
        if arg.annotation is not None
    ]
def _declaration_exprs(node: ast.AST) -> list[ast.AST]:
    parts: list[ast.AST] = list(getattr(node, "decorator_list", ()))
    args = getattr(node, "args", None)
    if args is not None:
        parts.extend(args.defaults)
        parts.extend(d for d in args.kw_defaults if d is not None)
        parts.extend(_arg_annotations(args))
    returns = getattr(node, "returns", None)
    if returns is not None:
        parts.append(returns)
    parts.extend(getattr(node, "type_params", ()))
    return parts
def _iter_own_scope_nodes(nodes: Iterable[ast.AST]) -> Iterator[ast.AST]:
    stack = list(reversed(list(nodes)))
    while stack:
        node = stack.pop()
        yield node
        if isinstance(node, _OWN_SCOPE_DEFERRED_TYPES):
            stack.extend(reversed(_declaration_exprs(node)))
            continue
        stack.extend(ast.iter_child_nodes(node))
_COMPREHENSION_SCOPE_TYPES = (
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
def _call_root_is_comprehension_bound(
    call: ast.Call, bound_names: frozenset[str]
) -> bool:
    qualified = dotted_name(call.func)
    return bool(
        qualified and qualified.split(".", 1)[0] in bound_names)
def _iter_own_scope_calls(
    nodes: Iterable[ast.AST],
    bound_names: frozenset[str] = frozenset(),
) -> Iterator[ast.Call]:
    for node in nodes:
        if (isinstance(node, ast.Call)
                and not _call_root_is_comprehension_bound(node, bound_names)):
            yield node
        if isinstance(node, _OWN_SCOPE_DEFERRED_TYPES):
            yield from _iter_own_scope_calls(
                _declaration_exprs(node), bound_names)
            continue
        if isinstance(node, _COMPREHENSION_SCOPE_TYPES):
            generators = node.generators
            # 先绑定：``generators`` 为空时下面仍会读 ``inner_names``，
            # 只在 if 内赋值会留下 UnboundLocalError 口子。
            inner_names = bound_names
            if generators:
                first = generators[0]
                yield from _iter_own_scope_calls((first.iter,), bound_names)
                inner_names = bound_names | frozenset(
                    name
                    for generator in generators
                    for name in iter_unpack_target_names(generator.target)
                )
                for generator in generators:
                    nested: list[ast.AST] = [generator.target, *generator.ifs]
                    if generator is not first:
                        nested.append(generator.iter)
                    yield from _iter_own_scope_calls(nested, inner_names)
            values = ((node.key, node.value)
                      if isinstance(node, ast.DictComp) else (node.elt,))
            yield from _iter_own_scope_calls(values, inner_names)
            continue
        yield from _iter_own_scope_calls(
            ast.iter_child_nodes(node), bound_names)
def collect_calls_from_nodes(body_nodes: list[ast.stmt]) -> set[str]:
    calls: set[str] = set()
    for ch in _iter_own_scope_calls(body_nodes):
        name = call_tail_name(ch) or None
        if name:
            calls.add(name)
        qualified = dotted_name(ch.func)
        if qualified:
            calls.add(qualified)
    return calls
_ONLY_OLD = frozenset(("old",))
_ONLY_NEW = frozenset(("new",))
_SELF_RECEIVER_ROOTS = frozenset(("self", "cls"))
def _call_root_name(call: str) -> str:
    return call.split(".", 1)[0] if "." in call else ""
def _collect_binding_names(names: set[str], node: ast.AST) -> None:
    if isinstance(node, ast.Assign):
        for target in node.targets:
            names.update(iter_unpack_target_names(target))
    elif isinstance(node, (ast.AnnAssign, ast.AugAssign, ast.NamedExpr,
                           ast.For, ast.AsyncFor)):
        names.update(iter_unpack_target_names(node.target))
    elif isinstance(node, ast.withitem) and node.optional_vars is not None:
        names.update(iter_unpack_target_names(node.optional_vars))
    elif isinstance(node, (ast.Import, ast.ImportFrom)):
        names.update(import_stmt_binds(node))
    elif isinstance(node, (ast.MatchAs, ast.MatchStar)):
        if node.name is not None:
            names.add(node.name)
    elif isinstance(node, ast.MatchMapping) and node.rest is not None:
        names.add(node.rest)
    elif isinstance(
        node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef,
               ast.ExceptHandler)
    ) and node.name:
        names.add(node.name)
    elif (hasattr(ast, "TypeAlias") and isinstance(node, ast.TypeAlias)
          and isinstance(node.name, ast.Name)):
        names.add(node.name.id)
def _class_declaration_exprs(node: ast.ClassDef) -> list[ast.AST]:
    return [
        *node.decorator_list,
        *node.bases,
        *node.keywords,
        *getattr(node, "type_params", ()),
    ]
def _iter_binding_scope_nodes(nodes: Iterable[ast.AST]) -> Iterator[ast.AST]:
    stack = list(reversed(list(nodes)))
    while stack:
        node = stack.pop()
        yield node
        if isinstance(node, (*_DEFERRED_SCOPE_TYPES, ast.Lambda)):
            stack.extend(reversed(_declaration_exprs(node)))
            continue
        if isinstance(node, ast.ClassDef):
            stack.extend(reversed(_class_declaration_exprs(node)))
            continue
        if isinstance(node, ast.comprehension):
            stack.extend(reversed([node.iter, *node.ifs]))
            continue
        stack.extend(ast.iter_child_nodes(node))
def _local_bound_names(node: ast.AST) -> frozenset[str]:
    names = collect_param_names(node)
    outer_names: set[str] = set()
    for child in _iter_binding_scope_nodes(node.body):
        if isinstance(child, (ast.Global, ast.Nonlocal)):
            outer_names.update(child.names)
            continue
        if isinstance(child, (ast.Import, ast.ImportFrom)):
            continue
        _collect_binding_names(names, child)
    names.difference_update(outer_names)
    return frozenset(names)
def _versioned_call_kept(call: str, local_names: frozenset[str]) -> bool:
    if "." not in call:
        return call not in local_names
    root = _call_root_name(call)
    if root in _SELF_RECEIVER_ROOTS:
        return True
    return root not in local_names
def _scoped_calls(calls: Iterable[str],
                  local_names: frozenset[str]) -> set[str]:
    return {call for call in calls if _versioned_call_kept(call, local_names)}
def _call_impl_sides(call: str) -> frozenset[str]:
    sides: set[str] = set()
    if _OLD_IMPL_FN.search(call):
        sides.add("old")
    if _NEW_IMPL_FN.search(call):
        sides.add("new")
    return frozenset(sides)
def _classify_impl_calls(
    calls: Iterable[str], local_names: frozenset[str] | None = None
) -> tuple[set[str], set[str]]:
    old_calls: set[str] = set()
    new_calls: set[str] = set()
    scoped = calls if local_names is None else _scoped_calls(
        calls, local_names)
    for call in scoped:
        sides = _call_impl_sides(call)
        if sides == _ONLY_OLD:
            old_calls.add(call)
        elif sides == _ONLY_NEW:
            new_calls.add(call)
    return old_calls, new_calls
_VERSION_SEGMENT_RE = re.compile(r"v\d+", re.IGNORECASE)
_MODULE_STEM_PREFIX_RE = re.compile(
    r"^(?:(?:old|new|legacy|deprecated|backups?)_|v\d+_)", re.IGNORECASE)
_MODULE_STEM_INFIX_MARKER_RE = re.compile(
    r"_(?:old|new|legacy|deprecated|backups?)_", re.IGNORECASE)
_MODULE_STEM_INFIX_VERSION_RE = re.compile(
    r"(?<=[A-Za-z0-9])_v\d+_(?=[A-Za-z0-9])", re.IGNORECASE)
_MODULE_STEM_SUFFIX_RE = re.compile(
    r"(?:_old|_new|_v\d+|_legacy|_deprecated|_bak|_backups?|_prev"
    r"|_next|_refactored)$",
    re.IGNORECASE,
)
def _module_segment_stem(segment: str) -> str:
    if _VERSION_SEGMENT_RE.fullmatch(segment):
        return ""
    stem = _MODULE_STEM_PREFIX_RE.sub("", segment)
    stem = _MODULE_STEM_INFIX_MARKER_RE.sub("_", stem)
    stem = _MODULE_STEM_INFIX_VERSION_RE.sub("_", stem)
    return _MODULE_STEM_SUFFIX_RE.sub("", stem) or segment
def _module_stem(name: str) -> str:
    return ".".join(
        stem for stem in (_module_segment_stem(seg) for seg in name.split("."))
        if stem
    )
def _imports_module(name: str, target: str) -> bool:
    if name == target or name.startswith(target + "."):
        return True
    return name.endswith("." + target)
def _package_of(file_path: str, skill_dir: Path | None = None) -> str:
    module_name = resolve_module_name(file_path)
    if Path(file_path).stem == "__init__":
        return module_name
    package = module_name.rpartition(".")[0]
    if package or skill_dir is None:
        return package
    try:
        relative = Path(file_path).resolve().relative_to(skill_dir.resolve())
    except ValueError:
        return package
    return ".".join(relative.parent.parts)
def _absolute_import_module(module: str, level: int, package: str) -> str:
    if level <= 0:
        return module
    parts = package.split(".") if package else []
    keep = len(parts) - (level - 1)
    if keep <= 0:
        return module
    base = ".".join(parts[:keep])
    if not module:
        return base
    return f"{base}.{module}"
def _node_import_names(
    node: ast.AST, known_modules: frozenset[str], package: str = ""
) -> set[str]:
    names: set[str] = set()
    if isinstance(node, ast.ImportFrom):
        module = _absolute_import_module(
            node.module or "", node.level, package)
        if module:
            names.add(module)
        for alias in node.names:
            if not alias.name or alias.name == "*":
                continue
            if not module:
                names.add(alias.name)
            else:
                candidate = f"{module}.{alias.name}"
                if candidate in known_modules:
                    names.add(candidate)
    elif isinstance(node, ast.Import):
        for alias in node.names:
            if alias.name:
                names.add(alias.name)
    return names
def _known_import_modules(ctx: ScanContext) -> frozenset[str]:
    modules: set[str] = set()
    root = ctx.skill_dir.resolve()
    for file_path in ctx.py_files:
        resolved = resolve_module_name(file_path)
        if resolved and resolved != "__init__":
            modules.add(resolved)
        try:
            relative = Path(file_path).resolve().relative_to(root)
        except ValueError:
            continue
        parts = list(relative.parts)
        stem = Path(parts[-1]).stem
        if stem == "__init__":
            parts.pop()
        else:
            parts[-1] = stem
        if parts:
            modules.add(".".join(parts))
    return frozenset(modules)
def _collect_file_imports(ctx: ScanContext) -> dict[str, set[str]]:
    file_imports: dict[str, set[str]] = defaultdict(set)
    known_modules = _known_import_modules(ctx)
    for file_path, tree in ctx.file_trees.items():
        package = _package_of(file_path, ctx.skill_dir)
        for node in walk_nodes(tree):
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                file_imports[file_path].update(
                    _node_import_names(node, known_modules, package))
    return file_imports
def _old_new_module_pairs(
    all_modules: set[str],
) -> tuple[dict[str, list[str]], dict[str, list[str]]]:
    old_modules: dict[str, list[str]] = defaultdict(list)
    new_modules: dict[str, list[str]] = defaultdict(list)
    for mod in sorted(all_modules):
        stem = _module_stem(mod)
        if _OLD_MARKER_RE.search(mod):
            old_modules[stem].append(mod)
        elif _NEW_MODULE_PATTERNS.search(mod):
            new_modules[stem].append(mod)
    return old_modules, new_modules
@cache
def _file_module_stem(file_path: str) -> str:
    return resolve_module_name(file_path).rpartition('.')[2] or Path(file_path).stem
def _basename_def_index(ctx: ScanContext) -> dict[str, set[str]]:
    basename_defs: dict[str, set[str]] = defaultdict(set)
    for def_list in ctx.index.definitions.values():
        for entry in def_list:
            if entry.parent_class:
                continue
            basename_defs[_file_module_stem(entry.file_path)].add(entry.name)
    return basename_defs
def _module_importer_sets(
    file_imports: dict[str, set[str]], old_mod: str, new_mod: str
) -> tuple[set[str], set[str]]:
    old_importers: set[str] = set()
    new_importers: set[str] = set()
    for fp, mods in file_imports.items():
        for mod_name in mods:
            if _imports_module(mod_name, old_mod):
                old_importers.add(fp)
            if _imports_module(mod_name, new_mod):
                new_importers.add(fp)
    return old_importers, new_importers
def _import_bridge_item(
    old_mod: str, new_mod: str, old_importers: set[str],
    new_importers: set[str], overlap: set[str]
) -> CoexistenceItem:
    both_importers = old_importers & new_importers
    cross_importers = (old_importers - new_importers) | (
        new_importers - old_importers
    )
    confidence = 0.68
    if both_importers:
        confidence = 0.78
    if len(cross_importers) >= 2:
        confidence = min(confidence + 0.05, 0.85)
    return CoexistenceItem(
        pattern_type="import_bridge",
        old_name=old_mod,
        new_name=new_mod,
        old_file=min(old_importers),
        new_file=min(new_importers),
        old_lines=(0, 0),
        new_lines=(0, 0),
        confidence=confidence,
        evidence=[
            f"旧模块: {old_mod}，导入文件: {len(old_importers)} 个",
            f"新模块: {new_mod}，导入文件: {len(new_importers)} 个",
            f"同名定义: {sorted(overlap)[:10]}",
        ]
        + (
            [f"同时导入新旧模块的文件: {len(both_importers)} 个"]
            if both_importers
            else []
        ),
        suggestion=f"将所有导入从 '{old_mod}' 迁移到 '{new_mod}'，统一使用新模块",
    )
def detect_import_bridge(ctx: ScanContext) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    file_imports = _collect_file_imports(ctx)
    all_modules: set[str] = set()
    for mods in file_imports.values():
        all_modules.update(mods)
    old_modules, new_modules = _old_new_module_pairs(all_modules)
    basename_defs = _basename_def_index(ctx)
    for stem, old_mods in old_modules.items():
        for old_mod in old_mods:
            old_def_names = basename_defs.get(old_mod.split(".")[-1], set())
            for new_mod in new_modules.get(stem, []):
                new_def_names = basename_defs.get(
                    new_mod.split(".")[-1], set())
                overlap = old_def_names & new_def_names
                if not overlap:
                    continue
                old_importers, new_importers = _module_importer_sets(
                    file_imports, old_mod, new_mod)
                items.append(_import_bridge_item(
                    old_mod, new_mod, old_importers, new_importers, overlap))
    return items
_BranchHits = tuple[bool, bool]
@dataclass(frozen=True)
class _RoutingPair:
    if_calls: set[str]
    else_calls: set[str]
    new_calls: set[str]
    old_calls: set[str]
    if_hits: _BranchHits
    else_hits: _BranchHits
def _logic_body_stmts(body: list[ast.stmt]) -> list[ast.stmt]:
    return [
        stmt for stmt in body_without_docstring(body)
        if not isinstance(stmt, (ast.Import, ast.ImportFrom))
    ]
def _iter_detection_functions(
    tree: ast.AST, min_body_stmts: int
) -> Iterator[ast.FunctionDef | ast.AsyncFunctionDef]:
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if len(_logic_body_stmts(node.body)) >= min_body_stmts:
            yield node
def _branch_pattern_hits(calls: set[str]) -> _BranchHits:
    sides = [_call_impl_sides(c) for c in calls]
    return (any(s == _ONLY_NEW for s in sides),
            any(s == _ONLY_OLD for s in sides))
def _routing_calls_pair(
    if_calls: set[str], else_calls: set[str]
) -> _RoutingPair | None:
    if_hits = _branch_pattern_hits(if_calls)
    else_hits = _branch_pattern_hits(else_calls)
    if if_hits == else_hits:
        return None
    new_calls, old_calls = _routing_assign_sides(
        if_calls, else_calls, if_hits[0], else_hits[0])
    if new_calls and old_calls:
        return _RoutingPair(
            if_calls, else_calls, new_calls, old_calls, if_hits, else_hits)
    if if_hits[0] or else_hits[0]:
        return None
    fallback = _routing_fallback_old_calls(if_calls, else_calls)
    if fallback is None:
        return None
    return _RoutingPair(
        if_calls, else_calls, set(), fallback, if_hits, else_hits)
def _routing_assign_sides(
    if_calls: set[str], else_calls: set[str],
    if_has_new: bool, else_has_new: bool,
) -> tuple[set[str], set[str]]:
    if if_has_new:
        new_side, old_side = if_calls, else_calls
    elif else_has_new:
        new_side, old_side = else_calls, if_calls
    else:
        return set(), set()
    old_marked, new_in_old = _classify_impl_calls(old_side)
    old_in_new, new_marked = _classify_impl_calls(new_side)
    if new_in_old or old_in_new:
        return set(), set()
    return new_marked, old_marked
def _routing_fallback_old_calls(
    if_calls: set[str], else_calls: set[str]
) -> set[str] | None:
    old_calls, _ = _classify_impl_calls(if_calls | else_calls)
    return old_calls or None
def _branch_pattern_bonus(if_hits: _BranchHits, else_hits: _BranchHits) -> float:
    if (if_hits[0] and else_hits[1]) or (else_hits[0] and if_hits[1]):
        return 0.05
    return 0.0
def _routing_confidence(pair: _RoutingPair) -> float:
    conf = 0.75 if pair.new_calls and pair.old_calls else 0.65
    conf = min(conf + _branch_pattern_bonus(pair.if_hits, pair.else_hits), 0.85)
    if len(pair.if_calls | pair.else_calls) >= 4:
        conf = min(conf + 0.03, 0.85)
    return conf
def _build_routing_item(
    fpath: str,
    node: ast.FunctionDef | ast.AsyncFunctionDef,
    stmt: ast.If,
    cond_text: str,
    local_names: frozenset[str],
) -> CoexistenceItem | None:
    if_calls = _scoped_calls(collect_calls_from_nodes(stmt.body), local_names)
    else_calls = _scoped_calls(
        collect_calls_from_nodes(stmt.orelse), local_names)
    if not if_calls or not else_calls:
        return None
    pair = _routing_calls_pair(if_calls, else_calls)
    if pair is None:
        return None
    return CoexistenceItem(
        old_name=node.name,
        new_name=(
            ", ".join(sorted(pair.new_calls)[:3])
            if pair.new_calls
            else UNSPECIFIED_TARGET
        ),
        old_file=fpath,
        new_file=fpath,
        old_lines=(node.lineno, node.end_lineno),
        new_lines=(stmt.lineno, stmt.end_lineno),
        confidence=_routing_confidence(pair),
        pattern_type="conditional_routing",
        evidence=[
            f"特征标志: {cond_text[:80]}",
            f"if 分支调用: {sorted(pair.if_calls)[:5]}",
            f"else 分支调用: {sorted(pair.else_calls)[:5]}",
        ],
        suggestion=f"确认特性标志 '{cond_text[:40]}' 是否可以移除，统一使用新旧实现中的一方",
    )
def _iter_feature_routing_ifs(
    node: ast.FunctionDef | ast.AsyncFunctionDef,
) -> Iterator[tuple[ast.If, str]]:
    for stmt in _iter_own_scope_nodes(node.body):
        if not (isinstance(stmt, ast.If) and stmt.orelse):
            continue
        cond_text = ast.unparse(stmt.test)
        if _FEATURE_KW.search(cond_text):
            yield stmt, cond_text
def detect_conditional_routing(ctx: ScanContext) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    for fpath, tree in ctx.file_trees.items():
        for node in _iter_detection_functions(tree, 1):
            items.extend(_routing_items_for_function(fpath, node))
    return items
def _routing_items_for_function(
    fpath: str, node: ast.FunctionDef | ast.AsyncFunctionDef
) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    local_names: frozenset[str] | None = None
    for stmt, cond_text in _iter_feature_routing_ifs(node):
        if local_names is None:
            local_names = _local_bound_names(node)
        item = _build_routing_item(fpath, node, stmt, cond_text, local_names)
        if item is not None:
            items.append(item)
    return items
def _module_scope_import_stmts(node: ast.AST) -> Iterator[ast.stmt]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        yield node
    for child in ast.iter_child_nodes(node):
        yield from _module_scope_import_stmts(child)
def _merge_import_bindings(
    bindings: dict[str, str], stmts: Iterable[ast.stmt]
) -> None:
    for stmt in stmts:
        bindings.update(_import_bindings_of(stmt))
def _import_bindings_of(stmt: ast.stmt) -> dict[str, str]:
    if isinstance(stmt, ast.ImportFrom):
        module = stmt.module or ""
        bindings: dict[str, str] = {}
        for alias in stmt.names:
            if alias.name == "*":
                continue
            local_name = alias.asname or alias.name
            bindings[local_name] = (
                f"{module}.{alias.name}" if module else alias.name)
        return bindings
    if isinstance(stmt, ast.Import):
        bindings: dict[str, str] = {}
        for alias in stmt.names:
            if alias.asname:
                bindings[alias.asname] = alias.name
                continue
            root = alias.name.split(".", 1)[0]
            bindings.setdefault(root, root)
            if root != alias.name:
                bindings.setdefault(alias.name, alias.name)
        return bindings
    return {}
def _binding_module_path(binding: str) -> str:
    if not binding:
        return ""
    return binding.rpartition(".")[0] if "." in binding else binding
def _module_import_bindings(tree: ast.AST) -> dict[str, str]:
    bindings: dict[str, str] = {}
    _merge_import_bindings(bindings, _module_scope_import_stmts(tree))
    return bindings
def _import_bindings_for(
    tree: ast.AST, node: ast.AST,
    module_bindings: dict[str, str] | None = None,
) -> dict[str, str]:
    bindings = dict(
        module_bindings if module_bindings is not None
        else _module_import_bindings(tree))
    own_imports = (
        child for child in _iter_binding_scope_nodes(node.body)
        if isinstance(child, (ast.Import, ast.ImportFrom))
    )
    _merge_import_bindings(bindings, own_imports)
    return bindings
def _delegate_definition_name(
    call: ast.Call, call_name: str, bindings: dict[str, str]
) -> str:
    if not isinstance(call.func, ast.Name):
        return call_name
    binding = bindings.get(call_name, "")
    if not binding:
        return call_name
    return binding.rpartition(".")[2] or call_name
def _lookup_call_module(import_bindings: dict[str, str], call_name: str) -> str | None:
    mod = import_bindings.get(call_name)
    if mod is not None:
        return mod
    seg = call_name
    while "." in seg:
        seg = seg.rsplit(".", 1)[0]
        mod = import_bindings.get(seg)
        if mod is not None:
            return mod
    return None
def _related_call_modules(
    import_bindings: dict[str, str], calls: set[str]
) -> set[str]:
    related: set[str] = set()
    for c in calls:
        mod = _lookup_call_module(import_bindings, c)
        if not mod:
            continue
        related.add(mod if "." in c else _binding_module_path(mod))
    return related
def _dual_write_item(
    fpath: str, node: ast.AST, old_calls: set[str], new_calls: set[str],
    related_modules: set[str]
) -> CoexistenceItem:
    is_cross_module = len(related_modules) >= 2
    conf = 0.68
    if is_cross_module:
        conf = 0.75
    if len(old_calls) >= 2 and len(new_calls) >= 2:
        conf = min(conf + 0.05, 0.85)
    return CoexistenceItem(
        old_name=node.name,
        new_name=", ".join(sorted(new_calls)[:3]),
        old_file=fpath,
        new_file=fpath,
        old_lines=(node.lineno, node.end_lineno),
        new_lines=(node.lineno, node.end_lineno),
        confidence=conf,
        pattern_type="dual_write_read",
        evidence=[
            f"旧API调用: {sorted(old_calls)[:5]}",
            f"新API调用: {sorted(new_calls)[:5]}",
        ]
        + (
            [f"跨模块导入: {sorted(related_modules)}"]
            if is_cross_module
            else []
        ),
        suggestion=f"函数 '{node.name}' 同时操作新旧系统，确认迁移完成后移除旧API调用",
    )
def detect_dual_write(ctx: ScanContext) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    for fpath, tree in ctx.file_trees.items():
        for node in _iter_detection_functions(tree, 2):
            all_calls = collect_calls_from_nodes(node.body)
            if not any(
                _OLD_IMPL_FN.search(c) or _NEW_IMPL_FN.search(c)
                for c in all_calls
            ):
                continue
            old_calls, new_calls = _classify_impl_calls(
                all_calls, _local_bound_names(node))
            if not old_calls or not new_calls:
                continue
            bindings = _import_bindings_for(tree, node)
            related_modules = _related_call_modules(
                bindings, old_calls | new_calls)
            items.append(_dual_write_item(
                fpath, node, old_calls, new_calls, related_modules))
    return items
_GENERIC_DELEGATE_NAMES = frozenset(
    {
        "set",
        "get",
        "add",
        "has",
        "fix",
        "run",
        "init",
        "start",
        "stop",
        "save",
        "load",
        "parse",
        "format",
        "process",
        "handle",
        "create",
        "update",
        "delete",
        "check",
        "test",
        "validate",
        "execute",
        "optimize",
        "register",
        "extract",
        "analyze",
        "detect",
        "build",
        "make",
        "apply",
        "commit",
        "rollback",
        "flush",
    }
)
_S6_BUILTIN_BASE = frozenset(
    {
        "print",
        "len",
        "range",
        "str",
        "int",
        "float",
        "list",
        "dict",
        "set",
        "tuple",
        "bool",
        "type",
        "isinstance",
        "hasattr",
        "getattr",
        "setattr",
        "open",
        "super",
        "property",
        "staticmethod",
        "classmethod",
    }
)
_BUILTIN_TOOL_NAMES = (
    _GENERIC_DELEGATE_NAMES
    | _S6_BUILTIN_BASE
    | frozenset(
        {
            "append",
            "extend",
            "insert",
            "pop",
            "popitem",
            "discard",
            "keys",
            "values",
            "items",
            "copy",
            "union",
            "intersection",
            "difference",
            "search",
            "match",
            "fullmatch",
            "findall",
            "finditer",
            "sub",
            "subn",
            "split",
            "rsplit",
            "join",
            "strip",
            "lstrip",
            "rstrip",
            "replace",
            "startswith",
            "endswith",
            "encode",
            "decode",
            "lower",
            "upper",
            "count",
            "find",
            "index",
            "read",
            "readline",
            "readlines",
            "write",
            "writelines",
            "close",
            "seek",
            "tell",
            "compile",
            "group",
            "groups",
            "walk",
        }
    )
)
def _is_public_function(node: ast.AST) -> bool:
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return False
    return not node.name.startswith("_")
_DELEGATION_BINDING_DECORATORS = frozenset({"staticmethod", "classmethod"})
_DELEGATION_DECORATOR_TARGETS = _DELEGATION_BINDING_DECORATORS | frozenset({
    f"builtins.{name}" for name in _DELEGATION_BINDING_DECORATORS
})
def _decorator_dotted_name(decorator: ast.AST) -> str:
    target = decorator.func if isinstance(decorator, ast.Call) else decorator
    return dotted_name(target) or ""
def _resolve_decorator_binding(
    tree: ast.AST,
    node: ast.FunctionDef | ast.AsyncFunctionDef,
    decorator: ast.AST,
    parents: dict[ast.AST, ast.AST],
    module_bindings: dict[str, str],
) -> str:
    qualified = _decorator_dotted_name(decorator)
    if not qualified:
        return ""
    root, _, suffix = qualified.partition(".")
    scope = parents.get(node)
    while scope is not None:
        if isinstance(scope, (ast.Module, ast.ClassDef, ast.FunctionDef,
                              ast.AsyncFunctionDef)):
            local_names = _delegation_shadow_names(
                scope, module_scope=False)
            if root in local_names:
                return ""
            bindings = (
                module_bindings if isinstance(scope, ast.Module)
                else _import_bindings_for(tree, scope, module_bindings)
            )
            binding = bindings.get(root)
            if binding:
                return f"{binding}.{suffix}" if suffix else binding
        scope = parents.get(scope)
    return qualified if not suffix else ""
def _delegation_decorators_compatible(
    tree: ast.AST,
    node: ast.FunctionDef | ast.AsyncFunctionDef,
    parents: dict[ast.AST, ast.AST],
    module_bindings: dict[str, str],
) -> bool:
    for decorator in node.decorator_list:
        target = decorator.func if isinstance(decorator, ast.Call) else decorator
        if type_last_name(target) not in _DELEGATION_BINDING_DECORATORS:
            return False
        resolved = _resolve_decorator_binding(
            tree, node, decorator, parents, module_bindings)
        if resolved not in _DELEGATION_DECORATOR_TARGETS:
            return False
    return True
def _delegation_call_from_body(body: list[ast.stmt]) -> ast.Call | None:
    if not body or any(
            not isinstance(stmt, (ast.Import, ast.ImportFrom))
            for stmt in body[:-1]):
        return None
    tail = body[-1]
    if not isinstance(tail, ast.Return):
        return None
    val = tail.value
    if isinstance(val, ast.Await):
        val = val.value
    return val if isinstance(val, ast.Call) else None
def _is_name_expr(node: ast.AST, name: str) -> bool:
    return isinstance(node, ast.Name) and node.id == name
def _keyword_forwarding_matches(
    call: ast.Call, expected_names: list[str], kwargs_name: str,
) -> bool:
    expected = set(expected_names)
    seen: set[str] = set()
    has_kwargs = False
    for keyword in call.keywords:
        if keyword.arg is None:
            if (has_kwargs or not kwargs_name
                    or not _is_name_expr(keyword.value, kwargs_name)):
                return False
            has_kwargs = True
            continue
        if (keyword.arg in seen or keyword.arg not in expected
                or not _is_name_expr(keyword.value, keyword.arg)):
            return False
        seen.add(keyword.arg)
    return seen == expected and has_kwargs == bool(kwargs_name)
def _is_pure_delegation_call(
    node: ast.AST, call: ast.Call, *, ignore_receiver: bool
) -> bool:
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return False
    args = node.args
    positional = [*args.posonlyargs, *args.args]
    if (ignore_receiver and positional
            and positional[0].arg in _SELF_RECEIVER_ROOTS):
        positional = positional[1:]
    positional_names = [arg.arg for arg in positional]
    kwonly_names = [arg.arg for arg in args.kwonlyargs]
    vararg_name = args.vararg.arg if args.vararg is not None else ""
    kwargs_name = args.kwarg.arg if args.kwarg is not None else ""
    if vararg_name:
        if len(call.args) != len(positional_names) + 1:
            return False
        if any(not _is_name_expr(value, name)
               for value, name in zip(call.args, positional_names)):
            return False
        starred = call.args[-1]
        if (not isinstance(starred, ast.Starred)
                or not _is_name_expr(starred.value, vararg_name)):
            return False
        return _keyword_forwarding_matches(call, kwonly_names, kwargs_name)
    prefix_size = len(call.args)
    if prefix_size > len(positional_names):
        return False
    if any(not _is_name_expr(value, name)
           for value, name in zip(call.args, positional_names)):
        return False
    expected_keywords = positional_names[prefix_size:] + kwonly_names
    return _keyword_forwarding_matches(call, expected_keywords, kwargs_name)
def is_delegation(node: ast.AST) -> str | None:
    call = _delegation_call_from_body(body_without_docstring(node.body))
    if call is None or not _is_pure_delegation_call(
            node, call, ignore_receiver=False):
        return None
    return call_tail_name(call) or None
def _receiver_root_name(node: ast.AST) -> str:
    while isinstance(node, ast.Attribute):
        node = node.value
    return node.id if isinstance(node, ast.Name) else ""
def _receiver_resolvable(call: ast.Call, module_roots: frozenset[str]) -> bool:
    if isinstance(call.func, ast.Name):
        return True
    if not isinstance(call.func, ast.Attribute):
        return False
    root = _receiver_root_name(call.func)
    return bool(root) and root in module_roots
def _has_implicit_receiver(
    node: ast.FunctionDef | ast.AsyncFunctionDef,
    parents: dict[ast.AST, ast.AST],
) -> bool:
    scope = parents.get(node)
    scope_types = (
        ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef,
        ast.Lambda,
    )
    while scope is not None and not isinstance(scope, scope_types):
        scope = parents.get(scope)
    if not isinstance(scope, ast.ClassDef):
        return False
    for decorator in node.decorator_list:
        target = decorator.func if isinstance(decorator, ast.Call) else decorator
        if type_last_name(target) == "staticmethod":
            return False
    return True
def _delegation_shadow_names(
    node: ast.AST, *, module_scope: bool,
) -> frozenset[str]:
    names = collect_param_names(node)
    outer_names: set[str] = set()
    for child in _iter_binding_scope_nodes(node.body):
        if isinstance(child, (ast.Global, ast.Nonlocal)):
            outer_names.update(child.names)
            continue
        if isinstance(child, (ast.Import, ast.ImportFrom)):
            continue
        if module_scope and isinstance(
                child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        _collect_binding_names(names, child)
    names.difference_update(outer_names)
    return frozenset(names)
def _cached_scope_maps(
    ctx: ScanContext, file_path: str, tree: ast.AST,
) -> tuple[dict[ast.AST, ast.AST], dict[ast.AST, frozenset[str]],
           dict[str, str]]:
    cached = ctx.scope_maps.get(file_path)
    if cached is None:
        parents, bindings = _delegation_scope_maps(tree)
        cached = (parents, bindings, _module_import_bindings(tree))
        ctx.scope_maps[file_path] = cached
    return cached
def _delegation_scope_maps(
    tree: ast.AST,
) -> tuple[dict[ast.AST, ast.AST], dict[ast.AST, frozenset[str]]]:
    parents = parent_map(tree)
    scopes = [tree, *(
        node for node in tree_nodes(tree)
        if isinstance(node, _DEFERRED_SCOPE_TYPES)
    )]
    module_shadows = _delegation_shadow_names(tree, module_scope=True)
    bindings = {
        scope: (module_shadows if scope is tree
                else _delegation_shadow_names(scope, module_scope=False))
        for scope in scopes
    }
    return parents, bindings
def _bare_name_is_lexically_bound(
    name: str,
    node: ast.AST,
    parents: dict[ast.AST, ast.AST],
    bindings: dict[ast.AST, frozenset[str]],
) -> bool:
    scope: ast.AST | None = node
    while scope is not None:
        if name in bindings.get(scope, frozenset()):
            return True
        scope = parents.get(scope)
    return False
def _call_is_lexically_bound(
    call: ast.Call,
    node: ast.AST,
    parents: dict[ast.AST, ast.AST],
    bindings: dict[ast.AST, frozenset[str]],
) -> bool:
    root = (call.func.id if isinstance(call.func, ast.Name)
            else _receiver_root_name(call.func))
    return bool(root) and _bare_name_is_lexically_bound(
        root, node, parents, bindings)
def _real_entries(
    target_entries: list[DefEntry], is_self: Callable[[DefEntry], bool]
) -> list[DefEntry]:
    return [
        entry
        for entry in sorted(target_entries, key=lambda e: (e.file_path, e.lineno))
        if not entry.is_stub and not is_self(entry)
    ]
def _module_level_functions(
    target_entries: list[DefEntry], file_path: str, lineno: int
) -> list[DefEntry]:
    return [
        entry for entry in _real_entries(
            target_entries,
            lambda e: e.file_path == file_path and e.lineno == lineno)
        if entry.kind == "function" and not entry.parent_class
    ]
def _module_stem_of(module_name: str) -> str:
    return module_name.rsplit('.', 1)[-1] if module_name else ''
def _delegation_module_stems(call: ast.Call,
                             bindings: dict[str, str]) -> set[str]:
    stems: set[str] = set()
    if isinstance(call.func, ast.Name):
        binding = bindings.get(call.func.id, '')
        stem = _module_stem_of(_binding_module_path(binding))
        return {stem} if stem else set()
    receiver = dotted_name(call.func.value)
    if not receiver:
        return set()
    resolved = _lookup_call_module(bindings, dotted_name(call.func) or '')
    if resolved:
        stems.add(_module_stem_of(resolved))
    prefix = receiver
    while prefix:
        module = bindings.get(prefix)
        if module:
            suffix = receiver[len(prefix):].strip('.')
            stems.add(_module_stem_of(
                f'{module}.{suffix}' if suffix else module))
            break
        prefix = prefix.rpartition('.')[0] if '.' in prefix else ''
    stems.discard('')
    return stems
def _delegation_real_target(
    target_entries: list[DefEntry], file_path: str, lineno: int,
    call: ast.Call, bindings: dict[str, str],
) -> DefEntry | None:
    if isinstance(call.func, ast.Name) and bindings.get(call.func.id):
        local_shadow = any(
            entry.file_path == file_path
            and entry.lineno != lineno
            and not entry.parent_class
            for entry in target_entries
        )
        if local_shadow:
            return None
    candidates = _module_level_functions(target_entries, file_path, lineno)
    module_stems = _delegation_module_stems(call, bindings)
    if module_stems:
        candidates = [entry for entry in candidates
                      if _file_module_stem(entry.file_path) in module_stems]
    else:
        candidates = [entry for entry in candidates
                      if entry.file_path == file_path]
    if len(candidates) != 1:
        return None
    return candidates[0]
def _parameter_defaults(args: ast.arguments) -> dict[str, ast.AST]:
    positional = [*args.posonlyargs, *args.args]
    defaults: list[ast.AST | None] = (
        [None] * (len(positional) - len(args.defaults))
        + list(args.defaults)
        + list(args.kw_defaults)
    )
    return {
        param.arg: default
        for param, default in zip(
            [*positional, *args.kwonlyargs], defaults)
        if default is not None
    }
def _keyword_target_param(
    args: ast.arguments, name: str
) -> ast.arg | None:
    return next(
        (param for param in [*args.args, *args.kwonlyargs]
         if param.arg == name),
        None,
    )
def _is_immutable_default_value(value: Any) -> bool:
    if isinstance(value, tuple):
        return all(_is_immutable_default_value(item) for item in value)
    return isinstance(
        value, (str, bytes, int, float, complex, bool, type(None), type(Ellipsis)))
def _same_default_expr(left: ast.AST, right: ast.AST | None) -> bool:
    if right is None or ast.dump(
            left, include_attributes=False) != ast.dump(
                right, include_attributes=False):
        return False
    try:
        value = ast.literal_eval(left)
    except (ValueError, TypeError, SyntaxError):
        return False
    return _is_immutable_default_value(value)
def _delegation_call_binds_target(
    target: ast.FunctionDef | ast.AsyncFunctionDef,
    call: ast.Call,
) -> bool:
    target_positional = [*target.args.posonlyargs, *target.args.args]
    target_positional_names = {param.arg for param in target_positional}
    target_posonly_names = {param.arg for param in target.args.posonlyargs}
    target_keywords = {
        param.arg: param
        for param in [*target.args.args, *target.args.kwonlyargs]
    }
    target_defaults = _parameter_defaults(target.args)
    bound: set[str] = set()
    positional_spread = False
    keyword_spread = False
    for position, value in enumerate(call.args):
        if isinstance(value, ast.Starred):
            positional_spread = True
            break
        if position < len(target_positional):
            bound.add(target_positional[position].arg)
        elif target.args.vararg is None:
            return False
    for keyword in call.keywords:
        if keyword.arg is None:
            keyword_spread = True
            continue
        target_param = target_keywords.get(keyword.arg)
        if target_param is None:
            if target.args.kwarg is None:
                return False
            continue
        if target_param.arg in bound:
            return False
        bound.add(target_param.arg)
    for param in [*target_positional, *target.args.kwonlyargs]:
        if param.arg in bound or param.arg in target_defaults:
            continue
        if positional_spread and param.arg in target_positional_names:
            continue
        if keyword_spread and param.arg not in target_posonly_names:
            continue
        return False
    return True
def _delegation_parameters_compatible(
    node: ast.FunctionDef | ast.AsyncFunctionDef,
    target: ast.FunctionDef | ast.AsyncFunctionDef,
    call: ast.Call,
    *,
    ignore_receiver: bool,
) -> bool:
    if not _delegation_call_binds_target(target, call):
        return False
    source_positional = [*node.args.posonlyargs, *node.args.args]
    if (ignore_receiver and source_positional
            and source_positional[0].arg in _SELF_RECEIVER_ROOTS):
        source_positional = source_positional[1:]
    target_positional = [*target.args.posonlyargs, *target.args.args]
    source_posonly_names = {param.arg for param in node.args.posonlyargs}
    target_posonly_names = {param.arg for param in target.args.posonlyargs}
    source_defaults = _parameter_defaults(node.args)
    target_defaults = _parameter_defaults(target.args)
    checks: list[tuple[str, ast.arg | None]] = []
    for index, param in enumerate(source_positional):
        target_param = (
            target_positional[index]
            if index < len(target_positional) else None)
        if param.arg in source_posonly_names:
            if target_param is None and target.args.vararg is None:
                return False
        elif (target_param is None
              or target_param.arg != param.arg
              or target_param.arg in target_posonly_names):
            return False
        if param.arg in source_defaults:
            checks.append((param.arg, target_param))
    for param in node.args.kwonlyargs:
        if param.arg in source_defaults:
            checks.append((
                param.arg, _keyword_target_param(target.args, param.arg)))
    return all(
        target_param is not None
        and _same_default_expr(
            source_defaults[source_name],
            target_defaults.get(target_param.arg),
        )
        for source_name, target_param in checks
    )
def _delegation_body_awaits_call(
    node: ast.FunctionDef | ast.AsyncFunctionDef,
) -> bool:
    body = body_without_docstring(node.body)
    tail = body[-1]
    value = tail.value if isinstance(tail, (ast.Return, ast.Expr)) else None
    return isinstance(value, ast.Await)
def _delegation_behavior_compatible(
    ctx: ScanContext,
    node: ast.FunctionDef | ast.AsyncFunctionDef,
    target_entry: DefEntry,
    call: ast.Call,
    *,
    ignore_receiver: bool,
) -> bool:
    target = _locate_entry_node(ctx, target_entry)
    if target is None or not _delegation_parameters_compatible(
            node, target, call, ignore_receiver=ignore_receiver):
        return False
    if not isinstance(node, ast.AsyncFunctionDef):
        return True
    return (
        isinstance(target, ast.AsyncFunctionDef)
        and _delegation_body_awaits_call(node)
    )
def detect_delegation(ctx: ScanContext) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    for file_path, tree in ctx.file_trees.items():
        parents, scope_bindings, module_bindings = _cached_scope_maps(
            ctx, file_path, tree)
        for node in walk_nodes(tree):
            if not _is_public_function(node):
                continue
            if not _delegation_decorators_compatible(
                    tree, node, parents, module_bindings):
                continue
            call = _delegation_call_from_body(
                body_without_docstring(node.body))
            if call is None:
                continue
            delegate_target = call_tail_name(call) or None
            if delegate_target is None:
                continue
            if (delegate_target == node.name
                    and isinstance(call.func, ast.Name)):
                continue
            ignore_receiver = _has_implicit_receiver(node, parents)
            if not _is_pure_delegation_call(
                    node, call, ignore_receiver=ignore_receiver):
                continue
            if delegate_target in _GENERIC_DELEGATE_NAMES:
                continue
            import_bindings = _import_bindings_for(
                tree, node, module_bindings)
            if not _receiver_resolvable(call, frozenset(import_bindings)):
                continue
            if _call_is_lexically_bound(
                    call, node, parents, scope_bindings):
                continue
            delegate_target = _delegate_definition_name(
                call, delegate_target, import_bindings)
            target_entries = ctx.index.definitions.get(delegate_target, [])
            if not target_entries:
                continue
            real_target = _delegation_real_target(
                target_entries, file_path, node.lineno,
                call, import_bindings)
            if real_target is None:
                continue
            if not _delegation_behavior_compatible(
                    ctx, node, real_target, call,
                    ignore_receiver=ignore_receiver):
                continue
            items.append(
                _delegation_item(file_path, node, delegate_target, real_target))
    return items
def _delegation_item(
    file_path: str,
    node: ast.FunctionDef | ast.AsyncFunctionDef,
    delegate_target: str,
    real_target: DefEntry,
) -> CoexistenceItem:
    return CoexistenceItem(
        pattern_type="delegation",
        old_name=node.name,
        new_name=delegate_target,
        old_file=file_path,
        new_file=real_target.file_path,
        old_lines=(node.lineno, node.end_lineno),
        new_lines=(real_target.lineno, real_target.end_lineno),
        confidence=0.90,
        evidence=[
            f"'{node.name}' 函数体仅委托调用 '{delegate_target}'",
            f"委托目标: {real_target.file_path}:{real_target.lineno}",
        ],
        suggestion=f"移除委托包装 '{node.name}'，直接使用 '{delegate_target}'",
    )
def _delegate_calls_in(node: ast.AST) -> dict[str, list[ast.Call]]:
    targets: dict[str, list[ast.Call]] = {}
    for child in _iter_own_scope_calls(node.body):
        name = call_tail_name(child) or None
        if name and name not in _BUILTIN_TOOL_NAMES:
            targets.setdefault(name, []).append(child)
    return targets
def _current_entry_deprecated(ctx: ScanContext, file_path: str, node: ast.AST) -> bool:
    cur_entry = next(
        (e for e in ctx.index.definitions.get(node.name, [])
         if e.file_path == file_path and e.lineno == node.lineno),
        None,
    )
    return bool(cur_entry is not None and cur_entry.is_deprecated)
def _partial_delegation_item(
    file_path: str, node: ast.AST, target_name: str,
    target: DefEntry, is_deprecated: bool
) -> CoexistenceItem:
    body_len = len(_logic_body_stmts(node.body))
    old_hint = _has_strong_old_hint(node.name)
    confidence = 0.82
    if is_deprecated:
        confidence = 0.90
    if old_hint:
        confidence = min(confidence + 0.05, 0.92)
    return CoexistenceItem(
        pattern_type="partial_delegation",
        old_name=node.name,
        new_name=target_name,
        old_file=file_path,
        new_file=target.file_path,
        old_lines=(node.lineno, node.end_lineno),
        new_lines=(target.lineno, target.end_lineno),
        confidence=confidence,
        evidence=[
            f"'{node.name}' 函数体中调用了 '{target_name}'（非唯一操作）",
            f"函数体含 {body_len} 个非导入语句（含旧逻辑残留）",
            f"委托目标: {target.file_path}:{target.lineno}",
        ]
        + (["旧函数含废弃标记"] if is_deprecated else [])
        + (["旧函数名含版本标记"] if old_hint else []),
        suggestion=f"将 '{node.name}' 完全委托给 '{target_name}'，或移除残留的旧逻辑",
    )
_AMBIGUOUS_OLD_SUFFIXES = ("_bak", "_backup", "_backups", "_prev")
_PREDICATE_NAME_HEADS = frozenset({
    "check", "is", "has", "detect", "find", "validate", "verify",
    "scan", "mark", "test", "ensure", "assert", "needs", "requires",
})
def _is_predicate_name(name: str) -> bool:
    head = name.strip("_").split("_", 1)[0].lower()
    return head in _PREDICATE_NAME_HEADS
def _has_strong_old_hint(name: str) -> bool:
    if not has_strict_old_hint(name):
        return False
    lowered = name.lower()
    if _is_predicate_name(name) and not lowered.startswith(
            ("old_", "legacy_", "deprecated_")):
        return False
    if not any(lowered.endswith(s) for s in _AMBIGUOUS_OLD_SUFFIXES):
        return True
    version = version_suffix(name)
    return version is not None and version < 2
def _has_migration_hint(node_name: str, is_deprecated: bool) -> bool:
    return _has_strong_old_hint(node_name) or is_deprecated
def _partial_delegation_targets(
    ctx: ScanContext, file_path: str, node: ast.AST, is_deprecated: bool,
    tree: ast.AST, parents: dict[ast.AST, ast.AST],
    scope_bindings: dict[ast.AST, frozenset[str]],
    module_bindings: dict[str, str],
) -> Iterator[tuple[str, DefEntry]]:
    if not _has_migration_hint(node.name, is_deprecated):
        return
    import_bindings = _import_bindings_for(
        tree, node, module_bindings)
    module_roots = frozenset(import_bindings)
    for target_name, calls in sorted(_delegate_calls_in(node).items()):
        target_name = _delegate_definition_name(
            calls[0], target_name, import_bindings)
        resolved: dict[tuple[str, int], DefEntry] = {}
        for call in calls:
            if not _receiver_resolvable(call, module_roots):
                continue
            if _call_is_lexically_bound(
                    call, node, parents, scope_bindings):
                continue
            target = _delegation_real_target(
                ctx.index.definitions.get(target_name, []), file_path,
                node.lineno, call, import_bindings)
            if target is not None:
                resolved[(target.file_path, target.lineno)] = target
        if len(resolved) != 1:
            continue
        yield target_name, next(iter(resolved.values()))
def detect_partial_delegation(ctx: ScanContext) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    for file_path, tree in ctx.file_trees.items():
        parents, scope_bindings, module_bindings = _cached_scope_maps(
            ctx, file_path, tree)
        for node in _iter_detection_functions(tree, 3):
            if not _is_public_function(node):
                continue
            is_deprecated = _current_entry_deprecated(ctx, file_path, node)
            for target_name, target in _partial_delegation_targets(
                    ctx, file_path, node, is_deprecated,
                    tree, parents, scope_bindings, module_bindings):
                items.append(_partial_delegation_item(
                    file_path, node, target_name, target, is_deprecated))
    return items
def _resolve_deprecated_replacement(
    ctx: ScanContext, entry: DefEntry
) -> tuple[str, DefEntry] | None:
    tree = _get_entry_tree(ctx, entry)
    if tree is None:
        return None
    replacement = entry.deprecated_replacement
    call = ast.Call(
        func=ast.Name(id=replacement, ctx=ast.Load()), args=[], keywords=[])
    bindings = _module_import_bindings(tree)
    replacement = _delegate_definition_name(call, replacement, bindings)
    target = _delegation_real_target(
        ctx.index.definitions.get(replacement, []),
        entry.file_path, entry.lineno, call, bindings)
    if target is None:
        return None
    return replacement, target
def detect_deprecated_markers(ctx: ScanContext) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    for entries in ctx.index.definitions.values():
        for entry in entries:
            if not entry.is_deprecated:
                continue
            if not entry.deprecated_replacement:
                continue
            resolved = _resolve_deprecated_replacement(ctx, entry)
            if resolved is None:
                continue
            replacement, real_target = resolved
            items.append(
                CoexistenceItem(
                    pattern_type="deprecated_marker",
                    old_name=entry.name,
                    new_name=replacement,
                    old_file=entry.file_path,
                    new_file=real_target.file_path,
                    old_lines=(entry.lineno, entry.end_lineno),
                    new_lines=(real_target.lineno, real_target.end_lineno),
                    confidence=0.95,
                    evidence=[
                        f"'{entry.name}' 标记为废弃，替代实现: '{replacement}'",
                        f"旧版: {entry.file_path}:{entry.lineno}",
                        f"新版: {real_target.file_path}:{real_target.lineno}",
                    ],
                    suggestion=f"移除废弃函数 '{entry.name}'，使用 '{replacement}'",
                )
            )
    return items
_TRAILING_MARKER_MAX_DISTANCE = 3
_LEADING_MARKER_MAX_DISTANCE = 6
def _line_indent(lines: list[str], lineno: int) -> int:
    if not 1 <= lineno <= len(lines):
        return 0
    line = lines[lineno - 1]
    return len(line) - len(line.lstrip())
def _def_entries_by_file(ctx: ScanContext) -> dict[str, list[DefEntry]]:
    by_file: dict[str, list[DefEntry]] = defaultdict(list)
    for entries in ctx.index.definitions.values():
        for entry in entries:
            by_file[entry.file_path].append(entry)
    return by_file
def _marker_gap_is_declaration_only(
    lines: list[str], lineno: int, target_lineno: int
) -> bool:
    for line_no in range(lineno + 1, target_lineno):
        text = lines[line_no - 1].strip()
        if not text or text.startswith(("#", "@")):
            continue
        return False
    return True
def _leading_marker_owner(
    entries: list[DefEntry], lines: list[str], lineno: int
) -> DefEntry | None:
    comment_indent = _line_indent(lines, lineno)
    leading = [
        entry for entry in entries
        if entry.lineno > lineno
        and entry.lineno - lineno <= _LEADING_MARKER_MAX_DISTANCE
        and _line_indent(lines, entry.lineno) == comment_indent
        and _marker_gap_is_declaration_only(lines, lineno, entry.lineno)
    ]
    return min(leading, key=lambda e: e.lineno) if leading else None
def _marker_owner_entry(
    entries: list[DefEntry], lines: list[str], lineno: int
) -> DefEntry | None:
    containing = [
        entry for entry in entries if entry.lineno <= lineno <= entry.end_lineno
    ]
    innermost = (max(containing, key=lambda e: (e.lineno, -e.end_lineno))
                 if containing else None)
    leading = _leading_marker_owner(entries, lines, lineno)
    if leading is not None and (
        innermost is None
        or _line_indent(lines, leading.lineno)
        > _line_indent(lines, innermost.lineno)
    ):
        return leading
    if innermost is not None:
        return innermost
    comment_indent = _line_indent(lines, lineno)
    trailing = [
        entry for entry in entries
        if entry.end_lineno < lineno
        and lineno - entry.end_lineno <= _TRAILING_MARKER_MAX_DISTANCE
        and comment_indent > _line_indent(lines, entry.lineno)
    ]
    return max(trailing, key=lambda e: e.end_lineno) if trailing else None
def _migration_replacement(line: str) -> str:
    ref_match = _MIGRATION_REF_PAT.search(line)
    if ref_match:
        return ref_match.group(1)
    return ""
def _migration_confidence(tag: str, action: str, replacement: str) -> float:
    conf = 0.60
    if tag.upper() in ("TODO", "FIXME"):
        conf = 0.68
    if action.lower().startswith(("migrat", "replac", "remov")):
        conf = min(conf + 0.08, 0.80)
    if replacement:
        conf = min(conf + 0.06, 0.82)
    if tag.upper() == "DEPRECATED":
        conf = min(conf + 0.10, 0.85)
    return conf
@dataclass(frozen=True)
class _MigrationMarker:
    line: str
    tag: str
    action: str
    replacement: str
    confidence: float
def _migration_marker_facts(line: str, marker: re.Match) -> _MigrationMarker:
    tag, action = marker.group(1), marker.group(2)
    replacement = _migration_replacement(line)
    return _MigrationMarker(
        line=line,
        tag=tag,
        action=action,
        replacement=replacement,
        confidence=_migration_confidence(tag, action, replacement),
    )
def _migration_marker_item(
    fpath: str, lineno: int, marker: _MigrationMarker,
    target_entry: DefEntry,
) -> CoexistenceItem:
    return CoexistenceItem(
        old_name=target_entry.name,
        new_name=marker.replacement or UNSPECIFIED_TARGET,
        old_file=fpath,
        new_file=fpath,
        old_lines=(target_entry.lineno, target_entry.end_lineno),
        new_lines=(lineno, lineno),
        confidence=marker.confidence,
        pattern_type="migration_marker",
        evidence=[
            f"标记: {marker.tag} at line {lineno}",
            f"注释: {marker.line.strip()[:100]}",
            f"所属函数: {target_entry.name}",
        ]
        + ([f"替代目标: {marker.replacement}"] if marker.replacement else []),
        suggestion=f"按注释 '{marker.tag}' 要求完成迁移: {marker.action}",
    )
def _migration_item_at(
    fpath: str,
    entries: list[DefEntry],
    lines: list[str],
    lineno: int,
    line: str,
    tag_match: re.Match,
) -> CoexistenceItem | None:
    target_entry = _marker_owner_entry(entries, lines, lineno)
    if target_entry is None:
        return None
    return _migration_marker_item(
        fpath, lineno, _migration_marker_facts(line, tag_match), target_entry)
def _comment_texts(
    fpath: str, source: str
) -> list[tuple[int, str]] | None:
    comments = comment_tokens(source)
    if comments is not None:
        return [(tok.start[0], tok.string) for tok in comments]
    _log.warning(
        "coexistence_detect:_comment_texts: 注释分词失败，回退整行扫描: %s",
        fpath,
    )
    return None
def detect_migration_markers(ctx: ScanContext) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    entries_by_file = _def_entries_by_file(ctx)
    for fpath, source in ctx.file_sources.items():
        lines = source.split("\n")
        entries = entries_by_file.get(fpath, [])
        comments = _comment_texts(fpath, source)
        candidates = (
            comments if comments is not None else list(enumerate(lines, 1))
        )
        for lineno, line in candidates:
            tag_match = _MIGRATION_TAGS.search(line)
            if tag_match is None:
                continue
            item = _migration_item_at(
                fpath, entries, lines, lineno, line, tag_match)
            if item is not None:
                items.append(item)
    return items
_CAMEL_TOKEN_RE: re.Pattern[str] = re.compile(
    r"[A-Z]+(?![a-z])|[A-Z][a-z0-9]*|[a-z]+\d*"
)
_SHADOW_SUFFIX: re.Pattern = re.compile(
    rf"^(.+?)(_new|_ng|_vnext|_next|_refactored|_revised"
    rf"|_v{_NEW_VERSION_NUMBER_PATTERN})$",
    re.IGNORECASE,
)
_GENERIC_NAME_BLACKLIST = frozenset(
    {
        "set",
        "get",
        "add",
        "has",
        "fix",
        "run",
        "init",
        "open",
        "close",
        "start",
        "stop",
        "reset",
        "clear",
        "save",
        "load",
        "parse",
        "format",
        "process",
        "handle",
        "create",
        "update",
        "delete",
        "remove",
        "find",
        "check",
        "test",
        "validate",
        "execute",
        "optimize",
        "register",
        "extract",
        "enhance",
        "summarize",
        "rewrite",
        "decompose",
        "go",
        "do",
        "use",
        "new",
        "old",
        "now",
        "all",
        "any",
        "one",
        "to_dict",
        "from_dict",
        "to_list",
        "to_str",
        "to_json",
        "from_json",
        "to_tuple",
        "to_set",
        "to_csv",
        "analyze",
        "detect",
        "summary",
        "report",
        "build",
        "make",
        "apply",
        "commit",
        "rollback",
        "flush",
        "refresh",
        "connect",
        "disconnect",
        "subscribe",
        "unsubscribe",
        "encode",
        "decode",
        "serialize",
        "deserialize",
        "clone",
        "copy",
        "merge",
        "split",
        "wrap",
        "unwrap",
    }
)
_SIM_GENERIC_NAMES = frozenset(
    {
        "__init__",
        "__post_init__",
        "__repr__",
        "__str__",
        "__eq__",
        "__hash__",
        "__len__",
        "__bool__",
        "to_dict",
        "from_dict",
        "to_json",
        "from_json",
        "fix",
        "run",
        "scan",
        "check",
        "get",
        "set",
    }
)
_MIXIN_COMMON_TOKENS = frozenset(
    {
        "base",
        "ops",
        "method",
        "class",
        "module",
        "var",
        "data",
        "pattern",
        "transform",
    }
)
def _name_stem(name: str) -> str:
    stem = re.sub(
        r"^(old_|new_|legacy_|deprecated_|v\d+_)",
        "",
        name,
        flags=re.IGNORECASE,
    )
    return re.sub(
        r"(_old|_new|_v\d+|_legacy|_deprecated|_bak|_backup|_prev)$",
        "",
        stem,
        flags=re.IGNORECASE,
    )
def _char_bigrams(text: str) -> set[str]:
    if len(text) < 2:
        return {text}
    return {text[i:i + 2] for i in range(len(text) - 1)}
_SIMILAR_NAME_THRESHOLD = 0.7
def _bigram_index(
    reals: list[tuple[str, list[DefEntry], str]]
) -> dict[str, set[int]]:
    index: dict[str, set[int]] = defaultdict(set)
    for position, (_name, _entries, stem) in enumerate(reals):
        for bigram in _char_bigrams(stem):
            index[bigram].add(position)
    return index
def _similar_name_candidates(
    name: str,
    reals: list[tuple[str, list[DefEntry], str]],
    bigram_index: dict[str, set[int]],
) -> list[tuple[str, list[DefEntry], str]]:
    stem = _name_stem(name).lower()
    grams = _char_bigrams(stem)
    need = max(1, math.ceil(_SIMILAR_NAME_THRESHOLD * len(grams)))
    counts: dict[int, int] = {}
    for gram in grams:
        for position in bigram_index.get(gram, ()):
            counts[position] = counts.get(position, 0) + 1
    candidates = [
        reals[position]
        for position, shared in counts.items()
        if shared >= need and reals[position][0] != name
    ]
    return sorted(candidates, key=lambda item: item[0])
def name_similarity(a: str, b: str) -> float:
    if a == b:
        return 1.0
    a_stem = _name_stem(a)
    b_stem = _name_stem(b)
    if a_stem == b_stem:
        return 0.95
    ga = _char_bigrams(a_stem.lower())
    gb = _char_bigrams(b_stem.lower())
    return len(ga & gb) / len(ga | gb)
def camel_tokens(name: str) -> set[str]:
    return {
        t.lower()
        for t in _CAMEL_TOKEN_RE.findall(name)
        if len(t) >= 2
    }
_COMMON_VERBS = frozenset(
    {
        "get",
        "set",
        "run",
        "add",
        "put",
        "del",
        "new",
        "old",
        "fix",
        "scan",
        "check",
        "test",
        "init",
        "make",
        "load",
        "save",
        "find",
        "show",
        "hide",
        "open",
        "close",
        "read",
        "write",
        "start",
        "stop",
        "send",
        "call",
        "exec",
        "eval",
        "log",
        "print",
        "format",
        "parse",
        "build",
        "create",
        "export",
        "import",
        "update",
        "delete",
        "remove",
        "clear",
        "has",
        "is",
        "can",
        "will",
        "not",
        "all",
        "the",
        "for",
        "auto",
        "quick",
        "rule",
        "rules",
        "file",
        "files",
        "detector",
        "score",
        "context",
        "project",
        "config",
        "data",
        "result",
        "report",
        "item",
        "items",
        "list",
        "name",
        "type",
        "value",
        "path",
        "code",
        "source",
        "base",
        "pipeline",
        "mixin",
        "handler",
        "manager",
        "executor",
        "scanner",
        "analyzer",
        "fixer",
        "checker",
        "wrapper",
        "adapter",
        "registry",
        "engine",
        "core",
        "ast",
        "security",
        "quality",
        "pattern",
        "diagnose",
        "diagnosis",
        "treatment",
        "validation",
        "verify",
        "with",
        "iter",
    }
)
def _token_set(name: str, stopwords: frozenset[str]) -> set[str]:
    return {
        token.lower()
        for token in _CAMEL_TOKEN_RE.findall(name)
        if len(token) >= 3 and token.lower() not in stopwords
    }
def name_tokens(name: str) -> set[str]:
    return _token_set(name, _COMMON_VERBS)
def _get_entry_tree(ctx: ScanContext, entry: DefEntry) -> ast.Module | None:
    tree = ctx.file_trees.get(entry.file_path)
    if tree is not None:
        return tree
    source = ctx.file_sources.get(entry.file_path)
    if source is None:
        source = read_source_text(entry.file_path)
        if source is None:
            return None
    tree, parse_error = parse_py_source(source)
    if tree is None:
        _log.debug(
            "coexistence_detect:_get_entry_tree: 条目源文件解析失败（跳过定位）: %s (%s)",
            entry.file_path, parse_error,
        )
    return tree
def _locate_func_node(
    tree: ast.Module, entry: DefEntry
) -> ast.FunctionDef | ast.AsyncFunctionDef | None:
    for node in walk_nodes(tree):
        if (
            isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            and node.lineno == entry.lineno
            and node.name == entry.name
        ):
            return node
    return None
def _locate_entry_node(
    ctx: ScanContext, entry: DefEntry
) -> ast.FunctionDef | ast.AsyncFunctionDef | None:
    tree = _get_entry_tree(ctx, entry)
    if tree is None:
        return None
    return _locate_func_node(tree, entry)
def _is_thin_delegate_body(body: list[ast.stmt]) -> bool:
    return (
        len(body) >= 2
        and isinstance(body[-1], ast.Return)
        and any(isinstance(stmt, (ast.Import, ast.ImportFrom))
                for stmt in body[:-1])
        and _delegation_call_from_body(body) is not None
    )
def is_thin_delegate_entry(ctx: ScanContext, entry: DefEntry) -> bool:
    node = _locate_entry_node(ctx, entry)
    if node is None:
        return False
    return _is_thin_delegate_body(body_without_docstring(node.body))
def _entry_param_names(ctx: ScanContext, entry: DefEntry) -> set[str] | None:
    node = _locate_entry_node(ctx, entry)
    if node is None:
        return None
    return collect_param_names(node)
def _mixin_tokens(name: str) -> set[str]:
    return _token_set(name.replace("Mixin", ""), _MIXIN_COMMON_TOKENS)
def _class_pair_rejects(old: DefEntry, new: DefEntry) -> bool:
    if not (camel_tokens(old.name) & camel_tokens(new.name)):
        return True
    if old.name in new.bases or new.name in old.bases:
        return True
    return (
        ("Mixin" in old.name or "Mixin" in new.name)
        and bool(_mixin_tokens(old.name) & _mixin_tokens(new.name))
    )
def _pair_item(
    pattern_type: str,
    old: DefEntry,
    new: DefEntry,
    confidence: float,
    evidence: list[str],
    suggestion: str,
) -> CoexistenceItem:
    return CoexistenceItem(
        pattern_type=pattern_type,
        old_name=old.name,
        new_name=new.name,
        old_file=old.file_path,
        new_file=new.file_path,
        old_lines=(old.lineno, old.end_lineno),
        new_lines=(new.lineno, new.end_lineno),
        confidence=confidence,
        evidence=evidence,
        suggestion=suggestion,
    )
def _generic_pair_rejected(old: DefEntry, new: DefEntry) -> bool:
    if old.name in _SIM_GENERIC_NAMES or new.name in _SIM_GENERIC_NAMES:
        return True
    return old.name.startswith("visit_") or new.name.startswith("visit_")
def _trivial_body_pair(old: DefEntry, new: DefEntry) -> bool:
    return old.end_lineno - old.lineno <= 3 and new.end_lineno - new.lineno <= 3
def _names_share_token(old: DefEntry, new: DefEntry) -> bool:
    return bool(name_tokens(old.name) & name_tokens(new.name))
def _shared_ref_pair(old: DefEntry, new: DefEntry) -> bool:
    return bool(
        (old.referenced_names - NOISE_REFS) & (new.referenced_names - NOISE_REFS)
    )
def _class_pair_invalid(old: DefEntry, new: DefEntry) -> bool:
    return (
        old.kind == "class"
        and new.kind == "class"
        and _class_pair_rejects(old, new)
    )
def _both_thin_delegate(ctx: ScanContext, old: DefEntry, new: DefEntry) -> bool:
    return is_thin_delegate_entry(ctx, old) and is_thin_delegate_entry(ctx, new)
def check_similarity_pair_valid(
    ctx: ScanContext, old: DefEntry, new: DefEntry
) -> bool:
    rejections = (
        _generic_pair_rejected(old, new),
        not _shared_ref_pair(old, new),
        _trivial_body_pair(old, new),
        _class_pair_invalid(old, new),
        not _names_share_token(old, new),
    )
    if any(rejections):
        return False
    return not _both_thin_delegate(ctx, old, new)
def _same_name_candidate(name: str) -> bool:
    if name.startswith("__") and name.endswith("__"):
        return False
    if name.startswith("test_"):
        return False
    if name in _GENERIC_NAME_BLACKLIST:
        return False
    return len(name) > 3
def _pair_has_lifecycle_signal(a: DefEntry, b: DefEntry) -> bool:
    return bool(
        a.is_dead or b.is_dead
        or a.is_deprecated or b.is_deprecated
        or a.is_stub or b.is_stub
    )
def _same_name_item(name: str, old: DefEntry, new: DefEntry,
                    unique_file_count: int) -> CoexistenceItem:
    confidence = 0.85
    if old.is_deprecated:
        confidence = 0.95
    if old.is_stub and not new.is_stub:
        confidence = max(confidence, 0.90)
    return _pair_item(
        "same_name",
        old,
        new,
        confidence,
        evidence=[
            f"同名定义 '{name}' 出现在 {unique_file_count} 个文件中",
            f"旧版: {old.file_path}:{old.lineno}"
            + (" (dead)" if old.is_dead else "")
            + (" (deprecated marker)" if old.is_deprecated else ""),
            f"新版: {new.file_path}:{new.lineno}",
        ],
        suggestion=f"移除旧版 '{old.name}'（{old.file_path}），保留新版（{new.file_path}）",
    )
def _cross_file_same_name_has_evidence(a: DefEntry, b: DefEntry) -> bool:
    return bool(
        a.is_deprecated or b.is_deprecated
        or a.is_stub or b.is_stub
        or _basename_signal(a, b) is not None
    )
def _same_name_items_for(
    name: str, entries: list[DefEntry], unique_file_count: int
) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    for a, b in combinations(entries, 2):
        if a.kind != b.kind or a.parent_class != b.parent_class:
            continue
        if not _pair_has_lifecycle_signal(a, b):
            continue
        if (a.file_path != b.file_path
                and not _cross_file_same_name_has_evidence(a, b)):
            continue
        old, new = determine_old_new(a, b)
        if old is None or new is None:
            pair = _dead_pair_tiebreak(a, b)
            if pair is None:
                continue
            old, new = pair
        items.append(_same_name_item(name, old, new, unique_file_count))
    return items
def detect_same_name(ctx: ScanContext) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    for name, entries in ctx.index.get_same_name_defs().items():
        if not _same_name_candidate(name):
            continue
        unique_file_count = len({entry.file_path for entry in entries})
        items.extend(_same_name_items_for(name, entries, unique_file_count))
    return items
def _iter_definitions(ctx: ScanContext) -> Iterator[DefEntry]:
    for entries in ctx.index.definitions.values():
        yield from entries
def _semantic_hash_groups(ctx: ScanContext) -> dict[str, list[DefEntry]]:
    hash_groups: dict[str, list[DefEntry]] = defaultdict(list)
    for entry in _iter_definitions(ctx):
        if entry.body_hash and not entry.is_stub:
            hash_groups[entry.body_hash].append(entry)
    return hash_groups
def _semantic_group_eligible(entry_body_hash: str, group: list[DefEntry]) -> bool:
    if len(group) < 2:
        return False
    if entry_body_hash in TRIVIAL_HASHES:
        return False
    return len(group) <= 20
def _semantic_pair_eligible(a: DefEntry, b: DefEntry) -> bool:
    if a.name == b.name:
        return False
    if a.kind != b.kind:
        return False
    if a.parent_class != b.parent_class:
        return False
    return a.is_dead or b.is_dead
def _semantic_similar_item(entry_body_hash: str, old: DefEntry,
                           new: DefEntry) -> CoexistenceItem:
    confidence = 0.75
    if old.is_dead and not new.is_dead:
        confidence = 0.80
    if old.is_deprecated:
        confidence = max(confidence, 0.85)
    return _pair_item(
        "semantic_similar",
        old,
        new,
        confidence,
        evidence=[
            f"'{old.name}' 与 '{new.name}' AST 结构哈希相同 ({entry_body_hash})",
            f"旧版: {old.file_path}:{old.lineno}"
            + (" (dead)" if old.is_dead else ""),
            f"新版: {new.file_path}:{new.lineno}",
        ],
        suggestion=f"移除旧版 '{old.name}'，保留功能等价的 '{new.name}'",
    )
def _semantic_items_for_group(
    ctx: ScanContext, entry_body_hash: str, group: list[DefEntry]
) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    for a, b in combinations(group, 2):
        if not _semantic_pair_eligible(a, b):
            continue
        old, new = determine_old_new(a, b)
        if old is None or new is None:
            pair = _dead_pair_tiebreak(a, b)
            if pair is None:
                continue
            old, new = pair
        if not check_similarity_pair_valid(ctx, old, new):
            continue
        items.append(_semantic_similar_item(entry_body_hash, old, new))
    return items
def detect_semantic_similar(ctx: ScanContext) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    for entry_body_hash, group in _semantic_hash_groups(ctx).items():
        if not _semantic_group_eligible(entry_body_hash, group):
            continue
        items.extend(_semantic_items_for_group(ctx, entry_body_hash, group))
    return items
def _stub_pools(
    ctx: ScanContext,
) -> tuple[list[DefEntry], dict[str, list[DefEntry]]]:
    stubs: list[DefEntry] = []
    reals: dict[str, list[DefEntry]] = defaultdict(list)
    for entry in _iter_definitions(ctx):
        if entry.is_stub:
            stubs.append(entry)
        else:
            reals[entry.name].append(entry)
    return stubs, reals
def _same_scope_reals(
    stub: DefEntry, reals: dict[str, list[DefEntry]]
) -> list[DefEntry]:
    return [
        r for r in reals.get(stub.name, [])
        if r.parent_class == stub.parent_class and r.kind == stub.kind
    ]
def _same_name_stub_items(
    stub: DefEntry, same_name_reals: list[DefEntry]
) -> list[CoexistenceItem]:
    return [
        _pair_item(
            "stub_real",
            stub,
            real,
            0.85,
            evidence=[
                f"桩函数 '{stub.name}' ({stub.file_path}:{stub.lineno})",
                f"同名实体: {real.file_path}:{real.lineno}",
            ],
            suggestion=f"移除桩函数 '{stub.name}'，保留实体实现",
        )
        for real in same_name_reals
    ]
def detect_stub_real(ctx: ScanContext) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    stubs, reals = _stub_pools(ctx)
    sorted_reals = [
        (name, entries, _name_stem(name).lower())
        for name, entries in sorted(reals.items())
    ]
    bigram_index = _bigram_index(sorted_reals)
    for stub in stubs:
        same_name_reals = _same_scope_reals(stub, reals)
        items.extend(_same_name_stub_items(stub, same_name_reals))
        if not same_name_reals:
            items.extend(_pair_similar_named_reals(
                stub, sorted_reals, bigram_index))
    return items
_SIBLING_ID_RE = re.compile(r"^(?P<prefix>.*?)(?P<suffix>_?[A-Za-z]?\d+)$")
def _sibling_id_names(a: str, b: str) -> bool:
    if a == b:
        return False
    a_match = _SIBLING_ID_RE.match(a)
    b_match = _SIBLING_ID_RE.match(b)
    if a_match is None or b_match is None:
        return False
    if a_match.group("prefix") != b_match.group("prefix"):
        return False
    return not (_VERSION_SUFFIX_RE.search(a) and _VERSION_SUFFIX_RE.search(b))
def _similar_name_pair_ok(stub: DefEntry, real: DefEntry) -> bool:
    if stub.kind != real.kind:
        return False
    if _sibling_id_names(stub.name, real.name):
        return False
    return not (stub.kind == "class" and _class_pair_rejects(stub, real))
def _pair_similar_named_reals(
    stub: DefEntry,
    reals: list[tuple[str, list[DefEntry], str]],
    bigram_index: dict[str, set[int]],
) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    for real_name, real_entries, _real_stem in _similar_name_candidates(
            stub.name, reals, bigram_index):
        sim = name_similarity(stub.name, real_name)
        if sim < _SIMILAR_NAME_THRESHOLD:
            continue
        for real in real_entries:
            if real.parent_class != stub.parent_class:
                continue
            if not _similar_name_pair_ok(stub, real):
                continue
            items.append(
                _pair_item(
                    "stub_real",
                    stub,
                    real,
                    0.70,
                    evidence=[
                        f"桩函数 '{stub.name}' ({stub.file_path}:{stub.lineno})",
                        f"相似名称实体 '{real.name}' ({real.file_path}:{real.lineno})",
                        f"名称相似度: {sim:.2f}",
                    ],
                    suggestion=f"移除桩函数 '{stub.name}'，使用 '{real.name}'",
                )
            )
    return items
def _collect_function_entries(ctx: ScanContext) -> dict[str, list[DefEntry]]:
    name_to_entries: dict[str, list[DefEntry]] = {}
    for entry in _iter_definitions(ctx):
        if entry.kind == "function":
            name_to_entries.setdefault(entry.name, []).append(entry)
    return name_to_entries
def _scope_groups(entries: list[DefEntry]) -> dict[str, list[DefEntry]]:
    scopes: dict[str, list[DefEntry]] = defaultdict(list)
    for entry in entries:
        scopes[entry.parent_class].append(entry)
    return scopes
def _signature_similar_enough(
    ctx: ScanContext, shadow: DefEntry, base: DefEntry
) -> bool:
    shadow_params = _entry_param_names(ctx, shadow)
    base_params = _entry_param_names(ctx, base)
    if shadow_params is None or base_params is None:
        return True
    if not (shadow_params or base_params):
        return True
    return len(shadow_params & base_params) / len(shadow_params | base_params) >= 0.5
def _pair_shadow_in_scope(
    ctx: ScanContext,
    scope: str,
    shadow_scopes: dict[str, list[DefEntry]],
    base_scopes: dict[str, list[DefEntry]],
    base_name: str,
    fname: str,
) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    scope_bases = base_scopes.get(scope, [])
    for shadow_entry in sorted(
            shadow_scopes[scope], key=lambda e: (e.file_path, e.lineno)):
        for base_entry in sorted(
                scope_bases, key=lambda e: (e.file_path, e.lineno)):
            if not _signature_similar_enough(ctx, shadow_entry, base_entry):
                continue
            conf = 0.78 if shadow_entry.file_path == base_entry.file_path else 0.72
            items.append(_pair_item(
                "shadow_function",
                base_entry,
                shadow_entry,
                conf,
                evidence=[
                    f"原始函数: {base_name} in {os.path.basename(base_entry.file_path)}",
                    f"阴影函数: {fname} in {os.path.basename(shadow_entry.file_path)}",
                ],
                suggestion=f"确认 '{base_name}' 和 '{fname}' 是否为新旧版本，将调用者迁移到新版后移除旧版",
            ))
    return items
def detect_shadow_functions(ctx: ScanContext) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    name_to_entries = _collect_function_entries(ctx)
    for fname in list(name_to_entries.keys()):
        m = _SHADOW_SUFFIX.match(fname)
        if not m:
            continue
        base_name = m.group(1)
        if base_name not in name_to_entries:
            continue
        shadow_scopes = _scope_groups(name_to_entries[fname])
        base_scopes = _scope_groups(name_to_entries[base_name])
        for scope in sorted(shadow_scopes):
            items.extend(_pair_shadow_in_scope(
                ctx, scope, shadow_scopes, base_scopes, base_name, fname
            ))
    return items
def is_unspecified_target(name: Any) -> bool:
    if isinstance(name, bytes):
        text = name.decode("utf-8", errors="replace")
    elif not name:
        text = ""
    else:
        text = str(name)
    text = text.strip()
    return not text or text == UNSPECIFIED_TARGET
COEXISTENCE_STRATEGIES: tuple[
    tuple[str, Callable[[ScanContext], list[CoexistenceItem]]], ...
] = (
    ("S1", detect_same_name),
    ("S2", detect_delegation),
    ("S6", detect_partial_delegation),
    ("S3", detect_semantic_similar),
    ("S4", detect_deprecated_markers),
    ("S5", detect_stub_real),
    ("S7", detect_import_bridge),
    ("S8", detect_conditional_routing),
    ("S9", detect_migration_markers),
    ("S10", detect_dual_write),
    ("S11", detect_shadow_functions),
)
def run_coexistence_strategies(ctx: ScanContext,
                               errors: list[str]) -> list[CoexistenceItem]:
    items: list[CoexistenceItem] = []
    for strategy_id, runner in COEXISTENCE_STRATEGIES:
        try:
            items.extend(runner(ctx))
        except Exception as exc:  # noqa: BLE001
            _log.warning("共存策略 %s 执行失败: %s: %s",
                         strategy_id, type(exc).__name__, exc, exc_info=True)
            errors.append(f"{strategy_id}: {type(exc).__name__}: {exc}")
    return items

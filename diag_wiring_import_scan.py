from __future__ import annotations

import ast
import logging
import os
import re
import sys
from collections import defaultdict
from collections.abc import Iterable, Iterator
from dataclasses import dataclass, field
from importlib import util
from typing import Any

from jwsgj.diag_shared_ast_nodes import (
    first_segment,
    import_fallback_import_lines,
    parse_source_tree,
)
from jwsgj.diag_shared_source_core import (
    TRY_TYPES,
    aligned_source_lines,
    read_source,
    read_source_with_fingerprint,
)
from jwsgj.diag_shared_source_scan import (
    is_import_like_line,
    string_comment_spans,
    strip_import_line_comment,
)
from jwsgj.diag_types_defs import finding_scan_exempt
from jwsgj.diag_types_vocab import PROJECT_ROOT_MARKERS
from jwsgj.diag_wiring_imports import check_UC01
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import (
    SOURCE_LAYOUT_ROOT_NAMES,
    infer_project_root,
    source_import_roots,
)
from jwsgj.runtime_scope import (
    SYS_TMP_ROOT,
    collect_py_files,
    is_scan_py_name,
    is_test_dir_name,
    is_test_file_path,
    is_under_root,
    keep_inventory_dir,
    safe_relpath,
)

_log = logging.getLogger(__name__)
__all__ = [
    'BareImport',
    'DepthError',
    'HubModule',
    'ImportScanContext',
    'build_import_scan_context',
    'check_GF16',
    'check_GF18',
    'collect_all_imports',
    'collect_internal_modules',
    'count_leading_dots',
    'detect_bare_imports',
    'detect_depth_errors',
    'detect_hub_modules',
    'detect_import_bloat',
    'dots_resolve_to_module',
    'enclosing_package_dots',
    'imports_in_line',
    'iter_import_lines',
    'iter_project_py_files',
    'path_depth',
    'resolve_project_package',
]
_log.info("diag_wiring_import_scan 导入事实与结构规则域已加载: %d 项导出",
          len(__all__))
_BRACKET_PAIRS = {'(': ')', '[': ']', '{': '}'}
_QUOTE_CHARS = ("'", '"')
_COMPOUND_HEAD_RE = re.compile(
    r'^\s*(?:async\s+)?(?:if|elif|else|try|except|finally|for|while|with|'
    r'def|class|match|case)\b')
def _quoted_span_end(line: str, start: int) -> int:
    quote = line[start]
    pos = start + 1
    while pos < len(line):
        ch = line[pos]
        if ch == "\\":
            pos += 2
            continue
        if ch == quote:
            return pos + 1
        pos += 1
    return len(line)
def _track_bracket(ch: str, stack: list[str]) -> None:
    if ch in _BRACKET_PAIRS:
        stack.append(_BRACKET_PAIRS[ch])
    elif ch in (')', ']', '}') and stack and stack[-1] == ch:
        stack.pop()
def _split_top_level_statements(line: str) -> list[str]:
    parts: list[str] = []
    stack: list[str] = []
    start = 0
    pos = 0
    lambda_depth = 0
    while pos < len(line):
        ch = line[pos]
        if ch in _QUOTE_CHARS:
            pos = _quoted_span_end(line, pos)
            continue
        if ch == '#':
            break
        if (not stack and line.startswith('lambda', pos)
                and (pos == 0 or not (
                    line[pos - 1].isalnum() or line[pos - 1] == '_'))
                and (pos + 6 == len(line) or not (
                    line[pos + 6].isalnum() or line[pos + 6] == '_'))):
            lambda_depth += 1
            pos += 6
            continue
        if ch == ';' and not stack:
            parts.append(line[start:pos])
            start = pos + 1
        elif ch == ':' and not stack and lambda_depth:
            lambda_depth -= 1
        elif (ch == ':' and not stack
              and _COMPOUND_HEAD_RE.match(line[start:pos])):
            parts.append(line[start:pos + 1])
            start = pos + 1
        else:
            _track_bracket(ch, stack)
        pos += 1
    parts.append(line[start:pos])
    return [part for part in parts if part.strip()]
_IMPORT_ALIAS_RE = re.compile(r'\s+as\s+')
def _import_segment_pairs(raw: str) -> list[tuple[str, str]]:
    pairs: list[tuple[str, str]] = []
    for statement in _split_top_level_statements(raw):
        body = strip_import_line_comment(statement)
        body = re.sub(r'^\s*import\s+', '', body)
        for seg in body.split(','):
            parts = _IMPORT_ALIAS_RE.split(seg.strip(), maxsplit=1)
            mod = parts[0].strip()
            if mod:
                pairs.append((mod, parts[1].strip() if len(parts) > 1 else ''))
    return pairs
def _import_segments(raw: str) -> list[str]:
    return [mod for mod, _alias in _import_segment_pairs(raw)]
def _source_lines(source: str) -> Iterator[str]:
    yield from source.replace("\r\n", "\n").replace("\r", "\n").split("\n")
_FROM_IMPORT_RE = re.compile(r'from\s+([.\w]+?)(?:\s+|(?<=\.))import\b')
_FROM_IMPORT_NAMES_RE = re.compile(
    r'from\s+[.\w]+?(?:\s+|(?<=\.))import\b\s*(.+)$')
_PLAIN_IMPORT_RE = re.compile(r'import\s+(.+)$')
_IMPORT_TARGET_RE = re.compile(r'[\w.]+')
def _import_forms(line: str) -> tuple[str, str, list[str]]:
    if m := _FROM_IMPORT_RE.match(line):
        return "from", "", [m.group(1)]
    if m := _PLAIN_IMPORT_RE.match(line):
        raw = m.group(1)
        return "import", raw, [mod for mod in _import_segments(raw)
                                if _IMPORT_TARGET_RE.fullmatch(mod)]
    return "", "", []
def imports_in_line(line: str) -> list[str]:
    return _import_forms(line)[2]
def _from_import_names(stmt: str) -> list[str]:
    match = _FROM_IMPORT_NAMES_RE.match(stmt)
    if not match:
        return []
    raw = match.group(1).strip()
    if raw.startswith('('):
        raw = raw[1:]
    raw = raw.rstrip(')').rstrip(',').strip()
    return re.findall(r'(?:^|,)\s*([^\W\d]\w*)', raw)
def _code_line_projections(source: str) -> list[str] | None:
    spans = string_comment_spans(source)
    if spans is None:
        return None
    projections: list[str] = []
    for row, text in enumerate(_source_lines(source), 1):
        indent = len(text) - len(text.lstrip())
        if not any(start <= indent < end
                   for start, end in spans.get(row, ())):
            projections.append(text)
            continue
        chars = list(text)
        for start, end in spans.get(row, ()):
            for col in range(max(start, 0), min(end, len(chars))):
                chars[col] = " "
        projections.append("".join(chars))
    return projections
def _iter_import_source_lines(filepath: str, source: str, tag: str):
    projections = _code_line_projections(source)
    for lineno, raw in enumerate(_source_lines(source), 1):
        projected = raw if projections is None else projections[lineno - 1]
        if not projected.strip():
            if is_import_like_line(raw.strip()):
                _log.debug("[%s] 跳过字符串/注释区域伪导入行: %s:%d",
                           tag, filepath, lineno)
            continue
        yield lineno, projected
def _paren_depth(text: str) -> int:
    depth = 0
    quote = ""
    escaped = False
    for ch in text:
        if quote:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == quote:
                quote = ""
            continue
        if ch in ("'", '"'):
            quote = ch
        elif ch == "#":
            break
        elif ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
    return depth
@dataclass
class _LogicalImportBuffer:
    pending: str = ""
    start: int = 0
    depth: int = 0
    def absorb(self, stmt: str, lineno: int) -> tuple[int, str] | None:
        continued = stmt.endswith("\\")
        if continued:
            stmt = stmt[:-1].rstrip()
        if not self.pending:
            if (not imports_in_line(stmt)
                    and not (continued and stmt == "import")):
                return None
            self.pending, self.start, self.depth = stmt, lineno, _paren_depth(stmt)
        else:
            self.pending = f"{self.pending} {stmt}".strip()
            self.depth += _paren_depth(stmt)
        if self.depth > 0 or continued:
            return None
        text, start = self.pending, self.start
        self.pending, self.depth = "", 0
        return start, text
    def take(self) -> tuple[int, str] | None:
        if not self.pending:
            return None
        return self.start, self.pending
def _logical_import_lines(filepath: str, source: str, tag: str):
    buffer = _LogicalImportBuffer()
    for lineno, raw in _iter_import_source_lines(filepath, source, tag):
        statements = _split_top_level_statements(raw)
        for statement in statements:
            stmt = strip_import_line_comment(statement.strip())
            if not stmt:
                continue
            merged = buffer.absorb(stmt, lineno)
            if merged is None:
                continue
            start, text = merged
            targets = imports_in_line(text)
            if targets:
                yield filepath, start, text, targets
    tail = buffer.take()
    if tail is not None:
        start, text = tail
        targets = imports_in_line(text)
        if targets:
            yield filepath, start, text, targets
def iter_import_lines(py_files, tag: str):
    for filepath in py_files:
        source, _fingerprint = read_source_with_fingerprint(filepath)
        if source is None:
            _log.debug("[%s] 逐行读取跳过（TOCTOU，该文件漏检）: %s",
                       tag, filepath)
            continue
        yield from _logical_import_lines(filepath, source, tag)
def _import_head_segments(sub: ast.AST) -> tuple[bool, list[str]]:
    if isinstance(sub, ast.ImportFrom):
        relative = sub.level >= 1
        if sub.module:
            return relative, [first_segment(sub.module)]
        return relative, [alias.name for alias in sub.names]
    if isinstance(sub, ast.Import):
        return False, [first_segment(alias.name) for alias in sub.names]
    return False, []
def _is_package_guard(node: ast.AST) -> bool:
    return (isinstance(node, ast.If)
            and any(isinstance(sub, ast.Name) and sub.id == '__package__'
                    for sub in walk_nodes(node.test)))
def _guard_exempts(source: str | None, filepath: str) -> dict[int, set[str]]:
    """收集「已由守卫语句明示」的裸导入行，返回 ``{行号: 模块头段名}``。

    两类守卫：①``if __package__:`` 分支配对；②``try: <相对导入> /
    except ImportError: <裸导入>`` 双模式回退。后者不识别时，每个双模式
    模块的每一处回退导入都会报成 GF-16 裸包内导入（P0）。
    """
    if not source:
        return {}
    tree = parse_source_tree(source, filepath)
    if tree is None:
        return {}
    exempts = _collect_package_guard_exempts(tree)
    for line_no, head in import_fallback_import_lines(tree).items():
        exempts.setdefault(line_no, set()).add(head)
    return exempts
def path_depth(filepath: str, root: str) -> int:
    rel = os.path.relpath(os.path.dirname(filepath), root)
    if rel == '.':
        return 0
    return len(rel.replace('\\', '/').split('/'))
def _file_import_root(filepath: str, project_root: str) -> str:
    root = os.path.abspath(project_root)
    return next(
        (source_root for source_root in source_import_roots(root)
         if is_under_root(filepath, source_root)),
        root,
    )
def _project_package_dots(filepath: str, project_root: str) -> int:
    root = os.path.abspath(project_root)
    if _is_package_dir(root):
        anchor = os.path.dirname(root)
    else:
        anchor = _file_import_root(filepath, root)
    if not is_under_root(filepath, anchor):
        return 0
    rel_dir = os.path.relpath(
        os.path.dirname(os.path.abspath(filepath)), anchor)
    if rel_dir == os.curdir:
        return 0
    return len(rel_dir.replace('\\', '/').split('/'))
def enclosing_package_dots(filepath: str, project_root: str | None = None) -> int:
    if project_root is not None:
        return _project_package_dots(filepath, project_root)
    dots = 0
    current = os.path.dirname(os.path.abspath(filepath))
    while _is_package_dir(current):
        dots += 1
        parent = os.path.dirname(current)
        if parent == current:
            break
        current = parent
    return dots
def dots_resolve_to_module(filepath: str, first_part: str,
                            dots: int, depth: int) -> bool:
    if not 1 <= dots <= depth + 1:
        return False
    resolved_dir = os.path.dirname(filepath)
    for _ in range(dots - 1):
        resolved_dir = os.path.dirname(resolved_dir)
    return (os.path.isfile(os.path.join(resolved_dir, first_part + '.py'))
            or os.path.isdir(os.path.join(resolved_dir, first_part)))
def relative_dots_for_module(filepath: str, first_part: str,
                              depth: int, *, project_root: str | None = None) -> int:
    max_dots = min(
        depth + 1, enclosing_package_dots(filepath, project_root))
    for dots in range(1, max_dots + 1):
        if dots_resolve_to_module(filepath, first_part, dots, depth):
            return dots
    return max_dots
def _temp_root_key(path: str) -> str:
    try:
        key = os.path.normcase(os.path.realpath(os.path.abspath(path)))
    except (OSError, ValueError):
        return ""
    return key.replace("\\", "/").lower().rstrip("/")
def _is_temp_root(path: str) -> bool:
    return _temp_root_key(path) == SYS_TMP_ROOT
def _is_marked_project_root(root: str) -> bool:
    return bool(root) and any(
        os.path.exists(os.path.join(root, marker))
        for marker in PROJECT_ROOT_MARKERS)
def _find_spec(module_path: str, *, quiet: bool = False) -> Any:
    try:
        return util.find_spec(module_path)
    except KeyboardInterrupt:
        raise
    except BaseException as e:
        # 即使 quiet=True 也要留痕：静默吞掉定位异常会让“模块未找到”与
        # “探测过程崩溃”不可区分。
        log_swallowed(
            __name__, e, context=f'_find_spec:{type(e).__name__}')
        if not quiet:
            _log.debug("find_spec 定位模块 %s 失败: %s", module_path, e)
        return None
@dataclass(frozen=True)
class _BareScanContext:
    filepath: str
    rel_file: str
    depth: int
    internal_modules: set[str]
    exempt_lines: dict[int, set[str]]
    package_names: frozenset = frozenset()
    package_import_roots: tuple = ()
    project_root: str = ""
def _bare_import_record(ctx: _BareScanContext, line_no: int,
                        line_stripped: str, target: str,
                        suggested: str) -> BareImport:
    return BareImport(
        file=ctx.rel_file,
        line=line_no,
        import_stmt=line_stripped,
        target_module=target,
        suggested_fix=suggested,
        risk="HIGH" if ctx.depth > 0 else "MEDIUM",
    )
def _resolves_from_dir(base_dir: str, target: str) -> bool:
    parts = [p for p in target.split('.') if p]
    if not parts:
        return False
    last = len(parts) - 1
    cur = base_dir
    for idx, part in enumerate(parts):
        if os.path.isfile(os.path.join(cur, part + '.py')):
            return idx == last
        pkg = os.path.join(cur, part)
        if not os.path.isdir(pkg):
            return False
        if idx == last:
            return True
        cur = pkg
    return True
def _inside_project_package(filepath: str, root: str, name: str) -> bool:
    root = os.path.abspath(root)
    if os.path.basename(os.path.normpath(root)) == name and _is_package_dir(root):
        return True
    package_dir = os.path.join(root, name)
    if not _is_package_dir(package_dir):
        return False
    try:
        rel = os.path.relpath(os.path.abspath(filepath), package_dir)
    except ValueError:  # jwsgj:silent-ok 纯值降级：入参不可解析时返回安全默认值，无副作用可留痕
        return False
    return not (rel == os.pardir or rel.startswith(os.pardir + os.sep)
                or os.path.isabs(rel))
def _skip_generic_bare(ctx: _BareScanContext, target: str) -> bool:
    first = first_segment(target)
    if first in ctx.package_names and _inside_project_package(
            ctx.filepath, ctx.project_root, first):
        return True
    if any(_resolves_from_dir(base, target)
           for base in ctx.package_import_roots):
        return True
    return _is_external_top_module(first)
def _is_internal_bare_name(first: str, internal_modules: set[str]) -> bool:
    return (first in internal_modules
            and not (first.startswith('__') and first.endswith('__')))
def _is_external_top_module(name: str) -> bool:
    if not name:
        return False
    if (name in sys.builtin_module_names
            or name in getattr(sys, "stdlib_module_names", ())):
        return True
    return _find_spec(name, quiet=True) is not None
def _is_exempt(ctx: _BareScanContext, line_no: int, first: str) -> bool:
    return first in ctx.exempt_lines.get(line_no, ())
def _bare_target_dots(ctx: _BareScanContext, first: str) -> int | None:
    dots = relative_dots_for_module(
        ctx.filepath, first, ctx.depth, project_root=ctx.project_root)
    if not dots_resolve_to_module(ctx.filepath, first, dots, ctx.depth):
        return None
    return dots
def _bare_from_import(ctx: _BareScanContext, line_no: int,
                      line_stripped: str, target: str) -> BareImport | None:
    first = first_segment(target)
    if not _is_internal_bare_name(first, ctx.internal_modules):
        return None
    if _is_exempt(ctx, line_no, first) or _skip_generic_bare(ctx, target):
        return None
    target_dots = _bare_target_dots(ctx, first)
    if target_dots is None:
        return None
    dots = '.' * target_dots
    return _bare_import_record(
        ctx, line_no, line_stripped, target, f"from {dots}{target} import ...")
def _relative_import_suggestion(dots: int, name: str,
                               alias: str = '') -> str:
    if not dots:
        return f"import {name} as {alias}" if alias else f"import {name}"
    prefix = '.' * dots
    if '.' in name:
        package, _dot, leaf = name.rpartition('.')
        if alias:
            return f"from {prefix}{package} import {leaf} as {alias}"
        top_level = name.split('.', 1)[0]
        return (f"from {prefix} import {top_level}; "
                f"from {prefix}{package} import {leaf}")
    suggestion = f"from {prefix} import {name}"
    return f"{suggestion} as {alias}" if alias else suggestion
def _bare_plain_imports(ctx: _BareScanContext, line_no: int,
                        line_stripped: str,
                        import_args: str) -> list[BareImport]:
    records: list[BareImport] = []
    for name, alias in _bare_import_segments(import_args, ctx.internal_modules):
        first = first_segment(name)
        if _is_exempt(ctx, line_no, first) or _skip_generic_bare(ctx, name):
            continue
        dots = _bare_target_dots(ctx, first)
        if dots is None:
            continue
        suggested = _relative_import_suggestion(dots, name, alias)
        records.append(_bare_import_record(
            ctx, line_no, line_stripped, name, suggested))
    return records
def detect_bare_imports(py_files: list[str], internal_modules: set[str],
                        root: str) -> list[BareImport]:
    results = []
    for fp in py_files:
        results.extend(_scan_file_bare_imports(fp, internal_modules, root))
    return results
def _is_package_dir(path: str) -> bool:
    return os.path.isfile(os.path.join(path, "__init__.py"))
def _package_dirs(base: str) -> list[str]:
    try:
        entries = sorted(os.listdir(base))
    except OSError as _e:
        if not isinstance(_e, FileNotFoundError):
            log_swallowed(
                __name__, _e, context=f'_package_dirs:{type(_e).__name__}')
        return []
    return [name for name in entries
            if not name.startswith(".")
            and _is_package_dir(os.path.join(base, name))]
def _layout_source_root(root: str) -> str:
    for name in SOURCE_LAYOUT_ROOT_NAMES:
        candidate = os.path.join(root, name)
        if os.path.isdir(candidate):
            return candidate
    return ""
def resolve_project_package(root: str) -> tuple[str, str, str]:
    root = os.path.abspath(root)
    if _is_package_dir(root):
        return (os.path.basename(os.path.normpath(root)), root,
                os.path.dirname(root))
    layout_root = _layout_source_root(root)
    if layout_root:
        packages = _package_dirs(layout_root)
        if len(packages) == 1:
            package_name = packages[0]
            return (package_name, os.path.join(layout_root, package_name),
                    layout_root)
        return "", "", layout_root
    packages = _package_dirs(root)
    if len(packages) == 1:
        package_name = packages[0]
        return package_name, os.path.join(root, package_name), root
    return "", "", root
def _project_package_names(root: str) -> frozenset:
    root = os.path.abspath(root)
    names: set[str] = set()
    if _is_package_dir(root):
        names.add(os.path.basename(os.path.normpath(root)))
    layout_root = _layout_source_root(root)
    if layout_root:
        names.update(_package_dirs(layout_root))
    names.update(_package_dirs(root))
    return frozenset(names)
def _package_import_roots(root: str) -> tuple[str, ...]:
    root = os.path.abspath(root)
    roots = [os.path.dirname(root) if _is_package_dir(root) else root]
    roots.extend(source_import_roots(root))
    return tuple(dict.fromkeys(roots))
def _scan_file_bare_imports(filepath: str, internal_modules: set[str],
                            root: str) -> list[BareImport]:
    source, _fingerprint = read_source_with_fingerprint(filepath)
    if source is None:
        _log.debug("[GF-16] 逐行读取跳过（TOCTOU，该文件漏检）: %s", filepath)
        return []
    rel_file = os.path.relpath(filepath, root)
    depth = path_depth(filepath, root)
    ctx = _BareScanContext(
        filepath=filepath,
        rel_file=rel_file,
        depth=depth,
        internal_modules=internal_modules,
        exempt_lines=_guard_exempts(source, filepath),
        package_names=_project_package_names(root),
        package_import_roots=_package_import_roots(root),
        project_root=os.path.abspath(root),
    )
    results: list[BareImport] = []
    for _fp, line_no, line, _targets in _logical_import_lines(
            filepath, source, "GF-16"):
        results.extend(_scan_bare_line(ctx, line_no, line))
    return results
def _scan_bare_line(ctx: _BareScanContext, line_no: int,
                    line_stripped: str) -> list[BareImport]:
    form, raw_args, targets = _import_forms(line_stripped)
    if form == "from":
        item = _bare_from_import(ctx, line_no, line_stripped, targets[0])
        return [item] if item else []
    if form == "import":
        return _bare_plain_imports(ctx, line_no, line_stripped, raw_args)
    return []
def _bare_import_segments(import_args: str,
                          internal_modules: set[str]) -> list[tuple[str, str]]:
    results: list[tuple[str, str]] = []
    for name, alias in _import_segment_pairs(import_args):
        if not _IMPORT_TARGET_RE.fullmatch(name):
            continue
        if _is_internal_bare_name(first_segment(name), internal_modules):
            results.append((name, alias))
    return results
def _relative_import_segments(stmts: list[ast.stmt]) -> set[str]:
    segments: set[str] = set()
    for stmt in stmts:
        for sub in walk_nodes(stmt):
            is_rel, heads = _import_head_segments(sub)
            if is_rel:
                segments.update(heads)
    return segments
def _absolute_import_heads(stmts: list[ast.stmt]) -> list[tuple[ast.AST, list[str]]]:
    found: list[tuple[ast.AST, list[str]]] = []
    for stmt in stmts:
        for sub in walk_nodes(stmt):
            is_rel, heads = _import_head_segments(sub)
            if not is_rel and heads:
                found.append((sub, heads))
    return found
def _collect_package_guard_exempts(tree: ast.AST) -> dict[int, set[str]]:
    exempts: dict[int, set[str]] = {}
    for node in walk_nodes(tree):
        if not _is_package_guard(node):
            continue
        _pair_guard_branch_exempts(node.body, node.orelse, exempts)
        _pair_guard_branch_exempts(node.orelse, node.body, exempts)
    return exempts
def _pair_guard_branch_exempts(relative_stmts: list[ast.stmt],
                               absolute_stmts: list[ast.stmt],
                               exempts: dict[int, set[str]]) -> None:
    rel_first = _relative_import_segments(relative_stmts)
    if not rel_first:
        return
    for sub, heads in _absolute_import_heads(absolute_stmts):
        for first in rel_first.intersection(heads):
            exempts.setdefault(sub.lineno, set()).add(first)
@dataclass
class BareImport:
    file: str = ""
    line: int = 0
    import_stmt: str = ""
    target_module: str = ""
    suggested_fix: str = ""
    risk: str = ""
    def to_dict(self) -> dict:
        return dict(self.__dict__)
def collect_internal_modules(py_files: list[str], project_root: str) -> set[str]:
    root = os.path.abspath(project_root)
    internal: set[str] = set()
    for fp in py_files:
        base = os.path.basename(fp)
        if base != '__init__.py':
            internal.add(os.path.splitext(base)[0])
        import_root = _file_import_root(fp, root)
        if not is_under_root(fp, import_root):
            continue
        rel_dir = os.path.relpath(
            os.path.dirname(os.path.abspath(fp)), import_root)
        if rel_dir != os.curdir:
            internal.update(rel_dir.replace('\\', '/').split('/'))
    return internal
def collect_all_imports(py_files: list[str]) -> dict[str, list[tuple[int, str, str]]]:
    all_imports: dict[str, list[tuple[int, str, str]]] = {}
    for filepath, lineno, stmt, targets in iter_import_lines(
            py_files, "GF-16/18"):
        for target in targets:
            all_imports.setdefault(filepath, []).append((lineno, stmt, target))
    return all_imports
def _walk_error(err: OSError) -> None:
    _log.warning("[GF-16] 目录遍历受限，扫描结果可能不完整: %s", err)
def iter_project_py_files(root: str) -> list[str]:
    files: list[str] = []
    for dirpath, dirs, filenames in os.walk(root, onerror=_walk_error):
        dirs[:] = [d for d in dirs
                   if keep_inventory_dir(d) and not is_test_dir_name(d)]
        for name in filenames:
            if is_scan_py_name(name):
                files.append(os.path.join(dirpath, name))
    files.sort()
    return files
@dataclass(frozen=True)
class ImportScanContext:
    project_root: str = ""
    py_files: tuple[str, ...] = ()
    internal_modules: frozenset[str] = frozenset()
def build_import_scan_context(project_root: str) -> ImportScanContext:
    root = os.path.abspath(project_root)
    py_files = tuple(iter_project_py_files(root))
    return ImportScanContext(
        project_root=root,
        py_files=py_files,
        internal_modules=frozenset(
            collect_internal_modules(list(py_files), root)),
    )
def _outermost_package_parent(filepath: str) -> str:
    current = os.path.dirname(os.path.abspath(filepath))
    parent = ""
    while _is_package_dir(current):
        parent = os.path.dirname(current)
        if parent == current:
            break
        current = parent
    return parent
def _root_inside_system_temp(root: str) -> bool:
    if not root:
        return False
    key = _temp_root_key(root)
    return bool(key) and (
        key == SYS_TMP_ROOT or key.startswith(SYS_TMP_ROOT + "/"))
def _bounded_project_root(filepath: str, root: str) -> str:
    if not root or not filepath:
        return root
    if not _root_inside_system_temp(root) or _is_marked_project_root(root):
        return root
    return (_outermost_package_parent(filepath)
            or os.path.dirname(os.path.abspath(filepath)))
def _context_for(filepath: str, context: ImportScanContext | None
                 ) -> ImportScanContext:
    if (context is not None and context.project_root
            and is_under_root(filepath, context.project_root)):
        return context
    root = _bounded_project_root(filepath, infer_project_root(filepath))
    return build_import_scan_context(root)
_DEFAULT_FILEPATH = ''
def check_GF16(filepath: str = _DEFAULT_FILEPATH,
               context: ImportScanContext | None = None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    if not filepath:
        return []
    ctx = _context_for(filepath, context)
    project_root = ctx.project_root
    return [
        {
            "rule_id": "GF-16",
            "severity": "P0",
            "file": os.path.normpath(os.path.join(project_root, item.file)),
            "line": item.line,
            "message": f"裸包内导入: {item.import_stmt}",
            "category": "import_safety",
        }
        for item in _scan_file_bare_imports(
            filepath, set(ctx.internal_modules), project_root)
    ]
_MATCH_TYPES = (ast.Match,) if hasattr(ast, "Match") else ()
class _CondMarker(ast.NodeVisitor):
    def __init__(self, node_ids: set[int]) -> None:
        self._node_ids: set[int] = node_ids
        self._depth: int = 0
    def visit(self, node: ast.AST) -> None:
        if self._depth > 0:
            self._node_ids.add(id(node))
        if isinstance(node, (ast.If, *TRY_TYPES, *_MATCH_TYPES,
                              ast.ExceptHandler)):
            self._depth += 1
            self.generic_visit(node)
            self._depth -= 1
        else:
            self.generic_visit(node)
_EXEMPT_IMPORT_CATEGORIES = frozenset({"conditional", "type_annotation"})
_TYPE_ANNOTATION_NAMES = frozenset({
    'List', 'Dict', 'Set', 'Tuple', 'Optional', 'Union', 'Any',
    'Callable', 'Iterator', 'Iterable', 'Sequence', 'Mapping',
    'TypeVar', 'Generic', 'Protocol', 'NamedTuple', 'TypedDict',
    'Literal', 'Final', 'ClassVar', 'NoReturn', 'Type', 'cast',
    'overload', 'runtime_checkable', 'dataclass_transform',
    'Annotated', 'Path', 'IO', 'Pattern', 'Match',
})
def _register_import_node(node, conditional_node_ids, all_imports,
                          rel_path):
    if isinstance(node, ast.ImportFrom):
        if node.module == "__future__":
            return
        aliases = [a for a in node.names if a.name != '*']
    else:
        aliases = node.names
    cat = "conditional" if id(node) in conditional_node_ids else "top_level"
    for alias in aliases:
        name = alias.asname or (
            alias.name if isinstance(node, ast.ImportFrom)
            else first_segment(alias.name))
        all_imports.append(
            {"file": rel_path, "line": node.lineno, "import": name, "category": cat})
def _collect_bloat_names(tree, conditional_node_ids, all_imports, rel_path):
    for node in walk_nodes(tree):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            _register_import_node(node, conditional_node_ids, all_imports,
                                  rel_path)
def _bloat_tree_from_ctx(fpath: str, source: str, ctx: Any):
    if ctx is not None and hasattr(ctx, "get_ast"):
        try:
            return ctx.get_ast(fpath)
        except Exception as e:
            _log.debug("[ImportBloat] ctx AST 通道故障，回退直解析 %s: %s",
                       fpath, e)
    return parse_source_tree(source, fpath)
def _iter_bloat_file_trees(fpaths: list, ctx: Any):
    for fp in fpaths:
        source = read_source(fp, ctx)
        if source is None:
            continue
        tree = _bloat_tree_from_ctx(fp, source, ctx)
        if tree is not None:
            yield fp, tree, source
def _scan_bloat_imports(skill_dir: str, fpaths: list, ctx: Any) -> tuple:
    unused_by_file: dict[str, set[tuple[int, str]]] = {}
    all_imports = []
    for fp, tree, source in _iter_bloat_file_trees(fpaths, ctx):
        rel_path = safe_relpath(fp, skill_dir)
        conditional_node_ids = set()
        try:
            _CondMarker(conditional_node_ids).visit(tree)
        except RecursionError:
            conditional_node_ids.clear()
            _log.warning(
                "[ImportBloat] AST 访问器递归超限，条件导入分类降级"
                "为 top_level: %s", rel_path)
        _collect_bloat_names(tree, conditional_node_ids, all_imports, rel_path)
        unused_by_file[rel_path] = {
            (issue["line"], issue["import_name"])
            for issue in check_UC01(
                tree, aligned_source_lines(source), rel_path)
        }
    return all_imports, unused_by_file
def _select_unused_imports(
        all_imports: list,
        unused_by_file: dict[str, set[tuple[int, str]]],
) -> list:
    unused = []
    for imp in all_imports:
        imp_name = imp["import"]
        unused_names = unused_by_file.get(imp["file"], set())
        if ((imp["line"], imp_name) not in unused_names
                or imp.get("category") in _EXEMPT_IMPORT_CATEGORIES):
            continue
        if imp_name in _TYPE_ANNOTATION_NAMES:
            imp["category"] = "type_annotation"
        unused.append(imp)
    return unused
def _build_bloat_report(all_imports: list, unused: list) -> dict:
    by_cat = {"top_level": 0, "conditional": 0, "type_annotation": 0}
    for u in unused:
        cat = u.get("category", "top_level")
        by_cat[cat] += 1
    total = len(all_imports)
    countable_total = sum(
        1 for imp in all_imports
        if imp.get("category", "top_level") not in _EXEMPT_IMPORT_CATEGORIES)
    unused_count = by_cat["top_level"]
    return {
        "total_imports": total,
        "unused_imports": unused_count,
        "bloat_ratio": round(unused_count / max(countable_total, 1), 3),
        "by_category": by_cat,
        "details": unused,
    }
def detect_import_bloat(skill_dir: str | None, ctx: Any = None) -> dict:
    if not skill_dir:
        return _build_bloat_report([], [])
    if (ctx is not None and hasattr(ctx, 'py_files')
            and hasattr(ctx, 'get_source') and hasattr(ctx, 'get_ast')):
        fpaths = list(ctx.py_files)
    else:
        fpaths = [os.path.join(skill_dir, rel)
                  for rel in collect_py_files(skill_dir)]
    fpaths = [fp for fp in fpaths
              if not is_test_file_path(safe_relpath(fp, skill_dir))]
    all_imports, unused_by_file = _scan_bloat_imports(skill_dir, fpaths, ctx)
    unused = _select_unused_imports(all_imports, unused_by_file)
    return _build_bloat_report(all_imports, unused)
@dataclass
class DepthError:
    file: str = ""
    line: int = 0
    import_stmt: str = ""
    current_depth: int = 0
    dots_used: int = 0
    expected_dots: int = 0
    fix: str = ""
    def to_dict(self) -> dict:
        return dict(self.__dict__)
@dataclass(frozen=True)
class _DepthScanContext:
    filepath: str
    rel_file: str
    depth: int
    expected_dots: int
    internal_modules: set[str]
    project_root: str
def count_leading_dots(target: str) -> int:
    dots = 0
    while dots < len(target) and target[dots] == '.':
        dots += 1
    return dots
def _iter_relative_imports(
        imports: Iterable[tuple[int, str, str]],
) -> Iterator[tuple[int, str, int, str]]:
    for line_no, stmt, target in imports:
        dots = count_leading_dots(target)
        if dots:
            yield line_no, stmt, dots, target[dots:]
def _depth_error(ctx: _DepthScanContext, line_no: int, stmt: str,
                 dots: int, fix: str) -> DepthError:
    return DepthError(
        file=ctx.rel_file,
        line=line_no,
        import_stmt=stmt,
        current_depth=ctx.depth,
        dots_used=dots,
        expected_dots=ctx.expected_dots,
        fix=fix,
    )
def _depth_ok(ctx: _DepthScanContext, first_part: str, dots: int) -> bool:
    return (dots <= ctx.expected_dots
            and dots_resolve_to_module(
                ctx.filepath, first_part, dots, ctx.depth))
def _from_dot_import_names(stmt: str, dots: int) -> list[str]:
    if not re.match(rf'from\s+\.{{{dots}}}(?:\s+|(?=import\b))', stmt):
        return []
    return _from_import_names(stmt)
def _validate_pure_dot_names(ctx: _DepthScanContext, line_no: int,
                             stmt: str, dots: int) -> list[DepthError]:
    errors: list[DepthError] = []
    names = _from_dot_import_names(stmt, dots)
    overdepth = dots > ctx.expected_dots
    if overdepth and not names:
        return [_depth_error(
            ctx, line_no, stmt, dots,
            _pure_dot_fix(ctx.expected_dots, '*'))]
    for name in names:
        internal = name in ctx.internal_modules
        if (not overdepth
                and (not internal or dots == ctx.expected_dots
                     or _depth_ok(ctx, name, dots))):
            continue
        suggested = (_suggested_dots(ctx, name) if internal
                     else ctx.expected_dots)
        errors.append(_depth_error(
            ctx, line_no, stmt, dots,
            _pure_dot_fix(suggested, name)))
    return errors
def _suggested_dots(ctx: _DepthScanContext, name: str) -> int:
    dots = relative_dots_for_module(
        ctx.filepath, name, ctx.depth, project_root=ctx.project_root)
    if dots_resolve_to_module(ctx.filepath, name, dots, ctx.depth):
        return dots
    return ctx.expected_dots
def _pure_dot_fix(expected_dots: int, name: str) -> str:
    if not expected_dots:
        return '' if name == '*' else f'import {name}'
    return f'from {"." * expected_dots} import {name}'
def _validate_named_target(ctx: _DepthScanContext, line_no: int, stmt: str,
                           dots: int, remainder: str) -> DepthError | None:
    first_part = first_segment(remainder)
    internal = first_part in ctx.internal_modules
    overdepth = dots > ctx.expected_dots
    if not internal and not overdepth:
        return None
    if _depth_ok(ctx, first_part, dots):
        return None
    suggested = (_suggested_dots(ctx, first_part) if internal
                 else ctx.expected_dots)
    return _depth_error(
        ctx, line_no, stmt, dots,
        _named_import_fix(suggested, remainder))
def _named_import_fix(expected_dots: int, remainder: str) -> str:
    if not expected_dots:
        return f'from {remainder} import ...'
    return f'from {"." * expected_dots}{remainder} import ...'
def detect_depth_errors(all_imports: dict, internal_modules: set[str],
                        root: str) -> list[DepthError]:
    results: list[DepthError] = []
    for filepath, imports in all_imports.items():
        rel_file = os.path.relpath(filepath, root)
        depth = path_depth(filepath, root)
        ctx = _DepthScanContext(
            filepath=filepath,
            rel_file=rel_file,
            depth=depth,
            expected_dots=enclosing_package_dots(filepath, root),
            internal_modules=internal_modules,
            project_root=root,
        )
        for line_no, stmt, dots, remainder in _iter_relative_imports(imports):
            if remainder:
                error = _validate_named_target(
                    ctx, line_no, stmt, dots, remainder)
                if error:
                    results.append(error)
            else:
                results.extend(
                    _validate_pure_dot_names(ctx, line_no, stmt, dots))
    return results
def check_GF18(filepath: str = _DEFAULT_FILEPATH,
               context: ImportScanContext | None = None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    if not filepath:
        return []
    target = os.path.abspath(filepath)
    ctx = _context_for(target, context)
    project_root = ctx.project_root
    return [
        {
            "rule_id": "GF-18",
            "severity": "P1",
            "file": os.path.normpath(os.path.join(project_root, item.file)),
            "line": item.line,
            "message": f"导入深度误算: {item.import_stmt}",
            "category": "import_safety",
        }
        for item in detect_depth_errors(
            collect_all_imports([target]),
            set(ctx.internal_modules), project_root)
    ]
_HUB_THRESHOLD_DEFAULT = 50
_HUB_RISK_HIGH_COUNT = 100
@dataclass
class HubModule:
    module_path: str = ""
    import_count: int = 0
    relative_imports: list[str] = field(default_factory=list)
    risk: str = ""
    def to_dict(self) -> dict:
        return dict(self.__dict__)
def detect_hub_modules(all_imports: dict, root: str,
                       hub_threshold: int = _HUB_THRESHOLD_DEFAULT
                       ) -> list[HubModule]:
    root_base = os.path.basename(os.path.normpath(root))
    root_prefixed = _is_package_dir(root)
    import_files = _count_hub_references(
        all_imports, root, root_base, root_prefixed=root_prefixed)
    results = []
    for target, files in import_files.items():
        record = _hub_module_record(target, files, hub_threshold,
                                    root, root_base)
        if record is not None:
            results.append(record)
    return results
def _hub_statement_targets(stmt: str, target: str) -> tuple[str, ...]:
    names = _from_import_names(stmt)
    dots = count_leading_dots(target)
    if dots and not target[dots:]:
        return tuple(target + name for name in names) or (target,)
    if not names:
        return (target,)
    separator = "" if target.endswith(".") else "."
    return (target, *(f"{target}{separator}{name}" for name in names))
def _count_hub_references(all_imports: dict, root: str, root_base: str,
                          *, root_prefixed: bool) -> dict[str, set[str]]:
    import_files: dict[str, set[str]] = defaultdict(set)
    for filepath, imports in all_imports.items():
        for _line_no, _stmt, target in imports:
            for expanded in _hub_statement_targets(_stmt, target):
                clean = _normalize_hub_key(
                    filepath, expanded, root, root_base,
                    root_prefixed=root_prefixed)
                if clean:
                    import_files[clean].add(filepath)
    return import_files
def _hub_module_record(target: str, files: set[str], hub_threshold: int,
                       root: str, root_base: str) -> HubModule | None:
    count = len(files)
    if count < hub_threshold or '.' not in target:
        return None
    relative_imports = _first_relative_imports(
        _hub_candidate_paths(target, root, root_base))
    if not relative_imports:
        return None
    return HubModule(
        module_path=target,
        import_count=count,
        relative_imports=relative_imports,
        risk="HIGH" if count >= _HUB_RISK_HIGH_COUNT else "MEDIUM"
    )
def _hub_candidate_paths(target: str, root: str,
                         root_base: str) -> list[str]:
    parts = target.split('.')
    part_seqs = [parts]
    if parts[0] == root_base:
        part_seqs.append(parts[1:])
    candidate_roots = [root, *source_import_roots(root)]
    return [
        path
        for base in candidate_roots
        for seq in part_seqs
        for path in (os.path.join(base, *seq) + '.py',
                     os.path.join(base, *seq, '__init__.py'))
    ]
def _first_relative_imports(paths: list[str]) -> list[str]:
    for path in paths:
        if not os.path.exists(path):
            continue
        relative_imports = _read_relative_imports(path)
        if relative_imports:
            return relative_imports
    return []
def _read_relative_imports(path: str) -> list[str]:
    source, _fingerprint = read_source_with_fingerprint(path)
    if source is None:
        return []
    source_lines = list(_source_lines(source))
    relative_imports: list[str] = []
    reported_lines: set[int] = set()
    for _fp, lineno, _stmt, targets in _logical_import_lines(
            path, source, "GF-17"):
        if (not any(target.startswith('.') for target in targets)
                or lineno in reported_lines):
            continue
        reported_lines.add(lineno)
        relative_imports.append(source_lines[lineno - 1].strip())
    return relative_imports
def _normalize_hub_key(filepath: str, target: str, root: str,
                       root_base: str, *, root_prefixed: bool) -> str:
    if not target.startswith('.'):
        return target
    layout_key = _normalize_layout_hub_key(filepath, target, root)
    if layout_key:
        return layout_key
    fallback = target.lstrip('.')
    dots = count_leading_dots(target)
    actual = target[dots:]
    dir_parts = _relative_dir_parts(filepath, root)
    if dir_parts is None:
        return fallback
    up = dots - 1
    if up > len(dir_parts):
        return fallback
    if up:
        dir_parts = dir_parts[:len(dir_parts) - up]
    key_parts = _hub_key_parts(root_prefixed, root_base, dir_parts, actual)
    if key_parts is None:
        return fallback
    return '.'.join(p for p in key_parts if p)
def _normalize_layout_hub_key(filepath: str, target: str,
                              root: str) -> str | None:
    if not target.startswith('.'):
        return None
    for layout_root in source_import_roots(root):
        dir_parts = _relative_dir_parts(filepath, layout_root)
        if dir_parts is None:
            continue
        dots = count_leading_dots(target)
        up = dots - 1
        if up > len(dir_parts):
            continue
        trimmed = dir_parts[:len(dir_parts) - up] if up else dir_parts
        actual = target[dots:]
        return '.'.join([*trimmed, actual] if actual else trimmed)
    return None
def _relative_dir_parts(filepath: str, root: str) -> list[str] | None:
    try:
        rel = os.path.relpath(filepath, root)
    except ValueError as _e:
        log_swallowed(
            __name__, _e,
            context=f'_relative_dir_parts:{type(_e).__name__}')
        return None
    if rel.startswith('..'):
        return None
    return rel.replace('\\', '/').split('/')[:-1]
def _hub_key_parts(root_prefixed: bool, root_base: str,
                   dir_parts: list[str], actual: str) -> list[str] | None:
    tail = [actual] if actual else []
    if root_prefixed:
        return [root_base] + dir_parts + tail
    if not dir_parts:
        return None
    return dir_parts + tail

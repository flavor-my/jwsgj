from __future__ import annotations

import ast
import builtins
import io
import keyword
import logging
import os
import re
import symtable
import tokenize
from collections import Counter, defaultdict, deque
from collections.abc import Callable, Iterable, Iterator, Mapping
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Self

from jwsgj.diag_module_surface import (
    GENERIC_PROJECT_PRUNE_DIRS,
    iter_module_level_nodes,
    iter_target_py_files,
    package_roots_for,
    prune_target_dirs,
)
from jwsgj.diag_shared_ast_nodes import (
    assign_targets_value,
    collect_annotation_names,
    is_type_checking_guard,
    iter_module_level_stmts,
    iter_unpack_target_names,
    resolve_import_binding,
    typing_guard_aliases,
    typing_type_checking_names,
)
from jwsgj.diag_shared_ast_surface import (
    collect_module_exports_ordered,
    is_all_target,
    module_export_names,
)
from jwsgj.diag_shared_ast_views import (
    collect_lexical_scope_table,
    parent_map,
    scope_shadows_import,
)
from jwsgj.diag_shared_source_core import (
    byte_col_to_char_col,
    parse_cached,
    parse_py_file,
    read_source,
    read_source_with_fingerprint,
)
from jwsgj.diag_shared_source_scan import (
    string_token_row_spans,
)
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    detect_cycles,
    is_test_file_path,
    relative_module_base,
    resolve_internal_dependency,
    resolve_scan_root,
)
from jwsgj.skill_profile import detect_layout

__all__ = [
    'BUILTIN_NAMES',
    'DESIGN_EXPECTED_MARKER',
    'ENTRY_POINT_PATTERNS',
    'EXEMPT_DIRS',
    'ArchitectureCheckStage',
    'CollectionResult',
    'ConsumerReport',
    'ImportBinding',
    'ModuleReferenceCollector',
    'ZeroConsumerChecker',
    'build_import_graph',
    'collect_lazy_registered_names',
    'collect_referenced_names',
    'collect_test_symbol_consumers',
    'detect_import_cycles',
    'export_assignment_targets',
    'export_table_pairs',
    'extract_module_state_names',
    'get_module_consumers',
    'import_binding_name',
    'is_dotted_module_name',
    'is_export_surface_name',
    'iter_import_bindings',
    'iter_import_stmts',
    'iter_module_assigns',
    'loading_chain_diag',
    'module_import_stmts',
    'normalize_module_name',
    'offset_in_string_literal',
    'read_import_names_text',
    'split_import_names',
    'unused_import_bindings',
    'zero_consumer_summary',
]
_log = logging.getLogger(__name__)
@dataclass(frozen=True)
class ImportBinding:
    imported: str
    bound: str
    lineno: int
    stmt: ast.stmt | None = None
    alias_lineno: int = 0
def import_binding_name(node: ast.Import | ast.ImportFrom,
                        alias: ast.alias) -> str | None:
    if isinstance(node, ast.Import):
        return alias.asname or alias.name.split(".")[0]
    if alias.name == "*":
        return None
    return alias.asname or alias.name
_IMPORT_STMT_RE = re.compile(
    r"(?:^|;)[ \t]*(?:from\s+(?P<module>[.\w]+)\s+import|"
    r"import\s+(?P<plain>[^;\n#]+))",
    re.MULTILINE,
)
def _offset_in_line_comment(content: str, offset: int) -> bool:
    line_start = content.rfind("\n", 0, offset) + 1
    return "#" in content[line_start:offset]
def iter_import_stmts(content: str) -> Iterator[re.Match]:
    masked = None
    masked_ready = False
    for match in _IMPORT_STMT_RE.finditer(content):
        if not masked_ready:
            masked = _non_code_token_mask(content)
            masked_ready = True
        if masked is not None:
            if match.start() < len(masked) and masked[match.start()] == " ":
                continue
        elif (match.group(0).startswith(";")
              and _offset_in_line_comment(content, match.start())):
            continue
        yield match
def _import_match_indented(content: str, match) -> bool:
    line_start = content.rfind("\n", 0, match.start()) + 1
    return content[line_start:line_start + 1] in (" ", "\t")
def _strip_line_comments(text: str) -> str:
    return "\n".join(line.split("#", 1)[0] for line in text.split("\n"))
def read_import_names_text(content: str,
                           span: tuple[int, int]) -> tuple[str, int, int]:
    start, end = span
    names_text = _strip_line_comments(content[start:end])
    stmt_line_end = content.find("\n", end)
    if stmt_line_end == -1:
        stmt_line_end = len(content)
    while True:
        continued = names_text.rstrip().endswith("\\")
        if not continued and names_text.count("(") <= names_text.count(")"):
            return names_text, end, stmt_line_end
        if continued:
            names_text = names_text.rstrip()[:-1]
        nl = content.find("\n", end)
        if nl == -1:
            return names_text, end, stmt_line_end
        nxt = content.find("\n", nl + 1)
        if nxt == -1:
            nxt = len(content)
        _row_text = _strip_line_comments(content[nl + 1:nxt])
        _semi = _row_text.find(";")
        if _semi != -1:
            names_text += " " + _row_text[:_semi]
            return names_text, nl + 1 + _semi, nxt
        names_text += " " + _row_text
        end = nxt
        stmt_line_end = nxt
def split_import_names(names_text: str) -> list[str]:
    cleaned = names_text.replace("(", " ").replace(")", " ")
    return [seg.strip() for seg in cleaned.split(",") if seg.strip()]
_ALIAS_TEXT_RE = re.compile(r"\s+as\s+")
def _split_alias_text(alias_text: str) -> tuple[str, str | None]:
    parts = _ALIAS_TEXT_RE.split(alias_text.strip(), maxsplit=1)
    imported = parts[0].strip()
    return imported, parts[1].strip() if len(parts) == 2 else None
def is_dotted_module_name(text: str) -> bool:
    return bool(text) and all(part.isidentifier() for part in text.split("."))
def offset_in_string_literal(content: str, offset: int, row_spans=None) -> bool:
    if row_spans is None or offset < 0:
        return False
    spans = row_spans.get(content.count("\n", 0, offset) + 1)
    if not spans:
        return False
    col = offset - (content.rfind("\n", 0, offset) + 1)
    return any(s <= col < e for s, e in spans)
_LAZY_IMPORT_SCOPE_NODES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
def _iter_module_import_nodes(tree: ast.Module, *,
                               skip_type_checking: bool = False
                               ) -> list[ast.stmt]:
    out: list[ast.stmt] = []
    typing_aliases = typing_guard_aliases(tree) if skip_type_checking else None
    type_checking_names = (typing_type_checking_names(tree)
                           if skip_type_checking else None)
    def _visit(node: ast.AST) -> None:
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            out.append(node)
            return
        if isinstance(node, _LAZY_IMPORT_SCOPE_NODES):
            return
        if (skip_type_checking and isinstance(node, ast.If)
                and is_type_checking_guard(
                    node.test, typing_aliases, type_checking_names)):
            for child in node.orelse:
                _visit(child)
            return
        _collect(node)
    def _collect(node: ast.AST) -> None:
        for child in ast.iter_child_nodes(node):
            _visit(child)
    _collect(tree)
    return out
def module_import_stmts(content: str, filename: str, *,
                         skip_type_checking: bool = False
                         ) -> list[ast.stmt] | None:
    try:
        tree = parse_cached(content, filename)
    except PARSE_DEGRADE_EXC as _e:
        log_swallowed(
            __name__, _e,
            context=f'module_import_stmts:{type(_e).__name__}')
        return None
    return _iter_module_import_nodes(
        tree, skip_type_checking=skip_type_checking)
def _literal_name_set(elements) -> set[str]:
    return {elt.value for elt in elements
            if isinstance(elt, ast.Constant) and isinstance(elt.value, str)}
def _export_list_names(value: ast.expr) -> set[str] | None:
    if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        return _literal_name_set(value.elts)
    if isinstance(value, ast.BinOp) and isinstance(value.op,
                                                  (ast.Add, ast.BitOr)):
        return _concat_export_names(value) or None
    return None
def _concat_export_names(value: ast.BinOp) -> set[str]:
    names: set[str] = set()
    for side in (value.left, value.right):
        if isinstance(side, ast.Name) and side.id == "__all__":
            continue
        sub = _export_list_names(side)
        if sub:
            names.update(sub)
    return names
def export_assignment_targets(node: ast.stmt) -> list[ast.Name]:
    if isinstance(node, ast.Assign):
        return [t for t in node.targets if isinstance(t, ast.Name)]
    if isinstance(node, ast.AugAssign):
        _is_merge_op = isinstance(node.op, (ast.Add, ast.BitOr))
        return _name_target(node.target) if _is_merge_op else []
    if isinstance(node, ast.AnnAssign):
        return _name_target(node.target)
    return []
def _name_target(target) -> list[ast.Name]:
    return [target] if isinstance(target, ast.Name) else []
def export_table_pairs(node: ast.stmt) -> list[tuple[str, set[str]]]:
    pairs: list[tuple[str, set[str]]] = []
    for target in export_assignment_targets(node):
        pair = _export_pair_for_target(node.value, target)
        if pair is not None:
            pairs.append(pair)
    return pairs
_EXPORT_SURFACE_TOKENS = frozenset({
    "lazy", "exports", "export", "imports", "registry",
    "surface", "anchor", "anchors", "facade", "reimport", "reimports",
})
def _name_segments(name: str) -> tuple[str, ...]:
    spaced = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", "_", str(name or ""))
    return tuple(part for part in re.split(r"[^0-9a-z]+", spaced.lower()) if part)
def is_export_surface_name(name: str) -> bool:
    return any(seg in _EXPORT_SURFACE_TOKENS for seg in _name_segments(name))
def _is_export_surface_table(value: ast.expr) -> bool:
    if not isinstance(value, ast.Dict) or not value.keys:
        return False
    return all(isinstance(key, ast.Constant) and isinstance(key.value, str)
               and is_dotted_module_name(key.value) for key in value.keys)
def _export_pair_for_target(value, target: ast.Name):
    if target.id == "__all__":
        names = _export_list_names(value)
        return ("__all__", names) if names else None
    if is_export_surface_name(target.id) and _is_export_surface_table(value):
        return (target.id, _literal_name_set(value.keys))
    return None
def _iter_import_stmts(stmts: Iterable[ast.stmt]) -> Iterator[ast.stmt]:
    found = [node for stmt in stmts for node in walk_nodes(stmt)
             if isinstance(node, (ast.Import, ast.ImportFrom))]
    yield from sorted(found, key=lambda node: (node.lineno, node.col_offset))
def _import_channel_exempt(node: ast.ImportFrom) -> bool:
    return node.module == "__future__"
def iter_import_bindings(
        source: ast.Module | Iterable[ast.stmt]) -> list[ImportBinding]:
    stmts = source.body if isinstance(source, ast.Module) else source
    bindings: list[ImportBinding] = []
    for stmt in _iter_import_stmts(stmts):
        if isinstance(stmt, ast.ImportFrom):
            if _import_channel_exempt(stmt):
                continue
        elif not isinstance(stmt, ast.Import):
            continue
        for alias in stmt.names:
            bound = import_binding_name(stmt, alias)
            if bound is not None:
                alias_line = getattr(alias, "lineno", 0) or stmt.lineno
                bindings.append(ImportBinding(
                    alias.name, bound, stmt.lineno, stmt, alias_line))
    return bindings
def unused_import_bindings(
        bindings: Iterable[ImportBinding],
        is_used: Callable[[ImportBinding], bool],
        is_exempt: Callable[[ImportBinding], bool] | None = None,
) -> list[ImportBinding]:
    return [binding for binding in bindings
            if not is_used(binding)
            and not (is_exempt is not None and is_exempt(binding))]
def iter_module_assigns(
    tree: ast.AST,
) -> Iterator[tuple[str, int, int, ast.expr]]:
    for node in iter_module_level_stmts(tree):
        end_ln = getattr(node, "end_lineno", node.lineno)
        if isinstance(node, ast.Assign):
            for target in node.targets:
                for name in iter_unpack_target_names(target):
                    yield name, node.lineno, end_ln, node.value
        elif (
            isinstance(node, ast.AnnAssign)
            and node.value is not None
            and isinstance(node.target, ast.Name)
        ):
            yield node.target.id, node.lineno, end_ln, node.value
def extract_module_state_names(tree: ast.AST) -> set[str]:
    return {name for name, _s, _e, _v in iter_module_assigns(tree)}
BUILTIN_NAMES = (frozenset(dir(builtins))
                 - frozenset(keyword.kwlist)) | frozenset({
    'self', 'cls', 'args', 'kwargs',
})
def collect_referenced_names(node: ast.AST) -> set[str]:
    names: set[str] = set()
    builtins = BUILTIN_NAMES
    for child in walk_nodes(node):
        if isinstance(child, ast.Name) and child.id not in builtins:
            names.add(child.id)
        elif isinstance(child, ast.Attribute) and child.attr not in builtins:
            names.add(child.attr)
    return names
def normalize_module_name(rel_path: str) -> str:
    name = rel_path.replace("\\", "/").replace("/", ".")
    if name.lower().endswith(".py"):
        name = name[:-len(".py")]
    if name.lower().endswith(".__init__"):
        return name[: -len(".__init__")]
    if name.lower() == "__init__":
        return ""
    return name
def _add_import_edge(candidate: str, mod_name: str, module_names: set,
                     import_edges: dict[str, set]) -> bool:
    if candidate not in module_names or candidate == mod_name:
        return False
    import_edges[mod_name].add(candidate)
    return True
def _module_key(py_file: Path, base: str) -> str:
    path = str(py_file)
    try:
        rel = os.path.relpath(path, base) if base else os.path.basename(path)
    except ValueError as exc:
        log_swallowed(__name__, exc, context="_module_key:ValueError")
        rel = os.path.basename(path)
    return normalize_module_name(rel)
def _project_package_key_prefix(skill_dir: str) -> str:
    if not str(skill_dir or "").strip():
        return ""
    layout = detect_layout(str(skill_dir))
    if not layout.is_package:
        return ""
    try:
        rel = os.path.relpath(layout.package_root, str(skill_dir))
    except ValueError as exc:
        log_swallowed(
            __name__, exc, context="_project_package_key_prefix:ValueError")
        return ""
    if rel in ("", ".") or rel == ".." or rel.startswith(f"..{os.sep}"):
        return ""
    return normalize_module_name(rel)
def _physical_package_key(dotted_name: str, root_pkg: str,
                          key_prefix: str) -> str:
    if not key_prefix or not root_pkg:
        return ""
    if dotted_name == root_pkg:
        return key_prefix
    prefix = f"{root_pkg}."
    if not dotted_name.startswith(prefix):
        return ""
    return f"{key_prefix}.{dotted_name[len(prefix):]}"
def _top_level_defs(tree: ast.Module) -> tuple[list[str], list[str]]:
    funcs: list[str] = []
    classes: list[str] = []
    for node in iter_module_level_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            funcs.append(node.name)
        elif isinstance(node, ast.ClassDef):
            classes.append(node.name)
    return funcs, classes
class ArchitectureCheckStage:
    def __init__(self, name: str = "architecture_check",
                 skill_dir: str | None = None) -> None:
        self.name = name
        self.description = "Check module separation, dependency direction, SRP"
        self.skill_dir = skill_dir
    def run(self, context: dict[str, Any]) -> dict[str, Any]:
        issues: list = []
        warnings: list = []
        skill_dir = self.skill_dir or context.get("skill_dir", "")
        target_declared = self.skill_dir is not None or "skill_dir" in context
        if not skill_dir:
            if target_declared:
                issues.append("Architecture check: skill_dir 必须为非空目录路径")
            return {"passed": not issues, "issues": issues,
                    "warnings": warnings, "stage": self.name}
        if not os.path.isdir(skill_dir):
            issues.append(
                f"Architecture check: skill_dir 不存在或不是目录: {skill_dir}")
            return {"passed": False, "issues": issues, "warnings": warnings,
                    "stage": self.name}
        try:
            py_files = list(
                iter_target_py_files(skill_dir, include_tests=False))
            parse_cache: dict = {}
            self._check_module_separation(py_files, warnings, parse_cache)
            _, import_edges = self._detect_import_edges(
                py_files, parse_cache, skill_dir)
            self._report_cycles(import_edges, issues)
            self._check_naming_convention(py_files, issues)
            self._check_function_srp(py_files, warnings, parse_cache)
            warnings.extend(_domain_reciprocity_warnings(import_edges))
        except Exception as exc:  # noqa: BLE001
            _log.debug("架构检查异常降级为 warning: %s", exc)
            warnings.append(f"Architecture check error (skipped): {exc}")
            issues.append(f"Architecture check error (blocked): {exc}")
        return {
            "passed": not issues,
            "issues": issues,
            "warnings": warnings,
            "stage": self.name,
        }
    @staticmethod
    def _report_cycles(import_edges: dict[str, set], issues: list) -> None:
        graph = {node: sorted(import_edges[node])
                 for node in sorted(import_edges)}
        for cycle in detect_cycles(graph):
            nodes = [module or '__init__' for module in cycle]
            if len(nodes) == 1:
                issues.append(
                    f"Circular dependency: {nodes[0]} -> {nodes[0]}")
            elif len(nodes) == 2:
                issues.append(
                    f"Circular dependency: {nodes[0]} <-> {nodes[1]}")
            else:
                issues.append(
                    f"Circular dependency: {' -> '.join(nodes + [nodes[0]])}")
    @staticmethod
    def _check_naming_convention(py_files: list, issues: list) -> None:
        for py_file in py_files:
            if py_file.stem == "__init__":
                continue
            if (not py_file.stem.isidentifier()
                    or py_file.stem != py_file.stem.lower()
                    or keyword.iskeyword(py_file.stem)):
                issues.append(
                    f"Naming: {py_file.name} should use snake_case"
                )
    @staticmethod
    def _read_and_parse(py_file: Path, _cache: dict) -> ast.Module | None:
        if py_file in _cache:
            return _cache[py_file]
        _source, tree = parse_py_file(str(py_file), quiet=True)
        _cache[py_file] = tree
        return tree
    def _check_module_separation(self, py_files: list, warnings: list,
                                 _cache: dict) -> None:
        for py_file in py_files:
            fname = py_file.name
            if fname == "__init__.py":
                continue
            tree = self._read_and_parse(py_file, _cache)
            if tree is None:
                continue
            top_funcs, top_classes = _top_level_defs(tree)
            total_defs = len(top_funcs) + len(top_classes)
            if total_defs > 20:
                warnings.append(
                    f"Module separation: {fname} has {total_defs} top-level definitions"
                )
    def _detect_import_edges(self, py_files: list, _cache: dict,
                             base_dir: str = "") -> tuple[set, dict[str, set]]:
        base = (base_dir or self.skill_dir or
                (os.path.dirname(str(py_files[0])) if py_files else ""))
        root_pkg = _root_package_name(base)
        key_prefix = _project_package_key_prefix(base)
        keys = {f: _module_key(f, base) for f in py_files}
        module_names = set(keys.values())
        import_edges: dict[str, set] = {n: set() for n in module_names}
        for py_file in py_files:
            tree = self._read_and_parse(py_file, _cache)
            if tree is None:
                continue
            is_init = py_file.name == "__init__.py"
            for node in _iter_module_import_nodes(
                    tree, skip_type_checking=True):
                self._collect_edge_from_node(
                    node, keys[py_file], is_init, module_names, import_edges,
                    root_pkg, key_prefix)
        return module_names, import_edges
    @staticmethod
    def _relative_base(key: str, is_init: bool, level: int) -> str | None:
        parts = [p for p in (key if is_init else
                             key.rpartition('.')[0]).split('.') if p]
        if level > len(parts) + 1:
            return None
        return '.'.join(parts[:len(parts) - level + 1])
    def _module_candidates(self, dotted: str, root_pkg: str,
                           key_prefix: str = "") -> list[str]:
        cleaned = (dotted or '').strip('.')
        if not cleaned:
            return []
        parts = cleaned.split('.')
        head, _, rest = cleaned.partition('.')
        physical = _physical_package_key(cleaned, root_pkg, key_prefix)
        if physical:
            physical_parts = physical.split('.')
            root_depth = len(key_prefix.split('.'))
            cands = [physical]
            cands.extend(
                '.'.join(physical_parts[:i])
                for i in range(root_depth, len(physical_parts)))
            return list(dict.fromkeys(cands))
        cands = [cleaned]
        if root_pkg and head == root_pkg:
            cands.append(rest)
            if rest:
                relative_parts = rest.split('.')
                cands.extend(
                    '.'.join(relative_parts[:i])
                    for i in range(1, len(relative_parts)))
                cands.append('')
        cands.extend('.'.join(parts[:i]) for i in range(1, len(parts)))
        return list(dict.fromkeys(cands))
    def _add_resolved_edge(self, candidates, mod_name, module_names,
                           import_edges) -> bool:
        hit = False
        for candidate in candidates:
            hit = _add_import_edge(
                candidate, mod_name, module_names, import_edges) or hit
        return hit
    def _collect_edge_from_node(self, node, mod_name, is_init, module_names,
                                import_edges, root_pkg: str,
                                key_prefix: str = "") -> None:
        if isinstance(node, ast.Import):
            for alias in node.names:
                cands = self._same_package_candidates(
                    alias.name, root_pkg, key_prefix, mod_name)
                if cands is None:
                    cands = self._module_candidates(
                        alias.name, root_pkg, key_prefix)
                self._add_resolved_edge(cands, mod_name,
                                        module_names, import_edges)
            return
        if not isinstance(node, ast.ImportFrom):
            return
        base = self._relative_base(mod_name, is_init, node.level) \
            if node.level else ''
        if base is None:
            return
        target = (f"{base}.{node.module}" if base and node.module
                  else node.module or base)
        aliases = [a.name for a in node.names if a.name != '*']
        if node.level:
            if node.module:
                # `from .x import y` 只依赖子模块（含中间子包），不记本包
                # __init__ 边：标准包布局由 __init__ 再导出子模块，记本包边
                # 会让任何包都成环（与 _LoadingGraphBuilder.record_relative
                # 同口径）。
                self._add_resolved_edge(
                    [cand for cand in self._module_candidates(
                        target, root_pkg, key_prefix) if cand != base],
                    mod_name, module_names, import_edges)
                return
            # `from . import X`：X 是子模块/子包时只记 X；X 既非子模块也非
            # 子包（__init__ 导出符号）或为 ``*`` 时才记本包 __init__ 边。
            hit_all = bool(aliases)
            for alias in aliases:
                dotted = f"{base}.{alias}" if base else alias
                hit_all = self._add_resolved_edge(
                    self._module_candidates(
                        dotted, root_pkg, key_prefix)[:1], mod_name,
                    module_names, import_edges) and hit_all
            if not hit_all:
                _add_import_edge(base, mod_name, module_names, import_edges)
                self._add_resolved_edge(
                    self._module_candidates(target, root_pkg, key_prefix),
                    mod_name, module_names, import_edges)
            return
        if (self._is_same_package_import(node.module, root_pkg)
                and self._in_package(mod_name, key_prefix)):
            # 同包绝对导入（``from 本包.x import y`` / ``import 本包.x``）不记本包
            # __init__ 边，与 _LoadingGraphBuilder.record_absolute 同口径；
            # 仅 ``from 本包 import X`` 中 X 既非子模块也非子包时才记本包边。
            # 包外脚本（scripts 布局）导入本包仍记包初始化边。
            if node.module == root_pkg:
                hit_all = bool(aliases)
                for alias in aliases:
                    hit_all = self._add_resolved_edge(
                        self._same_package_candidates(
                            f"{target}.{alias}", root_pkg, key_prefix,
                            mod_name),
                        mod_name, module_names, import_edges) and hit_all
                if not hit_all:
                    _add_import_edge(key_prefix, mod_name,
                                     module_names, import_edges)
                return
            self._add_resolved_edge(
                self._same_package_candidates(target, root_pkg, key_prefix,
                                              mod_name),
                mod_name, module_names, import_edges)
            for alias in aliases:
                self._add_resolved_edge(
                    self._same_package_candidates(
                        f"{target}.{alias}", root_pkg, key_prefix,
                        mod_name),
                    mod_name, module_names, import_edges)
            return
        if not aliases:
            self._add_resolved_edge(
                self._module_candidates(target, root_pkg, key_prefix), mod_name,
                module_names, import_edges)
            return
        for alias in aliases:
            dotted = f"{target}.{alias}" if target else alias
            self._add_resolved_edge(
                self._module_candidates(
                    dotted, root_pkg, key_prefix)[:2], mod_name,
                module_names, import_edges)
            self._add_resolved_edge(
                self._module_candidates(target, root_pkg, key_prefix), mod_name,
                module_names, import_edges)
    @staticmethod
    def _is_same_package_import(module: str | None, root_pkg: str) -> bool:
        return (bool(module) and bool(root_pkg)
                and module.split(".")[0] == root_pkg)
    @staticmethod
    def _in_package(mod_name: str, key_prefix: str) -> bool:
        return (not key_prefix or mod_name == key_prefix
                or mod_name.startswith(key_prefix + "."))
    def _same_package_candidates(self, dotted: str, root_pkg: str,
                                 key_prefix: str, mod_name: str,
                                 ) -> list[str] | None:
        if not self._is_same_package_import(dotted, root_pkg):
            return None
        if not self._in_package(mod_name, key_prefix):
            return None
        if dotted == root_pkg:
            return None
        return [cand for cand in self._module_candidates(
            dotted, root_pkg, key_prefix) if cand != key_prefix]
    def _check_function_srp(self, py_files: list, warnings: list,
                             _cache: dict) -> None:
        for py_file in py_files:
            tree = self._read_and_parse(py_file, _cache)
            if tree is None:
                continue
            top_funcs, _top_classes = _top_level_defs(tree)
            pub_funcs = [name for name in top_funcs
                         if not name.startswith("_")]
            if len(pub_funcs) <= 5:
                continue
            prefixes = {fn_name.split("_")[0] for fn_name in pub_funcs
                        if "_" in fn_name}
            if len(prefixes) <= 3:
                continue
            warnings.append(
                f"SRP: {py_file.name} has {len(prefixes)} function prefixes, "
                f"may mix multiple responsibilities"
            )
_DOMAIN_ENTRY = ('__init__', '__main__')
def _infer_domain_prefixes(modules) -> tuple[str, ...]:
    counts = Counter()
    for module in modules:
        head, sep, _tail = str(module).partition('_')
        if sep and len(head) >= 2 and head.isalpha():
            counts[head + '_'] += 1
    return tuple(prefix for prefix, n in counts.items() if n >= 2)
def _domain_of(module: str, prefixes: tuple[str, ...]) -> str:
    if module in _DOMAIN_ENTRY:
        return ''
    for prefix in prefixes:
        if module.startswith(prefix):
            return prefix.rstrip('_')
    return module
def _domain_reciprocity_warnings(import_graph: dict) -> list:
    modules = set(import_graph)
    for deps in import_graph.values():
        modules.update(deps)
    prefixes = _infer_domain_prefixes(modules)
    counts = Counter()
    for src, deps in import_graph.items():
        left = _domain_of(src, prefixes)
        for dep in deps:
            right = _domain_of(dep, prefixes)
            if right and right != left:
                counts[(left, right)] += 1
    return [
        f"Domain mutual dependency: {a} <-> {b} ({n} forward / {counts[(b, a)]} backward edges)"
        for (a, b), n in sorted(counts.items())
        if a < b and counts.get((b, a))
    ]
def _warn_walk_error(exc: OSError) -> None:
    _log.warning("[ZCC] 目录遍历失败，零消费者结果不完整: %s", exc)
def _iter_lazy_surface_files(skill_dir: str):
    for file_path in iter_target_py_files(skill_dir, include_tests=False):
        yield str(file_path)
def _is_surface_table(value: ast.expr) -> bool:
    return (_is_export_surface_table(value)
            and any(isinstance(item, ast.Tuple) for item in value.values))
def _iter_lazy_table_items(value: ast.Dict):
    for key, item in zip(value.keys, value.values, strict=True):
        if (isinstance(key, ast.Constant) and isinstance(key.value, str)
                and isinstance(item, ast.Tuple)):
            yield key.value, item
def _iter_surface_tables(tree: ast.Module) -> Iterator[ast.Dict]:
    for node in iter_module_level_stmts(tree):
        pair = assign_targets_value(node)
        if pair is None:
            continue
        targets, value = pair
        if (len(targets) != 1
                or not isinstance(targets[0], ast.Name)
                or not is_export_surface_name(targets[0].id)
                or not _is_surface_table(value)):
            continue
        yield value
def _iter_surface_modules(tree: ast.Module) -> set[str]:
    modules: set[str] = set()
    for value in _iter_surface_tables(tree):
        modules.update(key for key, _item in _iter_lazy_table_items(value))
    return modules
def _lazy_symbols_from_tree(tree: ast.Module) -> set[str]:
    names: set[str] = set()
    for value in _iter_surface_tables(tree):
        for _key, item in _iter_lazy_table_items(value):
            for elt in item.elts:
                if isinstance(elt, ast.Constant) and isinstance(elt.value, str):
                    names.add(elt.value)
    return names
def collect_lazy_registered_names(skill_dir: str) -> set[str]:
    names: set[str] = set()
    for p in _iter_lazy_surface_files(skill_dir):
        source = read_source(p)
        if source is None:
            _log.warning("[Topology] 扫描失败,跳过 %s", p)
            continue
        try:
            tree = parse_cached(source)
        except PARSE_DEGRADE_EXC as e:
            _log.warning("lazy 登记表解析失败，lazy 豁免证据缺失"
                         "（死函数候选将失去消费锚点豁免）: %s: %s", p, e)
            continue
        names.update(_lazy_symbols_from_tree(tree))
    return names
def _fd_read_source(fpath: str) -> str | None:
    source = read_source(fpath)
    if source is None:
        _log.warning("[Topology] 扫描失败,跳过 %s", fpath)
    return source
_MERGED_WORD_RE = re.compile(r'(?<![A-Za-z0-9])merged(?![A-Za-z0-9])')
ENTRY_POINT_PATTERNS = frozenset({
    '__init__.py', '__main__.py', 'facade.py', '_version.py',
    '_version_meta.py', 'conftest.py', 'setup.py', '_all_exports.py',
})
EXEMPT_DIRS = frozenset(GENERIC_PROJECT_PRUNE_DIRS) | frozenset({
    '.rundata', '_versions', '.merged_backups', 'tests',
    '.pytest_cache', 'mutation', 'backups',
})
DESIGN_EXPECTED_MARKER = "[ZCC-EXPECTED]"
def _root_package_name(skill_dir: str) -> str:
    if not str(skill_dir or "").strip():
        return ''
    layout = detect_layout(str(skill_dir))
    if layout.is_package and layout.package_name.isidentifier():
        return layout.package_name
    name = os.path.basename(os.path.abspath(str(skill_dir)))
    return name if name.isidentifier() else ''
SHADOWED_KEY_MARK = "::shadowed::"
def _is_import_only(stmts: list[ast.stmt]) -> bool:
    return bool(stmts) and all(
        isinstance(n, (ast.Import, ast.ImportFrom)) for n in stmts)
def _is_static_all_value(value: ast.AST | None) -> bool:
    if isinstance(value, ast.Name):
        return value.id == "__all__"
    if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        return all(isinstance(elt, ast.Constant)
                   and isinstance(elt.value, str) for elt in value.elts)
    return (isinstance(value, ast.BinOp)
            and isinstance(value.op, (ast.Add, ast.BitOr))
            and _is_static_all_value(value.left)
            and _is_static_all_value(value.right))
def _is_static_all_decl(node: ast.AST) -> bool:
    value = getattr(node, "value", None)
    if not _is_static_all_value(value):
        return False
    if isinstance(node, ast.Assign):
        return any(is_all_target(t) for t in node.targets)
    if isinstance(node, ast.AnnAssign):
        return is_all_target(node.target)
    if isinstance(node, ast.AugAssign):
        return (is_all_target(node.target)
                and isinstance(node.op, (ast.Add, ast.BitOr)))
    return False
def _nontrivial_top_level_stmts(tree: ast.Module) -> list[ast.stmt]:
    non_trivial: list[ast.stmt] = []
    for node in ast.iter_child_nodes(tree):
        if (isinstance(node, ast.Expr)
                and isinstance(node.value, ast.Constant)
                and isinstance(node.value.value, str)):
            continue
        non_trivial.append(node)
    return non_trivial
_COMPAT_MARKER_RE = re.compile(
    r"兼容|\bcompat(?:ible|ibility)?\b|\bre[- ]?exports?\b",
    re.IGNORECASE,
)
def _has_compat_marker(source: str) -> bool:
    return _COMPAT_MARKER_RE.search(source) is not None
def _parse_source(source: str, context: str) -> ast.Module | None:
    try:
        return parse_cached(source)
    except PARSE_DEGRADE_EXC as e:
        _log.warning("[ZCC] %s 解析失败,降级跳过: %s", context, e)
        return None
_MAGIC_OR_POLYMORPHIC = frozenset({
    "__init__", "__new__", "__del__", "__str__", "__repr__", "__eq__",
    "__hash__", "__call__", "__getitem__", "__setitem__", "__len__",
    "__iter__", "__next__", "__contains__", "__enter__", "__exit__",
    "__getattr__", "__setattr__", "__post_init__",
    "to_dict", "to_json", "summary", "run", "execute",
    "scan", "build", "analyze", "check", "detect", "process",
    "register", "dispatch", "handle", "configure", "setup",
})
@dataclass
class CollectionResult:
    classes: list[str] = field(default_factory=list)
    functions: list[str] = field(default_factory=list)
    imports_out: list[str] = field(default_factory=list)
    from_import_entries: set[str] = field(default_factory=set)
    nodes: list[ast.AST] = field(default_factory=list)
    owners: list[int | None] = field(default_factory=list)
    def_names: list[str] = field(default_factory=list)
    top_defs: list[tuple[str, set[str]]] = field(default_factory=list)
    module_refs: set[str] = field(default_factory=set)
    call_refs: dict[str, float] = field(default_factory=dict)
class _ImportIndex(defaultdict[str, set[str]]):
    def __init__(self) -> None:
        super().__init__(set)
        self._symbol_consumers: dict[tuple[str, str], set[str]] = defaultdict(set)
    def add_symbol_consumer(
        self, source_file: str, symbol: str, consumer_file: str,
    ) -> None:
        self._symbol_consumers[(source_file, symbol)].add(consumer_file)
    def consumers_for(self, source_file: str, symbol: str) -> set[str]:
        return set(self._symbol_consumers.get((source_file, symbol), ()))
@dataclass(slots=True)
class _WalkBundle:
    nodes: list[ast.AST]
    owners: list[int | None]
    def_names: list[str]
    def_lines: list[int]
@dataclass
class _ImportEdges:
    module: list[str] = field(default_factory=list)
    bare: list[str] = field(default_factory=list)
    resolved_module: list[str] = field(default_factory=list)
    resolved: list[str] = field(default_factory=list)
    def add_bare(self: Self, path: str, module_level: bool) -> None:
        self.bare.append(path)
        if module_level:
            self.module.append(path)
    def add_resolved(self: Self, path: str, module_level: bool) -> None:
        self.resolved.append(path)
        if module_level:
            self.resolved_module.append(path)
    def as_dict(self: Self) -> dict[str, list[str]]:
        return {"module": self.module, "all": self.bare,
                "resolved_module": self.resolved_module,
                "resolved": self.resolved}
def _bind_import_aliases(node: ast.Import, bound: dict[str, str]) -> None:
    for alias in node.names:
        if alias.asname:
            bound[alias.asname] = alias.name
        else:
            head = alias.name.split(".")[0]
            bound[head] = head
def _bind_importfrom_aliases(
    node: ast.ImportFrom, base: str, bound: dict[str, str],
) -> None:
    for alias in node.names:
        if alias.name == "*":
            continue
        bound[alias.asname or alias.name] = (
            f"{base}.{alias.name}" if base else alias.name)
def _resolve_module_path(root: Path, module_name: str) -> str | None:
    parts = [part for part in module_name.replace("/", ".").split(".")
             if part]
    if not parts:
        init_py = root / "__init__.py"
        return str(init_py) if init_py.is_file() else None
    current = root
    for part in parts[:-1]:
        package_dir = current / part
        if (package_dir / "__init__.py").is_file():
            current = package_dir
            continue
        if (current / f"{part}.py").is_file():
            return None
        if not package_dir.is_dir():
            return None
        current = package_dir
    leaf = parts[-1]
    init_py = current / leaf / "__init__.py"
    if init_py.is_file():
        return str(init_py)
    module_py = current / f"{leaf}.py"
    return str(module_py) if module_py.is_file() else None
def _rel_name_entries(
    node: ast.ImportFrom, base_dir: Path,
) -> list[tuple[str, Path, bool]]:
    if node.module:
        alias_base = base_dir.joinpath(*node.module.split("."))
        module_is_multi = "." in node.module
        return (
            [(relative_module_base(node.module),
              base_dir, module_is_multi)]
            + [(a.name, alias_base, True) for a in node.names])
    return [("__init__", base_dir, False)] + [
        (a.name, base_dir, False) for a in node.names if a.name != "*"]
def _importfrom_alias_names(node: ast.ImportFrom) -> list[str] | None:
    """可判定的别名列表；星号导入或全为星号时返回 ``None``（无法收敛）。"""
    aliases = [alias.name for alias in node.names if alias.name != "*"]
    if not aliases or len(aliases) != len(node.names):
        return None
    return aliases
def _rel_aliases_all_submodules(
    collector: ModuleReferenceCollector, node: ast.ImportFrom,
    base_dir: Path,
) -> bool:
    aliases = _importfrom_alias_names(node)
    if aliases is None:
        return False
    return all(_resolve_dep_cached(collector, name, base_dir)
               for name in aliases)
def _is_own_package_initializer(target: str, filepath: Path) -> bool:
    """``target`` 是否为 ``filepath`` 自身（含祖先）包的 ``__init__.py``。"""
    if os.path.basename(target) != "__init__.py":
        return False
    package_dir = os.path.normcase(os.path.dirname(os.path.abspath(target)))
    current = os.path.normcase(
        os.path.dirname(os.path.abspath(str(filepath))))
    while True:
        if current == package_dir:
            return True
        parent = os.path.dirname(current)
        if parent == current:
            return False
        current = parent
_DEF_SCOPE_NODES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
def _track_top_level_def(
    node: ast.AST, depth: int, owner: int | None,
    def_names: list[str], def_lines: list[int],
) -> int | None:
    if depth == 0 and isinstance(
            node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        if node.name in def_names:
            return def_names.index(node.name)
        def_names.append(node.name)
        def_lines.append(node.lineno)
        return len(def_names) - 1
    return owner
def _ref_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    return None
def _bucket_refs_from_walk(
    walk: _WalkBundle,
) -> tuple[list[tuple[str, set[str]]], set[str]]:
    buckets: list[set[str]] = [set() for _ in walk.def_names]
    module_refs: set[str] = set()
    builtins = BUILTIN_NAMES
    for node, owner in zip(walk.nodes, walk.owners, strict=True):
        ref = _ref_name(node)
        if ref is None or ref in builtins:
            continue
        (module_refs if owner is None else buckets[owner]).add(ref)
    order = sorted(range(len(walk.def_names)),
                   key=lambda i: (walk.def_lines[i], i))
    top_defs = [(walk.def_names[i], buckets[i]) for i in order]
    return top_defs, module_refs
def _resolve_dep_cached(
    collector: ModuleReferenceCollector, import_module: str, base_dir: Path,
) -> str | None:
    key = (import_module, str(base_dir))
    cache = collector._dep_resolve_cache
    if key in cache:
        return cache[key]
    dep = resolve_internal_dependency(import_module, base_dir)
    cache[key] = dep
    return dep
def _rel_import_target_pkg(rel_path: str, level: int) -> tuple[str, ...] | None:
    pkg_parts = Path(rel_path).parts[:-1]
    if level > len(pkg_parts) + 1:
        return None
    return pkg_parts[:len(pkg_parts) - (level - 1)]
def _rel_path_or_none(
    collector: ModuleReferenceCollector, fpath_str: str | None,
) -> str | None:
    if fpath_str is None:
        return None
    path = Path(fpath_str)
    if not path.is_relative_to(collector.skill_dir):
        return None
    return str(path.relative_to(collector.skill_dir))
def _rel_module_prefix(
    collector: ModuleReferenceCollector, rel_path: str, level: int,
) -> str | None:
    try:
        package_rel = Path(rel_path).relative_to(
            collector._package_root.relative_to(collector.skill_dir))
    except ValueError:
        return None
    target_pkg = _rel_import_target_pkg(str(package_rel), level)
    if target_pkg is None:
        return None
    return ".".join((collector._package_name,) + target_pkg)
def _collect_importfrom_names(
    collector: ModuleReferenceCollector, node: ast.ImportFrom, rel_path: str,
) -> list[str]:
    base = _importfrom_base_module(collector, node, rel_path)
    if base is None:
        return []
    alias_names: list[str] = []
    for alias in node.names:
        if alias.name == "*":
            continue
        name = collector.importable_submodule_name(base, alias.name)
        if name:
            alias_names.append(name)
    return [base, *alias_names]
def _importfrom_base_module(
    collector: ModuleReferenceCollector, node: ast.ImportFrom,
    rel_path: str | None,
) -> str | None:
    if node.level <= 0:
        return node.module
    if rel_path is None:
        return None
    prefix = _rel_module_prefix(collector, rel_path, node.level)
    if prefix is None:
        return None
    return f"{prefix}.{node.module}" if node.module else prefix
def _abs_own_init_covered(
    collector: ModuleReferenceCollector, node: ast.ImportFrom,
    filepath: Path,
) -> bool:
    """``from 本包 import 子模块`` 的本包 ``__init__`` 边在运行时是 no-op。

    仅当被导入模块正是导入方自身/祖先包的 ``__init__`` 且所有别名都解析为
    子模块/子包时成立；``from 本包 import 符号``（别名不是模块）仍保留该边
    ——符号来自 ``__init__`` 的导出面，是真实依赖。
    """
    if not node.module:
        return False
    init_file = collector.module_to_file(node.module)
    if not init_file or not _is_own_package_initializer(init_file, filepath):
        return False
    aliases = _importfrom_alias_names(node)
    if aliases is None:
        return False
    return all(collector.module_to_file(f"{node.module}.{name}")
               for name in aliases)
def _record_abs_importfrom_edges(
    collector: ModuleReferenceCollector, node: ast.ImportFrom,
    filepath: Path, module_level: bool, edges: _ImportEdges,
) -> None:
    names = ([node.module] + [f"{node.module}.{alias.name}"
                              for alias in node.names]
             if node.module else
             [alias.name for alias in node.names])
    drop_own_init = _abs_own_init_covered(collector, node, filepath)
    for name in names:
        if drop_own_init and name == node.module:
            continue
        target = collector.module_to_file(name)
        if target:
            edges.add_resolved(target, module_level)
def _record_rel_importfrom_edges(
    collector: ModuleReferenceCollector, node: ast.ImportFrom,
    filepath: Path, module_level: bool, edges: _ImportEdges,
) -> None:
    rel_path = _rel_path_or_none(collector, str(filepath))
    target_pkg = (_rel_import_target_pkg(rel_path, node.level)
                  if rel_path is not None else None)
    if target_pkg is None:
        return
    base_dir = collector.skill_dir.joinpath(*target_pkg)
    entries = _rel_name_entries(node, base_dir)
    if not node.module and _rel_aliases_all_submodules(
            collector, node, base_dir):
        # `from . import 子模块`：父包 __init__ 已在初始化链上（运行时 no-op），
        # 只依赖子模块本身。保留该边会让「__init__ 再导出子模块 + 子模块再
        # from . import 兄弟模块」这一最常见健康结构成环——与
        # ArchitectureCheckStage / _LoadingGraphBuilder.record_relative 同口径。
        entries = entries[1:]
    module_target = ""
    for index, (name, resolve_base, force_resolved) in enumerate(entries):
        dep = _resolve_dep_cached(collector, name, resolve_base)
        if not dep:
            continue
        resolved_path = _resolve_module_path(resolve_base, dep)
        if resolved_path is None:
            continue
        if node.module and index == 0:
            module_target = resolved_path
        elif (node.module and module_target
              and Path(module_target).name != "__init__.py"):
            continue
        if node.level == 1 and not force_resolved:
            edges.add_bare(dep, module_level)
            continue
        edges.add_resolved(resolved_path, module_level)
def _record_importfrom_edges(
    collector: ModuleReferenceCollector, node: ast.ImportFrom,
    filepath: Path, module_level: bool, edges: _ImportEdges,
) -> None:
    if not node.level:
        _record_abs_importfrom_edges(
            collector, node, filepath, module_level, edges)
        return
    _record_rel_importfrom_edges(
        collector, node, filepath, module_level, edges)
def _register_import_node(
    collector: ModuleReferenceCollector, node: ast.AST,
    module_level: bool, filepath: Path, edges: _ImportEdges,
) -> tuple | None:
    if isinstance(node, ast.ImportFrom):
        _record_importfrom_edges(
            collector, node, filepath, module_level, edges)
        return (node.lineno, "from", None, node.module, node.level)
    if not isinstance(node, ast.Import):
        return None
    for alias in node.names:
        target = collector.module_to_file(alias.name)
        if target:
            edges.add_resolved(target, module_level)
    return (node.lineno, "import", [a.name for a in node.names], None, 0)
def _accumulate_call_ref(
    collector: ModuleReferenceCollector, node: ast.AST,
    bound_modules: _ScopedModuleBindings, call_refs: dict[str, float],
) -> None:
    attribution = _call_attribution(
        node, bound_modules, collector.module_to_file)
    if attribution is None:
        return
    module_name, method_name = attribution
    target_file = collector.module_to_file(module_name)
    if target_file is None:
        return
    weight = (collector.WEIGHT_POLYMORPHIC
              if method_name in _MAGIC_OR_POLYMORPHIC
              else collector.WEIGHT_CALL)
    call_refs[target_file] = call_refs.get(target_file, 0) + weight
def _call_attribution(
    node: ast.AST, bound_modules: dict[str, str],
    resolve_module: Callable[[str], str | None],
) -> tuple[str, str] | None:
    if not isinstance(node, ast.Call):
        return None
    parts = _attribute_chain(node.func)
    if parts is None or len(parts) < 2:
        return None
    root_binding = bound_modules.get(node, parts[0])
    if root_binding is None:
        return None
    chain = [segment for segment in (*root_binding.split("."), *parts[1:])
             if segment]
    for end in range(len(chain) - 1, 0, -1):
        module_name = ".".join(chain[:end])
        if resolve_module(module_name) is not None:
            return module_name, chain[-1]
    return None
def _register_importfrom_symbol_sources(
    collector: ModuleReferenceCollector, node: ast.ImportFrom,
    consumer_file: str,
) -> None:
    rel_path = _rel_path_or_none(collector, consumer_file)
    base = _importfrom_base_module(collector, node, rel_path)
    if base is None:
        return
    base_file = collector.module_to_file(base)
    if base_file is None:
        return
    for alias in node.names:
        if alias.name == "*":
            continue
        if collector.module_to_file(f"{base}.{alias.name}") is not None:
            continue
        collector._import_index.add_symbol_consumer(
            base_file, alias.name, consumer_file)
def _register_ref_index_entries(
    collector: ModuleReferenceCollector, node: ast.AST, fpath_str: str,
    name_index: dict[str, list[str]] | None,
) -> None:
    if isinstance(node, (ast.ImportFrom, ast.Import)):
        for alias in node.names:
            key = import_binding_name(node, alias)
            if key is not None:
                collector._import_index[key].add(fpath_str)
    if isinstance(node, ast.ImportFrom):
        _register_importfrom_symbol_sources(collector, node, fpath_str)
    if name_index is None:
        return
    ref = _ref_name(node)
    if ref is not None:
        name_index[ref].append(fpath_str)
_IMPORT_SCOPE_NODES = _DEF_SCOPE_NODES + (ast.Lambda,)
@dataclass(frozen=True)
class _ScopedModuleBindings:
    tables: dict[ast.AST, dict[str, str]]
    parents: dict[ast.AST, ast.AST]
    lexical: Any
    def get(self, node: ast.AST, name: str) -> str | None:
        scope = node
        while scope is not None and scope not in self.lexical.bound:
            scope = self.parents.get(scope)
        if (scope is not None
                and scope_shadows_import(self.lexical, scope, name)):
            return None
        return resolve_import_binding(self.tables, self.parents, node, name)
def _import_declaration_scope(scope: ast.AST, name: str, scope_parents: dict,
                              declarations: dict) -> ast.AST:
    kind = declarations.get(scope, {}).get(name)
    if kind == "global":
        while scope in scope_parents:
            scope = scope_parents[scope]
        return scope
    if kind == "nonlocal":
        target = scope_parents.get(scope)
        while isinstance(target, ast.ClassDef):
            target = scope_parents.get(target)
        return target if target is not None else scope
    return scope
def _scoped_module_bindings(
    collector: ModuleReferenceCollector, tree: ast.Module, fpath_str: str,
) -> _ScopedModuleBindings:
    parents = parent_map(tree)
    scope_parents: dict[ast.AST, ast.AST] = {}
    declarations: dict[ast.AST, dict[str, str]] = {}
    imports: list[tuple[ast.Import | ast.ImportFrom, ast.AST]] = []
    stack = [(child, tree)
             for child in reversed(list(ast.iter_child_nodes(tree)))]
    while stack:
        node, scope = stack.pop()
        child_scope = scope
        if isinstance(node, _IMPORT_SCOPE_NODES):
            child_scope = node
            scope_parents[node] = scope
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            imports.append((node, scope))
            continue
        elif isinstance(node, (ast.Global, ast.Nonlocal)):
            kind = "global" if isinstance(node, ast.Global) else "nonlocal"
            declared = declarations.setdefault(scope, {})
            for name in node.names:
                declared[name] = kind
        for child in reversed(list(ast.iter_child_nodes(node))):
            stack.append((child, child_scope))
    tables: dict[ast.AST, dict[str, str]] = {}
    rel_path = _rel_path_or_none(collector, fpath_str)
    for node, scope in imports:
        bound: dict[str, str] = {}
        if isinstance(node, ast.Import):
            _bind_import_aliases(node, bound)
        else:
            base = _importfrom_base_module(collector, node, rel_path)
            if base is None:
                continue
            _bind_importfrom_aliases(node, base, bound)
        for name, module in bound.items():
            target = _import_declaration_scope(
                scope, name, scope_parents, declarations)
            tables.setdefault(target, {})[name] = module
    return _ScopedModuleBindings(
        tables, parents, collect_lexical_scope_table(tree))
class ModuleReferenceCollector:
    WEIGHT_CALL = 3.0
    WEIGHT_POLYMORPHIC = 1.0
    def __init__(self: Self, skill_dir: Path) -> None:
        self.skill_dir = Path(skill_dir)
        layout = detect_layout(str(self.skill_dir))
        self._package_root = (Path(layout.package_root) if layout.is_package
                              else self.skill_dir)
        self._package_name = self._module_identity_prefix(layout)
        self._module_file_cache: dict[str, str | None] = {}
        self._dep_resolve_cache: dict[tuple[str, str], str | None] = {}
        self._name_index: dict[str, list[str]] = defaultdict(list)
        self._import_index = _ImportIndex()
        self._top_level_refs: dict[str, list[tuple[str, set[str]]]] = {}
        self._module_level_refs: dict[str, set[str]] = {}
        self._all_declarations: dict[str, set[str]] = {}
        self._module_state_names: dict[str, set[str]] = {}
        self._import_edges: dict[str, dict[str, list[str]]] = {}
        self._import_nodes: dict[str, list[tuple]] = {}
    def _module_identity_prefix(self: Self, layout) -> str:
        if not layout.is_package:
            return self.skill_dir.name
        package_root = Path(layout.package_root)
        if (package_root.parent == self.skill_dir
                and package_root.name != self.skill_dir.name):
            return f"{self.skill_dir.name}.{package_root.name}"
        return layout.package_name
    def collect_file(self: Self, filepath: Path, tree: ast.AST) -> CollectionResult:
        fp_s = str(filepath)
        rel_path = str(filepath.relative_to(self.skill_dir))
        classes, functions, imports_out, from_import_entries = \
            self._collect_module_entries(tree, rel_path)
        walk = self._walk_collect_shared(tree, fp_s, filepath)
        bound_modules = _scoped_module_bindings(self, tree, fp_s)
        top_defs, module_refs = _bucket_refs_from_walk(walk)
        self._top_level_refs[fp_s] = top_defs
        self._module_level_refs[fp_s] = module_refs
        self._all_declarations[fp_s] = module_export_names(tree)
        self._module_state_names[fp_s] = extract_module_state_names(tree)
        self._register_indexes_from_walk(
            walk, fp_s, self._name_index, bound_modules)
        call_refs = self._collect_call_references(walk, bound_modules)
        return CollectionResult(
            classes=classes, functions=functions,
            imports_out=imports_out,
            from_import_entries=from_import_entries,
            nodes=walk.nodes, owners=walk.owners, def_names=walk.def_names,
            top_defs=top_defs, module_refs=module_refs,
            call_refs=call_refs)
    def _collect_module_entries(
        self: Self, tree: ast.AST, rel_path: str,
    ) -> tuple[list[str], list[str], list[str], set[str]]:
        classes: list[str] = []
        functions: list[str] = []
        for node in iter_module_level_nodes(tree):
            if isinstance(node, ast.ClassDef):
                classes.append(node.name)
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                functions.append(node.name)
        imports_out, from_import_entries = self._collect_module_imports(
            tree, rel_path)
        return (list(dict.fromkeys(classes)), list(dict.fromkeys(functions)),
                imports_out, from_import_entries)
    def _collect_module_imports(
        self: Self, tree: ast.AST, rel_path: str,
    ) -> tuple[list[str], set[str]]:
        imports_out: list[str] = []
        from_import_entries: set[str] = set()
        for node in walk_nodes(tree):
            if isinstance(node, ast.Import):
                imports_out.extend(alias.name for alias in node.names)
            elif isinstance(node, ast.ImportFrom):
                names = _collect_importfrom_names(self, node, rel_path)
                imports_out.extend(names)
                from_import_entries.update(names)
        return imports_out, from_import_entries
    @property
    def import_edges(self: Self) -> dict[str, dict[str, list[str]]]:
        return self._import_edges
    @property
    def import_nodes(self: Self) -> dict[str, list[tuple]]:
        return self._import_nodes
    @property
    def name_index(self: Self) -> dict[str, list[str]]:
        return self._name_index
    @property
    def import_index(self: Self) -> dict[str, set[str]]:
        return self._import_index
    @property
    def symbol_consumers(self: Self) -> dict[tuple[str, str], set[str]]:
        return dict(self._import_index._symbol_consumers)
    @property
    def top_level_refs(self: Self) -> dict[str, list[tuple[str, set[str]]]]:
        return self._top_level_refs
    @property
    def module_level_refs(self: Self) -> dict[str, set[str]]:
        return self._module_level_refs
    @property
    def all_declarations(self: Self) -> dict[str, set[str]]:
        return self._all_declarations
    @property
    def module_state_names(self: Self) -> dict[str, set[str]]:
        return self._module_state_names
    def _walk_collect_shared(
        self: Self, tree: ast.AST, fp_s: str, filepath: Path,
    ) -> _WalkBundle:
        nodes: list[ast.AST] = []
        owners: list[int | None] = []
        def_names: list[str] = []
        def_lines: list[int] = []
        edges = _ImportEdges()
        import_nodes: list[tuple] = []
        typing_aliases = typing_guard_aliases(tree)
        type_checking_names = typing_type_checking_names(tree)
        queue: deque = deque()
        queue.append((tree, 0, None, False))
        while queue:
            node, depth, owner, lazy = queue.popleft()
            nodes.append(node)
            owners.append(owner)
            child_owner = _track_top_level_def(
                node, depth, owner, def_names, def_lines)
            child_depth = depth + (1 if isinstance(node, _DEF_SCOPE_NODES)
                                   else 0)
            child_lazy = lazy or isinstance(node, _LAZY_IMPORT_SCOPE_NODES)
            if (isinstance(node, ast.If)
                    and is_type_checking_guard(
                        node.test, typing_aliases, type_checking_names)):
                queue.append((node.test, child_depth, child_owner, lazy))
                for child in node.body:
                    queue.append((child, child_depth, child_owner, True))
                for child in node.orelse:
                    queue.append((child, child_depth, child_owner, lazy))
            else:
                for child in ast.iter_child_nodes(node):
                    queue.append(
                        (child, child_depth, child_owner, child_lazy))
            entry = _register_import_node(
                self, node, not lazy, filepath, edges)
            if entry is not None:
                import_nodes.append(entry)
        self._import_edges[fp_s] = edges.as_dict()
        self._import_nodes[fp_s] = import_nodes
        return _WalkBundle(nodes=nodes, owners=owners, def_names=def_names,
                           def_lines=def_lines)
    def _register_indexes_from_walk(
        self: Self, walk: _WalkBundle, fpath_str: str,
        name_index: dict[str, list[str]] | None,
        bound_modules: _ScopedModuleBindings,
    ) -> None:
        for node in walk.nodes:
            _register_ref_index_entries(self, node, fpath_str, name_index)
        _register_attribute_symbol_sources(
            self, walk.nodes, fpath_str, bound_modules)
    def _collect_call_references(
            self: Self, walk: _WalkBundle,
            bound_modules: _ScopedModuleBindings,
    ) -> dict[str, float]:
        walk_nodes = walk.nodes
        call_refs: dict[str, float] = {}
        for node in walk_nodes:
            _accumulate_call_ref(self, node, bound_modules, call_refs)
        return call_refs
    def module_to_file(self: Self, module_name: str) -> str | None:
        root_names = {self.skill_dir.name, self._package_name}
        for root_name in sorted(root_names, key=len, reverse=True):
            if module_name == root_name:
                module_name = ""
                break
            prefix = root_name + "."
            if root_name and module_name.startswith(prefix):
                module_name = module_name[len(prefix):]
                break
        if module_name in self._module_file_cache:
            return self._module_file_cache[module_name]
        roots = list(dict.fromkeys((self._package_root, self.skill_dir)))
        result = None
        for root in roots:
            result = _resolve_module_path(root, module_name)
            if result is not None:
                break
        self._module_file_cache[module_name] = result
        return result
    def importable_submodule_name(
        self: Self, base: str, alias_name: str,
    ) -> str | None:
        candidate = f"{base}.{alias_name}" if base else alias_name
        return candidate if self.module_to_file(candidate) else None
    def file_to_module(self: Self, rel_path: str) -> str:
        normalized = rel_path.replace("\\", "/")
        if normalized.lower().endswith(".py"):
            normalized = normalized[:-3]
        return normalized.replace("/", ".")
def _register_importfrom_consumers(
    node: ast.ImportFrom,
    base_module: str,
    resolver: ModuleReferenceCollector,
    alias_files: dict[str, str],
    symbol_consumers: dict[str, set[str]],
) -> None:
    for alias in node.names:
        if alias.name == "*":
            continue
        _register_alias_or_symbol(
            resolver, base_module, alias,
            alias_files, symbol_consumers)
def _register_alias_or_symbol(
    resolver: ModuleReferenceCollector, module: str, alias: ast.alias,
    alias_files: dict[str, str],
    symbol_consumers: dict[str, set[str]],
) -> None:
    sub_file = resolver.module_to_file(f"{module}.{alias.name}")
    if sub_file is not None:
        alias_files[alias.asname or alias.name] = sub_file
        return
    base_file = resolver.module_to_file(module)
    if base_file is not None:
        symbol_consumers[base_file].add(alias.name)
def _register_import_aliases(
    node: ast.Import,
    resolver: ModuleReferenceCollector,
    alias_files: dict[str, str],
) -> None:
    for alias in node.names:
        mod_file = resolver.module_to_file(alias.name)
        if mod_file is None:
            continue
        bound_name = alias.asname or alias.name
        alias_files[bound_name] = mod_file
def _register_test_import_node(
    node: ast.AST,
    resolver: ModuleReferenceCollector,
    alias_files: dict[str, str],
    symbol_consumers: dict[str, set[str]],
    rel_path: str | None,
) -> None:
    if isinstance(node, ast.ImportFrom):
        base_module = _importfrom_base_module(resolver, node, rel_path)
        if base_module is not None:
            _register_importfrom_consumers(
                node, base_module, resolver, alias_files, symbol_consumers)
    elif isinstance(node, ast.Import):
        _register_import_aliases(node, resolver, alias_files)
def _attribute_chain(node: ast.AST) -> list[str] | None:
    parts: list[str] = []
    current = node
    while isinstance(current, ast.Attribute):
        parts.append(current.attr)
        current = current.value
    if not isinstance(current, ast.Name):
        return None
    parts.append(current.id)
    parts.reverse()
    return parts
def _module_attribute_target(
    node: ast.AST, bound_modules: _ScopedModuleBindings,
    resolve_module: Callable[[str], str | None], *,
    load_only: bool = True,
) -> tuple[str, str] | None:
    if (not isinstance(node, ast.Attribute)
            or (load_only and not isinstance(node.ctx, ast.Load))):
        return None
    parts = _attribute_chain(node)
    if parts is None or len(parts) < 2:
        return None
    root_binding = bound_modules.get(node, parts[0])
    if root_binding is None:
        return None
    chain = [segment for segment in (*root_binding.split("."), *parts[1:])
             if segment]
    for split in range(len(chain) - 1, 0, -1):
        module_name = ".".join(chain[:split])
        if resolve_module(module_name) is not None:
            return module_name, chain[split]
    return None
def _register_attribute_symbol_sources(
    collector: ModuleReferenceCollector, nodes: Iterable[ast.AST],
    consumer_file: str, bound_modules: _ScopedModuleBindings,
) -> None:
    for node in nodes:
        target = _module_attribute_target(
            node, bound_modules, collector.module_to_file)
        if target is None:
            continue
        source_file = collector.module_to_file(target[0])
        if source_file is not None and source_file != consumer_file:
            collector._import_index.add_symbol_consumer(
                source_file, target[1], consumer_file)
def _collect_test_file_symbols(
    tp: Path,
    resolver: ModuleReferenceCollector,
    symbol_consumers: dict[str, set[str]],
) -> None:
    source, _fingerprint = read_source_with_fingerprint(str(tp))
    if source is None:
        _log.debug("[Topology] 测试消费方扫描跳过 %s: 读取失败", tp.name)
        return
    tree = _parse_source(source, str(tp))
    if tree is None:
        return
    alias_files: dict[str, str] = {}
    rel_path = _rel_path_or_none(resolver, str(tp))
    for node in walk_nodes(tree):
        _register_test_import_node(node, resolver, alias_files,
                                   symbol_consumers, rel_path)
    if not alias_files:
        return
    bound_modules = _scoped_module_bindings(resolver, tree, str(tp))
    for node in walk_nodes(tree):
        target = _module_attribute_target(
            node, bound_modules, resolver.module_to_file, load_only=False)
        if target is None:
            continue
        source_file = resolver.module_to_file(target[0])
        if source_file is not None:
            symbol_consumers[source_file].add(target[1])
def collect_test_symbol_consumers(
    skill_dir: Path | str,
) -> dict[str, set[str]]:
    root = Path(skill_dir)
    resolver = ModuleReferenceCollector(root)
    symbol_consumers: dict[str, set[str]] = defaultdict(set)
    for tp in sorted(iter_target_py_files(root, include_tests=True)):
        if is_test_file_path(str(tp)):
            _collect_test_file_symbols(tp, resolver, symbol_consumers)
    return dict(symbol_consumers)
def _read_tree(fpath: str, context: str) -> ast.Module | None:
    source = _fd_read_source(fpath)
    return _parse_source(source, context) if source is not None else None
def _is_thin_compat_stub(source: str, non_trivial: list[ast.stmt],
                         is_compat: bool) -> bool:
    _has_business_stmt = any(
        not isinstance(n, (ast.Import, ast.ImportFrom))
        and not _is_static_all_decl(n)
        for n in non_trivial)
    line_count = source.count('\n') + (
        1 if source and not source.endswith('\n') else 0)
    return (is_compat and line_count <= 6
            and not _has_business_stmt)
def _merged_redirect_target(stmts: list[ast.stmt]) -> str:
    for node in stmts:
        if (isinstance(node, ast.ImportFrom) and node.module
                and _MERGED_WORD_RE.search(node.module)):
            return node.module
    return ""
def _import_resolution_rank(rel_path: str) -> tuple[int, str]:
    stem = rel_path.replace("\\", "/").rsplit("/", 1)[-1]
    if stem.lower().endswith(".py"):
        stem = stem[:-len(".py")]
    if stem.lower() == "__init__":
        return (0, rel_path)
    if "." in stem:
        return (2, rel_path)
    return (1, rel_path)
@dataclass
class ConsumerReport:
    filepath: str
    module_name: str
    lines: int = 0
    is_pure_stub: bool = False
    is_entry_point: bool = False
    is_test_file: bool = False
    stub_target: str = ""
    design_expected: bool = False
    classification: str = ""
    recommendation: str = ""
    can_safely_delete: bool = False
    exports: list[str] = field(default_factory=list)
    consumer_count: int = 0
    shadowed_by: str = ""
    read_failed: bool = False
class _ImportGraphBuilder:
    def __init__(self, skill_dir: str = "") -> None:
        self.reset(skill_dir)
    def reset(self, skill_dir: str) -> None:
        self._skill_dir = skill_dir
        self._root_pkg = _root_package_name(skill_dir)
        self._package_key_prefix = _project_package_key_prefix(skill_dir)
        self._consumer_map = defaultdict(set)
        self._lazy_source_mods = None
        self._modules = {}
        self.analysis_complete = True
    def lazy_source_mods(self) -> set[str]:
        if self._lazy_source_mods is not None:
            return self._lazy_source_mods
        mods: set[str] = set()
        for lazy_path in _iter_lazy_surface_files(self._skill_dir):
            tree = _read_tree(lazy_path, "lazy 登记表")
            if tree is not None:
                mods.update(_iter_surface_modules(tree))
        self._lazy_source_mods = mods
        return mods
    def consumers_of(self, module_name: str) -> set[str]:
        return set(self._consumer_map.get(module_name, set()))
    def _register_module_consumers(self, dotted_key: str, consumer: str) -> None:
        self._consumer_map[dotted_key].add(consumer)
        parts = dotted_key.split(".")
        for i in range(1, len(parts)):
            parent = ".".join(parts[:i])
            if parent in self._modules:
                self._consumer_map[parent].add(consumer)
    def _resolve_relative_base(self, fp: str, skill_dir: str,
                               level: int) -> str | None:
        if level <= 0:
            return ''
        rel_path = os.path.relpath(fp, skill_dir)
        current_pkg = os.path.dirname(rel_path).replace(os.sep, '.')
        parts = [p for p in current_pkg.split('.') if p]
        if level > len(parts) + 1:
            return None
        return '.'.join(parts[:len(parts) - level + 1])
    @staticmethod
    def _strip_root_prefix(dotted_name: str, root_pkg: str) -> str:
        if not root_pkg:
            return ''
        prefix = f"{root_pkg}."
        return dotted_name[len(prefix):] if dotted_name.startswith(prefix) else ''
    @staticmethod
    def _absolute_candidates(dotted_name: str, root_pkg: str,
                             key_prefix: str = "") -> list[str]:
        candidates = [dotted_name]
        physical = _physical_package_key(
            dotted_name, root_pkg, key_prefix)
        if physical:
            candidates.append(physical)
        stripped = _ImportGraphBuilder._strip_root_prefix(
            dotted_name, root_pkg)
        if stripped or root_pkg == dotted_name != '':
            candidates.append(stripped)
        return list(dict.fromkeys(candidates))
    @staticmethod
    def _module_import_candidates(node: ast.ImportFrom, base: str,
                                  root_pkg: str,
                                  key_prefix: str = "") -> list[str]:
        if node.level > 0 and base:
            return [f"{base}.{node.module}"]
        return _ImportGraphBuilder._absolute_candidates(
            node.module, root_pkg, key_prefix)
    def _register_first_hit(self, candidates: list[str],
                            module_name: str) -> None:
        for cand in candidates:
            if cand not in self._modules:
                continue
            self._register_module_consumers(cand, module_name)
            break
    @staticmethod
    def _symbol_import_candidates(node: ast.ImportFrom, base: str,
                                  alias_name: str, root_pkg: str,
                                  key_prefix: str = "") -> list[str]:
        if node.level > 0 and base:
            return [f"{base}.{node.module}.{alias_name}"]
        candidates = [f"{node.module}.{alias_name}"]
        physical = _physical_package_key(
            candidates[0], root_pkg, key_prefix)
        if physical:
            candidates.append(physical)
        if root_pkg and node.module == root_pkg:
            candidates.append(alias_name)
        else:
            stripped = _ImportGraphBuilder._strip_root_prefix(
                node.module, root_pkg)
            if stripped:
                candidates.append(f"{stripped}.{alias_name}")
        return list(dict.fromkeys(candidates))
    def _register_imported_symbols(self, node: ast.ImportFrom, base: str,
                                   module_name: str) -> None:
        for alias in node.names:
            if alias.name == '*':
                continue
            self._register_first_hit(
                self._symbol_import_candidates(
                    node, base, alias.name, self._root_pkg,
                    self._package_key_prefix),
                module_name)
    def _register_bare_relative_symbols(self, node: ast.ImportFrom, base: str,
                                        module_name: str) -> None:
        if base and base in self._modules:
            self._register_module_consumers(base, module_name)
        for alias in node.names:
            if alias.name == '*':
                continue
            self._register_first_hit(
                self._bare_relative_symbol_candidates(
                    alias.name, base, self._root_pkg),
                module_name)
    @staticmethod
    def _bare_relative_symbol_candidates(alias_name: str, base: str,
                                          root_pkg: str) -> list[str]:
        if base:
            return [f"{base}.{alias_name}"]
        if root_pkg:
            return [alias_name, f"{root_pkg}.{alias_name}"]
        return [alias_name]
    def _walk_import_nodes(self, tree: ast.AST, fp: str, skill_dir: str,
                           module_name: str) -> None:
        for node in walk_nodes(tree):
            if not isinstance(node, (ast.ImportFrom, ast.Import)):
                continue
            if isinstance(node, ast.ImportFrom):
                base = self._resolve_relative_base(fp, skill_dir, node.level)
                if base is None:
                    continue
                if node.module:
                    self._register_first_hit(
                        self._module_import_candidates(
                            node, base, self._root_pkg,
                            self._package_key_prefix),
                        module_name)
                    self._register_imported_symbols(node, base, module_name)
                else:
                    self._register_bare_relative_symbols(node, base, module_name)
                continue
            for alias in node.names:
                self._register_first_hit(
                    self._absolute_candidates(
                        alias.name, self._root_pkg, self._package_key_prefix),
                    module_name)
    def analyze_imports(self, modules: dict[str, str], skill_dir: str) -> None:
        if skill_dir != self._skill_dir:
            self.reset(skill_dir)
        self._consumer_map = defaultdict(set)
        self._modules = modules
        self.analysis_complete = True
        for module_name, fp in modules.items():
            self._analyze_one_module(module_name, fp, skill_dir)
    def _analyze_one_module(self, module_name: str, fp: str,
                            skill_dir: str) -> None:
        tree = _read_tree(fp, f"消费图 {module_name}")
        if tree is None:
            self.analysis_complete = False
            return
        try:
            self._walk_import_nodes(tree, fp, skill_dir, module_name)
        except PARSE_DEGRADE_EXC as e:
            self.analysis_complete = False
            _log.warning("[ZCC] 消费图登记跳过 %s: %s", module_name, e)
class ZeroConsumerChecker:
    DETECTOR_ID = "ZCC"
    PATTERN_NAME = "零消费者导入"
    def __init__(self) -> None:
        self._graph = _ImportGraphBuilder()
        self._reset("")
    def _reset(self, skill_dir: str) -> None:
        self._module_exports: dict[str, list[str]] = {}
        self._all_modules: dict[str, str] = {}
        self._shadowed_by: dict[str, str] = {}
        self._scan_complete = True
        self._graph.reset(skill_dir)
    @property
    def scan_complete(self) -> bool:
        return self._scan_complete and self._graph.analysis_complete
    def scan_directory(self, skill_dir: str) -> list[ConsumerReport]:
        skill_dir = str(skill_dir)
        if not os.path.isdir(skill_dir):
            raise FileNotFoundError(f"项目目录不存在: {skill_dir}")
        self._reset(skill_dir)
        _log.info("[ZCC] 开始扫描: %s", skill_dir)
        self._scan_modules(skill_dir)
        self._graph.analyze_imports(self._all_modules, skill_dir)
        reports = self._generate_reports(skill_dir)
        dead_count = sum(1 for r in reports if r.can_safely_delete)
        if not self.scan_complete:
            _log.warning("[ZCC] 消费图扫描不完整，已阻断全部安全删除许可")
        _log.info("[ZCC] 扫描完成: %d 模块, %d 零消费者, %d 可安全删除, %d 被遮蔽",
                  len(self._all_modules), len(reports), dead_count,
                  len(self._shadowed_by))
        return reports
    def _on_walk_error(self, exc: OSError) -> None:
        self._scan_complete = False
        _warn_walk_error(exc)
    def _scan_modules(self, skill_dir: str) -> None:
        records: list[tuple[str, str, str, list[str]]] = []
        for root, dirs, files in os.walk(
                skill_dir, onerror=self._on_walk_error):
            prune_target_dirs(dirs, include_tests=True)
            for f in files:
                if f.startswith('.') or not f.lower().endswith('.py'):
                    continue
                records.append(self._scan_one_module(root, f, skill_dir))
        self._resolve_and_register(records)
    def _scan_one_module(self, root: str, fname: str,
                         skill_dir: str) -> tuple[str, str, str, list[str]]:
        fp = os.path.join(root, fname)
        rel = os.path.relpath(fp, skill_dir)
        module_name = normalize_module_name(rel)
        tree = _read_tree(fp, f"模块收集 {module_name}")
        if tree is None:
            self._scan_complete = False
        exports = (collect_module_exports_ordered(tree)[0]
                   if tree is not None else [])
        return rel, fp, module_name, exports
    def _resolve_and_register(
            self, records: list[tuple[str, str, str, list[str]]]) -> None:
        by_key: dict[str, list[tuple[str, str, str, list[str]]]] = defaultdict(list)
        for rec in records:
            by_key[rec[2]].append(rec)
        for key in sorted(by_key):
            ranked = sorted(by_key[key],
                            key=lambda r: _import_resolution_rank(r[0]))
            winner_rel, winner_fp, _winner_key, winner_exports = ranked[0]
            self._all_modules[key] = winner_fp
            self._module_exports[key] = winner_exports
            for loser_rel, loser_fp, _loser_key, loser_exports in ranked[1:]:
                shadow_key = (f"{key}{SHADOWED_KEY_MARK}"
                              f"{loser_rel.replace(os.sep, '/')}")
                self._all_modules[shadow_key] = loser_fp
                self._module_exports[shadow_key] = loser_exports
                self._shadowed_by[shadow_key] = winner_rel
                _log.warning(
                    "[ZCC] 同键导入遮蔽: %s 与 %s 同归一化键 %r，按 "
                    "Python 导入语义 %s 承接消费图键，%s 登记为遮蔽键"
                    "（import 永不可达，零消费者判定将报出）",
                    winner_rel.replace(os.sep, '/'),
                    loser_rel.replace(os.sep, '/'), key,
                    winner_rel.replace(os.sep, '/'), shadow_key)
    def _generate_reports(self, skill_dir: str) -> list[ConsumerReport]:
        reports = []
        for module_name, fp in self._all_modules.items():
            report = self._build_report(module_name, fp, skill_dir)
            if report is not None:
                reports.append(report)
        reports.sort(key=lambda r: r.module_name)
        reports.sort(
            key=lambda r: (r.can_safely_delete, not r.design_expected, r.lines),
            reverse=True,
        )
        return reports
    def _build_report(self, module_name: str, fp: str,
                      skill_dir: str) -> ConsumerReport | None:
        _consumers = self._graph.consumers_of(module_name) - {module_name}
        if _consumers:
            return None
        if module_name in self._graph.lazy_source_mods():
            return None
        rel = os.path.relpath(fp, skill_dir)
        fname = os.path.basename(fp)
        source = _fd_read_source(fp)
        read_failed = source is None
        if read_failed:
            lines = 0
            source = ''
        else:
            lines = len(source.splitlines())
        report = ConsumerReport(
            filepath=rel,
            module_name=module_name,
            lines=lines,
            exports=self._module_exports.get(module_name, []),
            consumer_count=len(_consumers),
            shadowed_by=self._shadowed_by.get(module_name, ""),
            read_failed=read_failed,
        )
        self._classify_report(report, source, lines, fname, rel)
        if report.can_safely_delete and not self.scan_complete:
            report.can_safely_delete = False
            report.recommendation = (
                '死兼容桩形态，但消费图扫描不完整，无法证明零消费者；保守保留.'
            )
        return report
    def _classify_report(self, report: ConsumerReport, source: str,
                         lines: int, fname: str, rel: str) -> None:
        if fname.lower() in ENTRY_POINT_PATTERNS:
            report.is_entry_point = True
            report.classification = 'ENTRY_POINT'
            report.recommendation = '入口文件,豁免'
        elif is_test_file_path(rel):
            report.is_test_file = True
            report.classification = 'EXEMPT_TEST'
            report.recommendation = '测试文件,豁免'
        elif report.read_failed:
            report.classification = 'UNREADABLE'
            report.recommendation = (
                '源码读取失败,无法判定桩形态与业务体量;需人工复核'
                '(不计入死桩).'
            )
        else:
            self._classify_dead_or_orphan(report, source, lines)
        if report.shadowed_by:
            report.recommendation += (
                f" 另: 被 {report.shadowed_by.replace(os.sep, '/')} 遮蔽"
                "（同归一化键已由胜者承接,import 解析永不可达）."
            )
    def _classify_dead_or_orphan(self, report: ConsumerReport,
                                 source: str, lines: int) -> None:
        is_stub, stub_target = self.is_pure_import_stub(source)
        report.is_pure_stub = is_stub
        report.stub_target = stub_target
        if DESIGN_EXPECTED_MARKER in source:
            report.design_expected = True
            report.classification = 'DESIGN_EXPECTED'
            report.can_safely_delete = False
            report.recommendation = '设计预期零消费,免复核.'
        elif is_stub:
            report.classification = 'DEAD_STUB'
            report.can_safely_delete = True
            if stub_target:
                report.recommendation = (
                    f"死兼容桩: 仅重导出到 {stub_target},零消费者.可安全删除."
                )
            else:
                report.recommendation = (
                    "死兼容桩: 仅兼容标记与重导出,无业务语句,零消费者."
                    "可安全删除."
                )
        else:
            report.classification = 'ORPHAN_UTIL'
            report.can_safely_delete = False
            report.recommendation = (
                f"孤儿工具模块: 含 {lines} 行业务逻辑但零消费者."
                "保留(可能为内部工具),建议人工确认."
            )
    @staticmethod
    def is_pure_import_stub(source: str) -> tuple[bool, str]:
        source = source.strip()
        if not source:
            return False, ''
        is_compat = _has_compat_marker(source)
        tree = _parse_source(source, "桩判定")
        if tree is None:
            return False, ''
        non_trivial = _nontrivial_top_level_stmts(tree)
        if not _is_import_only(non_trivial):
            return _is_thin_compat_stub(source, non_trivial, is_compat), ''
        target = _merged_redirect_target(non_trivial)
        if target:
            return True, target
        return is_compat, ''
    def get_module_consumers(self, module_name: str) -> set[str]:
        return self._graph.consumers_of(module_name)
    def get_deletable_stubs(self, skill_dir: str) -> list[str]:
        reports = self.scan_directory(skill_dir)
        return [r.filepath for r in reports if r.can_safely_delete]
    def get_summary(self, skill_dir: str) -> dict:
        reports = self.scan_directory(skill_dir)
        return {
            "total_files": len(self._all_modules),
            "deletable_files": sum(1 for r in reports if r.can_safely_delete),
            "consumerless_files": sum(1 for r in reports if r.consumer_count == 0),
            "reports": reports,
        }
def get_module_consumers(
    module_name: str,
    skill_dir: str | None = None,
    checker: ZeroConsumerChecker | None = None,
) -> set[str]:
    if checker is not None:
        return checker.get_module_consumers(module_name)
    if not skill_dir:
        return set()
    fresh = ZeroConsumerChecker()
    fresh.scan_directory(skill_dir)
    return fresh.get_module_consumers(module_name)
def zero_consumer_summary(skill_dir: str) -> dict:
    try:
        _zc_reports = ZeroConsumerChecker().scan_directory(skill_dir)
        _zc_summary = {
            "total": len(_zc_reports),
            "dead_stubs": [r.filepath for r in _zc_reports
                           if r.classification == "DEAD_STUB"],
            "orphan_utils": [r.filepath for r in _zc_reports
                             if r.classification == "ORPHAN_UTIL"],
            "unreadable": [r.filepath for r in _zc_reports
                           if r.classification == "UNREADABLE"],
            "can_delete": sum(1 for r in _zc_reports if r.can_safely_delete),
        }
        _log.info("[ZCC] 零消费者检测: %d 死桩, %d 孤儿工具, %d 可删除（仅报告，"
                    "死桩需 AI 评估后手动处置）",
                    len(_zc_summary["dead_stubs"]), len(_zc_summary["orphan_utils"]),
                    _zc_summary["can_delete"])
        if _zc_summary["dead_stubs"]:
            _log.warning("[ZCC] 死桩模块（仅报告不入队）: %s",
                           ", ".join(_zc_summary["dead_stubs"]))
        return _zc_summary
    except Exception as _ze:  # noqa: BLE001 — 刻意宽捕获：零消费者检测失败(降级不影响主流程): %s
        _log.warning("[ZCC] 零消费者检测失败(降级不影响主流程): %s", _ze, exc_info=True)
        return {"total": 0, "dead_stubs": [], "orphan_utils": [],
                "unreadable": [], "can_delete": 0,
                "error": str(_ze)[:200]}
@dataclass(frozen=True)
class _LoadingGraphIndex:
    stems_by_dir: dict[Path, set[str]]
    module_dirs: set[Path]
    pkg_roots: set[str]
    package_root: Path
    package_name: str = ''
    is_package: bool = False
def _loading_graph_module_key(sp: Path, f: Path) -> str:
    return f.relative_to(sp).with_suffix("").as_posix()
def _valid_prefix_import_nodes(
        content: str, filename: str,
) -> tuple[list[ast.stmt], str] | None:
    try:
        parse_cached(content, filename)
    except SyntaxError as exc:
        error_line = getattr(exc, "lineno", None)
        if error_line is None or error_line <= 1:
            return None
        prefix = "".join(
            content.splitlines(keepends=True)[:error_line - 1])
        if not prefix.strip():
            return None
        try:
            tree = parse_cached(prefix, filename)
        except PARSE_DEGRADE_EXC:
            return None
        return (
            _iter_module_import_nodes(tree, skip_type_checking=True),
            content[len(prefix):],
        )
    except PARSE_DEGRADE_EXC:
        return None
    return None
@dataclass
class _LoadingGraphBuilder:
    sp: Path
    index: _LoadingGraphIndex
    self_key: str = ""
    imports: list[str] = field(default_factory=list)
    def has_module(self, base: str, ref_dir: Path) -> bool:
        return base in self.index.stems_by_dir.get(ref_dir, ())
    def record(self, base: str, ref_dir: Path) -> bool:
        if not self.has_module(base, ref_dir):
            return False
        key = _loading_graph_module_key(self.sp, ref_dir / f"{base}.py")
        if key != self.self_key and key not in self.imports:
            self.imports.append(key)
        return True
    def record_names(self, names: list[str], ref_dir: Path) -> bool:
        if not names:
            return False
        hit_all = True
        for base in names:
            hit_pkg = self.record_pkg_dir(base, ref_dir)
            hit_module = False if hit_pkg else self.record(base, ref_dir)
            hit_all = hit_all and (hit_pkg or hit_module)
        return hit_all
    def _unique_module_dir(self, base: str) -> Path | None:
        """裸导入的模块不在根目录时，回退到唯一含它的子目录。"""
        hits = [d for d in self.index.module_dirs
                if d != self.sp
                and base in self.index.stems_by_dir.get(d, ())]
        return hits[0] if len(hits) == 1 else None

    def has_regular_package(self, base: str, parent: Path) -> bool:
        return "__init__" in self.index.stems_by_dir.get(parent / base, ())
    def record_pkg_dir(self, base: str, parent: Path) -> bool:
        pkg_dir = parent / base
        if not self.has_regular_package(base, parent):
            return False
        return self.record("__init__", pkg_dir)
    def root_module_precedes_package(self, base: str) -> bool:
        root_is_package = self.has_module("__init__", self.sp)
        return (not (base == self.sp.name and root_is_package)
                and self.has_module(base, self.sp)
                and not self.has_regular_package(base, self.sp))
    def record_dotted(self, segs: list[str], names: list[str],
                      base_dir: Path, *,
                      include_self_package: bool = True) -> None:
        cur = base_dir
        if include_self_package:
            self.record("__init__", cur)
        for seg in segs:
            nxt = cur / seg
            if "__init__" in self.index.stems_by_dir.get(nxt, ()):
                self.record("__init__", nxt)
                cur = nxt
                continue
            if seg in self.index.stems_by_dir.get(cur, ()):
                self.record(seg, cur)
                return
            if nxt in self.index.module_dirs:
                cur = nxt
                continue
            break
        else:
            self.record_names(names, cur)
            return
    def record_relative(self, level: int, module: str | None,
                        names: list[str], py_file: Path) -> None:
        base_dir = py_file.parent
        for _ in range(level - 1):
            base_dir = base_dir.parent
        if module:
            # 相对导入只依赖被导入的子模块，不依赖本包 __init__ 的导出内容；
            # 而 __init__ 再 `from . import 子模块` 是最常见的包布局。若把
            # 「包内相对导入 ⇒ 依赖本包 __init__」记成边，任何标准包都会成环。
            self.record_dotted(module.split("."), names, base_dir,
                               include_self_package=False)
        else:
            # `from . import X` 只有在 X 既不是子模块也不是子包时，才意味着
            # 依赖本包 __init__ 的导出符号；若 X 是子模块，记这条边会与
            # __init__ 的再导出（`from . import 子模块`）直接成环。
            if not self.record_names(names, base_dir):
                self.record("__init__", base_dir)
    def _package_dir(self, root_name: str) -> Path:
        if self.index.is_package and self.index.package_name == root_name:
            return self.index.package_root
        return self.sp if root_name == self.sp.name else self.sp / root_name
    def _is_current_package(self, package_dir: Path) -> bool:
        if not self.self_key:
            return False
        try:
            prefix = package_dir.relative_to(self.sp).as_posix()
        except ValueError:
            return False
        return (prefix == '.' or self.self_key == f'{prefix}/__init__'
                or self.self_key.startswith(f'{prefix}/'))
    def record_absolute(self, module: str, names: list[str]) -> None:
        parts = module.split(".")
        if self.root_module_precedes_package(parts[0]):
            self.record(parts[0], self.sp)
            return
        if parts[0] not in self.index.pkg_roots:
            ns_dir = self.sp / parts[0]
            if (ns_dir in self.index.module_dirs
                    and not self.has_module(parts[0], self.sp)):
                if len(parts) > 1:
                    self.record_dotted(parts[1:], names, ns_dir)
                else:
                    self.record_names(names, ns_dir)
                return
            self._record_root_or_fallback(parts, names)
            return
        package_dir = self._package_dir(parts[0])
        same_package = self._is_current_package(package_dir)
        if len(parts) == 1:
            if not same_package:
                self.record("__init__", package_dir)
                self.record_names(names, package_dir)
            elif not self.record_names(names, package_dir):
                self.record("__init__", package_dir)
            return
        self.record_dotted(
            parts[1:], names, package_dir,
            include_self_package=not same_package)
    def _record_root_or_fallback(self, parts: list[str],
                                 names: list[str]) -> None:
        if self.record(parts[0], self.sp):
            return
        # 双模式技能把 ``scripts/`` 挂进 sys.path：``from docx_lint
        # import ...`` / ``import docx_lint`` 里的模块不在根目录，而在某个
        # 子目录。仅在 **唯一命中** 时回退，避免同名模块产生歧义边。
        fallback = self._unique_module_dir(parts[0])
        if fallback is not None:
            self.record_dotted(parts, names, fallback,
                               include_self_package=False)
    def record_plain_import(self, names: list[str]) -> None:
        for mod in names:
            parts = mod.split(".")
            if self.root_module_precedes_package(parts[0]):
                self.record(parts[0], self.sp)
                continue
            if len(parts) >= 2 and parts[0] in self.index.pkg_roots:
                base_dir = self._package_dir(parts[0])
                self.record_dotted(
                    parts[1:], [], base_dir,
                    include_self_package=not self._is_current_package(base_dir))
            elif parts[0] == self.sp.name:
                self.record("__init__", self.sp)
            elif len(parts) > 1:
                ns_dir = self.sp / parts[0]
                if (ns_dir in self.index.module_dirs
                        and not self.has_module(parts[0], self.sp)):
                    self.record_dotted(parts[1:], [], ns_dir)
                else:
                    self._record_root_or_fallback(parts, [])
            elif not self.record_pkg_dir(parts[0], self.sp):
                self._record_root_or_fallback(parts, [])
    def edges_for_file(self, content: str, py_file: Path) -> list[str]:
        self.imports.clear()
        self.self_key = _loading_graph_module_key(self.sp, py_file)
        nodes = module_import_stmts(
            content, str(py_file), skip_type_checking=True)
        if nodes is None:
            return self.edges_regex_fallback(content, py_file)
        for node in nodes:
            self.record_import_stmt(node, py_file)
        return self.imports
    def record_import_stmt(self, node: ast.stmt, py_file: Path) -> None:
        if isinstance(node, ast.ImportFrom):
            names = [a.name.split(".")[0] for a in node.names
                     if a.name != "*"]
            if node.level:
                self.record_relative(node.level, node.module, names, py_file)
            else:
                self.record_absolute(node.module or "", names)
            return
        self.record_plain_import([a.name for a in node.names])
    def edges_regex_fallback(self, content: str,
                             py_file: Path) -> list[str]:
        remaining = content
        prefix_result = _valid_prefix_import_nodes(content, str(py_file))
        if prefix_result is not None:
            prefix_nodes, remaining = prefix_result
            for node in prefix_nodes:
                self.record_import_stmt(node, py_file)
        row_spans = string_token_row_spans(remaining)
        for match in iter_import_stmts(remaining):
            if _import_match_indented(remaining, match):
                continue
            self._edge_from_match(remaining, match, row_spans, py_file)
        return self.imports
    def _edge_from_match(self, content: str, match, row_spans,
                         py_file: Path) -> None:
        if offset_in_string_literal(content, match.start(), row_spans):
            return
        if match.group("plain") is not None:
            self.record_plain_import(
                _gb_plain_names_from_text(content, match.span("plain")))
            return
        mod = match.group("module")
        if mod.startswith("."):
            self.record_relative(
                len(mod) - len(mod.lstrip(".")), mod.lstrip(".") or None,
                _gb_bare_names_after_import(content, match.end()),
                py_file)
            return
        self.record_absolute(
            mod, _gb_bare_names_after_import(content, match.end()))
def _build_import_graph_with_errors(
        sp: Path, ctx=None,
) -> tuple[dict[str, list[str]], list[str]]:
    sp = Path(sp).resolve()
    stems_by_dir: dict[Path, set[str]] = {}
    py_files: list[Path] = []
    for py_file in iter_target_py_files(sp, include_tests=True):
        stems_by_dir.setdefault(py_file.parent, set()).add(py_file.stem)
        py_files.append(py_file)
    module_dirs = set(stems_by_dir)
    for directory in tuple(module_dirs):
        module_dirs.update(
            parent for parent in directory.parents
            if parent == sp or sp in parent.parents)
    module_dirs.add(sp)
    layout = detect_layout(str(sp))
    index = _LoadingGraphIndex(
        stems_by_dir=stems_by_dir,
        module_dirs=module_dirs,
        pkg_roots=package_roots_for(str(sp)),
        package_root=Path(layout.package_root) if layout.is_package else sp,
        package_name=layout.package_name if layout.is_package else '',
        is_package=bool(layout.is_package))
    imports_graph: dict[str, list[str]] = {}
    unreadable: list[str] = []
    for py_file in py_files:
        content = read_source(str(py_file), ctx)
        if content is None:
            unreadable.append(py_file.relative_to(sp).as_posix())
            _log.warning("[Topology] 导入图跳过不可读源文件: %s", py_file)
            continue
        module_key = _loading_graph_module_key(sp, py_file)
        imports_graph[module_key] = _LoadingGraphBuilder(
            sp=sp, index=index).edges_for_file(content, py_file)
    return imports_graph, unreadable
def build_import_graph(sp: Path, ctx=None) -> dict[str, list[str]]:
    graph, _unreadable = _build_import_graph_with_errors(sp, ctx)
    return graph
def _gb_bare_names_after_import(content: str, match_end: int) -> list[str]:
    names_text, _stmt_end, _stmt_line_end = read_import_names_text(
        content, (match_end, _from_import_names_end(content, match_end)))
    bases = (_split_alias_text(nm)[0].split(".")[0].strip()
             for nm in split_import_names(names_text))
    return [base for base in bases if base and base != "*"]
def _gb_plain_names_from_text(content: str,
                              span: tuple[int, int]) -> list[str]:
    names_text, _stmt_end, _stmt_line_end = read_import_names_text(
        content, span)
    names: list[str] = []
    for nm in split_import_names(names_text):
        mod = _split_alias_text(nm)[0]
        if is_dotted_module_name(mod):
            names.append(mod)
    return names
def detect_import_cycles(imports_graph: dict[str, list[str]]
                         ) -> tuple[bool, list[str]]:
    graph = {node: sorted(deps) for node, deps in imports_graph.items()}
    details: list[str] = []
    seen: set[frozenset[str]] = set()
    for cycle in detect_cycles(graph):
        key = frozenset(cycle)
        if key in seen:
            continue
        seen.add(key)
        details.append(f"循环依赖: {' -> '.join(cycle + [cycle[0]])}")
    return bool(details), details
def _mask_token_types() -> tuple[set[int], bool]:
    mask_types = {tokenize.COMMENT, tokenize.STRING}
    has_fstring_tokens = False
    for name in ("FSTRING_START", "FSTRING_MIDDLE", "FSTRING_END"):
        tok_type = getattr(tokenize, name, None)
        if tok_type is not None:
            mask_types.add(tok_type)
            has_fstring_tokens = True
    return mask_types, has_fstring_tokens
def _mask_token_span(masked: list[list[str]], tok_start: tuple,
                     tok_end: tuple) -> None:
    (srow, scol), (erow, ecol) = tok_start, tok_end
    for row in range(srow, min(erow, len(masked)) + 1):
        chars = masked[row - 1]
        begin = scol if row == srow else 0
        stop = ecol if row == erow else len(chars)
        for col in range(begin, min(stop, len(chars))):
            chars[col] = " "
def _is_masked_token(tok, mask_types: set[int],
                     has_fstring_tokens: bool) -> bool:
    if tok.type not in mask_types:
        return False
    if tok.type == tokenize.STRING and not has_fstring_tokens:
        prefix = re.match(r"[A-Za-z]*", tok.string)
        return not (prefix and "f" in prefix.group().lower())
    return True
def _non_code_token_mask(content: str) -> str | None:
    try:
        mask_types, has_fstring_tokens = _mask_token_types()
        masked = [list(row) for row in content.split("\n")]
        for tok in tokenize.generate_tokens(io.StringIO(content).readline):
            if _is_masked_token(tok, mask_types, has_fstring_tokens):
                _mask_token_span(masked, tok.start, tok.end)
        return "\n".join("".join(chars) for chars in masked)
    except (tokenize.TokenError, SyntaxError, ValueError, IndexError) as _e:
        log_swallowed(__name__, _e, context='_non_code_token_mask:tokenize')
        return None
def _line_starts(content: str) -> list[int]:
    starts = [0]
    pos = content.find("\n")
    while pos != -1:
        starts.append(pos + 1)
        pos = content.find("\n", pos + 1)
    return starts
def _evidence_excluding_spans(evidence: str,
                              spans: list[tuple[int, int]]) -> str:
    parts: list[str] = []
    pos = 0
    for s, e in sorted(spans):
        if e <= s:
            continue
        if s < pos:
            pos = max(pos, e)
            continue
        parts.append(evidence[pos:s])
        parts.append("\n")
        pos = e
    parts.append(evidence[pos:])
    return "".join(parts)
def _binding_from_alias_text(alias_text: str) -> str | None:
    imported, alias = _split_alias_text(alias_text)
    bound = alias if alias is not None else imported.split(".", maxsplit=1)[0]
    if not is_dotted_module_name(imported) or not bound.isidentifier():
        return None
    return bound
_NOQA_F401_RE = re.compile(
    r"\bnoqa\b(?P<codes>\s*:\s*[A-Za-z]+\d+"
    r"(?:\s*,\s*[A-Za-z]+\d+)*)?",
    re.IGNORECASE,
)
def _stmt_has_noqa_f401(stmt_text: str) -> bool:
    try:
        comments = [
            token.string[1:]
            for token in tokenize.generate_tokens(io.StringIO(stmt_text).readline)
            if token.type == tokenize.COMMENT
        ]
    except (tokenize.TokenError, SyntaxError, ValueError, IndexError) as exc:
        log_swallowed(__name__, exc, context="_stmt_has_noqa_f401:tokenize")
        comments = [seg.split("#", 1)[1]
                    for seg in stmt_text.split("\n")
                    if "#" in seg]
    for comment in comments:
        for match in _NOQA_F401_RE.finditer(comment):
            codes = match.group("codes")
            if codes is None or re.search(r"\bF401\b", codes, re.IGNORECASE):
                return True
    return False
def _di_stmt_char_span(node: ast.stmt, starts: list[int],
                       lines: list[str]) -> tuple[int, int]:
    return (starts[node.lineno - 1]
            + byte_col_to_char_col(lines[node.lineno - 1],
                                    node.col_offset),
            starts[node.end_lineno - 1]
            + byte_col_to_char_col(lines[node.end_lineno - 1],
                                    node.end_col_offset))
def _di_stmt_tail_offset(node: ast.stmt, content: str,
                         starts: list[int]) -> int:
    return starts[node.end_lineno] if node.end_lineno < len(starts) else len(content)
def _di_stmt_noqa_exempt(node: ast.stmt, content: str,
                         starts: list[int], lines: list[str]) -> bool:
    stmt_start = starts[node.lineno - 1] + byte_col_to_char_col(
        lines[node.lineno - 1], node.col_offset)
    return _stmt_has_noqa_f401(
        content[stmt_start:_di_stmt_tail_offset(node, content, starts)])
def _di_details(py_file: Path, bindings) -> list[str]:
    return [f"死导入: {py_file.name} 中导入了 '{binding.imported}' 但未使用"
            for binding in bindings]
_NO_REEXPORTS: frozenset[str] = frozenset()
def _annotation_global_names(tree: ast.AST, root) -> frozenset[str]:
    names: set[str] = set()
    parents: dict[int, object] = {}
    children: dict[int, list] = {}
    def _register(table) -> None:
        nested = list(table.get_children())
        children[id(table)] = nested
        for child in nested:
            parents[id(child)] = table
            _register(child)
    def _take_scope_table(table, node):
        if table is None:
            return None
        scope_type = "class" if isinstance(node, ast.ClassDef) else "function"
        nested = children[id(table)]
        for index, child in enumerate(nested):
            if (child.get_name() == node.name
                    and child.get_lineno() == node.lineno
                    and child.get_type() == scope_type):
                return nested.pop(index)
        return None
    def _is_global(table, name: str) -> bool:
        current = table
        allow_class = current.get_type() == "class"
        while current is not None:
            if current.get_type() == "class" and not allow_class:
                current = parents.get(id(current))
                continue
            try:
                symbol = current.lookup(name)
            except KeyError:
                symbol = None
            if symbol is not None:
                if current is root or symbol.is_global():
                    return True
                if not symbol.is_free():
                    return False
            allow_class = False
            current = parents.get(id(current))
        return False
    def _collect(annotation, table) -> None:
        found: set[str] = set()
        collect_annotation_names(annotation, found)
        if table is None:
            names.update(found)
            return
        names.update(name for name in found if _is_global(table, name))
    def _collect_type_params(node, table) -> None:
        for type_param in getattr(node, "type_params", ()):
            _collect(getattr(type_param, "bound", None), table)
            _collect(getattr(type_param, "default", None), table)
    def _visit(node, table) -> None:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            for child in walk_nodes(node.args):
                if isinstance(child, ast.arg):
                    _collect(child.annotation, table)
            _collect(node.returns, table)
            _collect_type_params(node, table)
            nested = _take_scope_table(table, node)
            for stmt in node.body:
                _visit(stmt, nested)
            return
        if isinstance(node, ast.ClassDef):
            for base in node.bases:
                _collect(base, table)
            for keyword_node in node.keywords:
                _collect(keyword_node.value, table)
            _collect_type_params(node, table)
            nested = _take_scope_table(table, node)
            for stmt in node.body:
                _visit(stmt, nested)
            return
        if isinstance(node, ast.AnnAssign):
            _collect(node.annotation, table)
            return
        if hasattr(ast, "TypeAlias") and isinstance(node, ast.TypeAlias):
            _collect_type_params(node, table)
            _collect(node.value, table)
            return
        for child in ast.iter_child_nodes(node):
            _visit(child, table)
    _register(root)
    _visit(tree, root)
    return frozenset(names)
# 绑定来源哨兵：``None`` = 全局名/已解绑，本对象 = 非导入语句绑定，
# 其余情况直接存放 ``Import`` / ``ImportFrom`` AST 节点。
_NON_IMPORT = object()


class _DiScopeScan:
    """AST 死导入判定使用的类体作用域引用扫描器。

    把「读 / 写 / 分支合并」拆成方法：``_read`` / ``_bind`` / ``_join``
    构成状态机，``_scan`` 只做语句分发，具体语句族分别落在
    ``_scan_binding``（绑定类）与 ``_scan_compound``（复合语句类）。
    拆分只为可读性与规模门禁，语义与原闭包实现逐字等价。

    绑定来源（``origin``）三态：``None`` = 全局名/已解绑，
    ``_NON_IMPORT`` = 非导入语句绑定，其余为 ``Import`` / ``ImportFrom`` 节点。
    """

    __slots__ = (
        'tree', 'lexical', 'scoped_names', 'global_names',
        'class_attribute_imports', 'current_class',
        'comprehension_nodes', 'try_nodes')

    def __init__(self, tree: ast.Module) -> None:
        self.tree = tree
        self.lexical = collect_lexical_scope_table(tree)
        self.scoped_names: dict[int, set[str]] = defaultdict(set)
        self.global_names: set[str] = set()
        self.class_attribute_imports: dict[
            tuple[str, str], set[ast.AST]] = defaultdict(set)
        self.current_class: ast.ClassDef | None = None
        self.comprehension_nodes = (
            ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
        self.try_nodes = (ast.Try, getattr(ast, "TryStar", ast.Try))

    def _function_bound(self, name: str) -> bool:
        scope = self.lexical.parent.get(self.current_class)
        while scope is not None:
            if (isinstance(scope, _LAZY_IMPORT_SCOPE_NODES)
                    and name in self.lexical.bound.get(scope, ())):
                return True
            scope = self.lexical.parent.get(scope)
        return False

    def _read(self, state: dict, name: str) -> None:
        for origin in state.get(name, {None}):
            if origin is None:
                if not self._function_bound(name):
                    self.global_names.add(name)
            elif origin is not _NON_IMPORT:
                self.scoped_names[id(origin)].add(name)

    @staticmethod
    def _bind(state: dict, name: str, origin) -> None:
        state[name] = {origin}

    @staticmethod
    def _copy(state: dict) -> dict:
        return {name: set(origins) for name, origins in state.items()}

    @staticmethod
    def _join(states: list[dict]) -> dict:
        names = set().union(*(set(state) for state in states))
        return {
            name: set().union(
                *(state.get(name, {None}) for state in states))
            for name in names
        }

    @staticmethod
    def _replace(state: dict, new_state: dict) -> None:
        state.clear()
        state.update(new_state)

    def _annotation(self, annotation, state: dict) -> None:
        names: set[str] = set()
        collect_annotation_names(annotation, names)
        for name in names:
            self._read(state, name)

    def _type_params(self, node, state: dict) -> None:
        for type_param in getattr(node, "type_params", ()):
            self._annotation(getattr(type_param, "bound", None), state)
            self._annotation(getattr(type_param, "default", None), state)

    def _target(self, target: ast.AST, state: dict,
                origin=_NON_IMPORT) -> None:
        if isinstance(target, ast.Name):
            self._bind(state, target.id, origin)
        elif isinstance(target, ast.Starred):
            self._target(target.value, state, origin)
        elif isinstance(target, (ast.Tuple, ast.List)):
            for element in target.elts:
                self._target(element, state, origin)
        else:
            self._scan(target, state)

    def _branch(self, state: dict, blocks: list[list[ast.stmt]]) -> None:
        states = []
        for block in blocks:
            branch = self._copy(state)
            self._scan_block(block, branch)
            states.append(branch)
        self._replace(state, self._join(states))

    def _scan_class(self, class_node: ast.ClassDef) -> None:
        self.current_class = class_node
        state: dict = {}
        self._scan_block(class_node.body, state)
        for name, origins in state.items():
            for origin in origins:
                if isinstance(origin, (ast.Import, ast.ImportFrom)):
                    self.class_attribute_imports[
                        (class_node.name, name)].add(origin)

    def _scan_block(self, stmts, state: dict) -> None:
        for stmt in stmts:
            self._scan(stmt, state)

    def _scan_function(self, node, state: dict) -> None:
        for decorator in node.decorator_list:
            self._scan(decorator, state)
        self._type_params(node, state)
        for default in node.args.defaults:
            self._scan(default, state)
        for default in node.args.kw_defaults:
            self._scan(default, state)
        for child in walk_nodes(node.args):
            if isinstance(child, ast.arg):
                self._annotation(child.annotation, state)
        self._annotation(node.returns, state)
        self._bind(state, node.name, _NON_IMPORT)

    def _scan(self, node, state: dict) -> None:
        if node is None:
            return
        if self._scan_binding(node, state):
            return
        if self._scan_compound(node, state):
            return
        for child in ast.iter_child_nodes(node):
            self._scan(child, state)

    def _scan_binding(self, node, state: dict) -> bool:
        """绑定类语句（名字 / 函数 / 类 / lambda / 推导式 / 导入 / 赋值）。"""
        if isinstance(node, ast.Name):
            if isinstance(node.ctx, ast.Load):
                self._read(state, node.id)
            elif isinstance(node.ctx, ast.Del):
                self._bind(state, node.id, None)
            else:
                self._bind(state, node.id, _NON_IMPORT)
            return True
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            self._scan_function(node, state)
            return True
        if isinstance(node, ast.ClassDef):
            for decorator in node.decorator_list:
                self._scan(decorator, state)
            self._type_params(node, state)
            for base in node.bases:
                self._scan(base, state)
            for keyword_node in node.keywords:
                self._scan(keyword_node.value, state)
            self._bind(state, node.name, _NON_IMPORT)
            return True
        if isinstance(node, ast.Lambda):
            for default in node.args.defaults:
                self._scan(default, state)
            for default in node.args.kw_defaults:
                self._scan(default, state)
            return True
        if isinstance(node, self.comprehension_nodes):
            if node.generators:
                self._scan(node.generators[0].iter, state)
            return True
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            self.scoped_names.setdefault(id(node), set())
            for alias in node.names:
                bound = import_binding_name(node, alias)
                if bound is not None:
                    self._bind(state, bound, node)
            return True
        if isinstance(node, ast.Assign):
            self._scan(node.value, state)
            for target in node.targets:
                self._target(target, state)
            return True
        if isinstance(node, ast.AnnAssign):
            self._scan(node.value, state)
            self._annotation(node.annotation, state)
            if node.value is not None:
                self._target(node.target, state)
            return True
        if isinstance(node, ast.AugAssign):
            if isinstance(node.target, ast.Name):
                self._read(state, node.target.id)
            else:
                self._scan(node.target, state)
            self._scan(node.value, state)
            if isinstance(node.target, ast.Name):
                self._bind(state, node.target.id, _NON_IMPORT)
            return True
        if isinstance(node, ast.NamedExpr):
            self._scan(node.value, state)
            self._target(node.target, state)
            return True
        if isinstance(node, ast.Delete):
            for target in node.targets:
                self._target(target, state, None)
            return True
        return False

    def _scan_compound(self, node, state: dict) -> bool:
        """复合语句（循环 / 条件 / with / try / match / type 别名）。"""
        if isinstance(node, (ast.For, ast.AsyncFor)):
            self._scan(node.iter, state)
            body = self._copy(state)
            self._target(node.target, body)
            self._scan_block(node.body, body)
            otherwise = self._copy(state)
            self._scan_block(node.orelse, otherwise)
            self._replace(state, self._join([body, otherwise]))
            return True
        if isinstance(node, ast.While):
            self._scan(node.test, state)
            self._branch(state, [node.body, node.orelse])
            return True
        if isinstance(node, ast.If):
            self._scan(node.test, state)
            self._branch(state, [node.body, node.orelse])
            return True
        if isinstance(node, (ast.With, ast.AsyncWith)):
            for item in node.items:
                self._scan(item.context_expr, state)
                if item.optional_vars is not None:
                    self._target(item.optional_vars, state)
            self._scan_block(node.body, state)
            return True
        if isinstance(node, self.try_nodes):
            self._scan_try(node, state)
            return True
        if hasattr(ast, "Match") and isinstance(node, ast.Match):
            self._scan_match(node, state)
            return True
        if hasattr(ast, "TypeAlias") and isinstance(node, ast.TypeAlias):
            self._type_params(node, state)
            self._annotation(node.value, state)
            if isinstance(node.name, ast.Name):
                self._bind(state, node.name.id, _NON_IMPORT)
            return True
        return False

    def _scan_try(self, node, state: dict) -> None:
        base = self._copy(state)
        body = self._copy(state)
        self._scan_block(node.body, body)
        self._scan_block(node.orelse, body)
        paths = [body]
        handler_base = self._join([base, body])
        for handler in node.handlers:
            branch = self._copy(handler_base)
            self._scan(handler.type, branch)
            if handler.name:
                self._bind(branch, handler.name, _NON_IMPORT)
            self._scan_block(handler.body, branch)
            if handler.name:
                self._bind(branch, handler.name, None)
            paths.append(branch)
        self._replace(state, self._join(paths))
        self._scan_block(node.finalbody, state)

    def _scan_match(self, node, state: dict) -> None:
        self._scan(node.subject, state)
        base = self._copy(state)
        paths = [base]
        for case in node.cases:
            branch = self._copy(base)
            self._scan(case.pattern, branch)
            for pattern in walk_nodes(case.pattern):
                capture = None
                if isinstance(pattern, (ast.MatchAs, ast.MatchStar)):
                    capture = pattern.name
                elif isinstance(pattern, ast.MatchMapping):
                    capture = pattern.rest
                if capture:
                    self._bind(branch, capture, _NON_IMPORT)
            self._scan(case.guard, branch)
            self._scan_block(case.body, branch)
            paths.append(branch)
        self._replace(state, self._join(paths))

    @staticmethod
    def _method_receiver(node) -> str | None:
        if any(
                (isinstance(decorator, ast.Name)
                 and decorator.id == 'staticmethod')
                or (isinstance(decorator, ast.Attribute)
                    and decorator.attr == 'staticmethod')
                for decorator in node.decorator_list):
            return None
        params = [*node.args.posonlyargs, *node.args.args]
        return params[0].arg if params else None

    def run(self) -> tuple[dict[int, frozenset[str]], frozenset[str]]:
        method_receivers: dict[ast.AST, tuple[str, str]] = {}
        for class_node in walk_nodes(self.tree):
            if not isinstance(class_node, ast.ClassDef):
                continue
            self._scan_class(class_node)
            for method in class_node.body:
                if not isinstance(method,
                                  (ast.FunctionDef, ast.AsyncFunctionDef)):
                    continue
                receiver = self._method_receiver(method)
                if receiver is not None:
                    method_receivers[method] = (class_node.name, receiver)
        parents = parent_map(self.tree)
        for node in walk_nodes(self.tree):
            if not (isinstance(node, ast.Attribute)
                    and isinstance(node.ctx, ast.Load)
                    and isinstance(node.value, ast.Name)):
                continue
            origins = set(self.class_attribute_imports.get(
                (node.value.id, node.attr), ()))
            current: ast.AST | None = node
            nested_scopes: list[ast.AST] = []
            while current is not None:
                method = method_receivers.get(current)
                if method is not None:
                    class_name, receiver = method
                    if (node.value.id == receiver
                            and not any(
                                receiver in self.lexical.bound.get(scope, ())
                                for scope in nested_scopes)):
                        origins.update(self.class_attribute_imports.get(
                            (class_name, node.attr), ()))
                    break
                if current in self.lexical.bound:
                    nested_scopes.append(current)
                current = parents.get(current)
            for origin in origins:
                self.scoped_names[id(origin)].add(node.attr)
        return ({key: frozenset(value)
                 for key, value in self.scoped_names.items()},
                frozenset(self.global_names))


def _di_unused_bindings(
        bindings, rest: str,
        is_exempt=None,
        reexport_names: frozenset[str] = _NO_REEXPORTS,
        referenced_names: frozenset[str] | None = None,
        reference_stmt_ids: set[int] | None = None,
        scoped_reference_names: Mapping[int, frozenset[str]] | None = None,
) -> list[ImportBinding]:
    def _used(binding: ImportBinding) -> bool:
        if binding.bound in reexport_names:
            return True
        if (scoped_reference_names is not None
                and id(binding.stmt) in scoped_reference_names):
            return binding.bound in scoped_reference_names[id(binding.stmt)]
        if (referenced_names is not None and reference_stmt_ids is not None
                and id(binding.stmt) in reference_stmt_ids):
            return binding.bound in referenced_names
        return re.search(
            rf"\b{re.escape(binding.bound)}\b", rest) is not None
    return unused_import_bindings(bindings, _used, is_exempt)
_INLINED_COMPREHENSIONS = (ast.ListComp, ast.SetComp, ast.DictComp)
def _comprehension_outer_load_names(node: ast.expr) -> set[str]:
    """内联推导式中解析到外层作用域的 Load 名。

    推导式自身绑定（迭代目标、海象赋值）先收集再统一剔除，避免元素表达式
    先于迭代目标被遍历而漏判；lambda 与生成器表达式体是独立作用域，只保留
    在外层求值的默认值、参数注解与首个可迭代对象。
    """
    bound: set[str] = set()
    loads: set[str] = set()
    pending: list[ast.AST] = [node]
    while pending:
        current = pending.pop()
        for child in ast.iter_child_nodes(current):
            if isinstance(child, ast.Name):
                (loads if isinstance(child.ctx, ast.Load)
                 else bound).add(child.id)
                continue
            if isinstance(child, ast.GeneratorExp):
                pending.append(child.generators[0].iter)
                continue
            if isinstance(child, ast.Lambda):
                pending.extend(_scope_header_exprs(child))
                continue
            pending.append(child)
    return loads - bound
def _scope_header_exprs(node) -> list[ast.expr]:
    """函数/lambda 头部中在外层作用域求值的表达式。"""
    args = node.args
    exprs: list[ast.expr] = [*getattr(node, "decorator_list", ())]
    exprs.extend(args.defaults)
    exprs.extend(default for default in args.kw_defaults
                 if default is not None)
    for param in (*args.posonlyargs, *args.args, *args.kwonlyargs,
                  args.vararg, args.kwarg):
        if param is not None and param.annotation is not None:
            exprs.append(param.annotation)
    returns = getattr(node, "returns", None)
    if returns is not None:
        exprs.append(returns)
    exprs.extend(_type_param_exprs(node))
    return exprs
def _type_param_exprs(node) -> list[ast.expr]:
    exprs: list[ast.expr] = []
    for type_param in getattr(node, "type_params", ()):
        for attr in ("bound", "default"):
            value = getattr(type_param, attr, None)
            if value is not None:
                exprs.append(value)
    return exprs
def _module_scope_comprehension_loads(tree: ast.AST) -> set[str]:
    """模块作用域内联推导式的 Load 名。

    CPython ≥3.12 按 PEP 709 内联 list/set/dict 推导式后，模块作用域中元素
    表达式、条件与海象操作数里的引用不再登记到 symtable，须从 AST 补采。
    函数/类体与 lambda 体内由 symtable 子表正确登记，这里只走在外层求值的
    头部表达式，避免函数局部同名参数把真实死导入误判为已使用。
    """
    loads: set[str] = set()
    pending: list[ast.AST] = [tree]
    while pending:
        node = pending.pop()
        if isinstance(node, _INLINED_COMPREHENSIONS):
            loads.update(_comprehension_outer_load_names(node))
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
            pending.extend(_scope_header_exprs(node))
            continue
        if isinstance(node, ast.ClassDef):
            pending.extend(node.decorator_list)
            pending.extend(node.bases)
            pending.extend(keyword.value for keyword in node.keywords)
            pending.extend(_type_param_exprs(node))
            continue
        pending.extend(ast.iter_child_nodes(node))
    return loads
def _di_global_reference_names(
    content: str, filename: str, tree: ast.Module, root=None,
) -> frozenset[str]:
    if root is None:
        root = symtable.symtable(content, filename, "exec")
    def _collect(table) -> set[str]:
        names = {symbol.get_name() for symbol in table.get_symbols()
                 if symbol.is_referenced() and symbol.is_global()}
        for child in table.get_children():
            names.update(_collect(child))
        return names
    return frozenset(_collect(root) | _annotation_global_names(tree, root)
                     | _module_scope_comprehension_loads(tree))
def _di_dead_imports_ast(content: str, evidence: str, py_file: Path,
                         nodes: list[ast.stmt],
                         reexport_names: frozenset[str] = _NO_REEXPORTS,
                         tree: ast.Module | None = None,
                         ) -> list[str]:
    starts = _line_starts(content)
    lines = content.split("\n")
    rest = _evidence_excluding_spans(
        evidence,
        [_di_stmt_char_span(nd, starts, lines) for nd in nodes])
    exempt = {id(nd) for nd in nodes
              if _di_stmt_noqa_exempt(nd, content, starts, lines)}
    referenced_names = None
    reference_stmt_ids = None
    scoped_reference_names = None
    if tree is not None:
        root = symtable.symtable(content, str(py_file), "exec")
        referenced_names = _di_global_reference_names(
            content, str(py_file), tree, root)
        scoped_reference_names, class_global_names = _DiScopeScan(tree).run()
        referenced_names = frozenset(
            referenced_names | class_global_names)
        reference_stmt_ids = (
            {id(node) for node in nodes} - set(scoped_reference_names))
    return _di_details(py_file, _di_unused_bindings(
        iter_import_bindings(nodes), rest,
        lambda binding: id(binding.stmt) in exempt,
        reexport_names, referenced_names, reference_stmt_ids,
        scoped_reference_names))
def _di_regex_excl_spans(content: str, row_spans) -> list[tuple[int, int]]:
    _excl: list[tuple[int, int]] = []
    for _m in iter_import_stmts(content):
        _span = _di_excl_span_for_match(content, _m, row_spans)
        if _span is not None:
            _excl.append(_span)
    return _excl
def _import_names_span(content: str, match) -> tuple[int, int]:
    if match.group("plain") is not None:
        return match.span("plain")
    return (match.end(), _from_import_names_end(content, match.end()))
def _di_excl_span_for_match(content: str, match, row_spans
                            ) -> tuple[int, int] | None:
    if offset_in_string_literal(content, match.start(), row_spans):
        return None
    return (match.start(),
            read_import_names_text(content, _import_names_span(
                content, match))[1])
def _from_import_names_end(content: str, pos: int) -> int:
    newline = content.find("\n", pos)
    semicolon = content.find(";", pos)
    if semicolon != -1 and (newline == -1 or semicolon < newline):
        return semicolon
    return newline if newline != -1 else len(content)
def _di_regex_match_bindings(content: str, match,
                             row_spans) -> list[ImportBinding]:
    if offset_in_string_literal(content, match.start(), row_spans):
        return []
    span = _import_names_span(content, match)
    names_text, _stmt_end, stmt_line_end = read_import_names_text(
        content, span)
    if _stmt_has_noqa_f401(content[span[0]:stmt_line_end]):
        return []
    lineno = content.count("\n", 0, match.start()) + 1
    bindings: list[ImportBinding] = []
    for name in split_import_names(names_text):
        bound = _binding_from_alias_text(name)
        if bound is not None:
            imported = _split_alias_text(name)[0]
            bindings.append(ImportBinding(imported, bound, lineno))
    return bindings
def _di_regex_bindings(content: str, row_spans) -> list[ImportBinding]:
    bindings: list[ImportBinding] = []
    for match in iter_import_stmts(content):
        if (match.group("plain") is None
                and match.group("module") == "__future__"):
            continue
        if _import_match_indented(content, match):
            continue
        bindings.extend(
            _di_regex_match_bindings(content, match, row_spans))
    return bindings
def _di_dead_imports_regex(content: str, evidence: str,
                           py_file: Path,
                           reexport_names: frozenset[str] = _NO_REEXPORTS
                           ) -> list[str]:
    row_spans = string_token_row_spans(content)
    rest = _evidence_excluding_spans(
        evidence, _di_regex_excl_spans(content, row_spans))
    bindings = _di_regex_bindings(content, row_spans)
    return _di_details(py_file, _di_unused_bindings(
        bindings, rest, reexport_names=reexport_names))
def _detect_dead_imports(sp: Path, ctx=None) -> tuple[bool, list[str]]:
    details: list[str] = []
    unreadable = 0
    for py_file in iter_target_py_files(sp, include_tests=True):
        if py_file.name == "__init__.py":
            continue
        content = read_source(str(py_file), ctx)
        if content is None:
            unreadable += 1
            _log.debug("[Topology] 死导入证据缺失,跳过不可读源文件: %s", py_file)
            continue
        evidence = _non_code_token_mask(content)
        if evidence is None:
            evidence = content
        tree = _parse_source(content, str(py_file))
        reexport_names = (frozenset(module_export_names(tree))
                          if tree is not None else frozenset())
        nodes = module_import_stmts(content, str(py_file))
        if nodes is not None:
            details.extend(_di_dead_imports_ast(
                content, evidence, py_file, nodes, reexport_names, tree=tree))
        else:
            details.extend(_di_dead_imports_regex(
                content, evidence, py_file, reexport_names))
    if unreadable:
        _log.warning(
            "[Topology] 死导入扫描覆盖不完整：%d 个源文件不可读已跳过",
            unreadable)
    return bool(details), details
def _loading_chain_error(detail: str) -> dict[str, Any]:
    return {"has_circular": None, "has_dead_import": None,
            "details": [], "status": "error", "error": detail}
def loading_chain_diag(skill_dir: str, ctx=None) -> dict[str, Any]:
    sp = resolve_scan_root(skill_dir)
    if sp is None:
        return _loading_chain_error("技能目录为空路径")
    if not sp.is_dir():
        _log.warning("[Topology] 加载链诊断目标不存在或不是目录: %s", sp)
        return _loading_chain_error(f"技能目录不存在或不是目录: {sp}")
    imports_graph, unreadable = _build_import_graph_with_errors(sp, ctx)
    if unreadable:
        return _loading_chain_error(
            f"{len(unreadable)} 个源文件不可读: {', '.join(unreadable[:5])}")
    has_circular, circular_details = detect_import_cycles(imports_graph)
    has_dead_import, dead_details = _detect_dead_imports(sp, ctx)
    return {
        "has_circular": has_circular,
        "has_dead_import": has_dead_import,
        "details": circular_details + dead_details,
    }

from __future__ import annotations

import ast
import hashlib
import logging
import os
import re
from collections import defaultdict
from collections.abc import Collection, Iterator
from dataclasses import asdict, dataclass, field
from importlib.util import resolve_name as resolve_relative_name
from itertools import combinations
from typing import Any

from jwsgj.diag_shared_ast_nodes import (
    TRY_NODE_TYPES,
    cyclomatic_complexity,
    is_docstring_stmt,
    is_static_method,
    iter_pattern_capture_names,
    iter_unpack_target_names,
    type_checking_body_node_ids,
)
from jwsgj.diag_shared_source_core import (
    SOURCE_READ_PARSE_ERRORS,
    read_source,
    resolve_module_name,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    is_pruned_scan_dir,
    is_py_source_file,
    is_transient_module_name,
    scan_exclude_dirs,
)

SECONDS_PER_DAY = 86400
__all__ = [
    'DEPRECATED_DOC_RE',
    'ArchCoexistenceItem',
    'ArchCoexistenceReport',
    'ArchScanContext',
    'FuncInfo',
    'ModuleInfo',
    'detect_dual_impl_a1',
    'extract_name_stem',
    'iter_module_scope_stmts',
    'iter_own_scope',
    'iter_skill_files',
    'make_func_info',
    'overlap_ratio_of',
    'stem_similarity',
    'version_name_pairs',
]
_log = logging.getLogger(__name__)
DEPRECATED_DOC_RE = re.compile(r'(deprecated|obsolete|已废弃|已弃用)', re.IGNORECASE)
_NAME_STEM_PREFIX_RE = re.compile(
    r'^(old_|new_|legacy_|deprecated_|_old_|_new_|_?v\d+_)', re.IGNORECASE)
_NAME_STEM_SUFFIX_RE = re.compile(
    r'(_old|_new|_v\d+|_legacy|_deprecated|_sync|_async)$', re.IGNORECASE)
if hasattr(ast, "Match"):
    _MATCH_TYPES = (ast.Match,)
    _MATCH_AS_STAR_TYPES = (ast.MatchAs, ast.MatchStar)
    _MATCH_MAPPING_TYPES = (ast.MatchMapping,)
    _MATCH_CASE_TYPES = (ast.match_case,)
else:
    _MATCH_TYPES = ()
    _MATCH_AS_STAR_TYPES = ()
    _MATCH_MAPPING_TYPES = ()
    _MATCH_CASE_TYPES = ()
_OPTIONAL_BINDING_NAME_ATTRS = (
    (ast.ExceptHandler, "name"),
    (_MATCH_AS_STAR_TYPES, "name"),
    (_MATCH_MAPPING_TYPES, "rest"),
)
_SCOPE_FRAME_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)
_NO_BOUND_NAMES: frozenset[str] = frozenset()
_TYPE_ALIAS_TYPES = ((ast.TypeAlias,) if hasattr(ast, "TypeAlias") else ())
_INHERITED_TYPE_PARAMS_MEMO_ATTR = "_arch_coexistence_inherited_type_params"
def _type_param_nodes(node: ast.AST) -> tuple[ast.AST, ...]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return tuple(getattr(node, "type_params", ()))
    return ()
def _type_param_names(nodes: Collection[ast.AST]) -> frozenset[str]:
    return frozenset(
        node.name for node in nodes if isinstance(getattr(node, "name", None), str))
def _inherited_type_param_nodes(node: ast.AST) -> tuple[ast.AST, ...]:
    return tuple(getattr(node, _INHERITED_TYPE_PARAMS_MEMO_ATTR, ()))
def _bound_type_param_nodes(node: ast.AST) -> tuple[ast.AST, ...]:
    return (*_type_param_nodes(node), *_inherited_type_param_nodes(node))
def _child_blocks_of_branch(st) -> list[ast.stmt]:
    return [*st.body, *st.orelse]
def _child_blocks_of_try(st) -> list[ast.stmt]:
    return [*st.body, *st.orelse, *st.finalbody,
            *[hs for h in st.handlers for hs in h.body]]
def _child_blocks_of_with(st) -> list[ast.stmt]:
    return [*st.body]
def _child_blocks_of_match(st) -> list[ast.stmt]:
    return [s for case in st.cases for s in case.body]
_MODULE_SCOPE_CHILD_BLOCKS = (
    ((ast.If, ast.While, ast.For, ast.AsyncFor), _child_blocks_of_branch),
    (TRY_NODE_TYPES, _child_blocks_of_try),
    ((ast.With, ast.AsyncWith), _child_blocks_of_with),
    (_MATCH_TYPES, _child_blocks_of_match),
)
def _module_scope_child_blocks(st):
    for types, extractor in _MODULE_SCOPE_CHILD_BLOCKS:
        if isinstance(st, types):
            return extractor(st)
    return None
def iter_module_scope_stmts(
        stmts: list[ast.stmt],
        excluded_node_ids: Collection[int] = ()):
    for st in stmts:
        if id(st) in excluded_node_ids:
            continue
        yield st
        children = _module_scope_child_blocks(st)
        if children is not None:
            yield from iter_module_scope_stmts(children, excluded_node_ids)
def _iter_module_walrus_names(
        stmt: ast.stmt, excluded_node_ids: Collection[int] = ()):
    stack = [stmt]
    while stack:
        n = stack.pop()
        if id(n) in excluded_node_ids:
            continue
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            stack.extend(n.decorator_list)
            stack.append(n.args)
            if n.returns is not None:
                stack.append(n.returns)
            continue
        if isinstance(n, ast.ClassDef):
            stack.extend(n.decorator_list)
            stack.extend(n.bases)
            stack.extend(n.keywords)
            continue
        if isinstance(n, ast.Lambda):
            stack.append(n.args)
            continue
        if isinstance(n, ast.NamedExpr) and isinstance(n.target, ast.Name):
            yield n.target.id
        stack.extend(ast.iter_child_nodes(n))
def _optional_binding_name(node: ast.AST) -> str | None:
    for types, attr in _OPTIONAL_BINDING_NAME_ATTRS:
        if isinstance(node, types):
            return getattr(node, attr, None)
    return None
def _add_module_path_prefixes(paths: set[str], module_name: str) -> None:
    parts = module_name.split('.')
    for index in range(1, len(parts) + 1):
        paths.add('.'.join(parts[:index]))
def _node_position(node: ast.AST) -> tuple[int, int]:
    return (getattr(node, "lineno", 0), getattr(node, "col_offset", 0))
def _record_module_values(mod_info: ModuleInfo, names, node: ast.AST) -> None:
    position = _node_position(node)
    for name in names:
        mod_info.global_vars.add(name)
        mod_info.value_binding_positions[name] = max(
            mod_info.value_binding_positions.get(name, (-1, -1)), position)
def _import_binding(alias: ast.alias) -> tuple[str, str]:
    local = alias.asname or alias.name.split('.', 1)[0]
    return local, alias.name if alias.asname else local
def _collect_module_import(node: ast.Import, mod_info: ModuleInfo) -> None:
    mod_info.abs_import_count += 1
    for alias in node.names:
        bound, target = _import_binding(alias)
        mod_info.imports.add(bound)
        mod_info.import_aliases[bound] = target
        mod_info.import_alias_positions[bound] = max(
            mod_info.import_alias_positions.get(bound, (-1, -1)),
            _node_position(node))
        _add_module_path_prefixes(mod_info.imports, alias.name)
_FUTURE_IMPORT_MODULE = "__future__"
def _iter_import_from_aliases(node: ast.ImportFrom, file_path: str):
    module_name = node.module or ""
    if node.level > 0:
        resolved_owner = resolve_module_name(file_path)
        is_package = os.path.basename(file_path).lower() == "__init__.py"
        package = (resolved_owner if is_package
                   else resolved_owner.rpartition(".")[0])
        module_name = resolve_relative_name(
            "." * node.level + module_name, package)
    for alias in node.names:
        if alias.name == '*':
            continue
        local = alias.asname or alias.name
        target = f"{module_name}.{alias.name}" if module_name else alias.name
        yield local, target
def _collect_module_import_from(node: ast.ImportFrom, mod_info: ModuleInfo) -> None:
    if node.module:
        if node.level == 0 and node.module == _FUTURE_IMPORT_MODULE:
            return
        _add_module_path_prefixes(mod_info.imports, node.module)
    for local, target in _iter_import_from_aliases(node, mod_info.file_path):
        mod_info.import_aliases[local] = target
        mod_info.import_alias_positions[local] = max(
            mod_info.import_alias_positions.get(local, (-1, -1)),
            _node_position(node))
    if node.level > 0:
        mod_info.rel_import_count += 1
    elif node.module:
        mod_info.abs_import_count += 1
def _collect_module_assignment(node: ast.Assign | ast.AnnAssign | ast.AugAssign,
                                mod_info: ModuleInfo) -> None:
    if isinstance(node, ast.AnnAssign):
        if isinstance(node.target, ast.Name) and node.value is not None:
            _record_module_values(mod_info, (node.target.id,), node)
        return
    if isinstance(node, ast.AugAssign):
        _record_module_values(
            mod_info, iter_unpack_target_names(node.target), node)
        return
    _record_module_values(
        mod_info, iter_unpack_target_names(node.targets), node)
def _binding_names_of_with(node: ast.With | ast.AsyncWith):
    for item in node.items:
        if item.optional_vars is not None:
            yield from iter_unpack_target_names(item.optional_vars)
def _binding_names_of_try(node):
    for handler in node.handlers:
        if handler.name:
            yield handler.name
def _binding_names_of_match(node):
    for case in node.cases:
        yield from iter_pattern_capture_names(case.pattern)
_BINDING_NAMES_DISPATCH = (
    ((ast.For, ast.AsyncFor), lambda node: iter_unpack_target_names(node.target)),
    ((ast.With, ast.AsyncWith), _binding_names_of_with),
    (TRY_NODE_TYPES, _binding_names_of_try),
    (_MATCH_TYPES, _binding_names_of_match),
)
def _iter_module_binding_names(node: ast.stmt):
    for types, extractor in _BINDING_NAMES_DISPATCH:
        if isinstance(node, types):
            yield from extractor(node)
            return
def _collect_module_binding(
        node, mod_info: ModuleInfo,
        excluded_node_ids: Collection[int] = ()) -> None:
    _record_module_values(
        mod_info, _iter_module_walrus_names(node, excluded_node_ids), node)
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        position = _node_position(node)
        mod_info.value_binding_positions[node.name] = max(
            mod_info.value_binding_positions.get(node.name, (-1, -1)), position)
    if isinstance(node, ast.Import):
        _collect_module_import(node, mod_info)
        return
    if isinstance(node, ast.ImportFrom):
        _collect_module_import_from(node, mod_info)
        return
    if isinstance(node, ast.Delete):
        _record_module_values(
            mod_info, iter_unpack_target_names(node.targets), node)
        return
    if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
        _collect_module_assignment(node, mod_info)
        return
    if _TYPE_ALIAS_TYPES and isinstance(node, _TYPE_ALIAS_TYPES):
        _record_module_values(mod_info, _bound_names_of(node, node), node)
        return
    _record_module_values(mod_info, _iter_module_binding_names(node), node)
def _register_call_style(mod_info: ModuleInfo, is_async: bool) -> None:
    if is_async:
        mod_info.has_async = True
    else:
        mod_info.has_sync = True
@dataclass
class ArchCoexistenceItem:
    strategy: str = ""
    summary: str = ""
    old_files: list[str] = field(default_factory=list)
    new_files: list[str] = field(default_factory=list)
    old_symbols: list[str] = field(default_factory=list)
    new_symbols: list[str] = field(default_factory=list)
    confidence: float = 0.0
    evidence: list[str] = field(default_factory=list)
    suggestion: str = ""
    severity: str = "warning"
    category: str = "arch_coexistence"
@dataclass
class ArchCoexistenceReport:
    skill_dir: str = ""
    total_files_scanned: int = 0
    items: list[ArchCoexistenceItem] = field(default_factory=list)
    by_strategy: dict[str, int] = field(default_factory=dict)
    errors: list[str] = field(default_factory=list)
    @property
    def total_items(self) -> int:
        return len(self.items)
    def to_dict(self) -> dict[str, Any]:
        return {
            "skill_dir": self.skill_dir,
            "total_files_scanned": self.total_files_scanned,
            "total_items": self.total_items,
            "by_strategy": dict(self.by_strategy),
            "items": [asdict(it) for it in self.items],
            "errors": self.errors,
        }
@dataclass
class FuncInfo:
    name: str
    qualified_name: str
    file_path: str
    lineno: int
    end_lineno: int
    is_async: bool = False
    is_public: bool = False
    class_name: str = ""
    params: list[str] = field(default_factory=list)
    return_annotation: str | None = None
    decorators: list[str] = field(default_factory=list)
    docstring: str | None = None
    body_hash: str = ""
    accessed_globals: set[str] = field(default_factory=set)
    called_functions: set[str] = field(default_factory=set)
    direct_called_functions: set[str] = field(default_factory=set)
    complexity: int = 0
    mtime: float = 0.0
    ast_node: Any = None
    has_try: bool = False
    has_raise: bool = False
@dataclass
class ModuleInfo:
    file_path: str
    module_name: str
    functions: dict[str, FuncInfo] = field(default_factory=dict)
    classes: dict[str, list[FuncInfo]] = field(default_factory=dict)
    class_names: dict[str, str] = field(default_factory=dict)
    imports: set[str] = field(default_factory=set)
    import_aliases: dict[str, str] = field(default_factory=dict)
    global_vars: set[str] = field(default_factory=set)
    rel_import_count: int = 0
    abs_import_count: int = 0
    has_async: bool = False
    has_sync: bool = False
    mtime: float = 0.0
    import_alias_positions: dict[str, tuple[int, int]] = field(default_factory=dict)
    value_binding_positions: dict[str, tuple[int, int]] = field(default_factory=dict)
    class_positions: dict[str, tuple[int, int]] = field(default_factory=dict)
    class_value_binding_positions: dict[str, dict[str, tuple[int, int]]] = field(
        default_factory=dict)
    def iter_class_groups(self) -> Iterator[tuple[str, list[FuncInfo]]]:
        for storage_key, methods in self.classes.items():
            yield self.class_names.get(storage_key, storage_key), methods
def _is_scanned_py(fname: str) -> bool:
    return (is_py_source_file(fname)
            and not fname.startswith('.')
            and not is_transient_module_name(fname))
def _package_prefix_of(skill_dir: str) -> str:
    root_init = os.path.join(skill_dir, "__init__.py")
    if not os.path.isfile(root_init):
        return ""
    resolved = resolve_module_name(root_init)
    return f"{resolved}." if resolved else ""
def _read_scan_text(fpath: str) -> str:
    source = read_source(fpath)
    if source is None:
        raise OSError(f"源码不可读: {fpath}")
    return source
@dataclass(frozen=True)
class _OwnScopeFacts:
    complexity: int
    called_functions: frozenset[str]
    direct_called_functions: frozenset[str]
    has_try: bool
    has_raise: bool
def _scan_own_scope_facts(node: ast.AST) -> _OwnScopeFacts:
    called: set[str] = set()
    direct_called: set[str] = set()
    has_try = False
    has_raise = False
    for child in iter_own_scope(node):
        if isinstance(child, TRY_NODE_TYPES):
            has_try = True
        elif isinstance(child, ast.Raise):
            has_raise = True
        if isinstance(child, ast.Call):
            func = child.func
            if isinstance(func, ast.Name):
                called.add(func.id)
                direct_called.add(func.id)
            elif isinstance(func, ast.Attribute):
                called.add(func.attr)
    return _OwnScopeFacts(
        complexity=cyclomatic_complexity(node, iter_own_scope),
        called_functions=frozenset(called),
        direct_called_functions=frozenset(direct_called),
        has_try=has_try, has_raise=has_raise)
def _extract_body_hash(node: ast.AST) -> str:
    try:
        body = list(getattr(node, "body", ()))
        if body and is_docstring_stmt(body[0]):
            body = body[1:]
        dumped = ast.dump(
            ast.Module(body=body, type_ignores=[]),
            annotate_fields=True, include_attributes=False)
        return hashlib.md5(dumped.encode(), usedforsecurity=False).hexdigest()[:16]
    except Exception as e:  # noqa: BLE001
        _log.warning("[ArchCoex] 提取body哈希失败,返回空: %s", e)
        return ""
def extract_name_stem(name: str) -> str:
    current = name
    while True:
        stripped = _NAME_STEM_PREFIX_RE.sub('', current)
        stripped = _NAME_STEM_SUFFIX_RE.sub('', stripped)
        if stripped == current:
            return stripped
        current = stripped
def _ngrams(text: str, n: int = 2) -> set[str]:
    padded = f"_{text}_"
    return {padded[i:i + n] for i in range(len(padded) - n + 1)}
def _name_similarity(a: str, b: str) -> float:
    ga, gb = _ngrams(a), _ngrams(b)
    return len(ga & gb) / len(ga | gb)
def stem_similarity(a: str, b: str) -> float:
    return _name_similarity(extract_name_stem(a), extract_name_stem(b))
def iter_skill_files(skill_dir: str) -> Iterator[tuple[str, str, str]]:
    skip = frozenset(scan_exclude_dirs(skill_dir))
    for root, dirs, files in os.walk(skill_dir):
        dirs[:] = sorted(d for d in dirs if not is_pruned_scan_dir(d, skip))
        for fname in sorted(files):
            fpath = os.path.join(root, fname)
            rel = os.path.relpath(fpath, skill_dir).replace('\\', '/')
            yield fname, fpath, rel
def _unique_key(base: str, occupied: Collection[str],
                first_candidate: str, separator: str) -> str:
    if base not in occupied:
        return base
    candidate = first_candidate
    sequence = 2
    while candidate in occupied:
        candidate = f"{first_candidate}{separator}{sequence}"
        sequence += 1
    return candidate
def _definition_key(base: str, lineno: int,
                    occupied: Collection[str]) -> str:
    return _unique_key(base, occupied, f"{base}@L{lineno}", "-")
def _active_module_import_aliases(mod_info: ModuleInfo) -> dict[str, str]:
    missing = (-1, -1)
    return {
        name: target for name, target in mod_info.import_aliases.items()
        if name not in mod_info.import_alias_positions
        or mod_info.import_alias_positions[name]
        > mod_info.value_binding_positions.get(name, missing)
    }
def _is_active_module_function(fi: FuncInfo, mod_info: ModuleInfo) -> bool:
    if fi.class_name or fi.ast_node is None:
        return True
    latest = mod_info.value_binding_positions.get(fi.name)
    return latest is None or _node_position(fi.ast_node) >= latest
def _is_active_class_group(storage_key: str, mod_info: ModuleInfo) -> bool:
    position = mod_info.class_positions.get(storage_key)
    if position is None:
        return True
    class_name = mod_info.class_names.get(storage_key, storage_key)
    latest = mod_info.value_binding_positions.get(class_name)
    return latest is None or position >= latest
class ArchScanContext:
    def __init__(self, skill_dir: str) -> None:
        self.skill_dir = os.path.abspath(skill_dir)
        self._package_prefix = _package_prefix_of(self.skill_dir)
        self.modules: dict[str, ModuleInfo] = {}
        self.all_functions: dict[str, FuncInfo] = {}
        self.call_graph: dict[str, set[str]] = defaultdict(set)
        self.file_tree_cache: dict[str, ast.AST] = {}
    def _module_name_of(self, rel_path: str) -> str:
        module_name = resolve_module_name(os.path.join(self.skill_dir, rel_path))
        prefix = self._package_prefix
        if prefix:
            root_module_name = prefix[:-1]
            if module_name == root_module_name:
                return root_module_name.rsplit('.', 1)[-1]
            if module_name.startswith(prefix):
                return module_name[len(prefix):]
        return module_name
    def scan_files(self, report: ArchCoexistenceReport) -> None:
        for fname, fpath, rel in iter_skill_files(self.skill_dir):
            if not _is_scanned_py(fname):
                continue
            report.total_files_scanned += 1
            try:
                self._parse_file(fpath, rel)
            except SOURCE_READ_PARSE_ERRORS as _e:
                _log.warning(
                    "arch_coexistence_scan:scan_files: parse_skipped %s: %s",
                    rel, type(_e).__name__, exc_info=True)
                report.errors.append(
                    f"解析 {rel} 失败: {type(_e).__name__}: {_e}")
            except Exception as e:  # noqa: BLE001
                _log.warning("arch_coexistence_scan:scan_files: %s: %s",
                             type(e).__name__, e, exc_info=True)
                report.errors.append(f"解析 {rel} 失败: {e}")
    def _parse_file(self, fpath: str, rel_path: str) -> None:
        tree = ast.parse(_read_scan_text(fpath), filename=fpath)
        mtime = os.path.getmtime(fpath)
        mod_name = self._module_name_of(rel_path)
        mod_info = ModuleInfo(file_path=fpath, module_name=mod_name, mtime=mtime)
        excluded_node_ids = frozenset(type_checking_body_node_ids(tree))
        for node in iter_module_scope_stmts(tree.body, excluded_node_ids):
            _collect_module_binding(node, mod_info, excluded_node_ids)
        self._collect_definitions(tree, mod_info, excluded_node_ids)
        storage_key = _unique_key(
            mod_name, self.modules, f"{mod_name}@{rel_path}", "#")
        self.modules[storage_key] = mod_info
        self.file_tree_cache[fpath] = tree
    def _register_all_function(self, fi: FuncInfo) -> None:
        fi.qualified_name = _definition_key(
            fi.qualified_name, fi.lineno, self.all_functions)
        self.all_functions[fi.qualified_name] = fi
    def _register_module_function(self, node: ast.FunctionDef | ast.AsyncFunctionDef,
                                  mod_info: ModuleInfo) -> None:
        is_async = isinstance(node, ast.AsyncFunctionDef)
        _register_call_style(mod_info, is_async)
        fi = make_func_info(node, mod_info)
        storage_key = _definition_key(node.name, node.lineno, mod_info.functions)
        mod_info.functions[storage_key] = fi
        self._register_all_function(fi)
    def _collect_class_functions(
            self, node: ast.ClassDef, mod_info: ModuleInfo,
            excluded_node_ids: Collection[int] = ()) -> list[FuncInfo]:
        class_funcs: list[FuncInfo] = []
        for item in iter_module_scope_stmts(node.body, excluded_node_ids):
            if not isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            is_async = isinstance(item, ast.AsyncFunctionDef)
            _register_call_style(mod_info, is_async)
            setattr(item, _INHERITED_TYPE_PARAMS_MEMO_ATTR, _type_param_nodes(node))
            fi = make_func_info(item, mod_info, class_name=node.name)
            class_funcs.append(fi)
            self._register_all_function(fi)
        return class_funcs
    def _collect_definitions(
            self, tree: ast.Module, mod_info: ModuleInfo,
            excluded_node_ids: Collection[int] = ()) -> None:
        for node in iter_module_scope_stmts(tree.body, excluded_node_ids):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                self._register_module_function(node, mod_info)
            elif isinstance(node, ast.ClassDef):
                storage_key = _definition_key(
                    node.name, node.lineno, mod_info.classes)
                mod_info.classes[storage_key] = self._collect_class_functions(
                    node, mod_info, excluded_node_ids)
                mod_info.class_names[storage_key] = node.name
                mod_info.class_positions[storage_key] = _node_position(node)
                mod_info.class_value_binding_positions[storage_key] = (
                    _class_value_binding_positions(
                        node, excluded_node_ids=excluded_node_ids))
    def build_call_index(self) -> None:
        name_to_qnames, qname_to_mod = self._collect_function_owners()
        for qname, fi in self.all_functions.items():
            self._resolve_caller_edges(qname, fi, name_to_qnames, qname_to_mod)
    def _collect_function_owners(
            self) -> tuple[dict[str, list[str]], dict[str, str]]:
        name_to_qnames: dict[str, list[str]] = defaultdict(list)
        qname_to_mod: dict[str, str] = {}
        for mod_name, mod_info in self.modules.items():
            for fi in mod_info.functions.values():
                if _is_active_module_function(fi, mod_info):
                    name_to_qnames[fi.name].append(fi.qualified_name)
                qname_to_mod[fi.qualified_name] = mod_name
            for storage_key, class_funcs in mod_info.classes.items():
                is_active = _is_active_class_group(storage_key, mod_info)
                latest_method_positions: dict[str, tuple[int, int]] = {}
                for fi in class_funcs:
                    if fi.ast_node is not None:
                        latest_method_positions[fi.name] = max(
                            latest_method_positions.get(fi.name, (-1, -1)),
                            _node_position(fi.ast_node))
                for name, position in mod_info.class_value_binding_positions.get(
                        storage_key, {}).items():
                    latest_method_positions[name] = max(
                        latest_method_positions.get(name, (-1, -1)), position)
                for fi in class_funcs:
                    if (is_active and (fi.ast_node is None or _node_position(fi.ast_node)
                                       >= latest_method_positions[fi.name])):
                        name_to_qnames[fi.name].append(fi.qualified_name)
                    qname_to_mod[fi.qualified_name] = mod_name
        return name_to_qnames, qname_to_mod
    def _resolve_caller_edges(self, qname: str, fi: FuncInfo,
                              name_to_qnames: dict[str, list[str]],
                              qname_to_mod: dict[str, str]) -> None:
        caller_mod = qname_to_mod.get(qname)
        if caller_mod is None:
            return
        caller_info = self.modules[caller_mod]
        call_sites = _own_scope_call_sites(fi.ast_node)
        local_binding_events = _local_binding_events(fi.ast_node, fi.file_path)
        external_names = (
            _declared_global_names(fi.ast_node) | _declared_nonlocal_names(fi.ast_node)
            if fi.ast_node is not None else set())
        local_names = {
            name for _position, name, _target in local_binding_events
            if name not in external_names}
        module_import_aliases = _active_module_import_aliases(caller_info)
        for callee_name in fi.called_functions:
            is_direct_call = callee_name in fi.direct_called_functions
            module_import = (
                module_import_aliases.get(callee_name) if is_direct_call else None)
            candidates = name_to_qnames.get(callee_name, [])
            same_module = [
                cand for cand in candidates
                if qname_to_mod[cand] == caller_mod
            ]
            fallback_needed = fi.ast_node is None
            if fi.ast_node is not None:
                for position, site_is_direct, receiver in call_sites.get(callee_name, []):
                    local_import_aliases = _local_binding_state_at(
                        local_binding_events, external_names, position)
                    if not site_is_direct:
                        root = receiver.partition(".")[0]
                        if (root not in ("self", "cls")
                                and ((root in local_names
                                      and root not in local_import_aliases)
                                     or (root in caller_info.global_vars
                                         and root not in module_import_aliases
                                         and root not in caller_info.class_names.values()))):
                            continue
                        import_aliases = {
                            **module_import_aliases, **local_import_aliases}
                        self._resolve_receiver_edges(
                            qname, fi, callee_name, receiver, candidates,
                            same_module, caller_info, import_aliases)
                        continue
                    local_import = local_import_aliases.get(callee_name)
                    if local_import is None and callee_name in local_names:
                        continue
                    imported_call = local_import or module_import
                    if imported_call is not None:
                        imported_candidates = name_to_qnames.get(
                            imported_call.rpartition(".")[2], [])
                        self._add_import_edges(
                            qname, imported_candidates, imported_call)
                        continue
                    fallback_needed = True
                if not is_direct_call or not fallback_needed:
                    continue
            elif is_direct_call and module_import is not None:
                imported_candidates = name_to_qnames.get(
                    module_import.rpartition(".")[2], [])
                self._add_import_edges(qname, imported_candidates, module_import)
                continue
            if fi.class_name and not is_direct_call:
                same_class = [
                    cand for cand in same_module
                    if self.all_functions[cand].class_name == fi.class_name
                ]
                if same_class:
                    self.call_graph[qname].update(same_class)
                    continue
            module_functions = [
                cand for cand in same_module
                if not self.all_functions[cand].class_name
            ]
            if module_functions:
                self.call_graph[qname].update(module_functions)
            elif (is_direct_call
                  and callee_name in caller_info.value_binding_positions
                  and callee_name not in module_import_aliases):
                continue
            elif len(same_module) == 1 and not (
                    is_direct_call and self.all_functions[same_module[0]].class_name):
                self.call_graph[qname].add(same_module[0])
            elif not same_module:
                cross_module = [
                    cand for cand in candidates
                    if not is_direct_call or not self.all_functions[cand].class_name
                ]
                if len(cross_module) == 1:
                    self.call_graph[qname].add(cross_module[0])
    def _resolve_receiver_edges(
            self, qname: str, fi: FuncInfo, callee_name: str,
            receiver: str, candidates: list[str], same_module: list[str],
            caller_info: ModuleInfo, import_aliases: dict[str, str]) -> None:
        if receiver in ("self", "cls") and fi.class_name:
            same_class = [
                cand for cand in same_module
                if self.all_functions[cand].class_name == fi.class_name
            ]
            self.call_graph[qname].update(same_class)
            return
        root = receiver.partition(".")[0]
        imported = import_aliases.get(root)
        if imported is None:
            if receiver not in caller_info.class_names.values():
                return
            qualified_receiver = f"{caller_info.module_name}.{receiver}"
        elif receiver == imported or receiver.startswith(f"{imported}."):
            qualified_receiver = receiver
        else:
            qualified_receiver = f"{imported}{receiver[len(root):]}"
        expected = f"{qualified_receiver}.{callee_name}"
        self._add_import_edges(qname, candidates, expected)
    def _add_import_edges(self, qname: str, candidates: list[str],
                          imported_name: str) -> None:
        expected_names = {imported_name}
        prefix = self._package_prefix
        if prefix:
            root_name = prefix[:-1].rsplit(".", 1)[-1]
            for package_prefix in (prefix, f"{root_name}."):
                if not imported_name.startswith(package_prefix):
                    continue
                relative_name = imported_name[len(package_prefix):]
                expected_names.add(relative_name)
                expected_names.add(f"{root_name}.{relative_name}")
        self.call_graph[qname].update(
            cand for cand in candidates
            if any(cand == expected or cand.startswith(f"{expected}@L")
                   for expected in expected_names))
    def get_node(self, fi: FuncInfo) -> ast.AST:
        if fi.file_path in self.file_tree_cache:
            return self.file_tree_cache[fi.file_path]
        try:
            tree = ast.parse(_read_scan_text(fi.file_path), filename=fi.file_path)
            self.file_tree_cache[fi.file_path] = tree
            return tree
        except SOURCE_READ_PARSE_ERRORS as e:
            _log.warning("[ArchCoex] 解析失败,回退空AST(不缓存,下次重试): %s: %s", fi.file_path, e)
            return ast.Module(body=[], type_ignores=[])
def _expr_dotted_name(expr: ast.expr) -> str | None:
    if isinstance(expr, ast.Name):
        return expr.id
    if isinstance(expr, ast.Attribute):
        return ast.unparse(expr)
    return None
def _decorator_name(dec: ast.AST) -> str | None:
    target = dec.func if isinstance(dec, ast.Call) else dec
    return _expr_dotted_name(target)
def _extract_decorator_names(node: ast.FunctionDef | ast.AsyncFunctionDef) -> list[str]:
    decorators: list[str] = []
    for dec in (node.decorator_list or []):
        name = _decorator_name(dec)
        if name is not None:
            decorators.append(name)
    return decorators
def _bound_names_of(sub: ast.AST, root: ast.AST) -> set[str]:
    if isinstance(sub, ast.arg):
        return {sub.arg}
    if isinstance(sub, ast.Name) and isinstance(sub.ctx, (ast.Store, ast.Del)):
        return {sub.id}
    if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {sub.name} if sub is not root else set()
    if isinstance(sub, (ast.Import, ast.ImportFrom)):
        return {alias.asname or alias.name.split('.')[0] for alias in sub.names}
    if _TYPE_ALIAS_TYPES and isinstance(sub, _TYPE_ALIAS_TYPES):
        return {sub.name.id} if isinstance(sub.name, ast.Name) else set()
    optional_name = _optional_binding_name(sub)
    return {optional_name} if optional_name else set()
def _function_annotation_parts(node: ast.FunctionDef | ast.AsyncFunctionDef):
    yield from _type_param_nodes(node)
    yield node.args
    if node.returns is not None:
        yield node.returns
def _iter_scope_frame_shallow(node: ast.AST):
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        yield from node.decorator_list
        yield from _function_annotation_parts(node)
        return
    if isinstance(node, ast.ClassDef):
        yield from node.decorator_list
        yield from _type_param_nodes(node)
        yield from node.bases
        yield from node.keywords
        return
    if isinstance(node, ast.Lambda):
        yield node.args
_OWN_SCOPE_MEMO_ATTR = "_arch_coexistence_own_scope"
def iter_own_scope(node: ast.AST):
    cached = getattr(node, _OWN_SCOPE_MEMO_ATTR, None)
    if cached is not None:
        yield from cached
        return
    collected: list[ast.AST] = []
    stack = list(reversed(list(ast.iter_child_nodes(node))))
    while stack:
        current = stack.pop()
        collected.append(current)
        yield current
        if isinstance(current, _SCOPE_FRAME_TYPES):
            children = _iter_scope_frame_shallow(current)
        else:
            children = ast.iter_child_nodes(current)
        stack.extend(reversed(list(children)))
    try:
        setattr(node, _OWN_SCOPE_MEMO_ATTR, tuple(collected))
    except (AttributeError, TypeError) as _memo_err:
        _log.debug(
            "arch_coexistence_scan:iter_own_scope: 缓存不可写，降级直算: %s",
            _memo_err)
def _own_scope_call_sites(
        node: ast.AST | None,
) -> dict[str, list[tuple[tuple[int, int], bool, str]]]:
    if node is None:
        return {}
    sites: dict[str, list[tuple[tuple[int, int], bool, str]]] = defaultdict(list)
    for child in iter_own_scope(node):
        if not isinstance(child, ast.Call):
            continue
        if isinstance(child.func, ast.Name):
            sites[child.func.id].append((_node_position(child), True, ""))
        elif isinstance(child.func, ast.Attribute):
            sites[child.func.attr].append((
                _node_position(child), False, ast.unparse(child.func.value)))
    return sites
def _own_scope_binding_entries(
        node: ast.AST, *, include_imports: bool,
        file_path: str | None = None,
        excluded_node_ids: Collection[int] = ()):
    own_scope_nodes = [
        sub for sub in iter_own_scope(node) if id(sub) not in excluded_node_ids]
    excluded_binding_nodes = {
        id(target)
        for sub in own_scope_nodes if isinstance(sub, ast.comprehension)
        for target in walk_nodes(sub.target)
    }
    excluded_binding_nodes.update(
        id(arg)
        for frame in own_scope_nodes
        if isinstance(frame, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))
        for arg in walk_nodes(frame.args) if isinstance(arg, ast.arg)
    )
    for sub in _bound_type_param_nodes(node):
        if id(sub) not in excluded_node_ids:
            yield sub, sub.name, None
    for sub in own_scope_nodes:
        if id(sub) in excluded_binding_nodes:
            continue
        if isinstance(sub, (ast.Import, ast.ImportFrom)):
            if not include_imports:
                continue
            if isinstance(sub, ast.Import):
                bindings = (_import_binding(alias) for alias in sub.names)
            elif file_path is not None:
                bindings = _iter_import_from_aliases(sub, file_path)
            else:
                bindings = (
                    (name, None) for name in _bound_names_of(sub, node))
        else:
            bindings = ((name, None) for name in _bound_names_of(sub, node))
        for name, target in bindings:
            yield sub, name, target
def _local_binding_events(node: ast.AST | None, file_path: str):
    if node is None:
        return []
    events = [
        (_node_position(sub), name, target)
        for sub, name, target in _own_scope_binding_entries(
            node, include_imports=True, file_path=file_path)
    ]
    events.sort(key=lambda event: event[0])
    return events
def _local_binding_state_at(events, external_names: set[str],
                            position: tuple[int, int] | None = None):
    latest: dict[str, str | None] = {}
    for event_position, name, target in events:
        if position is not None and event_position > position:
            break
        if target is None and name in external_names:
            continue
        latest[name] = target
    return {
        name: target for name, target in latest.items() if target is not None}
def _local_import_aliases(node: ast.AST | None,
                          file_path: str) -> dict[str, str]:
    if node is None:
        return {}
    external_names = _declared_global_names(node) | _declared_nonlocal_names(node)
    return _local_binding_state_at(
        _local_binding_events(node, file_path), external_names)
def _declared_global_names(node: ast.AST) -> set[str]:
    return {name for sub in iter_own_scope(node)
            if isinstance(sub, ast.Global) for name in sub.names}
def _declared_nonlocal_names(node: ast.AST) -> set[str]:
    return {name for sub in iter_own_scope(node)
            if isinstance(sub, ast.Nonlocal) for name in sub.names}
def _own_scope_binding_positions(node: ast.AST, *,
                                 include_imports: bool) -> dict[str, tuple[int, int]]:
    positions: dict[str, tuple[int, int]] = {}
    for sub, name, _target in _own_scope_binding_entries(
            node, include_imports=include_imports):
        positions[name] = max(
            positions.get(name, (-1, -1)), _node_position(sub))
    external_names = _declared_global_names(node) | _declared_nonlocal_names(node)
    for name in external_names:
        positions.pop(name, None)
    return positions
def _own_scope_bound_names(node: ast.AST, *,
                           include_imports: bool = True) -> set[str]:
    return set(_own_scope_binding_positions(
        node, include_imports=include_imports))
def _class_value_binding_positions(
        node: ast.ClassDef, *,
        excluded_node_ids: Collection[int] = ()) -> dict[str, tuple[int, int]]:
    wrapper = ast.Module(body=node.body, type_ignores=[])
    own_nodes = [
        sub for sub in iter_own_scope(wrapper) if id(sub) not in excluded_node_ids]
    bare_annotation_targets = {
        id(sub.target) for sub in own_nodes
        if isinstance(sub, ast.AnnAssign) and sub.value is None
        and isinstance(sub.target, ast.Name)}
    positions: dict[str, tuple[int, int]] = {}
    for sub, name, _target in _own_scope_binding_entries(
            wrapper, include_imports=True,
            excluded_node_ids=excluded_node_ids):
        if id(sub) in bare_annotation_targets:
            continue
        positions[name] = max(
            positions.get(name, (-1, -1)), _node_position(sub))
    external_names = {
        name for sub in own_nodes if isinstance(sub, (ast.Global, ast.Nonlocal))
        for name in sub.names}
    for name in external_names:
        positions.pop(name, None)
    return positions
_COMPREHENSION_TYPES = (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
def _comprehension_target_names(target: ast.AST) -> frozenset[str]:
    return frozenset(
        sub.id for sub in walk_nodes(target)
        if isinstance(sub, ast.Name) and isinstance(sub.ctx, (ast.Store, ast.Del))
    )
def _iter_comprehension_loads(node: ast.AST, bound: frozenset[str],
                             class_bound: frozenset[str] = _NO_BOUND_NAMES):
    scoped = bound
    outer_scope = class_bound
    for generator in node.generators:
        yield from _iter_scope_loads(generator.iter, scoped, outer_scope)
        outer_scope = frozenset()
        target_names = _comprehension_target_names(generator.target)
        yield from _iter_scope_loads(generator.target, scoped | target_names)
        scoped = scoped | target_names
        for condition in generator.ifs:
            yield from _iter_scope_loads(condition, scoped)
    if isinstance(node, ast.DictComp):
        yield from _iter_scope_loads(node.key, scoped)
        yield from _iter_scope_loads(node.value, scoped)
    else:
        yield from _iter_scope_loads(node.elt, scoped)
def _iter_scope_loads(node: ast.AST, bound: frozenset[str],
                     class_bound: frozenset[str] = _NO_BOUND_NAMES):
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        type_params = _type_param_nodes(node)
        annotation_bound = bound | _type_param_names(type_params)
        for decorator in node.decorator_list:
            yield from _iter_scope_loads(decorator, bound, class_bound)
        for outer_part in _function_annotation_parts(node):
            yield from _iter_scope_loads(outer_part, annotation_bound, class_bound)
        inner = frozenset(_own_scope_bound_names(node))
        scoped = ((bound | inner | _declared_nonlocal_names(node))
                  - _declared_global_names(node))
        for statement in node.body:
            yield from _iter_scope_loads(statement, frozenset(scoped))
        return
    if isinstance(node, ast.ClassDef):
        type_params = _type_param_nodes(node)
        type_param_names = _type_param_names(type_params)
        annotation_bound = bound | type_param_names
        for decorator in node.decorator_list:
            yield from _iter_scope_loads(decorator, bound, class_bound)
        for outer_part in (*type_params, *node.bases, *node.keywords):
            yield from _iter_scope_loads(outer_part, annotation_bound, class_bound)
        scoped = ((frozenset(_own_scope_bound_names(node))
                   | _declared_nonlocal_names(node))
                  - _declared_global_names(node))
        outer_bound = ((bound | type_param_names | _declared_nonlocal_names(node))
                       - _declared_global_names(node))
        for statement in node.body:
            yield from _iter_scope_loads(statement, outer_bound, scoped)
        return
    if isinstance(node, ast.Lambda):
        yield from _iter_scope_loads(node.args, bound, class_bound)
        lambda_bound = frozenset(_own_scope_bound_names(node))
        yield from _iter_scope_loads(node.body, bound | lambda_bound)
        return
    if isinstance(node, _COMPREHENSION_TYPES):
        yield from _iter_comprehension_loads(node, bound, class_bound)
        return
    if (isinstance(node, ast.Name)
            and isinstance(node.ctx, (ast.Load, ast.Store))
            and node.id not in bound and node.id not in class_bound):
        yield node.id
    elif (isinstance(node, ast.AugAssign)
          and isinstance(node.target, ast.Name)
          and node.target.id not in bound
          and node.target.id not in class_bound):
        yield node.target.id
    for child in ast.iter_child_nodes(node):
        yield from _iter_scope_loads(child, bound, class_bound)
def _extract_accessed_globals(node: ast.FunctionDef | ast.AsyncFunctionDef) -> set[str]:
    accessed: set[str] = set()
    for decorator in node.decorator_list:
        accessed.update(_iter_scope_loads(decorator, frozenset()))
    annotation_bound = _type_param_names(_bound_type_param_nodes(node))
    for outer_part in _function_annotation_parts(node):
        accessed.update(_iter_scope_loads(outer_part, annotation_bound))
    bound = frozenset(
        _own_scope_bound_names(node) | _declared_nonlocal_names(node))
    for statement in node.body:
        accessed.update(_iter_scope_loads(statement, bound))
    return accessed
def _qualified_name(mod_name: str, name: str, class_name: str) -> str:
    return f"{mod_name}.{class_name}.{name}" if class_name else f"{mod_name}.{name}"
def _function_params(node: ast.FunctionDef | ast.AsyncFunctionDef,
                     class_name: str = "") -> list[str]:
    a = node.args
    positional = (*a.posonlyargs, *a.args)
    receiver = (positional[0] if class_name and positional
                and positional[0].arg in ('self', 'cls')
                and not is_static_method(node) else None)
    args = (*positional, a.vararg, *a.kwonlyargs, a.kwarg)
    return [arg.arg for arg in args if arg is not None and arg is not receiver]
def make_func_info(node: ast.FunctionDef | ast.AsyncFunctionDef,
                    mod_info: ModuleInfo,
                    class_name: str = "") -> FuncInfo:
    name = node.name
    is_async = isinstance(node, ast.AsyncFunctionDef)
    qname = (_qualified_name(mod_info.module_name, name, class_name))
    params = _function_params(node, class_name)
    facts = _scan_own_scope_facts(node)
    return FuncInfo(
        name=name,
        qualified_name=qname,
        file_path=mod_info.file_path,
        lineno=node.lineno,
        end_lineno=getattr(node, 'end_lineno', node.lineno),
        is_async=is_async,
        is_public=not name.startswith('_'),
        class_name=class_name,
        params=params,
        decorators=_extract_decorator_names(node),
        docstring=ast.get_docstring(node),
        return_annotation=ast.unparse(node.returns) if node.returns else None,
        body_hash=_extract_body_hash(node),
        accessed_globals=_extract_accessed_globals(node),
        called_functions=set(facts.called_functions),
        direct_called_functions=set(facts.direct_called_functions),
        complexity=facts.complexity,
        mtime=mod_info.mtime,
        ast_node=node,
        has_try=facts.has_try,
        has_raise=facts.has_raise,
    )
_PAIR_VERSION_PATTERN = re.compile(
    r'_(v\d+|old|new|legacy|deprecated)$', re.IGNORECASE)
_PAIR_PREFIX_PATTERN = re.compile(
    r'^(old_|new_|legacy_|deprecated_|_old_|_new_|_v\d+_|v\d+_)',
    re.IGNORECASE)
_CLASS_VERSION_SUFFIX_RE = re.compile(
    r'(V\d+|_[vV]\d+|(?<![A-Za-z])v\d+|Old|New|Legacy|Deprecated'
    r'|_old|_new|_legacy|_deprecated)$')
_A1_STANDARD_INTERFACE_NAMES: set[str] = {
    '__init__', '__new__', '__repr__', '__str__', '__eq__', '__hash__',
    '__call__', '__len__', '__getitem__', '__setitem__', '__delitem__',
    '__iter__', '__next__', '__contains__', '__bool__', '__enter__',
    '__exit__', '__aenter__', '__aexit__', '__getattr__', '__setattr__',
    'visit', 'generic_visit', 'detect', 'analyze', 'from_dict', 'to_dict',
    'execute', 'run', 'get_source', 'get_ast',
    'register', 'extract', 'enhance', 'summarize', 'optimize',
}
_A1_GENERIC_PREFIX_BLACKLIST = (
    'visit_', '_visit_',
    '_get_call_', '_load_json', '_load_yaml', '_parse_',
    '_compute_', '_format_', '_extract_', '_generate_',
    '_build_', '_score_', '_grade_', '_check_',
)
_A1_RULE_NUM_PATTERN = re.compile(
    r'_[a-z]{2,4}\d+|'
    r'_rule_\d+|_bug_\d+|_detect_issue_\w+\d+$|'
    r'_fix_\w+\d+$|_check_\w+\d+$'
)
_OLD_NAME_MARK_RE = re.compile(
    r'(?:^|[^a-z0-9])(?:old|legacy|deprecated)(?:$|[^a-z0-9])'
    r'|_prev\b|_bak\b')
_NEW_NAME_MARK_RE = re.compile(
    r'(?:^|[^a-z0-9])(?:new)(?:$|[^a-z0-9])|_next\b')
_FUNC_VERSION_NUM_RE = re.compile(
    r'(?:^|_)v(\d+)(?:_|$)', re.IGNORECASE)
def _function_version_number(name_lower: str) -> int | None:
    matched = _FUNC_VERSION_NUM_RE.search(name_lower)
    return int(matched.group(1)) if matched is not None else None
def _class_version_parts(cls_name: str) -> tuple[str, str] | None:
    matched = _CLASS_VERSION_SUFFIX_RE.search(cls_name)
    if matched is None:
        return None
    stem = cls_name[:matched.start()].rstrip('_')
    return (stem, matched.group().lstrip('_')) if stem else None
def _owning_class_scope(fi: FuncInfo) -> str | None:
    if not fi.class_name:
        return None
    scope, sep, _name = fi.qualified_name.rpartition('.')
    return scope if sep and scope else fi.class_name
def _is_weak_pair_noise(fi_a: FuncInfo, fi_b: FuncInfo) -> bool:
    if _is_short_rule_method(fi_a) or _is_short_rule_method(fi_b):
        return True
    if fi_a.file_path == fi_b.file_path:
        return True
    if not fi_a.params or not fi_b.params:
        return True
    return _is_delegating_pair(fi_a, fi_b)
def _is_short_rule_method(fi: FuncInfo) -> bool:
    return fi.name.startswith('check_') and len(fi.name) <= 10
def _is_delegating_pair(fi_a: FuncInfo, fi_b: FuncInfo) -> bool:
    return fi_b.name in fi_a.called_functions or fi_a.name in fi_b.called_functions
def detect_dual_impl_a1(ctx: ArchScanContext, min_conf: float) -> list[ArchCoexistenceItem]:
    _stem_groups: dict[str, list[FuncInfo]] = defaultdict(list)
    for fi in ctx.all_functions.values():
        _stem_groups[extract_name_stem(fi.name).lower()].append(fi)
    items, paired_keys = _emit_a1a_named_items(_stem_groups, min_conf)
    items.extend(_emit_a1b_semantic_items(_stem_groups, min_conf, paired_keys))
    return items
def _partition_a1a_pairs(
        old_new_pairs: list[tuple[FuncInfo, FuncInfo, float, str, str]],
) -> tuple[list[tuple[FuncInfo, FuncInfo, float, str]],
           dict[tuple[str, ...], list[tuple[FuncInfo, FuncInfo, float, str]]]]:
    class_pair_groups: dict[tuple[str, ...], list[tuple[FuncInfo, FuncInfo, float, str]]] = {}
    non_class_pairs: list[tuple[FuncInfo, FuncInfo, float, str]] = []
    for old_fi, new_fi, conf, reason, kind in old_new_pairs:
        if kind == "class_version":
            key = _class_pair_key(old_fi, new_fi)
            class_pair_groups.setdefault(key, []).append((old_fi, new_fi, conf, reason))
        else:
            non_class_pairs.append((old_fi, new_fi, conf, reason))
    return non_class_pairs, class_pair_groups
def _emit_a1a_named_items(stem_groups: dict[str, list[FuncInfo]],
                          min_conf: float) -> tuple[list[ArchCoexistenceItem], set[frozenset[str]]]:
    non_class_pairs, class_pair_groups = _partition_a1a_pairs(
        _find_old_new_pairs(stem_groups))
    items, paired_keys = _emit_a1a_non_class_pairs(non_class_pairs, min_conf)
    cls_items, cls_keys = _emit_a1a_class_version_groups(class_pair_groups, min_conf)
    items.extend(cls_items)
    paired_keys |= cls_keys
    return items, paired_keys
def _old_new_evidence(old_fi: FuncInfo, new_fi: FuncInfo,
                      reason: str) -> list[str]:
    return [f"旧: {old_fi.qualified_name} (line {old_fi.lineno})",
            f"新: {new_fi.qualified_name} (line {new_fi.lineno})",
            f"匹配方式: {reason}"]
def _emit_a1a_non_class_pairs(non_class_pairs: list[tuple[FuncInfo, FuncInfo, float, str]],
                               min_conf: float) -> tuple[list[ArchCoexistenceItem], set[frozenset[str]]]:
    items: list[ArchCoexistenceItem] = []
    paired_keys: set[frozenset[str]] = set()
    for old_fi, new_fi, conf, reason in non_class_pairs:
        if conf < min_conf:
            continue
        paired_keys.add(frozenset((old_fi.qualified_name, new_fi.qualified_name)))
        items.append(_build_a1_pair_item(
            old_fi, new_fi, conf, reason,
            evidence=_old_new_evidence(old_fi, new_fi, reason),
        ))
    return items, paired_keys
def _emit_a1a_class_version_groups(class_pair_groups: dict[tuple[str, ...], list[tuple[FuncInfo, FuncInfo, float, str]]],
                                    min_conf: float) -> tuple[list[ArchCoexistenceItem], set[frozenset[str]]]:
    items: list[ArchCoexistenceItem] = []
    paired_keys: set[frozenset[str]] = set()
    for group in class_pair_groups.values():
        best = max(group, key=lambda x: x[2])
        old_fi, new_fi, conf, reason = best
        if conf < min_conf:
            continue
        for _o, _n, _, _ in group:
            paired_keys.add(frozenset((_o.qualified_name, _n.qualified_name)))
        other_methods = [o.name for o, _, _, _ in group if o.name != old_fi.name]
        evidence_lines = _old_new_evidence(old_fi, new_fi, reason)
        if other_methods:
            evidence_lines.append(f"同类对其他方法: {', '.join(sorted(set(other_methods)))}")
        items.append(_build_a1_pair_item(
            old_fi, new_fi, conf, reason, evidence=evidence_lines))
    return items, paired_keys
def _a1b_group_excluded(stem: str) -> bool:
    if stem in _A1_STANDARD_INTERFACE_NAMES:
        return True
    if any(stem.startswith(p) for p in _A1_GENERIC_PREFIX_BLACKLIST):
        return True
    if _A1_RULE_NUM_PATTERN.search(stem):
        return True
    return len(stem) < 6
def _a1b_pair_confidence(fi_a: FuncInfo, fi_b: FuncInfo,
                        params_a: set[str], params_b: set[str]) -> tuple[float, float]:
    param_overlap = overlap_ratio_of(params_a, params_b)
    if _is_weak_pair_noise(fi_a, fi_b):
        return 0.0, param_overlap
    if param_overlap < 0.6:
        return 0.0, param_overlap
    return 0.80 * (0.5 + 0.5 * param_overlap), param_overlap
def _emit_a1b_semantic_items(stem_groups: dict[str, list[FuncInfo]],
                             min_conf: float,
                             paired_keys: set[frozenset[str]]) -> list[ArchCoexistenceItem]:
    items: list[ArchCoexistenceItem] = []
    for stem, group_funcs in stem_groups.items():
        if len(group_funcs) < 2 or _a1b_group_excluded(stem):
            continue
        items.extend(_a1b_group_items(group_funcs, min_conf, paired_keys))
    return items
def _a1b_group_items(group_funcs: list[FuncInfo], min_conf: float,
                     paired_keys: set[frozenset[str]]) -> list[ArchCoexistenceItem]:
    items: list[ArchCoexistenceItem] = []
    for fi_a, fi_b in combinations(group_funcs, 2):
        item = _a1b_pair_item(fi_a, fi_b, min_conf, paired_keys)
        if item is not None:
            items.append(item)
    return items
def _a1b_pair_item(fi_a: FuncInfo, fi_b: FuncInfo, min_conf: float,
                   paired_keys: set[frozenset[str]]) -> ArchCoexistenceItem | None:
    if frozenset((fi_a.qualified_name, fi_b.qualified_name)) in paired_keys:
        return None
    params_a, params_b = set(fi_a.params), set(fi_b.params)
    conf, param_overlap = _a1b_pair_confidence(fi_a, fi_b, params_a, params_b)
    if conf < min_conf:
        return None
    old_fi, new_fi = _judge_old_new(fi_a, fi_b)
    return _a1_item(
        old_fi, new_fi, conf,
        summary=f"疑似同职责双实现: {old_fi.qualified_name} ↔ {new_fi.qualified_name}",
        evidence=[
            f"参数重叠度: {param_overlap:.2f}",
            f"A: {old_fi.qualified_name} ({'async' if old_fi.is_async else 'sync'}, params={old_fi.params})",
            f"B: {new_fi.qualified_name} ({'async' if new_fi.is_async else 'sync'}, params={new_fi.params})",
        ],
        suggestion="确认两个实现是否为同一职责的新旧版本，统一后移除旧版",
    )
def _find_old_new_pairs(stem_groups: dict[str, list[FuncInfo]]) -> list[tuple[FuncInfo, FuncInfo, float, str, str]]:
    pairs = []
    for group in stem_groups.values():
        if len(group) < 2:
            continue
        pairs.extend(_pair_group(group))
    return pairs
def _pair_group(group: list[FuncInfo]) -> list[tuple[FuncInfo, FuncInfo, float, str, str]]:
    pairs = []
    for fi_a, fi_b in combinations(group, 2):
        conf, reason, kind = _pair_confidence(fi_a, fi_b)
        if conf > 0:
            old_fi, new_fi = _judge_old_new(fi_a, fi_b)
            pairs.append((old_fi, new_fi, conf, reason, kind))
    return pairs
@dataclass(frozen=True)
class _PairFeatures:
    fi_a: FuncInfo
    fi_b: FuncInfo
    suffix_a: re.Match | None
    suffix_b: re.Match | None
    prefix_a: re.Match | None
    prefix_b: re.Match | None
    cls_ver_a: re.Match | None
    cls_ver_b: re.Match | None
    class_a: str
    class_b: str
    class_stem_a: str
    class_stem_b: str
def _pair_features(fi_a: FuncInfo, fi_b: FuncInfo) -> _PairFeatures:
    class_a = fi_a.class_name or ""
    class_b = fi_b.class_name or ""
    parts_a = _class_version_parts(class_a)
    parts_b = _class_version_parts(class_b)
    return _PairFeatures(
        fi_a=fi_a, fi_b=fi_b,
        suffix_a=_PAIR_VERSION_PATTERN.search(fi_a.name),
        suffix_b=_PAIR_VERSION_PATTERN.search(fi_b.name),
        prefix_a=_PAIR_PREFIX_PATTERN.search(fi_a.name),
        prefix_b=_PAIR_PREFIX_PATTERN.search(fi_b.name),
        cls_ver_a=_CLASS_VERSION_SUFFIX_RE.search(class_a) if parts_a else None,
        cls_ver_b=_CLASS_VERSION_SUFFIX_RE.search(class_b) if parts_b else None,
        class_a=class_a, class_b=class_b,
        class_stem_a=parts_a[0] if parts_a else class_a,
        class_stem_b=parts_b[0] if parts_b else class_b,
    )
_OLD_MARKER_WORDS = frozenset({"old", "legacy", "deprecated"})
_NEW_MARKER_WORD = "new"
_BASE_VERSION_RANK = 1
_VERSION_NUMBER_RANK_OFFSET = 2
_NEW_MARKER_RANK = 10 ** 9
def _marker_kind_text(text: str) -> tuple[str, int]:
    token = text.strip("_").lower()
    version = re.fullmatch(r'v(\d+)', token)
    if version is not None:
        return "num", int(version.group(1))
    if token in _OLD_MARKER_WORDS:
        return "old", 0
    return ("new", 0) if token == _NEW_MARKER_WORD else ("", 0)
def _marker_kind(marker: re.Match[str] | None) -> tuple[str, int]:
    return ("", 0) if marker is None else _marker_kind_text(marker.group())
def _markers_are_dual(marker_a: re.Match[str] | None,
                      marker_b: re.Match[str] | None) -> bool:
    kind_a, num_a = _marker_kind(marker_a)
    kind_b, num_b = _marker_kind(marker_b)
    if not kind_a or not kind_b:
        return False
    if kind_a == "num" and kind_b == "num":
        return num_a != num_b
    if kind_a == kind_b:
        return False
    if kind_a == "num":
        return num_a >= 2 if kind_b == "old" else True
    if kind_b == "num":
        return num_b >= 2 if kind_a == "old" else True
    return True
def _match_dual_version_marker(ft: _PairFeatures) -> tuple[float, str, str] | None:
    for marker_a, marker_b, label, kind in (
        (ft.suffix_a, ft.suffix_b, "版本后缀配对", "version_suffix"),
        (ft.prefix_a, ft.prefix_b, "版本前缀配对", "version_prefix"),
    ):
        if not _markers_are_dual(marker_a, marker_b):
            continue
        old_marker, new_marker = (
            (marker_a, marker_b) if _judge_old_new(ft.fi_a, ft.fi_b)[0] is ft.fi_a
            else (marker_b, marker_a))
        return 0.85, f"{label}: {old_marker.group()} vs {new_marker.group()}", kind
    return None
def _ordered_class_pair(ft: _PairFeatures) -> tuple[str, str]:
    if _judge_old_new(ft.fi_a, ft.fi_b)[0] is ft.fi_a:
        return ft.class_a, ft.class_b
    return ft.class_b, ft.class_a
def _match_class_version_one_sided(ft: _PairFeatures) -> tuple[float, str, str] | None:
    one_sided = (
        (ft.cls_ver_a and not ft.cls_ver_b
         and ft.class_stem_a.lower() == ft.class_b.lower())
        or (ft.cls_ver_b and not ft.cls_ver_a
            and ft.class_stem_b.lower() == ft.class_a.lower()))
    if not one_sided:
        return None
    old_cls, new_cls = _ordered_class_pair(ft)
    return 0.80, f"类名版本配对: {old_cls} vs {new_cls}", "class_version"
def _match_class_version_dual(ft: _PairFeatures) -> tuple[float, str, str] | None:
    if not (ft.cls_ver_a and ft.cls_ver_b
            and ft.class_stem_a.lower() == ft.class_stem_b.lower()):
        return None
    if (_same_version_suffix(ft.cls_ver_a.group(), ft.cls_ver_b.group())
            or _same_marker_family(ft.cls_ver_a.group(), ft.cls_ver_b.group())):
        return None
    old_cls, new_cls = _ordered_class_pair(ft)
    return 0.85, f"类名版本配对: {old_cls} vs {new_cls}", "class_version"
def _match_class_version(ft: _PairFeatures) -> tuple[float, str, str] | None:
    if ft.fi_a.name != ft.fi_b.name or ft.class_a == ft.class_b:
        return None
    return (_match_class_version_one_sided(ft)
            or _match_class_version_dual(ft))
def _match_sync_async(ft: _PairFeatures) -> tuple[float, str, str] | None:
    if ft.fi_a.is_async != ft.fi_b.is_async:
        return 0.75, "sync/async配对", "sync_async"
    return None
def _one_sided_marker(marker_a, marker_b) -> bool:
    return bool(marker_a) != bool(marker_b)
def _match_single_version_mark(ft: _PairFeatures) -> tuple[float, str, str] | None:
    single_suffix = _one_sided_marker(ft.suffix_a, ft.suffix_b)
    single_prefix = _one_sided_marker(ft.prefix_a, ft.prefix_b)
    if not (single_suffix or single_prefix):
        return None
    if _is_weak_pair_noise(ft.fi_a, ft.fi_b):
        return None
    if single_suffix:
        _sfx = ft.suffix_a or ft.suffix_b
        return 0.72, f"单侧版本标记配对: {_sfx.group()}", "single_suffix"
    _pfx = ft.prefix_a or ft.prefix_b
    return 0.72, f"单侧版本前缀配对: {_pfx.group()}", "single_prefix"
def _pair_confidence(fi_a: FuncInfo, fi_b: FuncInfo) -> tuple[float, str, str]:
    ft = _pair_features(fi_a, fi_b)
    return (_match_dual_version_marker(ft)
            or _match_class_version(ft)
            or _match_sync_async(ft)
            or _match_single_version_mark(ft)
            or (0.0, "", ""))
def _a1_item(old_fi: FuncInfo, new_fi: FuncInfo, conf: float, *,
             summary: str, evidence: list[str],
             suggestion: str) -> ArchCoexistenceItem:
    return ArchCoexistenceItem(
        strategy="A1",
        summary=summary,
        old_files=[old_fi.file_path],
        new_files=[new_fi.file_path],
        old_symbols=[old_fi.name],
        new_symbols=[new_fi.name],
        confidence=round(conf, 2),
        evidence=evidence,
        suggestion=suggestion,
        severity="warning",
    )
def _build_a1_pair_item(old_fi: FuncInfo, new_fi: FuncInfo, conf: float,
                        reason: str, evidence: list[str]) -> ArchCoexistenceItem:
    return _a1_item(
        old_fi, new_fi, conf,
        summary=f"同职责双实现: {old_fi.qualified_name} ↔ {new_fi.qualified_name} ({reason})",
        evidence=evidence,
        suggestion="确认新实现完全覆盖旧实现后，移除旧版",
    )
def _class_pair_key(old_fi: FuncInfo, new_fi: FuncInfo) -> tuple[str, ...]:
    return tuple(sorted(
        _owning_class_scope(fi) or fi.qualified_name for fi in (old_fi, new_fi)))
def version_name_pairs(class_names: Collection[str]
                        ) -> dict[frozenset[str], tuple[str, str]]:
    pairs: dict[frozenset[str], tuple[str, str]] = {}
    for cls_name in sorted(class_names, key=_version_sort_key):
        parts = _class_version_parts(cls_name)
        if parts is None:
            continue
        stem, suffix = parts
        if stem in class_names and stem != cls_name:
            other_name, other_suffix = stem, ""
        else:
            partner = _find_version_partner(cls_name, stem, suffix, class_names)
            if partner is None:
                continue
            other_name, other_suffix = partner
        key = frozenset((cls_name, other_name))
        if key in pairs:
            continue
        pairs[key] = _order_version_pair(
            cls_name, suffix, other_name, other_suffix)
    return pairs
def _find_version_partner(cls_name: str, stem: str, suffix: str,
                          class_names: Collection[str]) -> tuple[str, str] | None:
    ordered = sorted(set(class_names), key=_version_sort_key)
    current_index = ordered.index(cls_name)
    candidates = []
    for index, other_name in enumerate(ordered):
        if other_name == cls_name:
            continue
        parts = _class_version_parts(other_name)
        if (parts and parts[0] == stem
                and not _same_version_suffix(parts[1], suffix)
                and not _same_marker_family(parts[1], suffix)):
            candidates.append((abs(index - current_index), index,
                               other_name, parts[1]))
    if not candidates:
        return None
    _distance, _index, other_name, other_suffix = min(candidates)
    return other_name, other_suffix
def overlap_ratio_of(left: set, right: set) -> float:
    union = left | right
    if not union:
        return 0.0
    return len(left & right) / len(union)
def _parse_version_number(suffix: str) -> int | None:
    m = re.fullmatch(r'_?[vV](\d+)', suffix)
    return int(m.group(1)) if m else None
def _version_rank(suffix: str) -> int:
    token = (suffix or "").strip("_").lower()
    if token in _OLD_MARKER_WORDS:
        return 0
    if token == _NEW_MARKER_WORD:
        return _NEW_MARKER_RANK
    number = _parse_version_number(suffix)
    if number is not None:
        return _VERSION_NUMBER_RANK_OFFSET + number
    return _BASE_VERSION_RANK
def _version_sort_key(name: str) -> tuple[int, int, str]:
    parts = _class_version_parts(name)
    if parts is None:
        return (_BASE_VERSION_RANK, 0, name)
    return (_version_rank(parts[1]), 0, name)
def _same_marker_family(left: str, right: str) -> bool:
    kind_left, _ = _marker_kind_text(left)
    kind_right, _ = _marker_kind_text(right)
    return kind_left == kind_right and kind_left in ("old", "new")
def _same_version_suffix(left: str, right: str) -> bool:
    if left.lower() == right.lower():
        return True
    left_num = _parse_version_number(left)
    right_num = _parse_version_number(right)
    return left_num is not None and left_num == right_num
def _order_version_pair(cur_name: str, cur_suffix: str,
                        other_name: str, other_suffix: str) -> tuple[str, str]:
    cur_rank = _version_rank(cur_suffix)
    other_rank = _version_rank(other_suffix)
    if cur_rank < other_rank:
        return cur_name, other_name
    if other_rank < cur_rank:
        return other_name, cur_name
    return ((cur_name, other_name) if cur_name <= other_name
            else (other_name, cur_name))
def _judge_old_new(fi_a: FuncInfo, fi_b: FuncInfo) -> tuple[FuncInfo, FuncInfo]:
    score_a = _old_score_of(fi_a, fi_b)
    score_b = _old_score_of(fi_b, fi_a)
    if score_a > score_b:
        return fi_a, fi_b
    if score_b > score_a:
        return fi_b, fi_a
    key_a = (fi_a.file_path, fi_a.qualified_name)
    key_b = (fi_b.file_path, fi_b.qualified_name)
    return (fi_a, fi_b) if key_a <= key_b else (fi_b, fi_a)
def _version_marker_score(fi: FuncInfo, other: FuncInfo) -> float:
    version = _function_version_number(fi.name.lower())
    other_version = _function_version_number(other.name.lower())
    if version is not None and other_version is not None:
        if version < other_version:
            return 3.0
        if version > other_version:
            return -3.0
        return 0.0
    if version is None:
        return 0.0
    if _NEW_NAME_MARK_RE.search(other.name.lower()):
        return 3.0
    return -3.0
def _class_version_rank(fi: FuncInfo) -> tuple[int, bool]:
    parts = _class_version_parts(fi.class_name) if fi.class_name else None
    if parts is None:
        return _BASE_VERSION_RANK, False
    return _version_rank(parts[1]), True
def _cls_version_delta(fi: FuncInfo, other: FuncInfo) -> float:
    rank, marked = _class_version_rank(fi)
    other_rank, other_marked = _class_version_rank(other)
    if rank == other_rank:
        return 0.0
    weight = 3.0 if marked and other_marked else 1.0
    return weight if rank < other_rank else -weight
def _name_mark_score(fi: FuncInfo) -> float:
    name_lower = fi.name.lower()
    score = 0.0
    if _OLD_NAME_MARK_RE.search(name_lower):
        score += 3
    if _NEW_NAME_MARK_RE.search(name_lower):
        score -= 3
    return score
def _mtime_score(fi: FuncInfo, other: FuncInfo) -> float:
    if fi.mtime <= 0 or other.mtime <= 0:
        return 0.0
    if fi.mtime < other.mtime - SECONDS_PER_DAY:
        return 1.0
    if fi.mtime > other.mtime + SECONDS_PER_DAY:
        return -1.0
    return 0.0
def _doc_deprecation_score(fi: FuncInfo) -> float:
    if fi.docstring and DEPRECATED_DOC_RE.search(fi.docstring):
        return 3.0
    return 0.0
def _old_score_of(fi: FuncInfo, other: FuncInfo) -> float:
    score = _name_mark_score(fi)
    score += _version_marker_score(fi, other)
    score += _cls_version_delta(fi, other)
    if fi.is_async:
        score -= 0.5
    score += _mtime_score(fi, other)
    score += _doc_deprecation_score(fi)
    return score

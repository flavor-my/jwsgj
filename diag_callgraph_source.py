from __future__ import annotations  # noqa: I001
import ast
import logging
import os
import sys
import time as _time
from collections.abc import Iterable, Iterator
from dataclasses import dataclass
from typing import Any, ClassVar
from jwsgj.diag_callgraph_collect import ImportAliasCollector
from jwsgj.diag_callgraph_facts import (
    CALLGRAPH_PARSE_FAILURE_EXCS,
    FunctionNode,
    is_entry_point_name,
)
from jwsgj.diag_shared_ast_bindings import ScopeNameResolver
from jwsgj.diag_shared_ast_nodes import (
    FastDispatchNodeVisitor,
    ast_name,
    class_scope,
    cyclomatic_complexity,
    dotted_name,
    is_main_check,
    iter_module_scope_nodes,
    normalize_torn_name,
    parse_source_tree,
    path_to_dotted_module,
)
from jwsgj.diag_shared_ast_surface import (
    iter_all_export_entries,
    module_export_names,
)
from jwsgj.diag_shared_source_core import (
    read_source,
    read_source_with_fingerprint,
)
from jwsgj.log_config import log_swallowed, write_module_run
from jwsgj.runtime_scope import (
    is_diagnosis_out_of_scope,
    is_test_file_path,
    iter_py_files_under,
    prune_scan_dirnames,
    safe_relpath,
    scan_prune_dirs,
    validate_source_paths,
)
logger = logging.getLogger(__name__)
_DEFAULT_INCLUDE_TESTS: bool | None = None
__all__ = [
    "EntryPoint",
    "EntryPointDiscoverer",
    "same_source_file",
]
_PROPERTY_DECORATORS = frozenset({"property", "cached_property"})
_DATACLASS_DECORATORS = frozenset({
    "dataclass", "dataclasses.dataclass", "pydantic.dataclasses.dataclass",
    "define", "attr.define", "attrs.define",
    "frozen", "attr.frozen", "attrs.frozen",
    "mutable", "attr.mutable", "attrs.mutable",
    "attr.s", "attr.attrs", "attr.attributes",
})
_SCOPE_BARRIER_NODES: tuple[type[ast.AST], ...] = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)
def _max_traversable_ast_depth() -> int:
    return max(50, (sys.getrecursionlimit() - 256) // 5)
def _iter_ast_children(node):
    for _field in node._fields:
        value = getattr(node, _field, None)
        if hasattr(value, '_fields'):
            yield value
        elif isinstance(value, list):
            yield from (item for item in value if hasattr(item, '_fields'))
def _ast_nesting_depth(tree) -> int:
    depth = 0
    stack = [(tree, 1)]
    while stack:
        node, d = stack.pop()
        depth = max(depth, d)
        stack.extend((_child, d + 1) for _child in _iter_ast_children(node))
    return depth
def _str_file(value: Any) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, os.PathLike):
        try:
            _fs = os.fspath(value)
        except TypeError as exc:
            logger.debug("路径归一失败 %r: %s", value, exc)
            return ""
        return _fs if isinstance(_fs, str) else ""
    return ""
def _str_name(value: Any) -> str:
    return value if isinstance(value, str) else ""
def _keep_scanned_file(path: str, include_tests: bool | None,
                       project_root: str) -> bool:
    probe = (path if os.path.isabs(path)
             else os.path.join(project_root, path))
    relative = safe_relpath(probe, project_root)
    if (os.path.isabs(relative) or relative == ".."
            or relative.startswith("../")):
        return False
    if include_tests is True:
        return True
    if is_test_file_path(path):
        return False
    return include_tests is False or not is_diagnosis_out_of_scope(
        path, project_root)
def _gather_py_files(source_paths):
    for raw in source_paths:
        path = _str_file(raw)
        if not path:
            logger.warning("[CallGraph] 源路径形态非法: %r", raw)
            continue
        if os.path.isfile(path) and path.lower().endswith(".py"):
            yield os.path.abspath(path)
        elif os.path.isdir(path):
            yield from (os.path.abspath(f) for f in iter_py_files_under(path))
def _read_noncode_text(filepath: str) -> str | None:
    content = read_source(filepath)
    if content is None or "\x00" in content:
        return None
    return content
def _path_key(path: str) -> str:
    if not path:
        return ""
    return os.path.normcase(os.path.normpath(path))
def _real_path_key(path: str) -> str:
    if not path:
        return ""
    return os.path.normcase(os.path.realpath(path))
def _dedupe_paths(paths) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for path in paths:
        key = _real_path_key(path)
        if key in seen:
            continue
        seen.add(key)
        out.append(path)
    return out
def _source_root_module_aliases(
        owner, module_name: str, cache: dict[str, tuple[str, ...]],
) -> tuple[str, ...]:
    normalized = normalize_torn_name(module_name)
    if normalized in cache:
        return cache[normalized]
    parts = normalized.split(".")
    aliases = []
    for cut in range(1, len(parts)):
        source_root = os.path.join(owner.project_root, *parts[:cut])
        if not os.path.isdir(source_root):
            continue
        if os.path.isfile(os.path.join(source_root, "__init__.py")):
            continue
        aliases.append(".".join(parts[cut:]))
    cache[normalized] = tuple(aliases)
    return cache[normalized]
def _record_syntax_error(
        graph, filepath: str,
        exc: SyntaxError | ValueError | RecursionError | MemoryError) -> None:
    if not any(se.get("filepath") == filepath for se in graph.syntax_errors):
        graph.syntax_errors.append({
            "filepath": filepath,
            "line": getattr(exc, "lineno", None),
            "message": str(exc),
        })
def _cache_unparsable(ast_cache: dict, filepath: str, src) -> None:
    ast_cache[filepath] = (src, None)
def _parse_tree_guarded(graph, ast_cache: dict, filepath: str, src: str):
    try:
        return ast.parse(src, filename=filepath)
    except (SyntaxError, ValueError, RecursionError, MemoryError) as e:
        log_swallowed(__name__, e,
                      context=f'_SourceAstCacheMixin._guard_traversable:{type(e).__name__}')
        _record_syntax_error(graph, filepath, e)
        _cache_unparsable(ast_cache, filepath, src)
        return None
def _reject_deep_tree(graph, ast_cache: dict, filepath: str, src) -> tuple:
    _exc = RecursionError(
        f"AST 深度超限({_max_traversable_ast_depth()})，遍历将 RecursionError")
    _record_syntax_error(graph, filepath, _exc)
    _cache_unparsable(ast_cache, filepath, src)
    return (src, None)
class _SourceAstCacheMixin:
    def _depth_within_limit(self, filepath: str, tree) -> bool:
        memo = self._ast_depth_cache
        hit = memo.get(filepath)
        limit = _max_traversable_ast_depth()
        if hit is not None and hit[0] is tree:
            return hit[1] <= limit
        depth = _ast_nesting_depth(tree)
        memo[filepath] = (tree, depth)
        return depth <= limit
    def get_source_and_ast(self, filepath: str):
        if not os.path.isabs(filepath):
            _root = os.path.realpath(self.project_root)
            _norm = os.path.realpath(os.path.join(_root, filepath))
            try:
                _within = (os.path.commonpath(
                    [os.path.normcase(_root), os.path.normcase(_norm)])
                    == os.path.normcase(_root))
            except ValueError:
                _within = False
            if not _within or not os.path.isfile(_norm):
                logger.debug("[CallGraph] 源路径未落在项目根下(按不可读跳过): %s", filepath)
                self._ast_cache[_norm] = (None, None)
                return (None, None)
            filepath = _norm
        cached = self._ast_cache.get(filepath)
        if cached is not None:
            return cached
        if self._ctx is not None:
            return self._get_ctx_channel(filepath)
        return self._get_direct_channel(filepath)
    def _get_ctx_channel(self, filepath: str):
        try:
            src = self._ctx.get_source(filepath)
            tree = (self._ctx.get_ast(filepath)
                    if src is not None else None)
        except Exception as _ctx_e:  # noqa: BLE001 — 缓存通道故障须降级直读
            log_swallowed(__name__, _ctx_e, context=(
                f'_SourceAstCacheMixin._get_ctx_channel:{type(_ctx_e).__name__}'))
            return self._get_direct_channel(filepath)
        if src is None:
            self._ast_cache[filepath] = (None, None)
            return (None, None)
        if tree is None:
            pair = self._guard_traversable(filepath, src)
            if pair[1] is not None:
                _ctx_ast_cache = getattr(self._ctx, "_ast_cache", None)
                if isinstance(_ctx_ast_cache, dict):
                    _ctx_ast_cache[filepath] = pair[1]
            self._ast_cache[filepath] = pair
            return pair
        result = self._guard_traversable(filepath, src, tree)
        self._ast_cache[filepath] = result
        return result
    def _guard_traversable(self, filepath: str, src, tree=None):
        if tree is None:
            tree = _parse_tree_guarded(
                self.graph, self._ast_cache, filepath, src)
            if tree is None:
                return (src, None)
        if self._depth_within_limit(filepath, tree):
            return (src, tree)
        return _reject_deep_tree(
            self.graph, self._ast_cache, filepath, src)
    def _get_direct_channel(self, filepath: str):
        src, _ = read_source_with_fingerprint(filepath)
        if src is None:
            logger.warning("[CallGraph] 源文件读取失败: %s", filepath)
            self._ast_cache[filepath] = (None, None)
            return (None, None)
        result = self._guard_traversable(filepath, src)
        self._ast_cache[filepath] = result
        return result
class _FileInventoryMixin:
    def _collect_source_files(self, source_paths=None) -> list[str]:
        validate_source_paths(source_paths)
        if source_paths is None:
            return self._default_file_list()
        include_tests = self.include_tests
        files = _dedupe_paths(
            path for path in _gather_py_files(source_paths)
            if _keep_scanned_file(
                path, include_tests, self.project_root))
        if source_paths == [self.project_root]:
            self._file_list_cache = files
        return files
    def _default_file_list(self) -> list[str]:
        include_tests = self.include_tests
        if self._ctx is not None:
            return _dedupe_paths(
                f for f in self._ctx.py_files
                if _keep_scanned_file(f, include_tests, self.project_root))
        if self._file_list_cache is not None:
            return self._file_list_cache
        files = _dedupe_paths(
            f for f in _gather_py_files([self.project_root])
            if _keep_scanned_file(f, include_tests, self.project_root))
        self._file_list_cache = files
        return files
    def _scan_target(self, filepath: str):
        _source, tree = self.get_source_and_ast(filepath)
        rel_path = safe_relpath(filepath, self.project_root)
        return tree, rel_path, path_to_dotted_module(rel_path)
    def collect_build_scope_files(self) -> list[str]:
        if self._build_py_files is not None:
            return self._build_py_files
        return self._collect_source_files()
    def collect_callgraph_files(self) -> list[str]:
        scanned = self._scanned_abs
        files = set()
        for fp in self._locatable_function_paths():
            if os.path.isfile(fp) or (
                    scanned is not None and os.path.normpath(fp) in scanned):
                files.add(fp)
        return sorted(files)
    def _locatable_function_paths(self):
        for fnode in self.graph.functions.values():
            _fp = getattr(fnode, 'filepath', None)
            if isinstance(_fp, str) and _fp:
                yield os.path.join(self.project_root, _fp)
def _decorator_named(dec_name: str, target: str) -> bool:
    return dec_name == target or dec_name.endswith("." + target)
def _resolve_imported_dotted_name(name: str | None,
                                  import_aliases: dict) -> str | None:
    if not name:
        return name
    head, dot, tail = name.partition(".")
    imported = import_aliases.get(head)
    if not imported:
        return name
    return imported + dot + tail if dot else imported
def _has_property_decorator(decorators) -> bool:
    return any(_decorator_named(d, p)
               for d in decorators for p in _PROPERTY_DECORATORS)
def _decor_line(node) -> int:
    if node.decorator_list:
        return node.decorator_list[0].lineno
    return node.lineno
def _collect_exports_from_imports(node: ast.AST, exports: set[str]) -> None:
    if isinstance(node, ast.Import):
        for alias in node.names:
            exports.add(alias.asname or alias.name.split(".")[0])
        return
    if not isinstance(node, ast.ImportFrom):
        return
    if node.level == 0 and node.module == '__future__':
        return
    for alias in node.names:
        if alias.name != '*':
            exports.add(alias.asname or alias.name)
def _collect_all_exports(tree: ast.Module) -> set[str]:
    exports = set(module_export_names(tree))
    for node in iter_module_scope_nodes(tree, descend_classes=False):
        _collect_exports_from_imports(node, exports)
    return exports
class _FileScanContext:
    def __init__(self, filepath: str, module_name: str, all_exports) -> None:
        self.filepath = filepath
        self.module_name = module_name
        self.all_exports = all_exports
class _DefCollector(FastDispatchNodeVisitor):
    def __init__(self, scan: _FileScanContext, graph, file_symbols,
                 import_aliases=None) -> None:
        self.scan = scan
        self.graph = graph
        self.file_symbols = file_symbols
        self.import_aliases: dict = import_aliases or {}
        self._current_class: str | None = None
        self._class_path: str = ""
    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        parent_path = self._class_path
        self._class_path = (f"{parent_path}.{node.name}"
                            if parent_path else node.name)
        try:
            with class_scope(self, node):
                self._current_class = self._class_path
                self._register_dataclass_class(node)
                bases = self._collect_base_names(node)
                full_key = _qualify(self.scan.module_name,
                                    self._class_path)
                self.graph.class_files[full_key] = self.scan.filepath
                if bases:
                    self.graph.class_inheritance[full_key] = bases
                self.generic_visit(node)
        finally:
            self._class_path = parent_path
    def _register_dataclass_class(self, node: ast.ClassDef) -> None:
        for dec in node.decorator_list:
            dec_name = _resolve_imported_dotted_name(
                self._func_decorator_name(dec), self.import_aliases)
            if dec_name in _DATACLASS_DECORATORS:
                full_cls = _qualify(self.scan.module_name, self._class_path)
                self.graph.dataclass_classes.add(full_cls)
                self.graph.dataclass_options[full_cls] = (
                    self._dataclass_boolean_options(dec))
                break
    @staticmethod
    def _dataclass_boolean_options(dec) -> dict[str, bool]:
        if not isinstance(dec, ast.Call):
            return {}
        options = {}
        for keyword in dec.keywords:
            if keyword.arg not in {"init", "eq", "repr"}:
                continue
            value = keyword.value
            if (isinstance(value, ast.Constant)
                    and isinstance(value.value, bool)):
                options[keyword.arg] = value.value
        return options
    def _collect_base_names(self, node: ast.ClassDef) -> list[str]:
        names = [
            _resolve_imported_dotted_name(
                self._base_name_of(base), self.import_aliases)
            for base in node.bases
        ]
        return [name for name in names if name is not None]
    @staticmethod
    def _base_name_of(base) -> str | None:
        while isinstance(base, ast.Subscript):
            base = base.value
        if isinstance(base, ast.Name):
            return base.id
        if isinstance(base, ast.Attribute):
            return ast.unparse(base)
        return None
    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._add_function(node, False)
    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self._add_function(node, True)
    def _add_function(self, node, is_async):
        full_name = node.name
        if self._current_class:
            full_name = f"{self._current_class}.{node.name}"
            self.graph.class_methods[self._current_class].add(node.name)
        exported = self._exported_member(node.name, full_name)
        is_public = not node.name.startswith("_") or exported
        fnode, all_args, decorators = self._snapshot_function(
            node, full_name, is_public, is_async)
        self._register_singledispatch_semantics(full_name, decorators)
        key = _qualify(self.scan.module_name, full_name)
        self._attach_function_metadata(fnode, exported, all_args)
        self.graph.functions[key] = fnode
        self._register_file_symbol(fnode, node)
    def _snapshot_function(self, node, full_name: str, is_public: bool,
                           is_async: bool):
        all_args, params = self._collect_params(node)
        docstring = ast.get_docstring(node)
        complexity = cyclomatic_complexity(node)
        decorators, decorator_args = self._collect_decorator_info(node)
        semantic_decorators = [
            _resolve_imported_dotted_name(name, self.import_aliases)
            for name in decorators]
        is_property = _has_property_decorator(semantic_decorators)
        fnode = FunctionNode(
            name=full_name, filepath=self.scan.filepath,
            start_line=node.lineno, end_line=node.end_lineno or node.lineno,
            is_public=is_public, is_async=is_async,
            is_method=self._current_class is not None,
            class_name=self._current_class,
            decorators=decorators, decorator_args=decorator_args, params=params,
            returns=ast.unparse(node.returns) if node.returns else None,
            docstring=docstring, complexity=complexity,
            is_property=is_property,
            decor_line=_decor_line(node),
        )
        return fnode, all_args, decorators
    def _attach_function_metadata(self, fnode, exported: bool,
                                  all_args) -> None:
        fnode._project_root = self.graph.project_root
        fnode._in_all_exports = exported
        fnode.annotated_params = sum(
            1 for _a in all_args
            if _a.annotation is not None and _a.arg not in ("self", "cls"))
    def _exported_member(self, node_name: str, full_name: str) -> bool:
        exports = self.scan.all_exports
        if self._current_class:
            return full_name in exports
        return node_name in exports
    def _register_file_symbol(self, fnode, node) -> None:
        _file_bucket = self.file_symbols.setdefault(self.scan.filepath, {})
        if self._current_class:
            _file_bucket[f"{self._current_class}.{node.name}"] = fnode
            return
        _file_bucket[node.name] = fnode
    def _collect_params(self, node) -> tuple[list, list[str]]:
        all_args = node.args.posonlyargs + node.args.args
        if node.args.vararg:
            all_args.append(node.args.vararg)
        all_args.extend(node.args.kwonlyargs)
        if node.args.kwarg:
            all_args.append(node.args.kwarg)
        return all_args, [arg.arg for arg in all_args]
    @staticmethod
    def _func_decorator_name(dec) -> str | None:
        if isinstance(dec, ast.Name):
            return dec.id
        if isinstance(dec, ast.Attribute):
            return ast.unparse(dec)
        if isinstance(dec, ast.Call):
            return ast.unparse(dec.func)
        return None
    @staticmethod
    def _decorator_arg_value(arg) -> str | None:
        if isinstance(arg, ast.Name):
            return arg.id
        if isinstance(arg, ast.Attribute):
            return ast.unparse(arg)
        if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
            return arg.value
        return None
    def _decorator_arg_values(self, dec) -> list[str]:
        if not isinstance(dec, ast.Call):
            return []
        return [val for arg in dec.args
                if (val := self._decorator_arg_value(arg)) is not None]
    def _collect_decorator_info(self, node) -> tuple[list[str], dict[str, list[str]]]:
        decorators = []
        decorator_args: dict[str, list[str]] = {}
        for dec in node.decorator_list:
            dec_name = self._func_decorator_name(dec)
            if not dec_name:
                continue
            decorators.append(dec_name)
            dec_args = self._decorator_arg_values(dec)
            if dec_args:
                decorator_args[dec_name] = dec_args
        return decorators, decorator_args
    def _register_singledispatch_semantics(self, full_name: str,
                                            decorators: list[str]) -> None:
        semantic_decorators = [
            _resolve_imported_dotted_name(name, self.import_aliases)
            for name in decorators]
        is_singledispatch = any(
            _decorator_named(d, "singledispatch") for d in semantic_decorators)
        if is_singledispatch:
            key = _qualify(self.scan.module_name, full_name)
            self.graph.singledispatch_funcs.add(key)
        self._record_singledispatch_register(full_name, decorators)
    def _record_singledispatch_register(self, full_name: str, decorators: list[str]) -> None:
        for dec in decorators:
            if not dec.endswith(".register"):
                continue
            base_key = self._resolve_register_base_key(dec[:-9])
            registered_key = _qualify(self.scan.module_name, full_name)
            _reg_list = self.graph.singledispatch_register[base_key]
            if registered_key not in _reg_list:
                _reg_list.append(registered_key)
    def _resolve_register_base_key(self, base_name: str) -> str:
        imported_head = base_name.partition(".")[0]
        resolved_name = _resolve_imported_dotted_name(
            base_name, self.import_aliases)
        local_key = _qualify(self.scan.module_name, resolved_name)
        if local_key in self.graph.functions:
            return local_key
        if imported_head in self.import_aliases:
            return resolved_name
        return local_key
@dataclass
class EntryPoint:
    name: str
    filepath: str
    line: int
    entry_type: str
    callable_name: str | None = None
    module_path: str | None = None
def _first_module_ref(
    nodes: Iterable[ast.AST], mod_names: frozenset,
) -> ast.Name | None:
    return next(
        (n for n in nodes
         if isinstance(n, ast.Name) and n.id in mod_names), None)
def _iter_scope_nodes_preorder(root: ast.AST) -> Iterator[ast.AST]:
    stack: list[ast.AST] = list(reversed(list(ast.iter_child_nodes(root))))
    while stack:
        node = stack.pop()
        yield node
        if isinstance(node, _SCOPE_BARRIER_NODES):
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(node))))
def _iter_main_body_nodes(body: list[ast.stmt]) -> Iterator[ast.AST]:
    for stmt in body:
        yield stmt
        if isinstance(stmt, _SCOPE_BARRIER_NODES):
            continue
        yield from _iter_scope_nodes_preorder(stmt)
def _first_called_module_name(
    nodes: Iterable[ast.AST], mod_names: frozenset,
) -> ast.Name | None:
    for node in nodes:
        for sub in _iter_scope_nodes_preorder(node):
            if not isinstance(sub, ast.Call):
                continue
            func = sub.func
            if isinstance(func, ast.Name) and func.id in mod_names:
                return func
    return None
def _pick_main_block_anchor(anchors: list[str]) -> str | None:
    if not anchors:
        return None
    if len(anchors) == 1:
        return anchors[0]
    entry_named = [
        anchor for anchor in anchors
        if is_entry_point_name(normalize_torn_name(anchor).rsplit(".", 1)[-1])]
    return entry_named[0] if len(entry_named) == 1 else None
def _named_target(target: ast.AST, names: set | frozenset) -> bool:
    return isinstance(target, ast.Name) and target.id in names
def _defined_names_of(node: ast.AST) -> set[str]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {node.name}
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        names: set[str] = set()
        for alias in node.names:
            if alias.name == "*":
                continue
            if alias.asname:
                names.add(alias.asname)
            elif isinstance(node, ast.Import):
                names.add(alias.name.split(".")[0])
            else:
                names.add(alias.name)
        return names
    return set()
class EntryPointDiscoverer:
    _CLI_DICT_NAMES: ClassVar[frozenset] = frozenset({
        "commands", "COMMANDS", "cli_commands", "handlers", "actions"})
    _DECORATOR_SUFFIXES: ClassVar[set] = {"command", "task", "cli", "shared_task"}
    _MAIN_GUARD_CALL_NAMES: ClassVar[frozenset] = frozenset({
        "len", "print", "exit", "isinstance", "getattr", "hasattr",
        "int", "str", "float", "bool", "type", "range", "sorted",
        "open", "enumerate", "min", "max", "sum", "any", "all",
        "set", "list", "dict", "tuple", "repr", "format", "input",
        "basicConfig", "getLogger", "setLevel", "setFormatter",
        "addHandler", "addFilter",
        "debug", "info", "warning", "warn", "error", "exception",
        "critical", "log", "fatal",
        "ArgumentParser", "add_argument", "add_argument_group",
        "add_mutually_exclusive_group", "add_subparsers",
        "parse_args", "parse_known_args",
        "load_dotenv", "getenv", "filterwarnings", "simplefilter",
        "breakpoint", "quit",
    })
    @staticmethod
    def _named_assign_value(
            node: ast.AST, names: set | frozenset) -> ast.expr | None:
        if isinstance(node, ast.Assign):
            targets: list[ast.expr] = node.targets
        elif isinstance(node, (ast.AugAssign, ast.AnnAssign)):
            targets = [node.target]
        else:
            return None
        if not any(_named_target(t, names) for t in targets):
            return None
        return node.value
    @staticmethod
    def _module_defined_names(tree: ast.AST) -> frozenset[str]:
        names: set[str] = set()
        for node in _iter_scope_nodes_preorder(tree):
            names |= _defined_names_of(node)
        return frozenset(names)
    @staticmethod
    def _module_local_callables(tree: ast.AST) -> frozenset[str]:
        return frozenset(
            node.name for node in _iter_scope_nodes_preorder(tree)
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)))
    def __init__(self, project_root: str, ctx: Any = None,
                 include_tests: bool | None = _DEFAULT_INCLUDE_TESTS) -> None:
        self.project_root = os.path.abspath(project_root)
        self._ctx = ctx
        self.include_tests = include_tests
        self._logical_modules: dict[str, str] = {}
    def _resolve_ast(self, filepath: str, rel: str) -> ast.Module | None:
        tree = self._ast_from_ctx(filepath)
        if tree is not None:
            get_source = getattr(self._ctx, "get_source", None)
            if callable(get_source):
                try:
                    source = get_source(filepath)
                except Exception as _ctx_e:  # noqa: BLE001 — 源码缺失时保留既有汇总绑定降级
                    log_swallowed(__name__, _ctx_e, context=(
                        "EntryPointDiscoverer._resolve_ast:"
                        f"{type(_ctx_e).__name__}"))
                else:
                    if isinstance(source, str):
                        tree._jwsgj_source_text = source
            return tree
        return self._ast_from_file(filepath, rel)
    def _ast_from_ctx(self, filepath: str) -> ast.Module | None:
        if self._ctx is None:
            return None
        _get_ast = getattr(self._ctx, "get_ast", None)
        if not callable(_get_ast):
            return None
        try:
            return _get_ast(filepath)
        except Exception as _ctx_e:  # noqa: BLE001 — 缓存通道故障须降级直读
            log_swallowed(__name__, _ctx_e, context=(
                f'EntryPointDiscoverer._ast_from_ctx:{type(_ctx_e).__name__}'))
            return None
    @staticmethod
    def _ast_from_file(filepath: str, rel: str) -> ast.Module | None:
        source, _ = read_source_with_fingerprint(filepath)
        if source is None:
            logger.debug(
                "[business] skipped unreadable file in business entry "
                "discovery: %s", filepath)
            return None
        try:
            tree = ast.parse(source, filename=rel)
        except CALLGRAPH_PARSE_FAILURE_EXCS:
            logger.debug("[business] skipped file in business entry discovery", exc_info=True)
            return None
        tree._jwsgj_source_text = source
        return tree
    def _maybe_collect_cli_entry(
            self, node: ast.AST, mod: str, rel: str,
            out: list[EntryPoint], import_aliases: dict[str, str],
            binding_resolver: ScopeNameResolver | None) -> None:
        if not isinstance(node, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
            return
        _cli_value = self._named_assign_value(node, self._CLI_DICT_NAMES)
        if not isinstance(_cli_value, ast.Dict):
            return
        for key, val in zip(_cli_value.keys, _cli_value.values, strict=True):
            entry = self._cli_entry_of(
                key, val, mod, rel, import_aliases or {}, binding_resolver)
            if entry is not None:
                out.append(entry)
    def _cli_entry_of(self, key: ast.expr | None, val: ast.expr,
                      mod: str, rel: str, import_aliases: dict[str, str],
                      binding_resolver: ScopeNameResolver | None) -> EntryPoint | None:
        if not isinstance(val, ast.Name):
            return None
        if not isinstance(key, ast.Constant) or not isinstance(key.value, str):
            return None
        active_import = (binding_resolver.import_path(val)
                         if binding_resolver is not None else None)
        if active_import:
            imported = self._imported_callable_name(active_import)
            if imported is None:
                return None
            callable_name = imported
        elif binding_resolver is None and val.id in import_aliases:
            imported = self._imported_callable_name(import_aliases[val.id])
            if imported is None:
                return None
            callable_name = imported
        else:
            callable_name = _qualify(mod, val.id)
        return EntryPoint(
            name=f"cli:{key.value}",
            filepath=rel,
            line=val.lineno,
            entry_type="cli_command",
            callable_name=callable_name,
            module_path=mod,
        )
    def _maybe_collect_main_entry(
            self, node: ast.AST, mod_names: frozenset,
            local_callables: frozenset, mod: str, rel: str,
            out: list[EntryPoint],
            import_aliases: dict[str, str],
            local_class_paths: frozenset[str],
            binding_resolver: ScopeNameResolver | None) -> None:
        if not isinstance(node, ast.If):
            return
        if not is_main_check(node.test):
            return
        main_callable = self._find_main_block_callable(
            node, mod, mod_names, local_callables, import_aliases or {},
            local_class_paths, binding_resolver)
        out.append(EntryPoint(
            name=f"main:{rel}",
            filepath=rel,
            line=node.lineno,
            entry_type="main_block",
            callable_name=main_callable,
            module_path=mod,
        ))
    def _find_main_block_callable(
            self, node: ast.If, mod: str,
            mod_names: frozenset, local_callables: frozenset,
            import_aliases: dict[str, str],
            local_class_paths: frozenset[str],
            binding_resolver: ScopeNameResolver | None) -> str | None:
        guard_names = self._MAIN_GUARD_CALL_NAMES
        module_attrs: list[str] = []
        local_anchors: list[str] = []
        for child in _iter_main_body_nodes(node.body):
            if not isinstance(child, ast.Call):
                continue
            anchor = self._anchor_of_call(
                child, guard_names, mod_names, local_callables, mod,
                import_aliases, local_class_paths, binding_resolver)
            if anchor is not None:
                if anchor not in local_anchors:
                    local_anchors.append(anchor)
                continue
            module_attr = self._module_attr_anchor(
                child, guard_names, import_aliases)
            if module_attr is not None and module_attr not in module_attrs:
                module_attrs.append(module_attr)
        return (_pick_main_block_anchor([*module_attrs, *local_anchors])
                or _pick_main_block_anchor(module_attrs)
                or _pick_main_block_anchor(local_anchors))
    def _module_attr_anchor(self, call: ast.Call, guard_names: frozenset,
                            import_aliases: dict[str, str]) -> str | None:
        if not isinstance(call.func, ast.Attribute):
            return None
        if call.func.attr in guard_names:
            return None
        parts = [call.func.attr]
        cur = call.func.value
        while isinstance(cur, ast.Attribute):
            parts.append(cur.attr)
            cur = cur.value
        if not isinstance(cur, ast.Name):
            return None
        target = _str_name(import_aliases.get(cur.id, ""))
        parts.reverse()
        receiver = ".".join([target, *parts[:-1]]) if target else ""
        if not receiver or self._project_module_prefix(receiver) is None:
            return None
        callable_name = _qualify(target, ".".join(parts))
        return self._imported_callable_name(callable_name)
    def _project_relative_name(self, dotted: str) -> str:
        root_name = os.path.basename(self.project_root)
        relative = dotted
        if root_name and dotted == root_name:
            return ""
        if root_name and dotted.startswith(root_name + "."):
            relative = dotted[len(root_name) + 1:]
        parts = relative.split(".")
        for cut in range(len(parts), 0, -1):
            candidate = ".".join(parts[:cut])
            actual = self._logical_modules.get(candidate)
            if actual is not None:
                return ".".join([actual, *parts[cut:]])
        return relative
    def _module_file(self, dotted: str) -> bool:
        candidates = [dotted]
        relative = self._project_relative_name(dotted)
        if relative != dotted:
            candidates.append(relative)
        for candidate in candidates:
            base = os.path.join(
                self.project_root, candidate.replace(".", os.sep))
            if (os.path.isfile(base + ".py")
                    or os.path.isfile(os.path.join(base, "__init__.py"))):
                return True
        return False
    def _project_module_prefix(self, dotted: str) -> str | None:
        parts = dotted.split(".")
        for cut in range(len(parts), 0, -1):
            candidate = ".".join(parts[:cut])
            if self._module_file(candidate):
                return candidate
        return None
    def _package_reexport_target(self, package: str,
                                 member: str) -> str | None:
        candidates = [package]
        relative = self._project_relative_name(package)
        if relative != package:
            candidates.append(relative)
        for candidate in candidates:
            base = os.path.join(
                self.project_root, candidate.replace(".", os.sep))
            filepath = os.path.join(base, "__init__.py")
            if not os.path.isfile(filepath):
                continue
            rel = safe_relpath(filepath, self.project_root)
            tree = self._ast_from_file(filepath, rel)
            if tree is None:
                return None
            aliases: dict = {}
            ImportAliasCollector(rel, aliases).visit(tree)
            return aliases.get(rel, {}).get(member)
        return None
    def _imported_callable_name(self, alias: str) -> str | None:
        target = _str_name(alias)
        if not target or "." not in target:
            return None
        seen = set()
        while target not in seen:
            seen.add(target)
            module_name, _, member = target.rpartition(".")
            if self._project_module_prefix(module_name) is None:
                return target
            mapped = self._package_reexport_target(module_name, member)
            if mapped is None:
                break
            target = mapped
            if "." not in target:
                return None
        if self._module_file(target):
            return None
        module_name, _, _member = target.rpartition(".")
        if self._project_module_prefix(module_name) is not None:
            return self._project_relative_name(target)
        return target
    def _anchor_of_call(self, call: ast.Call, guard_names: frozenset,
                        mod_names: frozenset, local_callables: frozenset,
                        mod: str, import_aliases: dict[str, str],
                        local_class_paths: frozenset[str],
                        binding_resolver: ScopeNameResolver | None) -> str | None:
        callee = ast_name(call) or None
        if callee is None:
            return None
        if isinstance(call.func, ast.Name) and binding_resolver is not None:
            active_import = binding_resolver.import_path(call.func)
            if active_import:
                return self._imported_callable_name(active_import)
        if isinstance(call.func, ast.Name) and callee in local_callables:
            return _qualify(mod, callee)
        if isinstance(call.func, ast.Attribute):
            receiver = dotted_name(call.func.value)
            if receiver in local_class_paths:
                return _qualify(mod, f"{receiver}.{call.func.attr}")
        if callee in guard_names:
            inner = self._wrapped_local_callable(call, local_callables)
            if inner is None:
                return None
            if binding_resolver is not None:
                active_import = binding_resolver.import_path(inner)
                if active_import:
                    return self._imported_callable_name(active_import)
            return _qualify(mod, inner.id)
        if isinstance(call.func, ast.Name) and binding_resolver is None:
            imported = self._imported_callable_name(
                import_aliases.get(callee, ""))
            if imported:
                return imported
        wrapped = self._wrapped_module_ref(call, mod_names)
        if wrapped is None:
            return None
        if binding_resolver is not None:
            active_import = binding_resolver.import_path(wrapped)
            if active_import:
                return self._imported_callable_name(active_import)
        if binding_resolver is None and wrapped.id in import_aliases:
            return self._imported_callable_name(import_aliases[wrapped.id])
        return _qualify(mod, wrapped.id)
    @staticmethod
    def _wrapped_module_ref(
            call: ast.Call, mod_names: frozenset) -> ast.Name | None:
        operands = [*call.args, *(kw.value for kw in call.keywords)]
        wrapped = _first_module_ref(operands, mod_names)
        if wrapped is not None:
            return wrapped
        return _first_called_module_name(operands, mod_names)
    @staticmethod
    def _wrapped_local_callable(
            call: ast.Call, local_callables: frozenset) -> ast.Name | None:
        for operand in [*call.args, *(kw.value for kw in call.keywords)]:
            if isinstance(operand, ast.Name) and operand.id in local_callables:
                return operand
            for sub in _iter_scope_nodes_preorder(operand):
                if (isinstance(sub, ast.Call)
                        and isinstance(sub.func, ast.Name)
                        and sub.func.id in local_callables):
                    return sub.func
        return None
    def _maybe_collect_dec_entry(
            self, node: ast.AST, mod: str, rel: str,
            out: list[EntryPoint], class_name: str | None = None,
            import_aliases: dict[str, str] | None = None) -> None:
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return
        for dec in node.decorator_list:
            target = dec.func if isinstance(dec, ast.Call) else dec
            dec_name = _resolve_imported_dotted_name(
                dotted_name(target), import_aliases or {})
            if dec_name and dec_name.split(".")[-1] in self._DECORATOR_SUFFIXES:
                qualified_name = (
                    f"{class_name}.{node.name}" if class_name else node.name)
                out.append(EntryPoint(
                    name=f"decorator:{qualified_name}",
                    filepath=rel,
                    line=node.lineno,
                    entry_type="decorator_entry",
                    callable_name=_qualify(mod, qualified_name),
                    module_path=mod,
                ))
                break
    def _build_logical_modules(self, files: list[str]) -> dict[str, str]:
        candidates: dict[str, set[str]] = {}
        cache: dict[str, tuple[str, ...]] = {}
        for filepath in files:
            module = self._module_name(filepath)
            for alias in _source_root_module_aliases(self, module, cache):
                candidates.setdefault(alias, set()).add(module)
        return {
            alias: next(iter(modules))
            for alias, modules in candidates.items()
            if len(modules) == 1
        }
    def discover(self, source_paths: list[str] | None = None) -> list[EntryPoint]:
        _t0 = _time.monotonic()
        files = self._collect_files(source_paths)
        module_files = (files if source_paths is None
                        else self._collect_files(None))
        self._logical_modules = self._build_logical_modules(module_files)
        entries: list[EntryPoint] = []
        for filepath in files:
            rel = safe_relpath(filepath, self.project_root)
            tree = self._resolve_ast(filepath, rel)
            if tree is None:
                continue
            entries.extend(self._collect_file_entries(
                tree, rel, self._module_name(filepath)))
        write_module_run(
            "diag_callgraph_source", "EntryPointDiscoverer.discover",
            duration_ms=(_time.monotonic() - _t0) * 1000.0,
            files=len(files), entries=len(entries))
        return entries
    def _collect_file_entries(self, tree: ast.AST, rel: str,
                              mod: str) -> list[EntryPoint]:
        _cli_entries: list[EntryPoint] = []
        _main_entries: list[EntryPoint] = []
        _dec_entries: list[EntryPoint] = []
        mod_names = self._module_defined_names(tree)
        local_callables = self._module_local_callables(tree)
        local_class_paths = frozenset(
            path for path, _start, _end in _collect_class_spans(tree))
        _aliases: dict = {}
        ImportAliasCollector(rel, _aliases).visit(tree)
        import_aliases = _aliases.get(rel, {})
        local_binding_at: dict[str, tuple[int, int]] = {}
        import_binding_at: dict[str, tuple[int, int]] = {}
        for binding_node in _iter_scope_nodes_preorder(tree):
            if isinstance(binding_node, (
                    ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                local_binding_at[binding_node.name] = (
                    binding_node.lineno, binding_node.col_offset)
            elif isinstance(binding_node, (ast.Import, ast.ImportFrom)):
                position = (binding_node.lineno, binding_node.col_offset)
                for bound_name in _defined_names_of(binding_node):
                    import_binding_at[bound_name] = position
        binding_resolver = None
        source_text = getattr(tree, "_jwsgj_source_text", None)
        if isinstance(source_text, str):
            binding_resolver = ScopeNameResolver(
                source_text, rel, tree, set(import_aliases))
        for node in _iter_scope_nodes_preorder(tree):
            self._maybe_collect_cli_entry(
                node, mod, rel, _cli_entries, import_aliases,
                binding_resolver)
            self._maybe_collect_main_entry(
                node, mod_names, local_callables, mod, rel, _main_entries,
                import_aliases, local_class_paths, binding_resolver)
            self._maybe_collect_dec_entry(
                node, mod, rel, _dec_entries,
                import_aliases=import_aliases)
        for registered in _iter_registered_defs(tree):
            if registered.class_name:
                self._maybe_collect_dec_entry(
                    registered.node, mod, rel, _dec_entries,
                    registered.class_name, import_aliases)
        _api_entries: list[EntryPoint] = []
        for api_name, elt_line in iter_all_export_entries(tree):
            callable_name = _qualify(mod, api_name)
            import_at = import_binding_at.get(api_name)
            local_at = local_binding_at.get(api_name)
            if (api_name in import_aliases and import_at is not None
                    and (local_at is None or import_at > local_at)):
                imported = self._imported_callable_name(
                    import_aliases[api_name])
                if imported is not None:
                    callable_name = imported
            _api_entries.append(EntryPoint(
                name=f"api:{api_name}",
                filepath=rel,
                line=elt_line,
                entry_type="public_api",
                callable_name=callable_name,
                module_path=mod,
            ))
        if len(_main_entries) > 1:
            _main_entries = [_main_entries[-1]]
        return _cli_entries + _main_entries + _dec_entries + _api_entries
    def _collect_files(
            self, source_paths: list[str] | None) -> list[str]:
        if source_paths is None:
            source_paths = [self.project_root]
        elif isinstance(source_paths, (str, os.PathLike)):
            source_paths = [source_paths]
        files: list[str] = []
        seen: set[str] = set()
        for raw_path in source_paths:
            p = _str_file(raw_path)
            if not p:
                logger.warning("[business] 入口发现跳过非法路径: %r", raw_path)
                continue
            if os.path.isfile(p) and p.lower().endswith(".py"):
                candidates = [p]
            elif os.path.isdir(p):
                candidates = self._walk_dir_py_files(p)
            else:
                continue
            for candidate in candidates:
                absolute = os.path.abspath(candidate)
                if not _keep_scanned_file(
                        absolute, self.include_tests, self.project_root):
                    continue
                identity = _real_path_key(absolute)
                if identity in seen:
                    continue
                seen.add(identity)
                files.append(absolute)
        return files
    @staticmethod
    def _walk_dir_py_files(path: str) -> list[str]:
        files = []
        skip = scan_prune_dirs(path)
        for root, dirs, fnames in os.walk(path):
            prune_scan_dirnames(dirs, skip)
            dirs.sort()
            files.extend(
                os.path.join(root, fn) for fn in sorted(fnames)
                if fn.lower().endswith(".py") and not fn.startswith("."))
        return files
    def _module_name(self, filepath: str) -> str:
        rel = safe_relpath(filepath, self.project_root)
        return path_to_dotted_module(rel)
def _resolve_source_filepath(filepath: str, call_graph: Any) -> str:
    if not filepath or os.path.isabs(filepath):
        return filepath
    root = getattr(call_graph, "project_root", "") or ""
    return os.path.join(root, filepath) if root else filepath
def same_source_file(left: str, right: str, call_graph: Any) -> bool:
    if not isinstance(left, str) or not isinstance(right, str):
        return False
    if not left or not right:
        return False
    def _identity(value: str) -> str:
        return _real_path_key(_resolve_source_filepath(value, call_graph))
    return _identity(left) == _identity(right)
def _class_spans_for_file(
        filepath: str,
        call_graph: Any,
        cache: dict[str, list[tuple[str, int, int]] | None],
) -> list[tuple[str, int, int]] | None:
    resolved = _resolve_source_filepath(filepath, call_graph)
    key = _path_key(resolved)
    if key in cache:
        return cache[key]
    source, _ = read_source_with_fingerprint(resolved)
    tree = parse_source_tree(source, resolved) if source is not None else None
    if tree is None:
        cache[key] = None
        return None
    spans = _collect_class_spans(tree)
    cache[key] = spans
    return spans
def _collect_class_spans(tree: ast.AST) -> list[tuple[str, int, int]]:
    spans: list[tuple[str, int, int]] = []
    def _walk(node: ast.AST, parent: str) -> None:
        for child in ast.iter_child_nodes(node):
            if isinstance(child, ast.ClassDef):
                path = f"{parent}.{child.name}" if parent else child.name
                spans.append(
                    (path, child.lineno,
                     child.end_lineno or child.lineno))
                _walk(child, path)
            elif isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                    ast.Lambda)):
                continue
            else:
                _walk(child, parent)
    _walk(tree, "")
    return spans
def _parse_source_file(filepath: str, purpose: str) -> ast.AST | None:
    source = read_source(filepath)
    if source is None:
        logger.warning("[XV] %s：源文件读取失败，跳过: %s", purpose, filepath)
        return None
    return parse_source_tree(source, filepath)
def _qualify(prefix: str, name: str) -> str:
    return f"{prefix}.{name}" if prefix else name
@dataclass(frozen=True)
class _RegisteredDef:
    node: ast.AST
    qualname: str
    class_name: str = ""
def _iter_registered_defs(tree: ast.AST) -> Iterator[_RegisteredDef]:
    def walk_body(body: list[ast.stmt], class_name: str):
        for stmt in body:
            if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
                yield _RegisteredDef(
                    stmt,
                    f"{class_name}.{stmt.name}" if class_name else stmt.name,
                    class_name,
                )
            elif isinstance(stmt, ast.ClassDef):
                nested = (f"{class_name}.{stmt.name}"
                          if class_name else stmt.name)
                yield from walk_body(stmt.body, nested)
            else:
                yield from walk_control_flow(stmt, class_name)
    def walk_control_flow(node: ast.AST, class_name: str):
        for child in ast.iter_child_nodes(node):
            if isinstance(child, ast.Lambda):
                continue
            if isinstance(child, ast.stmt):
                yield from walk_body([child], class_name)
            else:
                yield from walk_control_flow(child, class_name)
    yield from walk_body(list(getattr(tree, "body", ()) or ()), "")
logger.info("%s 已加载: %d 项导出", __name__, len(__all__))

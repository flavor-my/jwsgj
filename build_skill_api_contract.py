# ruff: noqa: I001
from __future__ import annotations
import ast
import io
import logging
import os
import posixpath
import re
import tokenize
from collections.abc import Iterable, Iterator
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Any
from jwsgj.diag_antipattern import (
    DeadCodeEliminator,
    FacadeOptimizer,
    LazyImportEliminator,
    StubEliminator,
)
from jwsgj.diag_guard_dirfile import DirFileGuard
from jwsgj.diag_shared_ast_bindings import import_bound_names
from jwsgj.diag_shared_ast_nodes import (
    ast_name,
    is_main_check,
    is_public_name,
    is_type_checking_guard,
    iter_module_stmt_blocks,
    module_level_binding_names,
)
from jwsgj.diag_shared_ast_surface import (
    extract_function_info,
    replay_export_surface,
)
from jwsgj.diag_shared_source_core import (
    read_source_with_fingerprint,
    shared_source_and_tree,
    source_line_count,
)
from jwsgj.diag_types_normalize import signal_bool
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
)
from jwsgj.log_config import log_swallowed, observation_gate
from jwsgj.runtime_scope import (
    PY_SUFFIXES,
    coerce_skill_dir,
    is_out_of_scope_dir,
    is_pruned_scan_dir,
    is_test_dir_name,
    is_test_source_basename,
    is_transient_module_name,
    safe_relpath,
    scan_exclude_dirs,
    scan_prune_dirs,
)
from jwsgj.prevention_scope_facts import walk_nodes
_log = logging.getLogger(__name__)
__all__ = [
    'FunctionCallOptimizer',
    'FunctionOptimizationResult',
    'FunctionSchema',
    'IOSpec',
    'IOStandardizationChecker',
    'IOStandardizationReport',
    'ParameterSpec',
    'SkillApiScanner',
    'build_function_schema',
    'collect_api_names',
    'collect_skill_py_basenames',
    'extract_param_names',
    'extract_py_refs',
    'get_scan_files',
    'has_code_surface',
    'has_scan_files',
    'is_script_only_skill',
    'is_test_infrastructure',
    'iter_scan_function_entries',
    'run_architecture_quality_gate',
    'run_code_quality_gate',
    'run_io_standardization_gate',
    'scan_skill_api',
    'strip_url_tokens',
    'validate_skill_function_schemas',
]
_PY_FILE_GLOB = "*.[pP][yY]"
def _init_has_library_surface(path: Path) -> bool:
    try:
        content = read_source_with_fingerprint(str(path))[0]
        if content is None:
            raise OSError(f"源码不可读: {path}")
        tree = ast.parse(content, filename=str(path))
    except (OSError, PARSE_DEGRADE_EXC) as exc:
        _log.warning("初始化文件库面判定失败，保守按库文件处理: %s: %s", path, exc)
        return True
    statements = list(tree.body)
    if (statements and isinstance(statements[0], ast.Expr)
            and isinstance(statements[0].value, ast.Constant)
            and isinstance(statements[0].value.value, str)):
        statements = statements[1:]
    return any(
        not (isinstance(stmt, ast.ImportFrom) and not stmt.level
             and stmt.module == "__future__")
        for stmt in statements)
def _has_library_paths(paths: list[Path]) -> bool:
    return any(
        path.name != "__init__.py" or _init_has_library_surface(path)
        for path in paths)
def _is_scan_face_dir(name: str, exclude_dirs: frozenset[str] | set[str]) -> bool:
    return (name.lower() in exclude_dirs
            or is_out_of_scope_dir(name)
            or is_test_dir_name(name)
            or is_pruned_scan_dir(name, exclude_dirs))
_SCRIPT_MAIN_GUARD_RE = re.compile(
    r'^[ \t]*if[ \t]+__name__[ \t]*==[ \t]*([\'\"])__main__\1[ \t]*:'
    r'|^[ \t]*if[ \t]+([\'\"])__main__\2[ \t]*==[ \t]*__name__[ \t]*:',
    re.MULTILINE)
_SCRIPT_JSON_FLAGS = frozenset({"--output-json", "--json"})
_SCRIPT_DRY_RUN_FLAGS = frozenset({"--dry-run", "--dry_run"})
_SCRIPT_BOOLEAN_STORE_ACTIONS = frozenset({"store_true", "store_false"})
def _is_test_source_file(name: str) -> bool:
    return name.lower() == "conftest.py" or is_test_source_basename(name)
def _script_boolean_flags(tree: ast.AST | None) -> frozenset[str]:
    if tree is None:
        return frozenset()
    flags: set[str] = set()
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == "add_argument"):
            continue
        action = next((keyword.value for keyword in node.keywords
                       if keyword.arg == "action"), None)
        is_store_boolean = (isinstance(action, ast.Constant)
                            and action.value in _SCRIPT_BOOLEAN_STORE_ACTIONS)
        if not (is_store_boolean or ast_name(action) == "BooleanOptionalAction"):
            continue
        flags.update(
            arg.value for arg in node.args
            if isinstance(arg, ast.Constant)
            and isinstance(arg.value, str) and arg.value.startswith("-"))
    return frozenset(flags)
def _string_token_lines(content: str) -> dict[int, list[tuple[int, int]]]:
    spans: dict[int, list[tuple[int, int]]] = {}
    try:
        for tok in tokenize.generate_tokens(io.StringIO(content).readline):
            if tok.type != tokenize.STRING:
                continue
            (srow, scol), (erow, ecol) = tok.start, tok.end
            for row in range(srow, erow + 1):
                spans.setdefault(row, []).append((
                    scol if row == srow else 0,
                    ecol if row == erow else len(content),
                ))
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc,
            context=f'_string_token_lines:{type(_swallowed_exc).__name__}')
    return spans
def _script_has_main_guard(content: str) -> bool:
    spans = _string_token_lines(content)
    for lineno, line in enumerate(content.split("\n"), start=1):
        match = _SCRIPT_MAIN_GUARD_RE.match(line)
        if match is None:
            continue
        if not any(start <= match.start() < end
                   for start, end in spans.get(lineno, ())):
            return True
    return False
def _module_has_main_guard(tree: ast.AST) -> bool:
    stack = list(getattr(tree, 'body', ()) or ())
    while stack:
        node = stack.pop()
        if isinstance(node, ast.If) and is_main_check(node.test):
            return True
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        for block in iter_module_stmt_blocks(node):
            stack.extend(block)
    return False
def _module_public_api_names(tree: ast.Module) -> set[str]:
    replay = replay_export_surface(tree)
    if replay.declared and replay.exact:
        return set(replay.names)
    import_stmts = (
        stmt for stmt in tree.body
        if not (isinstance(stmt, ast.ImportFrom) and not stmt.level
                and stmt.module == "__future__"))
    names = module_level_binding_names(tree) | import_bound_names(import_stmts)
    return {name for name in names if is_public_name(name)}
class SkillApiScanner:
    @staticmethod
    def scan_skill_dir(skill_dir: str) -> dict[str, Any]:
        skill_dir = coerce_skill_dir(skill_dir)
        result: dict[str, Any] = {
            "skill_dir": skill_dir,
            "files": [],
            "scripts": [],
            "total_lines": 0,
            "total_public_functions": 0,
            "total_public_classes": 0,
            "file_tree": "",
        }
        if not skill_dir:
            return result
        skill_path = Path(skill_dir)
        if not skill_path.is_dir():
            return result
        module_paths = SkillApiScanner._iter_module_py_files(
            skill_path,
            frozenset(scan_exclude_dirs(str(skill_path)) | {"scripts"}),
            include_scripts=False)
        result["files"] = SkillApiScanner._scan_module_files(
            module_paths, skill_dir)
        if not _has_library_paths(module_paths):
            result["files"].extend(
                SkillApiScanner._scan_script_only_modules(
                    skill_path, skill_dir, module_paths))
        for file_info in result["files"]:
            result["total_lines"] += file_info.get("line_count", 0)
            result["total_public_functions"] += len(
                file_info.get("functions", []))
            result["total_public_classes"] += len(
                file_info.get("classes", []))
        result["scripts"] = SkillApiScanner._scan_script_channel(skill_path)
        result["file_tree"] = SkillApiScanner._build_file_tree(skill_path)
        return result
    @staticmethod
    def _scan_script_only_modules(
            skill_path: Path, skill_dir: str, module_paths: list[Path]) -> list:
        if _has_library_paths(module_paths):
            return []
        scripts_dir = skill_path / "scripts"
        if not scripts_dir.is_dir():
            return []
        files: list = []
        for py_file in SkillApiScanner._iter_script_py_files(
                scripts_dir, include_init=True):
            try:
                files.append(
                    SkillApiScanner._parse_py_file(str(py_file), skill_dir))
            except Exception as e:  # noqa: BLE001
                _log.warning("扫描脚本模块 %s 失败: %s", py_file, e)
        return files
    @staticmethod
    def _iter_script_py_files(
            directory: Path, *, include_init: bool = True) -> list[Path]:
        include_init = signal_bool(include_init)
        try:
            candidates = [p for p in directory.iterdir()
                          if p.is_file() and p.suffix.lower() in PY_SUFFIXES
                          and not p.name.startswith(".")]
        except OSError as e:
            _log.warning("扫描脚本目录失败，脚本通道降级为空: %s: %s", directory, e)
            return []
        return sorted(
            p for p in candidates
            if not is_transient_module_name(p.name)
            and not _is_test_source_file(p.name)
            and (include_init or p.name != "__init__.py"))
    @staticmethod
    def _iter_module_py_files(
            skill_path: Path, exclude_dirs: frozenset[str], *,
            include_scripts: bool = False) -> list[Path]:
        include_scripts = signal_bool(include_scripts)
        py_candidates: list[Path] = []
        try:
            for py_file in skill_path.rglob(_PY_FILE_GLOB):
                py_candidates.append(py_file)  # noqa: PERF402 — 保留异常前已收集条目
        except OSError as e:
            _log.warning("扫描目录时部分子目录不可读，已收集条目继续: %s: %s",
                         skill_path, e)
        return [
            py_file for py_file in sorted(py_candidates)
            if py_file.is_file()
            and not SkillApiScanner._should_skip_module_py(
                py_file, skill_path, exclude_dirs,
                include_scripts=include_scripts)
        ]
    @staticmethod
    def _scan_module_files(module_paths: list[Path], skill_dir: str) -> list:
        files: list = []
        for py_file in module_paths:
            try:
                files.append(
                    SkillApiScanner._parse_py_file(str(py_file), skill_dir))
            except Exception as e:  # noqa: BLE001
                _log.warning("扫描 %s 失败: %s", py_file, e)
        return files
    @staticmethod
    def _should_skip_module_py(
            py_file: Path, skill_path: Path, exclude_dirs: frozenset[str],
            *, include_scripts: bool) -> bool:
        return (SkillApiScanner._path_part_excluded(
                    py_file, skill_path, exclude_dirs,
                    include_scripts=include_scripts)
                or is_transient_module_name(py_file.name)
                or _is_test_source_file(py_file.name))
    @staticmethod
    def _path_part_excluded(
            py_file: Path, skill_path: Path, exclude_dirs: frozenset[str],
            *, include_scripts: bool) -> bool:
        try:
            rel_parts = py_file.relative_to(skill_path).parts
        except ValueError as e:
            _log.debug("路径计算失败（跳过）: %s: %s", py_file, e)
            return True
        lowered = {part.lower() for part in rel_parts}
        root_scripts = (not include_scripts and len(rel_parts) > 1
                        and rel_parts[0].lower() == "scripts")
        part_excludes = (exclude_dirs if include_scripts
                         else exclude_dirs - {"scripts"})
        return (any(d.lower() in lowered for d in exclude_dirs
                    if d.lower() != "scripts")
                or root_scripts
                or any(part.startswith(".") for part in rel_parts)
                or any(_is_scan_face_dir(part, part_excludes)
                       for part in rel_parts[:-1]))
    @staticmethod
    def _scan_script_channel(skill_path: Path) -> list:
        scripts: list = []
        scripts_dir = skill_path / "scripts"
        if scripts_dir.is_dir():
            for script_file in SkillApiScanner._iter_script_py_files(
                    scripts_dir, include_init=False):
                try:
                    script_info = SkillApiScanner._parse_script_file(str(script_file))
                    scripts.append(script_info)
                except Exception as e:  # noqa: BLE001
                    _log.warning("扫描脚本 %s 失败: %s", script_file, e)
        return scripts
    @staticmethod
    def _build_file_tree(skill_path: Path) -> str:
        lines = ["```", f"{skill_path.name}/"]
        exclude_dirs = frozenset(
            d.lower() for d in scan_exclude_dirs(str(skill_path)))
        try:
            lines.extend(SkillApiScanner._tree_lines(skill_path, "", exclude_dirs))
        except (OSError, RecursionError) as e:
            _log.warning("构建文件树失败,降级为最小树: %s: %s", skill_path, e)
            return "\n".join(["```", f"{skill_path.name}/", "```"])
        lines.append("```")
        return "\n".join(lines)
    @staticmethod
    def _tree_subdirs(skill_path, exclude_dirs: frozenset[str]) -> list:
        return sorted(
            d for d in skill_path.iterdir()
            if d.is_dir()
            and not d.is_symlink()
            and not _is_scan_face_dir(d.name, exclude_dirs)
        )
    @staticmethod
    def _tree_entries(directory, exclude_dirs: frozenset[str]) -> list:
        files = [
            p for p in sorted(directory.glob(_PY_FILE_GLOB))
            if p.is_file()
            and not p.name.startswith(".")
            and not is_transient_module_name(p.name)
            and not _is_test_source_file(p.name)
        ]
        return ([("file", p) for p in files]
                + [("dir", d) for d in SkillApiScanner._tree_subdirs(
                    directory, exclude_dirs)])
    @staticmethod
    def _tree_lines(directory, prefix: str, exclude_dirs: set[str]) -> list:
        lines: list[str] = []
        entries = SkillApiScanner._tree_entries(directory, exclude_dirs)
        for idx, (kind, item) in enumerate(entries):
            is_last = idx == len(entries) - 1
            branch = "└── " if is_last else "├── "
            if kind == "file":
                lines.append(f"{prefix}{branch}{item.name}")
                continue
            lines.append(f"{prefix}{branch}{item.name}/")
            lines.extend(SkillApiScanner._tree_lines(
                item, prefix + ("    " if is_last else "│   "), exclude_dirs))
        return lines
    @staticmethod
    def _read_source_compat(path: Path) -> str:
        text = read_source_with_fingerprint(str(path))[0]
        if text is None:
            raise OSError(f"源码不可读: {path}")
        return text
    @staticmethod
    def _parse_py_file(file_path: str, skill_dir: str) -> dict[str, Any]:
        path = Path(file_path)
        content = SkillApiScanner._read_source_compat(path)
        line_count = source_line_count(content)
        tree = SkillApiScanner._parse_source_ast(content, file_path)
        module_doc, functions, classes = (
            SkillApiScanner._collect_module_members(tree) if tree
            else ("", [], []))
        public_api_names = (_module_public_api_names(tree)
                            if tree is not None else set())
        rel_path = safe_relpath(str(path), skill_dir)
        return {
            "file": rel_path,
            "line_count": line_count,
            "module_doc": module_doc,
            "functions": functions,
            "classes": classes,
            "public_api_names": sorted(public_api_names),
        }
    @staticmethod
    def _parse_source_ast(
        content: str, file_path: str,
        parsed_tree: ast.Module | None = None,
    ) -> ast.Module | None:
        try:
            compile(content, file_path, "exec")
            return (parsed_tree if parsed_tree is not None
                    else ast.parse(content, filename=file_path))
        except PARSE_DEGRADE_EXC as e:
            _log.warning("[SkillDoc] 源码编译/解析失败,置None: %s: %s", file_path, e)
            return None
    @staticmethod
    def _is_public_member(node: ast.AST) -> bool:
        return (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                and is_public_name(node.name))
    @staticmethod
    def _doc_first_line(node) -> str:
        doc = ast.get_docstring(node)
        return doc.strip().split("\n")[0].strip() if doc else ""
    @staticmethod
    def _collect_module_members(tree) -> tuple[str, list, list]:
        module_doc = SkillApiScanner._doc_first_line(tree)
        functions: list[dict[str, Any]] = []
        classes: list[dict[str, Any]] = []
        for node, owner in _iter_scope_definitions(
                getattr(tree, "body", []) or [], None):
            if owner is not None:
                continue
            if isinstance(node, ast.ClassDef):
                if is_public_name(node.name):
                    classes.append(SkillApiScanner._extract_class(node))
                continue
            if (SkillApiScanner._is_public_member(node)
                    and not _is_typing_only_declaration(node)):
                functions.append(SkillApiScanner._extract_function(node))
        return module_doc, functions, classes
    @staticmethod
    def _fmt_ast_arg(arg: ast.arg) -> str:
        ann = ast.unparse(arg.annotation) if arg.annotation else ""
        return f"{arg.arg}: {ann}" if ann else arg.arg
    @staticmethod
    def _collect_positional_parts(args: ast.arguments) -> tuple[list, list]:
        all_args = [*args.posonlyargs, *args.args]
        parts = [SkillApiScanner._fmt_ast_arg(arg) for arg in all_args]
        defaults_start = len(parts) - len(args.defaults)
        for offset, default in enumerate(args.defaults):
            param_idx = defaults_start + offset
            if 0 <= param_idx < len(parts):
                parts[param_idx] += f"={ast.unparse(default)}"
        n_posonly = len(args.posonlyargs)
        return parts[:n_posonly], parts[n_posonly:]
    @staticmethod
    def _fmt_star_arg(arg: ast.arg, prefix: str) -> str:
        return prefix + SkillApiScanner._fmt_ast_arg(arg)
    @staticmethod
    def _format_var_kw_parts(args: ast.arguments) -> list:
        parts: list[str] = []
        if args.vararg:
            parts.append(SkillApiScanner._fmt_star_arg(args.vararg, "*"))
        elif args.kwonlyargs:
            parts.append("*")
        for arg, default in zip(args.kwonlyargs, args.kw_defaults, strict=False):
            part = SkillApiScanner._fmt_ast_arg(arg)
            if default is not None:
                part += f"={ast.unparse(default)}"
            parts.append(part)
        if args.kwarg:
            parts.append(SkillApiScanner._fmt_star_arg(args.kwarg, "**"))
        return parts
    @staticmethod
    def _extract_function(node: ast.FunctionDef | ast.AsyncFunctionDef) -> dict[str, Any]:
        first_line = SkillApiScanner._doc_first_line(node)
        function_info = extract_function_info(node)
        posonly_parts, plain_parts = SkillApiScanner._collect_positional_parts(node.args)
        args: list[str] = posonly_parts + (["/"] if posonly_parts else []) + plain_parts
        args.extend(SkillApiScanner._format_var_kw_parts(node.args))
        returns = ast.unparse(node.returns) if node.returns else ""
        signature = f"{node.name}({', '.join(args)})"
        if returns:
            signature += f" -> {returns}"
        return {
            "name": node.name,
            "signature": signature,
            "doc": first_line,
            "full_doc": function_info["full_doc"],
            "params": function_info["params"],
            "is_async": function_info["is_async"],
            "line_count": (node.end_lineno or node.lineno) - node.lineno + 1,
        }
    @staticmethod
    def _extract_class(node: ast.ClassDef) -> dict[str, Any]:
        methods: list[dict[str, Any]] = []
        for child, owner in _iter_scope_definitions(node.body, node):
            if owner is not node or not SkillApiScanner._is_public_member(child):
                continue
            if _is_typing_only_declaration(child):
                continue
            methods.append({
                "name": child.name,
                "doc": SkillApiScanner._doc_first_line(child),
            })
        return {
            "name": node.name,
            "doc": SkillApiScanner._doc_first_line(node),
            "methods": methods,
            "line_count": (node.end_lineno or node.lineno) - node.lineno + 1,
        }
    @staticmethod
    def _parse_script_file(file_path: str) -> dict[str, Any]:
        path = Path(file_path)
        content = SkillApiScanner._read_source_compat(path)
        tree = SkillApiScanner._parse_source_ast(content, file_path)
        doc = SkillApiScanner._doc_first_line(tree) if tree is not None else ""
        has_main = (_module_has_main_guard(tree) if tree is not None
                    else _script_has_main_guard(content))
        boolean_flags = _script_boolean_flags(tree)
        has_json = bool(boolean_flags & _SCRIPT_JSON_FLAGS)
        has_dry_run = bool(boolean_flags & _SCRIPT_DRY_RUN_FLAGS)
        return {
            "name": path.name,
            "doc": doc,
            "has_main": has_main,
            "has_json": has_json,
            "has_dry_run": has_dry_run,
        }
def scan_skill_api(skill_dir: str) -> dict[str, Any] | None:
    skill_dir = coerce_skill_dir(skill_dir)
    if not (skill_dir and os.path.isdir(skill_dir)):
        return None
    try:
        return SkillApiScanner.scan_skill_dir(skill_dir)
    except Exception as e:  # noqa: BLE001 - 刻意降级：记录日志不中断主流程
        _log.warning("重构时 API 扫描失败: %s", e)
        return None
def _skip_string_literal(s: str, i: int) -> int:
    ch = s[i]
    qtok = s[i:i + 3] if s[i:i + 3] == ch * 3 else ch
    j = i + len(qtok)
    n = len(s)
    while j < n:
        if s[j] == "\\":
            j += 2
            continue
        if s[j:j + len(qtok)] == qtok:
            j += len(qtok)
            break
        j += 1
    return j
_BRACKET_DELTA: dict[str, int] = {
    "(": 1, "[": 1, "{": 1, ")": -1, "]": -1, "}": -1,
}
def _is_balanced_group(inner: str) -> bool:
    depth = 0
    i = 0
    n = len(inner)
    while i < n:
        ch = inner[i]
        if ch in "'\"":
            i = _skip_string_literal(inner, i)
            continue
        depth += _BRACKET_DELTA.get(ch, 0)
        if depth < 0:
            return False
        i += 1
    return depth == 0
def _skip_lambda_header(s: str, i: int) -> int:
    n = len(s)
    j = i + len("lambda")
    depth = 0
    while j < n:
        ch = s[j]
        if ch in "'\"":
            j = _skip_string_literal(s, j)
            continue
        delta = _BRACKET_DELTA.get(ch, 0)
        if delta:
            depth += delta
            j += 1
            continue
        if ch == ":" and depth == 0:
            return j + 1
        j += 1
    return i + len("lambda")
def _is_lambda_keyword(s: str, i: int) -> bool:
    if not s.startswith("lambda", i):
        return False
    if i and (s[i - 1].isalnum() or s[i - 1] in "_."):
        return False
    end = i + len("lambda")
    return end >= len(s) or not (s[end].isalnum() or s[end] == "_")
def _split_top_level_commas(s: str) -> list[str]:
    pieces: list[str] = []
    buf: list[str] = []
    i = 0
    n = len(s)
    depth = 0
    while i < n:
        ch = s[i]
        if ch in "'\"":
            j = _skip_string_literal(s, i)
            buf.append(s[i:j])
            i = j
            continue
        if _is_lambda_keyword(s, i):
            j = _skip_lambda_header(s, i)
            if j > i + len("lambda"):
                buf.append(s[i:j])
                i = j
                continue
        if ch == "," and depth == 0:
            pieces.append("".join(buf).strip())
            buf = []
            i += 1
            continue
        depth = max(0, depth + _BRACKET_DELTA.get(ch, 0))
        buf.append(ch)
        i += 1
    tail = "".join(buf).strip()
    if tail:
        pieces.append(tail)
    return pieces
def _expand_tuple_params(p: str) -> list[str]:
    _p = p.strip()
    if not (_p.startswith("(") and _p.endswith(")")):
        return [p]
    inner = _p[1:-1]
    if not _is_balanced_group(inner):
        return [p]
    pieces = _split_top_level_commas(inner)
    out: list[str] = []
    for piece in pieces:
        out.extend(_expand_tuple_params(piece))
    return out
def _strip_signature_comments(s: str) -> str:
    pieces: list[str] = []
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch in "'\"":
            end = _skip_string_literal(s, i)
            pieces.append(s[i:end])
            i = end
            continue
        if ch == "#":
            newline = s.find("\n", i)
            if newline < 0:
                break
            pieces.append(" ")
            i = newline
            continue
        pieces.append(ch)
        i += 1
    return "".join(pieces)
def _locate_params_span(_s: str, _head) -> str:
    depth = 0
    end = -1
    _i = _head.end() - 1
    _n = len(_s)
    while _i < _n:
        _ch = _s[_i]
        if _ch in "'\"":
            _i = _skip_string_literal(_s, _i)
            continue
        _delta = _BRACKET_DELTA.get(_ch, 0)
        if _delta:
            depth += _delta
            if depth == 0:
                end = _i
                break
        _i += 1
    if end < 0:
        return _s[_head.end():]
    return _s[_head.end():end]
def _param_name_of(piece: str):
    _nm = re.match(r"^\*{0,2}\s*([^\W\d]\w*)", piece, re.UNICODE)
    if not _nm:
        return None
    name = _nm.group(1)
    if name in ("self", "cls"):
        return None
    return name
def extract_param_names(signature: str) -> list[str]:
    if isinstance(signature, bytes):
        signature = signature.decode("utf-8", "replace")
    if not isinstance(signature, str) or not signature:
        return []
    _s = _strip_signature_comments(signature.strip())
    _head = re.match(r"^[\w.]+\s*\(", _s)
    if not _head:
        return []
    inner = _locate_params_span(_s, _head)
    names: list[str] = []
    for p in _split_top_level_commas(inner):
        for piece in _expand_tuple_params(p):
            name = _param_name_of(piece)
            if name is not None:
                names.append(name)
    return names
_SCAN_SEQUENCE_TYPES = (list, tuple)
def _add_public_symbol_names(names: set, f_info: dict, key: str) -> None:
    entries = f_info.get(key)
    for entry in (entries if isinstance(entries, _SCAN_SEQUENCE_TYPES) else []):
        if (isinstance(entry, dict) and isinstance(entry.get("name"), str)
                and entry["name"]):
            names.add(entry["name"])
def get_scan_files(api_scan) -> list:
    if not isinstance(api_scan, dict):
        return []
    files = api_scan.get("files")
    return list(files) if isinstance(files, _SCAN_SEQUENCE_TYPES) else []
def collect_api_names(api_scan, include_module_names: bool = False) -> set:
    include_module_names = signal_bool(include_module_names)
    names: set = set()
    files = get_scan_files(api_scan)
    for f_info in files:
        if not isinstance(f_info, dict):
            continue
        if include_module_names:
            _fname = f_info.get("file")
            if isinstance(_fname, str) and _fname:
                basename = _fname.replace("\\", "/").rsplit("/", 1)[-1]
                names.add(os.path.splitext(basename)[0])
        _add_public_symbol_names(names, f_info, "functions")
        _add_public_symbol_names(names, f_info, "classes")
    return names
def iter_scan_function_entries(files) -> Iterator[tuple[str, dict]]:
    if not isinstance(files, _SCAN_SEQUENCE_TYPES):
        return
    for f_info in files:
        if not isinstance(f_info, dict):
            continue
        f_path = str(f_info.get("file", "") or "")
        functions = f_info.get("functions")
        if not isinstance(functions, _SCAN_SEQUENCE_TYPES):
            continue
        for func in functions:
            if isinstance(func, dict):
                yield f_path, func
def has_scan_files(api_scan) -> bool:
    return bool(get_scan_files(api_scan))
def has_code_surface(api_scan) -> bool | None:
    if not isinstance(api_scan, dict):
        return None
    files = api_scan.get("files")
    if not isinstance(files, _SCAN_SEQUENCE_TYPES):
        return None
    if get_scan_files(api_scan):
        return True
    scripts = api_scan.get("scripts")
    return bool(scripts) if isinstance(scripts, _SCAN_SEQUENCE_TYPES) else False
URL_TOKEN_RE = re.compile(
    r'(?:[A-Za-z][A-Za-z0-9+.\-]*://|www\.)\S+', re.IGNORECASE)
def strip_url_tokens(text: str) -> str:
    return URL_TOKEN_RE.sub(' ', _coerce_text(text))
_PY_REF_WITH_PATH_RE = re.compile(
    r'(?i)(?<![\w./:])'
    r'(?:[\w.\-]+/)*'
    r'[\w.\-]+\.py'
    r'(?![\w]|\.[\w])')
_SKILL_RESOURCE_DIR_PREFIXES = frozenset({"scripts", "references", "assets"})
_CROSS_SKILL_PY_REF_RE = re.compile(
    r'<[^<>\n]*>[^\s`)\]}>]*?\.py'
    r'|(?:\.\./)+[^\s`)\]}>]*?\.py',
    re.IGNORECASE)
def is_script_only_skill(skill_dir: str) -> bool:
    skill_dir = coerce_skill_dir(skill_dir)
    if not skill_dir or not os.path.isdir(skill_dir):
        return False
    if not os.path.isdir(os.path.join(skill_dir, "scripts")):
        return False
    skill_path = Path(skill_dir)
    module_paths = SkillApiScanner._iter_module_py_files(
        skill_path,
        frozenset(scan_exclude_dirs(str(skill_path)) | {"scripts"}),
        include_scripts=False)
    return not _has_library_paths(module_paths)
def _coerce_text(value: Any) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, bytes):
        return value.decode("utf-8", "replace")
    return ""
def _coerce_resource_dirs(value: Any) -> frozenset[str]:
    if value is None:
        return _SKILL_RESOURCE_DIR_PREFIXES
    if isinstance(value, str):
        return frozenset({value.lower()})
    if isinstance(value, bytes):
        return frozenset({value.decode("utf-8", "replace").lower()})
    if isinstance(value, os.PathLike):
        try:
            return frozenset({_coerce_text(os.fspath(value)).lower()})
        except (TypeError, ValueError, OSError):
            return _SKILL_RESOURCE_DIR_PREFIXES
    try:
        items = list(value)
    except TypeError:
        return _SKILL_RESOURCE_DIR_PREFIXES
    return frozenset(
        item.lower() for item in items
        if isinstance(item, str) and item)
def extract_py_refs(text: str, include_scripts: bool = False,
                    resource_dirs: Iterable[str] | None = None) -> set[str]:
    include_scripts = signal_bool(include_scripts)
    local = strip_url_tokens(_coerce_text(text)).replace("\\", "/")
    local = _CROSS_SKILL_PY_REF_RE.sub(' ', local)
    layout_dirs = _coerce_resource_dirs(resource_dirs)
    skip_prefixes = (layout_dirs if not include_scripts
                     else layout_dirs - {"scripts"})
    refs: set[str] = set()
    for ref in _PY_REF_WITH_PATH_RE.findall(local):
        parts = posixpath.normpath(ref).split('/')
        drive_root = (len(parts[0]) == 2 and parts[0][0].isalpha()
                      and parts[0][1] == ':')
        if (parts[0] == '..' or drive_root
                or parts[0].lower() in skip_prefixes):
            continue
        refs.add(parts[-1].lower())
    return refs
def is_test_infrastructure(py_file: Path, scope_root: Path) -> bool:
    try:
        py_path = Path(py_file)
        root_path = Path(scope_root)
    except (TypeError, ValueError):
        return False
    name = py_path.name
    if _is_test_source_file(name):
        return True
    try:
        parts = py_path.relative_to(root_path).parts
    except ValueError as _swallow_e:
        log_swallowed(
            __name__, _swallow_e, context='is_test_infrastructure:ValueError')
        return False
    return any(is_test_dir_name(part) for part in parts[:-1])
def collect_skill_py_basenames(skill_dir: str) -> set:
    skill_dir = coerce_skill_dir(skill_dir)
    if not skill_dir:
        return set()
    py_files = set()
    skip = scan_prune_dirs(skill_dir) | {
        name.lower() for name in scan_exclude_dirs(skill_dir)}
    for _root, dirs, files in os.walk(
            skill_dir,
            onerror=lambda err: _log.warning(
                "扫描 .py 基名时目录不可读，跳过并继续: %s", err)):
        dirs[:] = [d for d in dirs
                   if not is_pruned_scan_dir(d, skip)
                   and not is_test_dir_name(d)]
        for fname in files:
            if (fname.lower().endswith('.py')
                    and not fname.startswith('.')
                    and not is_transient_module_name(fname)
                    and not _is_test_source_file(fname)):
                py_files.add(fname.lower())
    return py_files
@dataclass
class IOSpec:
    func_name: str = ""
    file_path: str = ""
    has_input_schema: bool = False
    has_output_schema: bool = False
    input_types: dict[str, str] = field(default_factory=dict)
    param_names: list[str] = field(default_factory=list)
    params_with_defaults: set[str] = field(default_factory=set)
    vararg_name: str = ""
    kwarg_name: str = ""
    output_type: str = ""
    docstring: str = ""
    agent_example: str = ""
    score: float = 0.0
    issues: list[str] = field(default_factory=list)
@dataclass
class IOStandardizationReport:
    skill_dir: str = ""
    overall_score: float = 0.0
    func_specs: list[IOSpec] = field(default_factory=list)
    schema_coverage: float = 0.0
    type_annotation_coverage: float = 0.0
    semantic_gaps: list[dict] = field(default_factory=list)
    issues: list[str] = field(default_factory=list)
    suggestions: list[str] = field(default_factory=list)
    recommended_schemas: dict[str, dict] = field(default_factory=dict)
@dataclass
class ParameterSpec:
    name: str = ""
    type: str = "string"
    description: str = ""
    required: bool = True
    default: Any = None
    enum: list[str] | None = None
@dataclass
class FunctionSchema:
    name: str = ""
    description: str = ""
    parameters: list[ParameterSpec] = field(default_factory=list)
    returns: str = ""
    examples: list[str] = field(default_factory=list)
@dataclass
class FunctionOptimizationResult:
    original_schema: FunctionSchema | None = None
    optimized_schema: FunctionSchema | None = None
    issues: list[str] = field(default_factory=list)
    suggestions: list[str] = field(default_factory=list)
    score_before: float = 0.0
    score_after: float = 0.0
_MIN_DESC_LENGTH = 10
_WEIGHT_DESCRIPTION = 0.25
_WEIGHT_PARAMETERS = 0.35
_WEIGHT_RETURNS = 0.15
_WEIGHT_EXAMPLES = 0.25
_STEP_PARAMETER_SCORE = 0.1
_STEP_EXAMPLE_SCORE = 0.1
_SENTENCE_TERMINATORS = "。．.！!？?"
_SCHEMA_DECL_RE = re.compile(
    r"(?m)^[ \t]*(?:json\s*schema|schema)\s*[:：]", re.IGNORECASE)
_SEMANTIC_TYPE_CANON: dict[str, dict] = {
    "file_path": {"type": "string", "format": "path", "description": "文件路径"},
    "skill_dir": {"type": "string", "format": "path", "description": "技能目录路径"},
    "input_text": {"type": "string", "description": "用户输入文本"},
    "output_path": {"type": "string", "format": "path", "description": "输出文件路径"},
    "options": {"type": "object", "description": "可选参数字典"},
    "config": {"type": "object", "description": "配置对象"},
    "result": {"type": "object", "description": "操作结果字典"},
    "success": {"type": "boolean", "description": "操作是否成功"},
    "data": {"type": "array", "description": "数据列表"},
    "items": {"type": "array", "description": "项目列表"},
    "content": {"type": "string", "description": "文本内容"},
    "text": {"type": "string", "description": "文本字符串"},
    "json_data": {"type": "object", "description": "JSON数据对象"},
}
_PARAM_SEMANTIC_SUFFIXES: tuple[tuple[frozenset[str], dict], ...] = (
    (frozenset({"path", "paths", "file", "filename", "dir", "directory",
                "folder"}),
     {"type": "string", "format": "path", "description": "文件或目录路径"}),
    (frozenset({"text", "content", "message", "description"}),
     {"type": "string", "description": "文本内容"}),
    (frozenset({"options", "option", "config", "settings"}),
     {"type": "object", "description": "可选参数/配置对象"}),
    (frozenset({"result", "summary"}),
     {"type": "object", "description": "操作结果对象"}),
    (frozenset({"success", "ok"}),
     {"type": "boolean", "description": "操作是否成功"}),
    (frozenset({"items", "data", "records", "rows"}),
     {"type": "array", "description": "数据列表"}),
)
_PARAM_NAME_SPLIT_RE = re.compile(r"[^a-z0-9]+")
def _semantic_canon_for(param: str) -> dict | None:
    canon = _SEMANTIC_TYPE_CANON.get(param)
    if canon is not None:
        return canon
    tokens = [token for token in _PARAM_NAME_SPLIT_RE.split(param.lower())
              if token]
    if not tokens:
        return None
    last = tokens[-1]
    for suffixes, schema in _PARAM_SEMANTIC_SUFFIXES:
        if last in suffixes:
            return schema
    return None
_PY_TYPE_TO_SCHEMA: dict[str, str] = {
    "str": "string", "string": "string", "Path": "string", "PurePath": "string",
    "int": "integer", "integer": "integer",
    "float": "number", "number": "number", "complex": "string",
    "bool": "boolean", "boolean": "boolean",
    "list": "array", "List": "array", "tuple": "array", "Tuple": "array",
    "set": "array", "Set": "array", "frozenset": "array", "Sequence": "array",
    "dict": "object", "Dict": "object", "Mapping": "object",
    "None": "null", "NoneType": "null",
}
def _schema_str(value: Any) -> str:
    return value.strip() if isinstance(value, str) else ""
def _schema_list(value: Any) -> list[str]:
    if not isinstance(value, (list, tuple)):
        return []
    return [text for item in value if (text := _schema_str(item))]
def _schema_params(value: Any) -> list[ParameterSpec]:
    if not isinstance(value, (list, tuple)):
        return []
    return [p for p in value if isinstance(p, ParameterSpec)]
def _schema_param_names(spec: IOSpec) -> list[str]:
    if spec.param_names:
        return spec.param_names
    return list(spec.input_types)
def _function_schema_skeleton(spec: IOSpec) -> dict:
    return_type = _annotation_schema_type(spec.output_type) or "object"
    returns = {"type": return_type, "description": "Operation result"}
    return {  # jwsgj:suppress RT-01 — schema 骨架嵌套 dict 有类型契约消费方
        "function": spec.func_name,
        "description": (spec.docstring.split("\n")[0]
                        if spec.docstring else f"Execute {spec.func_name}"),
        "parameters": {"type": "object", "properties": {}, "required": []},
        "returns": returns,
    }
def _generate_recommended_schemas(func_specs: list[IOSpec]) -> dict[str, dict]:
    schemas = {}
    for spec in func_specs:
        if spec.has_input_schema and spec.has_output_schema:
            continue
        schema = _function_schema_skeleton(spec)
        for param in _schema_param_names(spec):
            schema["parameters"]["properties"][param] = _build_param_property(spec, param)
            if param not in spec.params_with_defaults:
                schema["parameters"]["required"].append(param)
        key = _dedup_schema_key(schemas, f"{Path(spec.file_path).name}::{spec.func_name}")
        schemas[key] = schema
    return schemas
def _build_param_property(spec: IOSpec, param: str) -> dict:
    canon = _semantic_canon_for(param)
    annot_schema_type = _annotation_schema_type(spec.input_types.get(param, ""))
    varparam_kind = _varparam_kind(spec, param)
    if varparam_kind:
        return _varparam_property(param, annot_schema_type, varparam_kind)
    if canon is None:
        return {"type": annot_schema_type or "string",
                "description": f"Parameter {param}"}
    if annot_schema_type and annot_schema_type != canon["type"]:
        return {"type": annot_schema_type, "description": f"Parameter {param}"}
    return _canon_property(canon)
_ANNOTATION_QUOTES = ("'", '"')
_ANNOTATION_OPENERS = "([{"
_ANNOTATION_CLOSERS = ")]}"
_ANNOTATION_STRING_PREFIXES = "rRuU"
_NONE_TYPE_NAMES = frozenset({"None", "NoneType"})
def _advance_annotation_state(ch: str, depth: int, quote: str,
                              openers: str, closers: str) -> tuple[int, str]:
    if quote:
        return depth, ("" if ch == quote else quote)
    if ch in _ANNOTATION_QUOTES:
        return depth, ch
    if ch in openers:
        return depth + 1, quote
    if ch in closers:
        return depth - 1, quote
    return depth, quote
def _iter_annotation_nesting(
    text: str,
    start: int = 0,
    openers: str = _ANNOTATION_OPENERS,
    closers: str = _ANNOTATION_CLOSERS,
) -> Iterator[tuple[int, str, int, str]]:
    depth = 0
    quote = ""
    escaped = False
    for pos in range(start, len(text)):
        ch = text[pos]
        if quote and escaped:
            escaped = False
            yield pos, ch, depth, quote
            continue
        if quote and ch == "\\":
            escaped = True
            yield pos, ch, depth, quote
            continue
        depth, quote = _advance_annotation_state(ch, depth, quote, openers, closers)
        yield pos, ch, depth, quote
def _is_wrapped_group(text: str) -> bool:
    if len(text) < 2 or text[0] != "(" or text[-1] != ")":
        return False
    for pos, ch, depth, quote in _iter_annotation_nesting(text):
        if not quote and ch == ")" and depth == 0:
            return pos == len(text) - 1
    return False
def _whole_string_literal_wrap(text: str) -> tuple[int, int] | None:
    start = 0
    while start < len(text) and text[start] in _ANNOTATION_STRING_PREFIXES:
        start += 1
    if start >= len(text) or text[start] not in _ANNOTATION_QUOTES:
        return None
    quote = text[start]
    delimiter = quote * 3 if text.startswith(quote * 3, start) else quote
    open_len = start + len(delimiter)
    pos = open_len
    while pos < len(text):
        if text[pos] == "\\":
            pos += 2
            continue
        if text.startswith(delimiter, pos):
            if pos + len(delimiter) == len(text):
                return open_len, len(delimiter)
            return None
        pos += 1
    return None
def _strip_annotation_wrappers(text: str) -> str:
    value = text.strip()
    while len(value) >= 2:
        string_wrap = _whole_string_literal_wrap(value)
        if string_wrap is not None:
            head, tail = string_wrap
            value = value[head:len(value) - tail].strip()
            continue
        if _is_wrapped_group(value):
            value = value[1:-1].strip()
            continue
        break
    return value
def _split_annotation_top_level(text: str, sep: str) -> list[str]:
    parts: list[str] = []
    buf: list[str] = []
    for _pos, ch, depth, quote in _iter_annotation_nesting(text):
        if ch == sep and depth == 0 and not quote:
            parts.append("".join(buf))
            buf = []
        else:
            buf.append(ch)
    parts.append("".join(buf))
    return parts
def _split_annotation_generic(text: str) -> tuple[str, str | None]:
    idx = text.find("[")
    if idx <= 0 or not text.endswith("]"):
        return text, None
    depth = 0
    for pos, ch, depth, quote in _iter_annotation_nesting(
            text, start=idx, openers="[", closers="]"):
        if not quote and ch == "]" and depth == 0 and pos != len(text) - 1:
            return text, None
    if depth != 0:
        return text, None
    return text[:idx].strip(), text[idx + 1:-1].strip()
def _is_none_annotation(part: str) -> bool:
    text = _strip_annotation_wrappers(_schema_str(part))
    return text.rsplit(".", 1)[-1].strip() in _NONE_TYPE_NAMES
def _single_type_member(parts: list[str]) -> str | None:
    meaningful = [p for p in parts if not _is_none_annotation(p)]
    return meaningful[0] if len(meaningful) == 1 else None
def _generic_schema_type(base_name: str, args: str) -> str | None:
    if base_name == "Union":
        only = _single_type_member(_split_annotation_top_level(args, ","))
        return _annotation_schema_type(only) if only else None
    if base_name == "Annotated":
        members = _split_annotation_top_level(args, ",")
        return _annotation_schema_type(members[0]) if members else None
    return _PY_TYPE_TO_SCHEMA.get(base_name)
def _annotation_schema_type(ptype: str) -> str | None:
    text = _strip_annotation_wrappers(_schema_str(ptype))
    if not text:
        return None
    union_parts = _split_annotation_top_level(text, "|")
    if len(union_parts) > 1:
        only = _single_type_member(union_parts)
        return _annotation_schema_type(only) if only else None
    base, args = _split_annotation_generic(text)
    base_name = base.rsplit(".", 1)[-1].strip()
    if args is None:
        return _PY_TYPE_TO_SCHEMA.get(base_name)
    if base_name == "Optional":
        return _annotation_schema_type(args)
    return _generic_schema_type(base_name, args)
def _union_members(text: str) -> list[str]:
    base, args = _split_annotation_generic(text)
    if args is not None and base.rsplit(".", 1)[-1].strip() == "Union":
        return _split_annotation_top_level(args, ",")
    return _split_annotation_top_level(text, "|")
_IDENTITY_BASE_ALIASES = {
    "List": "list", "Dict": "dict", "Tuple": "tuple", "Set": "set",
    "FrozenSet": "frozenset", "Type": "type", "Text": "str",
}
def _annotation_identity_arg(part: str) -> str:
    text = _strip_annotation_wrappers(_schema_str(part))
    if len(text) >= 2 and text[0] == "[" and text[-1] == "]":
        inner = text[1:-1].strip()
        if not inner:
            return "[]"
        return "[" + ", ".join(
            _annotation_identity_arg(member)
            for member in _split_annotation_top_level(inner, ",")
        ) + "]"
    identity = _annotation_identity(text)
    return identity or " ".join(text.split())
def _annotation_identity(ptype: str) -> str:
    text = _strip_annotation_wrappers(_schema_str(ptype))
    if not text:
        return ""
    base, args = _split_annotation_generic(text)
    base_name = base.rsplit(".", 1)[-1].strip()
    if args is not None and base_name == "Optional":
        return _annotation_identity(args)
    if args is not None and base_name == "Annotated":
        members = _split_annotation_top_level(args, ",")
        return _annotation_identity(members[0]) if members else ""
    if args is not None and base_name == "Union":
        only = _single_type_member(_split_annotation_top_level(args, ","))
        if only is not None:
            return _annotation_identity(only)
    if args is not None and base_name == "Literal":
        literal_args = ", ".join(
            part.strip() for part in _split_annotation_top_level(args, ",")
        )
        return f"Literal[{literal_args}]"
    members = _union_members(text)
    if len(members) > 1:
        kept = {
            identity for member in members
            if (identity := _annotation_identity(member))
        }
        if not kept:
            return ""
        return " | ".join(sorted(kept))
    if args is None and (base_name in _NONE_TYPE_NAMES or base_name == "Any"):
        return ""
    base_name = _IDENTITY_BASE_ALIASES.get(base_name, base_name)
    if args is None:
        return base_name
    args_text = ", ".join(
        _annotation_identity_arg(part)
        for part in _split_annotation_top_level(args, ",")
    )
    return f"{base_name}[{args_text}]"
def _varparam_kind(spec: IOSpec, param: str) -> str:
    if param and param == spec.vararg_name:
        return "vararg"
    if param and param == spec.kwarg_name:
        return "kwarg"
    return ""
def _varparam_property(param: str, item_type: str | None, kind: str) -> dict:
    if kind == "vararg":
        prop: dict = {"type": "array", "description": f"可变位置参数（*{param}）"}
        if item_type:
            prop["items"] = {"type": item_type}
        return prop
    prop = {"type": "object", "description": f"可变关键字参数（**{param}）"}
    if item_type:
        prop["additionalProperties"] = {"type": item_type}
    return prop
def _canon_property(canon: dict) -> dict:
    prop = {"type": canon["type"], "description": canon["description"]}
    if canon.get("format"):
        prop["format"] = canon["format"]
    return prop
def _dedup_schema_key(schemas: dict, key: str) -> str:
    if key not in schemas:
        return key
    dup = 2
    while f"{key}#{dup}" in schemas:
        dup += 1
    return f"{key}#{dup}"
def _annotation_text(node: ast.AST | None) -> str:
    if node is None:
        return ""
    return _strip_annotation_wrappers(ast.unparse(node))
_DECLARATION_ONLY_DECORATORS = frozenset({"overload"})
def _is_typing_only_declaration(
    node: ast.FunctionDef | ast.AsyncFunctionDef,
) -> bool:
    return any(
        ast_name(dec) in _DECLARATION_ONLY_DECORATORS
        for dec in node.decorator_list
    )
def _has_implicit_receiver(
    node: ast.FunctionDef | ast.AsyncFunctionDef, in_class: bool,
) -> bool:
    if not in_class:
        return False
    return not any(
        ast_name(dec) == "staticmethod"
        for dec in node.decorator_list
    )
def _type_checking_body_branch(test: ast.expr) -> bool | None:
    if is_type_checking_guard(test):
        return True
    if (isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not)
            and is_type_checking_guard(test.operand)):
        return False
    return None
def _iter_scope_definitions(
    stmts, owner: ast.ClassDef | None,
) -> Iterator[tuple[ast.AST, ast.ClassDef | None]]:
    for stmt in stmts:
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield stmt, owner
            continue
        if isinstance(stmt, ast.ClassDef):
            yield stmt, owner
            if is_public_name(stmt.name):
                yield from _iter_scope_definitions(stmt.body, stmt)
            continue
        if isinstance(stmt, ast.If):
            type_only_body = _type_checking_body_branch(stmt.test)
            if type_only_body is not None:
                if type_only_body:
                    runtime_branch = getattr(stmt, "orelse", None) or []
                else:
                    runtime_branch = getattr(stmt, "body", None) or []
                yield from _iter_scope_definitions(runtime_branch, owner)
                continue
        for block in iter_module_stmt_blocks(stmt):
            yield from _iter_scope_definitions(block, owner)
def _iter_public_function_defs(
    tree: ast.AST,
) -> Iterator[tuple[ast.FunctionDef | ast.AsyncFunctionDef, bool]]:
    for node, owner in _iter_scope_definitions(
            getattr(tree, "body", []) or [], None):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if _is_typing_only_declaration(node):
            continue
        yield node, _has_implicit_receiver(node, owner is not None)
class IOStandardizationChecker:
    def _validate_skill_dir(self, skill_dir: str | os.PathLike) -> tuple[Path, IOStandardizationReport | None]:
        raw_target = skill_dir
        skill_dir = coerce_skill_dir(skill_dir)
        if not skill_dir.strip():
            return Path(""), self._path_error_report(
                skill_dir,
                f"[IO-PATH] 目标目录载荷非法（非 str/PathLike/bytes 或纯空白）: "
                f"{raw_target!r}",
            )
        try:
            skill_path = Path(skill_dir)
            is_dir = skill_path.is_dir()
        except (ValueError, OSError) as _e:
            log_swallowed(
                __name__, _e,
                context='IOStandardizationChecker.check_skill:'
                        f'{type(_e).__name__}')
            return Path(""), self._path_error_report(
                skill_dir,
                f"[IO-PATH] 目标目录路径不可解析: {skill_dir!r}",
            )
        if not is_dir:
            return skill_path, self._path_error_report(
                str(skill_path),
                f"[IO-PATH] 目标目录不存在或不可访问: {skill_dir}",
            )
        return skill_path, None
    @staticmethod
    def _path_error_report(skill_dir: str, issue_prefix: str) -> IOStandardizationReport:
        return IOStandardizationReport(
            skill_dir=skill_dir,
            overall_score=0.0,
            issues=[(
                f"{issue_prefix}，"
                "本次未扫描任何文件（覆盖率 0% 为路径错误所致，非函数质量结论）"
            )],
            suggestions=["核对目标目录路径是否正确后再执行 I/O 标准化检查"],
        )
    def check_skill(self, skill_dir: str | os.PathLike) -> IOStandardizationReport:
        skill_path, err_report = self._validate_skill_dir(skill_dir)
        if err_report is not None:
            return err_report
        py_files = SkillApiScanner._iter_module_py_files(
            skill_path,
            frozenset(scan_exclude_dirs(str(skill_path))),
            include_scripts=True)
        all_specs: list[IOSpec] = []
        for py_file in py_files:
            all_specs.extend(self._check_file(str(py_file)))
        return self._build_report(skill_path, all_specs)
    def _build_report(self, skill_path: Path,
                      all_specs: list[IOSpec]) -> IOStandardizationReport:
        schema_coverage, type_coverage = self._compute_coverage(all_specs)
        report = IOStandardizationReport(
            skill_dir=str(skill_path),
            overall_score=round(
                (schema_coverage * 0.5 + type_coverage * 0.5) * 100, 1),
            func_specs=all_specs,
            schema_coverage=round(schema_coverage, 3),
            type_annotation_coverage=round(type_coverage, 3),
            semantic_gaps=self._collect_semantic_gaps(all_specs),
            recommended_schemas=_generate_recommended_schemas(all_specs),
        )
        report.issues = self._generate_io_issues(report)
        report.suggestions = self._generate_io_suggestions(report)
        return report
    @staticmethod
    def _compute_coverage(all_specs: list[IOSpec]) -> tuple[float, float]:
        total = max(len(all_specs), 1)
        with_schema = sum(
            1 for s in all_specs if s.has_input_schema and s.has_output_schema)
        with_annotation = sum(
            1 for s in all_specs if s.input_types or s.output_type)
        return with_schema / total, with_annotation / total
    @staticmethod
    def _collect_semantic_gaps(all_specs: list[IOSpec]) -> list[dict]:
        return [
            {
                "function": spec.func_name,
                "file": Path(spec.file_path).name,
                "gap": "missing_both_schemas",
            }
            for spec in all_specs
            if not spec.has_input_schema and not spec.has_output_schema
        ]
    def _check_file(self, file_path: str) -> list[IOSpec]:
        specs = []
        content, tree = shared_source_and_tree(file_path)
        if content is None or tree is None:
            _log.warning("_check_file skipped %s: read/parse failed", file_path)
            return specs
        tree = SkillApiScanner._parse_source_ast(content, file_path, tree)
        if tree is None:
            return specs
        for node, has_receiver in _iter_public_function_defs(tree):
            if not is_public_name(node.name):
                continue
            spec = self._analyze_function(
                node, file_path, is_method=has_receiver)
            specs.append(spec)
        return specs
    def _strip_method_receiver(self, positional_all: list, defaults: list) -> tuple[list, list]:
        if not positional_all:
            return positional_all, defaults
        receiver_has_default = len(defaults) > 0 and len(positional_all) - len(defaults) == 0
        return positional_all[1:], (defaults[1:] if receiver_has_default else defaults)
    @staticmethod
    def _register_param(spec: IOSpec, arg: ast.arg, *, optional: bool) -> None:
        spec.param_names.append(arg.arg)
        if optional:
            spec.params_with_defaults.add(arg.arg)
        if getattr(arg, "annotation", None):
            spec.input_types[arg.arg] = _annotation_text(arg.annotation)
    def _register_varparam(self, spec: IOSpec, arg: ast.arg, kind: str) -> None:
        if kind == "vararg":
            spec.vararg_name = arg.arg
        else:
            spec.kwarg_name = arg.arg
        self._register_param(spec, arg, optional=True)
    def _collect_param_specs(
        self, node: ast.FunctionDef | ast.AsyncFunctionDef, spec: IOSpec,
        *, is_method: bool,
    ) -> None:
        posonly = list(getattr(node.args, "posonlyargs", []) or [])
        positional_all = posonly + list(node.args.args)
        defaults = list(getattr(node.args, "defaults", []) or [])
        if is_method:
            positional_all, defaults = self._strip_method_receiver(
                positional_all, defaults)
        self._register_positional_params(spec, positional_all, defaults)
        if node.args.vararg is not None:
            self._register_varparam(spec, node.args.vararg, "vararg")
        self._register_keyword_only_params(
            spec,
            list(getattr(node.args, "kwonlyargs", []) or []),
            list(getattr(node.args, "kw_defaults", []) or []),
        )
        if node.args.kwarg is not None:
            self._register_varparam(spec, node.args.kwarg, "kwarg")
    @staticmethod
    def _register_positional_params(spec: IOSpec, positional_all: list,
                                    defaults: list) -> None:
        n_total = len(positional_all)
        n_defaults = len(defaults)
        for idx, arg in enumerate(positional_all):
            IOStandardizationChecker._register_param(
                spec, arg,
                optional=(n_defaults > 0 and idx >= n_total - n_defaults))
    @staticmethod
    def _register_keyword_only_params(spec: IOSpec, kwonlyargs: list,
                                      kw_defaults: list) -> None:
        for karg, kdef in zip(kwonlyargs, kw_defaults, strict=True):
            IOStandardizationChecker._register_param(
                spec, karg, optional=kdef is not None)
    def _analyze_function(
        self, node: ast.FunctionDef | ast.AsyncFunctionDef, file_path: str,
        *, is_method: bool = False,
    ) -> IOSpec:
        spec = IOSpec(func_name=node.name, file_path=file_path)
        doc = ast.get_docstring(node) or ""
        spec.docstring = doc
        self._collect_param_specs(node, spec, is_method=is_method)
        if node.returns:
            spec.output_type = _annotation_text(node.returns)
        has_param_docs = re.search(
            r"(?m)^[ \t]*(?:Args|Parameters|参数)\s*[:：]", doc, re.IGNORECASE)
        has_return_docs = re.search(
            r"(?m)^[ \t]*(?:Returns?|返回|Outputs?)\s*[:：]", doc, re.IGNORECASE)
        has_json_schema = bool(_SCHEMA_DECL_RE.search(doc))
        spec.has_input_schema = bool(
            has_param_docs or has_json_schema or spec.input_types
            or not spec.param_names
        )
        spec.has_output_schema = bool(has_return_docs or has_json_schema or spec.output_type)
        agent_ex = re.search(
            r"(?:Agent\s*)?(?:使用示例|Examples?)\s*[:：].*?(?=\n\n|$)",
            doc, re.DOTALL | re.IGNORECASE)
        if agent_ex:
            spec.agent_example = agent_ex.group(0).strip()
        spec.score = self._score_io_spec(spec)
        spec.issues.extend(self._collect_spec_issues(spec))
        return spec
    _CORE_DIMENSION_CAP = 90.0
    _AGENT_EXAMPLE_WEIGHT = 10.0
    def _score_io_spec(self, spec: IOSpec) -> float:
        core_dimensions = (
            (spec.has_input_schema, 30),
            (spec.has_output_schema, 30),
            (bool(spec.input_types), 20),
            (bool(spec.output_type), 20),
        )
        core = min(
            self._CORE_DIMENSION_CAP,
            sum(weight for hit, weight in core_dimensions if hit),
        )
        return core + (self._AGENT_EXAMPLE_WEIGHT if spec.agent_example else 0.0)
    def _collect_spec_issues(self, spec: IOSpec) -> list[str]:
        issues: list[str] = []
        if not spec.has_input_schema:
            issues.append("缺少输入参数说明或 JSON Schema 定义")
        if not spec.has_output_schema:
            issues.append("缺少返回值说明或 JSON Schema 定义")
        if not spec.agent_example:
            issues.append("缺少 Agent 使用示例")
        return issues
    def _generate_io_issues(self, report: IOStandardizationReport) -> list[str]:
        if not report.func_specs:
            return [
                "[IO-EMPTY] 未发现任何公开函数规格（覆盖率 0% 为空样本所致，非函数质量结论）"
            ]
        issues = []
        if report.schema_coverage < 0.5:
            issues.append(f"JSON Schema 覆盖率仅 {report.schema_coverage * 100:.1f}%，超过半数函数缺少结构化接口定义")
        if report.type_annotation_coverage < 0.5:
            issues.append(f"类型注解覆盖率仅 {report.type_annotation_coverage * 100:.1f}%，Agent 难以推断参数类型")
        type_map: dict[str, set[str]] = {}
        for spec in report.func_specs:
            varparams = {spec.vararg_name, spec.kwarg_name} - {""}
            for param, ptype in spec.input_types.items():
                if param in varparams:
                    continue
                identity = _annotation_identity(ptype)
                if identity:
                    type_map.setdefault(param, set()).add(identity)
        for param, types in type_map.items():
            if len(types) > 1:
                issues.append(f"语义断层: 参数 '{param}' 在不同函数中的类型不一致: {sorted(types)}")
        return issues
    def _generate_io_suggestions(self, report: IOStandardizationReport) -> list[str]:
        suggestions = []
        if report.schema_coverage < 0.8:
            suggestions.append("[Schema] 为核心函数添加 JSON Schema 定义，统一用 Dict[str, Any] 描述结构化输入输出")
        if report.type_annotation_coverage < 0.8:
            suggestions.append("[类型注解] 为所有公开函数添加参数和返回值类型提示（str/int/bool/Path/Dict/List等）")
        suggestions.append("[语义标准化] 统一同一概念的类型定义：file_path 一律用 Path/str，options 一律用 Dict[str, Any]")
        suggestions.append("[Agent示例] 在函数 docstring 中添加 'Agent使用示例:' 段落，展示参数和返回值的实际用法")
        suggestions.append("[输出结构] 确保返回值包含结构化数据（字典/列表），避免仅返回自然语言字符串")
        return suggestions
@dataclass(frozen=True)
class _SchemaFacts:
    name: str
    description: str
    parameters: list[ParameterSpec]
    parameters_valid: bool
    parameters_declared: bool
    invalid_parameter_count: int
    returns: str
    examples: list[str]
    invalid_example_count: int
def _schema_facts(schema: FunctionSchema) -> _SchemaFacts:
    parameters_valid = isinstance(schema.parameters, (list, tuple))
    parameters = _schema_params(schema.parameters)
    invalid_parameter_count = (
        len(schema.parameters) - len(parameters) if parameters_valid else 0
    )
    examples = _schema_list(schema.examples)
    return _SchemaFacts(
        name=_schema_str(schema.name),
        description=_schema_str(schema.description),
        parameters=parameters,
        parameters_valid=parameters_valid,
        parameters_declared=parameters_valid and bool(schema.parameters),
        invalid_parameter_count=invalid_parameter_count,
        returns=_schema_str(schema.returns),
        examples=examples,
        invalid_example_count=(
            len(schema.examples) - len(examples)
            if isinstance(schema.examples, (list, tuple)) else 0
        ),
    )
def _invalid_schema_entry_issues(facts: _SchemaFacts) -> list[str]:
    issues: list[str] = []
    if facts.invalid_parameter_count:
        issues.append(f"存在 {facts.invalid_parameter_count} 个非法参数定义")
    if facts.invalid_example_count:
        issues.append(f"存在 {facts.invalid_example_count} 个非法示例定义")
    return issues
def _collect_optimization_gaps(returns: str, examples: list[str], desc: str,
                               parameters_valid: bool
                               ) -> tuple[list[str], list[str]]:
    checks = (
        (parameters_valid, "函数缺少参数定义", "添加 ParameterSpec 参数定义"),
        (bool(returns), "函数缺少返回值类型", "添加返回值类型注解"),
        (bool(examples), "函数缺少使用示例", "添加至少一个调用示例"),
        (bool(desc), "函数缺少描述", "添加简洁的功能描述"),
    )
    issues = [issue for present, issue, _ in checks if not present]
    suggestions = [suggestion for present, _, suggestion in checks if not present]
    return issues, suggestions
class FunctionCallOptimizer:
    def _optimize_param(self, param: ParameterSpec) -> ParameterSpec:
        raw = _schema_str(param.description)
        name = _schema_str(param.name)
        desc = raw or f"参数 {name}".strip()
        if desc[-1] not in _SENTENCE_TERMINATORS:
            desc += "。"
        return replace(param, name=name, description=desc)
    def _validate_parameters(self, parameters: list[ParameterSpec]) -> list[str]:
        issues: list[str] = []
        for p in parameters:
            name = _schema_str(p.name)
            if not name:
                issues.append("存在未命名的参数")
            if not _schema_str(p.type):
                issues.append(f"参数 '{name}' 缺少类型声明")
            if not _schema_str(p.description):
                issues.append(f"参数 '{name}' 缺少描述")
        return issues
    def validate(self, schema: FunctionSchema) -> list[str]:
        facts = _schema_facts(schema)
        issues: list[str] = []
        if not facts.name:
            issues.append("函数名为空")
        issues.extend(self._validate_description(facts.description))
        if not facts.parameters_valid:
            issues.append("缺少参数定义")
        else:
            issues.extend(self._validate_parameters(facts.parameters))
        issues.extend(_invalid_schema_entry_issues(facts))
        if not facts.returns:
            issues.append("缺少返回值类型声明")
        if not facts.examples:
            issues.append("缺少使用示例")
        return issues
    @staticmethod
    def _validate_description(desc: str) -> list[str]:
        desc = _schema_str(desc)
        if not desc:
            return ["缺少函数描述"]
        if len(desc) < _MIN_DESC_LENGTH:
            return [f"函数描述过短({len(desc)}字符)，建议至少{_MIN_DESC_LENGTH}字符"]
        return []
    def _score_schema(self, schema: FunctionSchema) -> float:
        facts = _schema_facts(schema)
        earned = (
            (_WEIGHT_DESCRIPTION
             if len(facts.description) >= _MIN_DESC_LENGTH else 0.0)
            + min(_WEIGHT_PARAMETERS,
                  len(facts.parameters) * _STEP_PARAMETER_SCORE)
            + (_WEIGHT_RETURNS if facts.returns else 0.0)
            + min(_WEIGHT_EXAMPLES, len(facts.examples) * _STEP_EXAMPLE_SCORE)
        )
        applicable_weight = (
            1.0 if not facts.parameters_valid or facts.parameters_declared
            else 1.0 - _WEIGHT_PARAMETERS)
        return earned / applicable_weight
    def optimize(self, schema: FunctionSchema) -> FunctionOptimizationResult:
        facts = _schema_facts(schema)
        new_params = [self._optimize_param(p) for p in facts.parameters]
        opt = FunctionSchema(
            name=facts.name,
            description=facts.description or f"函数 {facts.name}",
            parameters=new_params,
            returns=facts.returns,
            examples=facts.examples or [f"调用 {facts.name} 示例"],
        )
        score_before = self._score_schema(schema)
        score_after = self._score_schema(opt)
        issues, suggestions = _collect_optimization_gaps(
            facts.returns, facts.examples, facts.description,
            facts.parameters_valid)
        issues.extend(_invalid_schema_entry_issues(facts))
        return FunctionOptimizationResult(
            original_schema=schema,
            optimized_schema=opt,
            issues=issues,
            suggestions=suggestions,
            score_before=score_before,
            score_after=score_after,
        )
@observation_gate("IO standardization check")
def run_io_standardization_gate(target_dir: str) -> None:
    target_dir = coerce_skill_dir(target_dir)
    if not target_dir or not os.path.isdir(target_dir):
        _log.warning(
            "[init] IO standardization skipped: invalid target %r",
            target_dir)
        return
    io_report = IOStandardizationChecker().check_skill(target_dir)
    _log.info(
        "[init] IO标准化: schema覆盖=%.2f 类型注解覆盖=%.2f 问题%d条 建议%d条",
        io_report.schema_coverage,
        io_report.type_annotation_coverage,
        len(io_report.issues), len(io_report.suggestions))
def _collect_init_antipatterns(init_py_path: str) -> list[dict]:
    issues: list[dict] = []
    issues.extend(LazyImportEliminator().detect(init_py_path))
    issues.extend(DeadCodeEliminator().detect(init_py_path))
    issues.extend(StubEliminator().detect(init_py_path))
    facade = FacadeOptimizer().check(init_py_path)
    if facade.get("error") is not None:
        issues.append({
            "type": "C1_facade", "line": 0,
            "message": str(facade["error"]),
        })
    elif not facade.get("ok", True):
        issues.append({
            "type": "C1_facade", "line": 0,
            "message": "门面数量 {} 超过上限 {}".format(
                facade.get("facade_count"), facade.get("max_facade")),
        })
    return issues
@observation_gate("Code quality baseline check")
def run_code_quality_gate(target_dir: str) -> None:
    target_dir = coerce_skill_dir(target_dir)
    if not target_dir or not os.path.isdir(target_dir):
        _log.warning(
            "[init] Code quality baseline skipped: invalid target %r",
            target_dir)
        return
    init_py_path = os.path.join(target_dir, "__init__.py")
    if not os.path.isfile(init_py_path):
        return
    ap_issues = _collect_init_antipatterns(init_py_path)
    if ap_issues:
        _log.warning("[init] Code quality baseline found %d anti-patterns in __init__.py", len(ap_issues))
        for iss in ap_issues[:5]:
            _log.warning("[init]   %s (line %s)", iss.get("type", "?"), iss.get("line", "?"))
    else:
        _log.info("[init] Code quality baseline: passed")
@observation_gate("Architecture quality check")
def run_architecture_quality_gate(target_dir: str) -> None:
    target_dir = coerce_skill_dir(target_dir)
    if not target_dir or not os.path.isdir(target_dir):
        _log.warning(
            "[init] Architecture quality check skipped: invalid target %r",
            target_dir)
        return
    arch_result = DirFileGuard().check_directory(target_dir)
    arch_violations = getattr(arch_result, 'arch_violations', []) or []
    if arch_violations or not getattr(arch_result, 'ok', True):
        _log.warning(
            "[init] Architecture quality check found %d issues (ok=%s): %s",
            len(arch_violations), getattr(arch_result, 'ok', True),
            getattr(arch_result, 'message', ''))
    else:
        _log.info("[init] Architecture quality check: passed")
def build_function_schema(
    skill_name: str, description: str
) -> FunctionOptimizationResult:
    skill_name = _schema_str(skill_name)
    description = _schema_str(description)
    func_name = skill_name.replace("-", "_")
    schema = FunctionSchema(
        name=func_name,
        description=description,
        parameters=[
            ParameterSpec(
                name="input", type="string", required=False, default="",
                description="用户输入或任务描述",
            ),
        ],
    )
    return FunctionCallOptimizer().optimize(schema)
def validate_skill_function_schemas(schemas: list[FunctionSchema]) -> dict[str, list[str]]:
    optimizer = FunctionCallOptimizer()
    results: dict[str, list[str]] = {}
    if isinstance(schemas, FunctionSchema):
        candidates = (schemas,)
    elif (isinstance(schemas, Iterable)
          and not isinstance(schemas, (str, bytes, dict))):
        candidates = schemas
    elif schemas is None:
        candidates = ()
    else:
        candidates = (schemas,)
    for i, schema in enumerate(candidates):
        if not isinstance(schema, FunctionSchema):
            key = _dedup_schema_key(results, f"(invalid #{i})")
            results[key] = [f"非法函数规格定义: {type(schema).__name__}"]
            continue
        key = _dedup_schema_key(
            results, _schema_str(schema.name) or f"(unnamed #{i})")
        results[key] = optimizer.validate(schema)
    return results

from __future__ import annotations

import argparse
import ast
import importlib.util
import json
import logging
import math
import os
import re
import subprocess
import sys
import time
from collections import Counter, defaultdict
from collections.abc import Iterable
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any

from jwsgj.diag_guard_io import (
    compile_error,
)
from jwsgj.diag_guard_state import (
    read_json_artifact,
    write_json_artifact,
)
from jwsgj.diag_types_vocab import DIAGNOSIS_METHOD_BUDGET_S
from jwsgj.diag_shared_ast_bindings import (
    binding_names_of,
    module_binding_names,
)
from jwsgj.diag_shared_ast_nodes import (
    assign_targets_value,
    iter_scope_statements,
    relative_import_targets,
)
from jwsgj.diag_shared_ast_surface import collect_module_exports_ordered
from jwsgj.diag_shared_source_core import (
    ASTUtils,
    aligned_source_lines,
    parse_cached,
    parse_py_file,
    read_source_with_fingerprint,
    resolve_module_name,
)
from jwsgj.diag_types_normalize import (
    is_number,
)
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import (
    WORKSPACE_ENV_VAR,
    get_workspace_output_dir,
    is_workspace_root_available,
    subprocess_noartifact_env,
)
from jwsgj.runtime_scope import (
    DEFAULT_TEST_DIR_NAME,
    TEST_DIR_CANDIDATES,
    is_py_source_file,
    is_test_source_basename,
    is_under_root,
    iter_py_files,
    py_stem,
    resolve_search_root,
)

_log = logging.getLogger(__name__)
__all__ = [
    'CONTRACT_COMMANDS',
    'INFRA_CONTRACT_ENV_VAR',
    'INFRA_CONTRACT_FILENAME',
    'INFRA_CONTRACT_SCHEMA',
    'APISnapshot',
    'APISurfaceExtractor',
    'GateSeverity',
    'GateViolation',
    'InfraContractReport',
    'InfraContractStage',
    'PostRefactorValidator',
    'RefactorValidationResult',
    'StageGateChecker',
    'ValidationItem',
    'ValidationReport',
    'build_infra_contract',
    'check_import_edge_removed',
    'check_infra_contract',
    'cmd_contract',
    'diff_infra_contract',
    'diff_module_signatures',
    'discover_infra_modules',
    'load_module_signatures',
    'normalize_prev_signatures',
    'register_cli_contract',
    'resolve_infra_contract_path',
    'validate_all_exports',
]
_log.info("refactor_api_contract 已加载: %d 项导出", len(__all__))
class GateSeverity(Enum):
    BLOCK = "block"
    WARN = "warn"
    INFO = "info"
@dataclass
class GateViolation:
    gate_id: str
    severity: GateSeverity
    description: str
    detail: str = ""
    def to_dict(self) -> dict:
        return {
            "gate_id": self.gate_id,
            "severity": self.severity.value,
            "description": self.description,
            "detail": self.detail,
        }
@dataclass
class RefactorValidationResult:
    source_dir: str
    target_dir: str
    passed: bool
    violations: list[GateViolation]
    stats: dict
    def summary(self) -> str:
        if self.passed:
            return f"PASSED: {self.source_dir} → {self.target_dir}"
        blocks = [v for v in self.violations if v.severity == GateSeverity.BLOCK]
        warns = [v for v in self.violations if v.severity == GateSeverity.WARN]
        return f"BLOCKED ({len(blocks)} blocks, {len(warns)} warns)"
    def to_dict(self) -> dict:
        return {
            "source_dir": self.source_dir,
            "target_dir": self.target_dir,
            "passed": self.passed,
            "summary": self.summary(),
            "violations": [v.to_dict() for v in self.violations],
            "stats": self.stats,
        }
def _normalize_size_threshold(value, default: float) -> float:
    if not is_number(value):
        return default
    ratio = float(value)
    if not math.isfinite(ratio) or ratio <= 0:
        return default
    return ratio
def _text_dir(value: Any) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, os.PathLike):
        return os.fspath(value)
    return ""
def _absolute_directory_module_label(directory: str) -> str:
    init_path = os.path.join(directory, "__init__.py")
    if os.path.isfile(init_path):
        return resolve_module_name(init_path)
    return os.path.basename(os.path.normpath(directory))
_GATE_EXCLUDED_BASENAMES = frozenset({"__init__.py"})
_SOURCE_CONTAINER_DIRS = ("src", "python", "lib")
_DEFAULT_PROJECT_ROOT = ""
class StageGateChecker:
    SIZE_RATIO_THRESHOLD = 0.3
    @staticmethod
    def _safe_getsize(filepath: str) -> int:
        try:
            return os.path.getsize(filepath)
        except OSError as _e:
            log_swallowed(__name__, _e, context='StageGateChecker._safe_getsize:OSError')
            return 0
    @staticmethod
    def _match_target_candidates(base_stem: str,
                                 target_paths: Iterable[str]) -> list[str]:
        exact = [t for t in target_paths
                 if os.path.basename(t) == base_stem + '.py']
        siblings = [
            t for t in target_paths
            if t not in exact
            and (os.path.basename(t).startswith(base_stem + '_')
                 or os.path.basename(t).endswith('_' + base_stem + '.py'))]
        return exact + siblings
    def __init__(self, source_root: str = _DEFAULT_PROJECT_ROOT,
                 target_root: str = _DEFAULT_PROJECT_ROOT) -> None:
        self.source_root = _text_dir(source_root)
        self.target_root = _text_dir(target_root)
    def check(
        self,
        source_subdir: str,
        target_subdir: str,
        size_threshold: float | None = None,
    ) -> RefactorValidationResult:
        violations: list[GateViolation] = []
        stats: dict = {}
        if (not isinstance(source_subdir, str) or not source_subdir.strip()
                or not isinstance(target_subdir, str)
                or not target_subdir.strip()):
            violations.append(GateViolation(
                gate_id="GATE-FILE",
                severity=GateSeverity.BLOCK,
                description="Source/target subdirectory required",
                detail=(f"source_subdir={source_subdir!r}, "
                        f"target_subdir={target_subdir!r}；空子目录会被"
                        "解析成项目根，源目标自比自不可作为迁移证据"),
            ))
            stats.update(source_files=0, target_files=0,
                         source_non_empty=0, target_non_empty=0)
            return RefactorValidationResult(
                source_dir=str(source_subdir), target_dir=str(target_subdir),
                passed=False, violations=violations, stats=stats)
        src_dir = (os.path.join(self.source_root, source_subdir)
                   if self.source_root else source_subdir)
        tgt_dir = (os.path.join(self.target_root, target_subdir)
                   if self.target_root else target_subdir)
        if (os.path.normcase(os.path.realpath(src_dir))
                == os.path.normcase(os.path.realpath(tgt_dir))):
            violations.append(GateViolation(
                gate_id="GATE-FILE",
                severity=GateSeverity.BLOCK,
                description="Source and target directories must differ",
                detail=(f"source={src_dir!r}, target={tgt_dir!r}；"
                        "同一目录自比自不可作为迁移证据"),
            ))
        src_all, tgt_all, src_ok, tgt_ok = self._gate_file(
            src_dir, tgt_dir, violations, stats)
        self._gate_api(src_all, tgt_all, src_ok, tgt_ok, violations)
        self._gate_size(self._module_files(src_all),
                        self._module_files(tgt_all),
                        size_threshold, violations)
        self._gate_import(src_dir, tgt_dir, source_subdir, violations)
        gate_counts = Counter(v.gate_id for v in violations)
        stats.update(api_issues=gate_counts["GATE-API"],
                     size_warnings=gate_counts["GATE-SIZE"],
                     import_issues=gate_counts["GATE-IMPORT"])
        has_blocks = any(v.severity == GateSeverity.BLOCK for v in violations)
        return RefactorValidationResult(
            source_dir=source_subdir,
            target_dir=target_subdir,
            passed=not has_blocks,
            violations=violations,
            stats=stats,
        )
    @staticmethod
    def _module_files(files: list[str]) -> list[str]:
        return [f for f in files
                if os.path.basename(f) not in _GATE_EXCLUDED_BASENAMES]
    def _gate_file(self, src_dir, tgt_dir, violations, stats):
        src_listing = self._list_py_files(src_dir)
        src_ok = src_listing is not None
        src_all = src_listing or []
        src_files = self._module_files(src_all)
        if not src_ok:
            violations.append(GateViolation(
                gate_id="GATE-FILE",
                severity=GateSeverity.BLOCK,
                description="Source directory unreadable",
                detail=f"Source directory cannot be listed: {src_dir}",
            ))
        elif not os.path.isdir(src_dir):
            violations.append(GateViolation(
                gate_id="GATE-FILE",
                severity=GateSeverity.BLOCK,
                description="Source directory not found",
                detail=f"Source directory missing: {src_dir}",
            ))
        elif not src_all:
            violations.append(GateViolation(
                gate_id="GATE-FILE",
                severity=GateSeverity.BLOCK,
                description="Source directory has no Python files",
                detail=(f"Source directory contains no Python files: {src_dir}；"
                        "空源目录不能作为迁移已验证的证据"),
            ))
        tgt_listing = self._list_py_files(tgt_dir)
        tgt_ok = tgt_listing is not None
        tgt_all = tgt_listing or []
        tgt_files = self._module_files(tgt_all)
        tgt_exists = os.path.isdir(tgt_dir)
        if not tgt_ok:
            violations.append(GateViolation(
                gate_id="GATE-FILE",
                severity=GateSeverity.BLOCK,
                description="Target directory unreadable",
                detail=f"Target directory cannot be listed: {tgt_dir}",
            ))
        elif src_all and not tgt_exists:
            violations.append(GateViolation(
                gate_id="GATE-FILE",
                severity=GateSeverity.BLOCK,
                description="Target directory not found",
                detail=f"Target directory missing: {tgt_dir}",
            ))
        elif src_all and not tgt_all:
            violations.append(GateViolation(
                gate_id="GATE-FILE",
                severity=GateSeverity.BLOCK,
                description="Target directory has no Python files",
                detail=(f"Target directory contains no Python files: {tgt_dir}；"
                        "空目标目录不能作为迁移已验证的证据"),
            ))
        stats["source_files"] = len(src_files)
        stats["target_files"] = len(tgt_files)
        stats["source_non_empty"] = len(
            [f for f in src_files if self._safe_getsize(f) >= 50])
        stats["target_non_empty"] = len(
            [f for f in tgt_files if self._safe_getsize(f) >= 50])
        if (tgt_ok and tgt_exists
                and stats["target_non_empty"] < stats["source_non_empty"]):
            violations.append(GateViolation(
                gate_id="GATE-FILE",
                severity=GateSeverity.BLOCK,
                description="Target has fewer non-empty files than source",
                detail=f"Source: {stats['source_non_empty']} non-empty, "
                       f"Target: {stats['target_non_empty']} non-empty",
            ))
        return src_all, tgt_all, src_ok, tgt_ok
    def _gate_api(self, src_files, tgt_files, src_ok, tgt_ok,
                  violations) -> None:
        src_api, src_unreadable = self._extract_public_api(src_files)
        tgt_api, tgt_unreadable = self._extract_public_api(tgt_files)
        for path in src_unreadable:
            violations.append(GateViolation(
                gate_id="GATE-API",
                severity=GateSeverity.BLOCK,
                description="Source file API surface unreadable",
                detail=f"API 面不可验证（不可读/不可解析）: {path}",
            ))
        for path in tgt_unreadable:
            violations.append(GateViolation(
                gate_id="GATE-API",
                severity=GateSeverity.BLOCK,
                description="Target file API surface unreadable",
                detail=f"API 面不可验证（不可读/不可解析）: {path}",
            ))
        if not src_ok or not tgt_ok:
            return
        for src_file, src_symbols in src_api.items():
            base_name = os.path.splitext(os.path.basename(src_file))[0]
            matched = self._match_target_candidates(base_name, tgt_api)
            if not matched:
                violations.append(GateViolation(
                    gate_id="GATE-API",
                    severity=GateSeverity.WARN,
                    description=f"No target file found for source: {base_name}",
                    detail=f"Source file: {src_file}",
                ))
            candidates = list(tgt_api)
            self._append_api_gap_violations(
                violations, base_name, src_symbols, candidates, tgt_api)
    @staticmethod
    def _append_api_gap_violations(
        violations: list[GateViolation],
        base_name: str,
        src_symbols: dict,
        candidates: list[str],
        tgt_api: dict[str, dict],
    ) -> None:
        reported: set[str] = set()
        for kind, src_names in (("classes", src_symbols["classes"]),
                                ("functions", src_symbols["functions"]),
                                ("exports", src_symbols["all"])):
            target_keys = ("all",) if kind == "exports" else (kind, "all")
            target_names: set[str] = set()
            for candidate in candidates:
                candidate_api = tgt_api[candidate]
                bindings = candidate_api.get("bindings")
                public_symbols = candidate_api["public_symbols"]
                for key in target_keys:
                    names = candidate_api[key]
                    if key == "all" and bindings is not None:
                        names = names & bindings
                    if kind in ("classes", "functions"):
                        expected = "class" if kind == "classes" else "function"
                        names = {
                            name for name in names
                            if (meta := public_symbols.get(name)) is None
                            or meta.get("kind") in (expected, "import")
                            or (meta.get("kind") == "const"
                                and meta.get("interface") == "type=expr")
                        }
                    target_names |= names
            missing = src_names - target_names - reported
            if not missing:
                continue
            reported |= missing
            violations.append(GateViolation(
                gate_id="GATE-API",
                severity=GateSeverity.BLOCK,
                description=f"Missing {kind} in target for {base_name}",
                detail=(f"Missing {kind}: "
                        f"{', '.join(sorted(missing)[:5])}"),
            ))
    def _gate_size(self, src_files, tgt_files, size_threshold,
                   violations) -> None:
        size_threshold = _normalize_size_threshold(
            size_threshold, self.SIZE_RATIO_THRESHOLD)
        for src_file in src_files:
            src_sz = self._safe_getsize(src_file)
            if src_sz < 100:
                continue
            violation = self._size_gap(src_file, src_sz, tgt_files,
                                       size_threshold)
            if violation is not None:
                violations.append(violation)
    def _size_gap(self, src_file: str, src_sz: int, tgt_files: list[str],
                  size_threshold: float) -> GateViolation | None:
        base_full = os.path.basename(src_file)
        base_stem = os.path.splitext(base_full)[0]
        matching = self._match_target_candidates(base_stem, tgt_files)
        if not matching:
            return None
        tgt_sz = sum(self._safe_getsize(t) for t in matching)
        if tgt_sz >= src_sz * size_threshold:
            return None
        return GateViolation(
            gate_id="GATE-SIZE",
            severity=GateSeverity.WARN,
            description=f"Size ratio below threshold for {base_full}",
            detail=(f"Source: {src_sz}B, "
                    f"Target({len(matching)} file(s)): {tgt_sz}B, "
                    f"Ratio: {tgt_sz / max(src_sz, 1):.1%}"),
        )
    def _gate_import(self, src_dir, tgt_dir, source_subdir,
                     violations) -> None:
        src_prefix = self._source_module_prefix(src_dir, source_subdir)
        if src_prefix:
            violations.extend(self._reverse_import_violations(
                tgt_dir, src_prefix, source_subdir))
    def _reverse_import_violations(self, tgt_dir: str, src_prefix: str,
                                   source_subdir: str) -> list[GateViolation]:
        found: list[GateViolation] = []
        for tgt_file in self._list_py_files(tgt_dir) or ():
            label, is_package = self._target_module_label(tgt_file)
            for mod in self._extract_import_modules(
                    tgt_file, label, is_package, expand_submodules=True):
                if mod == src_prefix or mod.startswith(src_prefix + '.'):
                    found.append(GateViolation(
                        gate_id="GATE-IMPORT",
                        severity=GateSeverity.BLOCK,
                        description=("Target file imports source module: "
                                     f"{os.path.basename(tgt_file)}"),
                        detail=(f"Import '{mod}' references source directory "
                                f"'{source_subdir}'；迁移收尾删除源目录会"
                                "断裂该导入链"),
                    ))
                    break
        return found
    def _source_module_prefix(self, src_dir: str, source_subdir: str) -> str:
        base = source_subdir
        if self.source_root:
            try:
                rel = os.path.relpath(src_dir, self.source_root)
            except ValueError as _e:
                log_swallowed(__name__, _e, context='StageGateChecker._source_module_prefix:ValueError')
                rel = None
            if rel is not None and rel not in (os.curdir, os.pardir) \
                    and not rel.startswith(os.pardir + os.sep):
                base = rel
            elif os.path.isabs(src_dir):
                return _absolute_directory_module_label(src_dir)
        elif os.path.isabs(src_dir):
            return _absolute_directory_module_label(src_dir)
        return _migration_import_label(self.source_root, base)
    def _target_module_label(self, tgt_file: str) -> tuple[str | None, bool]:
        root = self.target_root
        is_package = os.path.basename(tgt_file).lower() == "__init__.py"
        if not root and os.path.isabs(tgt_file):
            return resolve_module_name(tgt_file), is_package
        try:
            rel = os.path.relpath(tgt_file, root or os.curdir)
        except ValueError as _e:
            log_swallowed(__name__, _e, context='StageGateChecker._target_module_label:ValueError')
            if os.path.isabs(tgt_file):
                return resolve_module_name(tgt_file), is_package
            return None, False
        if rel == os.pardir or rel.startswith(os.pardir + os.sep):
            if os.path.isabs(tgt_file):
                return resolve_module_name(tgt_file), is_package
            return None, False
        label = _migration_import_label(root, rel)
        if is_package and label.lower() == "__init__":
            return "", True
        return label, is_package
    def _extract_import_modules(self, filepath: str,
                                module_label: str | None,
                                is_package: bool,
                                expand_submodules: bool) -> list[str]:
        source, _fingerprint = read_source_with_fingerprint(filepath)
        if source is None:
            return []
        try:
            tree = parse_cached(source, filename=filepath)
        except PARSE_DEGRADE_EXC as e:
            _log.warning("[refactor_api_contract] _extract_import_modules 跳过 %s: %s", filepath, e)
            return []
        modules: list[str] = []
        for node in walk_nodes(tree):
            modules.extend(self._node_import_modules(
                node, module_label, is_package, expand_submodules))
        return modules
    @staticmethod
    def _node_import_modules(node: ast.AST,
                             module_label: str | None,
                             is_package: bool,
                             expand_submodules: bool) -> list[str]:
        if isinstance(node, ast.Import):
            return [alias.name for alias in node.names]
        if not isinstance(node, ast.ImportFrom):
            return []
        if node.level == 0:
            if not node.module:
                return []
            if not expand_submodules:
                return [node.module]
            mods = [node.module]
            mods.extend(f"{node.module}.{alias.name}"
                        for alias in node.names if alias.name != "*")
            return mods
        if module_label is None:
            return []
        resolved = _infra_resolve_from_target(
            module_label, node, "", is_package=is_package)
        if resolved is None:
            return []
        if resolved:
            return [resolved] + [f"{resolved}.{alias.name}"
                                 for alias in node.names
                                 if alias.name != "*"]
        return [alias.name for alias in node.names if alias.name != "*"]
    def _list_py_files(self, directory: str) -> list[str] | None:
        if not os.path.isdir(directory):
            return []
        try:
            return sorted(
                path for path in iter_py_files(directory)
                if is_py_source_file(path))
        except OSError as e:
            _log.warning(
                "[StageGateChecker] 目录列举失败（按不可验证处理）: %s: %s",
                directory, e)
            return None
    def _extract_public_api(self, files: list[str]
                            ) -> tuple[dict[str, dict], list[str]]:
        api: dict[str, dict] = {}
        unreadable: list[str] = []
        extractor = APISurfaceExtractor()
        for fpath in files:
            snapshot = extractor.extract(fpath)
            if not snapshot.readable:
                unreadable.append(fpath)
                continue
            exports = snapshot.exports
            api[fpath] = {
                "classes": set(exports.get("classes", [])),
                "functions": set(exports.get("functions", [])),
                "all": set(exports.get("all", [])),
                "bindings": set(getattr(snapshot, "_bound_names", ())),
                "public_symbols": dict(getattr(
                    snapshot, "_public_symbols", {})),
            }
        return api, unreadable
@dataclass
class APISnapshot:
    exports: dict[str, list[str]] = field(default_factory=dict)
    timestamp: float = 0.0
    signatures: dict[str, str] = field(default_factory=dict)
    readable: bool = True
    method_bindings: dict[str, list[str]] = field(default_factory=dict)
def _snapshot_exports(snapshot: APISnapshot) -> dict:
    exports = getattr(snapshot, "exports", None)
    if not isinstance(exports, dict):
        return {}
    return {key: value for key, value in exports.items()
            if isinstance(key, str)}
def _snapshot_signatures(snapshot: APISnapshot) -> dict:
    signatures = getattr(snapshot, "signatures", None)
    if not isinstance(signatures, dict):
        return {}
    return {key: value for key, value in signatures.items()
            if isinstance(key, str)}
def _snapshot_method_bindings(snapshot: APISnapshot) -> dict[str, list[str]]:
    bindings = getattr(snapshot, "method_bindings", None)
    if not isinstance(bindings, dict):
        return {}
    return {
        key: [item for item in value if isinstance(item, str)]
        for key, value in bindings.items()
        if isinstance(key, str) and isinstance(value, (list, tuple))
    }
def _export_names(exports: dict, key: str) -> set[str]:
    value = exports.get(key)
    if not isinstance(value, (list, tuple, set, frozenset)):
        return set()
    return {name for name in value if isinstance(name, str)}
def _is_public_surface_name(name: str, export_names: set[str]) -> bool:
    return not name.startswith("_") or name in export_names
def _safe_unparse_expr(x: ast.AST | None) -> str:
    if x is None:
        return ""
    try:
        return ast.unparse(x)
    except (ValueError, TypeError, SyntaxError) as _e:
        log_swallowed(__name__, _e, context='_safe_unparse_expr:ValueError')
        return "..."
def _fmt_param(name: str, annotation: ast.AST | None = None) -> str:
    if annotation is None:
        return name
    return f"{name}: {_safe_unparse_expr(annotation)}"
def _type_params_text(node: ast.AST) -> str:
    params = getattr(node, "type_params", None) or ()
    if not params:
        return ""
    return "[" + ", ".join(_safe_unparse_expr(param) for param in params) + "]"
def _format_signature(node: ast.FunctionDef | ast.AsyncFunctionDef) -> str:
    args = node.args
    parts: list[str] = []
    _format_positional(args, parts)
    _format_kwonly(args, parts)
    if args.kwarg is not None:
        parts.append("**" + _fmt_param(args.kwarg.arg, args.kwarg.annotation))
    signature = ("async " if isinstance(node, ast.AsyncFunctionDef) else "")
    signature += _type_params_text(node) + "(" + ", ".join(parts) + ")"
    if node.returns is not None:
        signature += " -> " + _safe_unparse_expr(node.returns)
    return signature
def _positional_layout(args: ast.arguments
                       ) -> list[tuple[ast.arg | None, ast.AST | None]]:
    positional = [*args.posonlyargs, *args.args]
    defaults = list(args.defaults)
    pad = len(positional) - len(defaults)
    layout: list[tuple[ast.arg | None, ast.AST | None]] = []
    for index, arg in enumerate(positional):
        if args.posonlyargs and index == len(args.posonlyargs):
            layout.append((None, None))
        layout.append(
            (arg, defaults[index - pad] if index >= pad else None))
    if args.posonlyargs and not args.args:
        layout.append((None, None))
    return layout
def _format_positional(args: ast.arguments, parts: list[str]) -> None:
    for arg, default in _positional_layout(args):
        if arg is None:
            parts.append("/")
            continue
        text = _fmt_param(arg.arg, arg.annotation)
        if default is not None:
            text += " = " + _safe_unparse_expr(default)
        parts.append(text)
def _format_kwonly(args: ast.arguments, parts: list[str]) -> None:
    if args.vararg is not None:
        parts.append("*" + _fmt_param(args.vararg.arg, args.vararg.annotation))
    elif args.kwonlyargs:
        parts.append("*")
    for a, d in zip(args.kwonlyargs, args.kw_defaults, strict=True):
        s = _fmt_param(a.arg, a.annotation)
        if d is not None:
            s += " = " + _safe_unparse_expr(d)
        parts.append(s)
class APISurfaceExtractor:
    def extract(self, filepath: str) -> APISnapshot:
        fp = Path(filepath)
        if not fp.exists():
            return APISnapshot(readable=False)
        source, _fingerprint = read_source_with_fingerprint(str(fp))
        if source is None:
            _log.debug("[refactor_api_contract] extract 源文件读取失败，API 快照按空处理: %s", fp)
            return APISnapshot(readable=False)
        try:
            tree = parse_cached(source, filename=str(fp))
        except PARSE_DEGRADE_EXC as _e:
            log_swallowed(__name__, _e, context='APISurfaceExtractor.extract:SyntaxError')
            return APISnapshot(readable=False)
        exports, signatures = self._surface_from_tree(tree)
        snapshot = APISnapshot(
            exports=exports, timestamp=time.time(), signatures=signatures,
            method_bindings=_public_class_method_bindings(tree))
        public_symbols = _infra_public_symbol_table(tree)
        snapshot._bound_names = frozenset(public_symbols)
        snapshot._public_symbols = public_symbols
        return snapshot
    @staticmethod
    def _surface_from_tree(tree: ast.Module
                           ) -> tuple[dict[str, list[str]], dict[str, str]]:
        exports: dict[str, list[str]] = {"classes": [], "functions": [], "all": []}
        signatures: dict[str, str] = {}
        export_order = collect_module_exports_ordered(tree)[0]
        export_names = set(export_order)
        for node, _in_handler in iter_scope_statements(tree, include_defs=True):
            if isinstance(node, ast.ClassDef) and _is_public_surface_name(
                    node.name, export_names):
                exports["classes"].append(node.name)
                method_signatures = _class_public_surface(node)[2]
                for method_name, signature in method_signatures.items():
                    signatures[f"{node.name}.{method_name}"] = signature
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) \
                    and _is_public_surface_name(node.name, export_names):
                exports["functions"].append(node.name)
                signatures[node.name] = _format_signature(node)
        exports["all"] = export_order
        return exports, signatures
    def compare(self, before: APISnapshot, after: APISnapshot) -> dict:
        added, removed = self._surface_diff(before, after)
        signature_added, signature_removed = self._signature_lifecycle_diff(
            before, after)
        signature_changes = self._signature_changes(before, after)
        return {
            "added": added,
            "removed": removed,
            "changed": bool(
                added or removed or signature_added or signature_removed
                or signature_changes),
            "signature_added": signature_added,
            "signature_removed": signature_removed,
            "signature_changes": signature_changes,
        }
    @staticmethod
    def _surface_diff(before: APISnapshot, after: APISnapshot
                      ) -> tuple[list[str], list[str]]:
        added: list[str] = []
        removed: list[str] = []
        before_exports = _snapshot_exports(before)
        after_exports = _snapshot_exports(after)
        for key in sorted(set(before_exports) | set(after_exports)):
            before_set = _export_names(before_exports, key)
            after_set = _export_names(after_exports, key)
            added.extend(f"{key}:{a}" for a in sorted(after_set - before_set))
            removed.extend(f"{key}:{r}" for r in sorted(before_set - after_set))
        return added, removed
    @staticmethod
    def _signature_lifecycle_diff(
            before: APISnapshot, after: APISnapshot) -> tuple[list[str], list[str]]:
        before_names = set(_snapshot_signatures(before))
        after_names = set(_snapshot_signatures(after))
        added = sorted(after_names - before_names)
        removed = sorted(before_names - after_names)
        return added, removed
    @staticmethod
    def _signature_changes(before: APISnapshot, after: APISnapshot) -> list[str]:
        changes = []
        before_sigs = _snapshot_signatures(before)
        after_sigs = _snapshot_signatures(after)
        has_bindings = all(
            "method_bindings" in getattr(snapshot, "__dict__", {})
            for snapshot in (before, after))
        before_bindings = _snapshot_method_bindings(before) if has_bindings else {}
        after_bindings = _snapshot_method_bindings(after) if has_bindings else {}
        for name in sorted(set(before_sigs) & set(after_sigs)):
            if not isinstance(name, str):
                continue
            kind = "classes" if "." in name else "functions"
            if before_sigs[name] != after_sigs[name]:
                changes.append(
                    f"{kind}:{name}: {before_sigs[name]}"
                    f" -> {after_sigs[name]}")
            before_binding = before_bindings.get(name, [])
            after_binding = after_bindings.get(name, [])
            if before_binding != after_binding:
                changes.append(
                    f"{kind}:{name}: binding {before_binding} -> {after_binding}")
        return changes
def _valid_module_name(module: Any) -> bool:
    return (isinstance(module, str) and bool(module)
            and all(part.isidentifier() for part in module.split(".")))
def _resolve_module_file(root_dir: str, module: str) -> tuple[str | None, bool]:
    if not _valid_module_name(module):
        return None, False
    root_dir = _text_dir(root_dir)
    segs = module.split('.')
    pkg_init = os.path.join(root_dir, *segs, '__init__.py')
    if os.path.isfile(pkg_init):
        return pkg_init, True
    fpath = os.path.join(root_dir, *segs) + '.py'
    if os.path.isfile(fpath):
        return fpath, False
    return None, False
def _func_sig(node: ast.FunctionDef | ast.AsyncFunctionDef) -> dict:
    _a = node.args
    _args = ["/" if arg is None else arg.arg
             for arg, _default in _positional_layout(_a)]
    if not _a.vararg and _a.kwonlyargs:
        _args.append('*')
    if _a.vararg:
        _args.append('*' + _a.vararg.arg)
    _args.extend(p.arg for p in _a.kwonlyargs)
    if _a.kwarg:
        _args.append('**' + _a.kwarg.arg)
    return {
        "type": ("async_function"
                 if isinstance(node, ast.AsyncFunctionDef) else "function"),
        "args": _args,
        "signature": _format_signature(node),
        "line": node.lineno,
    }
def _class_public_surface(
        node: ast.ClassDef) -> tuple[list[str], list[str], dict[str, str]]:
    statements = [
        statement
        for statement, _in_handler in iter_scope_statements(
            node, include_defs=True)
    ]
    method_signatures = {
        item.name: _format_signature(item)
        for item in statements
        if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
        and (not item.name.startswith('_')
             or (item.name.startswith('__') and item.name.endswith('__')))
    }
    methods = sorted(method_signatures)
    attrs = sorted({
        name
        for item in statements
        if isinstance(item, (ast.Assign, ast.AnnAssign))
        for name in module_binding_names(item)
        if not name.startswith('_')
    })
    return methods, attrs, method_signatures
_METHOD_BINDING_DECORATORS = frozenset({
    "property", "cached_property", "staticmethod", "classmethod",
    "getter", "setter", "deleter",
})
_PROPERTY_ACCESSOR_DECORATORS = frozenset({"getter", "setter", "deleter"})
def _binding_decorator_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name):
        name = node.id
    elif isinstance(node, ast.Attribute):
        name = node.attr
    else:
        return None
    return name if name in _METHOD_BINDING_DECORATORS else None
def _class_method_bindings(node: ast.ClassDef) -> dict[str, list[str]]:
    bindings: dict[str, list[str]] = {}
    for item, _in_handler in iter_scope_statements(node, include_defs=True):
        if not isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if item.name.startswith('_') and not (
                item.name.startswith('__') and item.name.endswith('__')):
            continue
        decorators = [name for decorator in item.decorator_list
                      if (name := _binding_decorator_name(decorator)) is not None]
        if (item.name in bindings
                and _PROPERTY_ACCESSOR_DECORATORS.intersection(decorators)):
            bindings[item.name] = list(dict.fromkeys(
                [*bindings[item.name], *decorators]))
        elif decorators:
            bindings[item.name] = decorators
        else:
            bindings.pop(item.name, None)
    return bindings
def _public_class_method_bindings(tree: ast.Module) -> dict[str, list[str]]:
    export_names = set(collect_module_exports_ordered(tree)[0])
    bindings: dict[str, list[str]] = {}
    for node, _in_handler in iter_scope_statements(tree, include_defs=True):
        if not isinstance(node, ast.ClassDef) or not _is_public_surface_name(
                node.name, export_names):
            continue
        for method_name, decorators in _class_method_bindings(node).items():
            bindings[f"{node.name}.{method_name}"] = decorators
    return bindings
def _class_sig(node: ast.ClassDef) -> dict:
    methods, attrs, method_signatures = _class_public_surface(node)
    sig = {
        "type": "class",
        "methods": methods,
        "attrs": attrs,
        "method_signatures": method_signatures,
        "method_bindings": _class_method_bindings(node),
        "line": node.lineno,
    }
    type_params = _type_params_text(node)
    if type_params:
        sig["type_params"] = type_params
    return sig
def _collect_public_signatures(tree: ast.Module) -> dict:
    sigs: dict = {}
    export_names = set(collect_module_exports_ordered(tree)[0])
    for node, _in_handler in iter_scope_statements(tree, include_defs=True):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if _is_public_surface_name(node.name, export_names):
                sigs[node.name] = _func_sig(node)
        elif isinstance(node, ast.ClassDef) and _is_public_surface_name(
                node.name, export_names):
            sigs[node.name] = _class_sig(node)
    return sigs
def _sig_interface_view(sig: dict) -> dict:
    return {k: v for k, v in sig.items() if k != "line"}
def load_module_signatures(root_dir: str, module: str) -> tuple[dict | None, str | None]:
    if not _valid_module_name(module):
        return None, "invalid module name"
    fpath, _ = _resolve_module_file(root_dir, module)
    if fpath is None:
        return None, "file not found"
    result = ASTUtils.parse_file(fpath)
    if result is None:
        return None, "cannot parse"
    tree, _ = result
    return _collect_public_signatures(tree), None
def normalize_prev_signatures(raw: object) -> dict:
    if not isinstance(raw, dict):
        return {}
    return {mod: entries for mod, entries in raw.items()
            if isinstance(entries, dict)}
def _diff_signature(module: str, name: str, prev_sig: object,
                    cur: dict) -> dict | None:
    if name not in cur:
        return {"module": module, "name": name,
                "change": "removed", "prev": prev_sig}
    if not isinstance(prev_sig, dict):
        return {"module": module, "name": name,
                "error": "invalid prev signature"}
    current_view = _sig_interface_view(cur[name])
    previous_view = _sig_interface_view(prev_sig)
    if "method_bindings" not in prev_sig:
        current_view.pop("method_bindings", None)
    if current_view != previous_view:
        return {"module": module, "name": name, "change": "modified",
                "prev": prev_sig, "current": cur[name]}
    return None
def diff_module_signatures(module: str, prev_sigs: dict,
                           root_dir: str) -> tuple[list[dict], int]:
    current, err = load_module_signatures(root_dir, module)
    if current is None:
        return [{"module": module, "error": err}], 0
    if not isinstance(prev_sigs, dict):
        return [{"module": module,
                 "error": "invalid prev signatures"}], 0
    base = prev_sigs.get(module)
    if not isinstance(base, dict):
        return [{"module": module, "error": "no snapshot"}], 0
    changed: list[dict] = []
    unchanged = 0
    for name, sig in base.items():
        change = _diff_signature(module, name, sig, current)
        if change is None:
            unchanged += 1
        else:
            changed.append(change)
    return changed, unchanged
def _matches_import_target(name: str, to_module: str) -> bool:
    return name == to_module or name.startswith(to_module + ".")
def _relative_import_candidates(
        node: ast.ImportFrom,
        from_pkg_segs: list) -> tuple[list[str], list[str]]:
    rel_targets = relative_import_targets(from_pkg_segs, node)
    if rel_targets:
        return (list(rel_targets), []) if node.module else ([], list(rel_targets))
    if node.module:
        return [node.module], []
    return [], [a.name for a in node.names if a.name != "*"]
def _importfrom_candidates(node: ast.ImportFrom,
                           from_pkg_segs: list) -> list[str]:
    if node.level == 0:
        bases = [node.module] if node.module else []
        candidates: list[str] = []
    else:
        bases, candidates = _relative_import_candidates(node, from_pkg_segs)
    candidates.extend(bases)
    for base in bases:
        candidates.extend(f"{base}.{a.name}" for a in node.names)
    return candidates
def _import_name_candidates(node: ast.Import) -> list[str]:
    return [alias.name for alias in node.names]
def _import_candidates(node: ast.AST, from_pkg_segs: list) -> list[str]:
    if isinstance(node, ast.ImportFrom):
        return _importfrom_candidates(node, from_pkg_segs)
    if isinstance(node, ast.Import):
        return _import_name_candidates(node)
    return []
def _source_line_at(lines: list[str], lineno: int) -> str:
    if not isinstance(lineno, int) or lineno < 1 or lineno > len(lines):
        return ""
    return lines[lineno - 1].strip()
def _scan_import_edges(tree: ast.Module, code: str, to_module: str,
                       from_pkg_segs: list,
                       root_package: str = "") -> list[dict]:
    still_importing: list[dict] = []
    lines = aligned_source_lines(code)
    for node in walk_nodes(tree):
        candidates = _import_candidates(node, from_pkg_segs)
        if root_package:
            candidates += [
                candidate[len(root_package) + 1:]
                for candidate in candidates
                if candidate.startswith(root_package + ".")
            ]
        if any(_matches_import_target(c, to_module) for c in candidates):
            still_importing.append({
                "line": node.lineno,
                "symbols": [a.name for a in node.names],
                "source": _source_line_at(lines, node.lineno),
            })
    return still_importing
def check_import_edge_removed(from_module: str, to_module: str,
                              root_dir: str) -> dict:
    if not _valid_module_name(from_module):
        return {"removed": False, "still_imports": [], "source_file": None,
                "import_count": 0, "note": "invalid from_module"}
    if not _valid_module_name(to_module):
        return {"removed": False, "still_imports": [], "source_file": None,
                "import_count": 0, "note": "invalid to_module"}
    root_text = _text_dir(root_dir)
    if not root_text or not os.path.isdir(root_text):
        return {"removed": False, "still_imports": [], "source_file": None,
                "import_count": 0, "note": "invalid root_dir"}
    fpath, is_pkg_init = _resolve_module_file(root_text, from_module)
    if fpath is None:
        return {"removed": True, "still_imports": [], "source_file": None,
                "import_count": 0,
                "note": f"module file for {from_module} not found (possibly deleted)"}
    result = ASTUtils.parse_file(fpath)
    if result is None:
        return {"removed": False, "still_imports": [], "source_file": fpath,
                "import_count": 0,
                "note": "file cannot be parsed; removal unproven"}
    from_pkg_segs = (from_module.split('.') if is_pkg_init
                     else from_module.split('.')[:-1])
    tree, code = result
    still_importing = _scan_import_edges(
        tree, code, to_module, from_pkg_segs,
        root_package=_infra_root_package(root_text))
    return {
        "removed": not still_importing,
        "still_imports": still_importing,
        "source_file": fpath,
        "import_count": len(still_importing),
    }
@dataclass
class ValidationItem:
    filepath: str = ""
    syntax_pass: bool = False
    api_surface_pass: bool = True
    api_diff: dict = field(default_factory=dict)
@dataclass
class ValidationReport:
    items: list[ValidationItem] = field(default_factory=list)
    @property
    def passed(self) -> int:
        return sum(1 for i in self.items if i.syntax_pass)
    @property
    def failed(self) -> int:
        return sum(1 for i in self.items if not i.syntax_pass)
    @property
    def api_surface_failed(self) -> int:
        return sum(1 for i in self.items if not i.api_surface_pass)
    def all_pass(self) -> bool:
        return self.failed == 0 and self.api_surface_failed == 0
    def to_dict(self) -> dict:
        return {
            "total": len(self.items),
            "passed": self.passed,
            "failed": self.failed,
            "api_surface_failed": self.api_surface_failed,
            "items": [
                {
                    "filepath": i.filepath,
                    "syntax_pass": i.syntax_pass,
                    "api_surface_pass": i.api_surface_pass,
                    "api_diff": i.api_diff,
                }
                for i in self.items
            ],
        }
_COLLECTED_SUMMARY_RE = re.compile(r"(\d+) tests? collected")
def _is_collectable_test_file(path: str) -> bool:
    name = os.path.basename(path)
    return is_py_source_file(name) and is_test_source_basename(name)
def _count_collected(stdout: str) -> int:
    match = _COLLECTED_SUMMARY_RE.search(stdout)
    if match:
        return int(match.group(1))
    return sum(1 for line in stdout.splitlines() if "::" in line)
_DEFAULT_COLLECT_TIMEOUT = 30
# 采集上限不得短于方法预算：否则方法里一次较长采集会被静默截断，
# 基线被当成「空 API 集」，属于典型的假阴性。单一真源见
# ``diag_types_vocab.DIAGNOSIS_METHOD_BUDGET_S``。
_MAX_COLLECT_TIMEOUT = int(DIAGNOSIS_METHOD_BUDGET_S)
def _normalize_collect_timeout(value: Any) -> int:
    if isinstance(value, bool):
        return _DEFAULT_COLLECT_TIMEOUT
    seconds = None
    if isinstance(value, (int, float)):
        seconds = float(value)
    elif isinstance(value, str):
        try:
            seconds = float(value.strip())
        except ValueError:
            seconds = None
    if seconds is None or not math.isfinite(seconds) or seconds <= 0:
        return _DEFAULT_COLLECT_TIMEOUT
    return max(1, int(min(seconds, _MAX_COLLECT_TIMEOUT)))
class PostRefactorValidator:
    def __init__(self, skill_dir: str = _DEFAULT_PROJECT_ROOT) -> None:
        root_text = _text_dir(skill_dir)
        self.skill_dir = os.path.abspath(root_text) if root_text else ""
        self._baseline: dict[str, APISnapshot] = {}
    def _resolve(self, fp: str) -> str:
        resolved = (fp if os.path.isabs(fp)
                    else os.path.join(self.skill_dir, fp))
        return os.path.normcase(os.path.abspath(resolved))
    def register_api_baseline(self, files: list[str]) -> int:
        count = 0
        extractor = APISurfaceExtractor()
        for fp in files:
            resolved = self._resolve(fp)
            if os.path.isfile(resolved):
                self._baseline[resolved] = extractor.extract(resolved)
                count += 1
        return count
    def validate(self, files: list[str]) -> ValidationReport:
        items: list[ValidationItem] = []
        extractor = APISurfaceExtractor()
        for fp in files:
            resolved = self._resolve(fp)
            syntax_pass = False
            source, _fingerprint = read_source_with_fingerprint(resolved)
            if source is None:
                _log.debug("[refactor_api_contract] validate 源文件读取失败（验证降级）: %s", resolved)
            else:
                syntax_pass = not compile_error(
                    source, resolved, "refactor_api_contract.validate")
            api_surface_pass = True
            api_diff: dict = {}
            if resolved in self._baseline:
                before = self._baseline[resolved]
                after = extractor.extract(resolved)
                api_diff = extractor.compare(before, after)
                if not before.readable:
                    api_diff["baseline_error"] = (
                        "baseline source unreadable or unparseable")
                if not after.readable:
                    api_diff["current_error"] = (
                        "current source unreadable or unparseable")
                api_surface_pass = (
                    before.readable and after.readable and not any(
                        api_diff.get(key) for key in (
                            "removed", "signature_removed", "signature_changes")))
            items.append(ValidationItem(
                filepath=fp,
                syntax_pass=syntax_pass,
                api_surface_pass=api_surface_pass,
                api_diff=api_diff,
            ))
        return ValidationReport(items=items)
    def validate_migration(self, source_dir: str, target_dir: str) -> dict:
        checker = StageGateChecker(
            source_root=self.skill_dir, target_root=self.skill_dir)
        result = checker.check(source_dir, target_dir)
        return {
            "passed": result.passed,
            "violations": [v.to_dict() for v in result.violations],
            "stats": result.stats,
        }
    def _discover_test_dir(self) -> str:
        root = Path(self.skill_dir or ".")
        parents = [root, *(root / name for name in _SOURCE_CONTAINER_DIRS)]
        candidates: list[Path] = [
            parent / name
            for parent in parents
            for name in TEST_DIR_CANDIDATES
        ]
        src = root / "src"
        if src.is_dir():
            try:
                for child in sorted(src.iterdir()):
                    if child.is_dir():
                        candidates.extend(child / name
                                          for name in TEST_DIR_CANDIDATES)
            except OSError as exc:
                _log.debug(
                    "[refactor_api_contract] src 子目录枚举失败: %s", exc)
        for candidate in candidates:
            try:
                if candidate.is_dir():
                    return str(candidate)
            except OSError:
                continue
        return str(root / DEFAULT_TEST_DIR_NAME)
    def validate_test_loadability(self, files: list[str] | None = None,
                                  timeout: int = _DEFAULT_COLLECT_TIMEOUT
                                  ) -> dict:
        timeout = _normalize_collect_timeout(timeout)
        test_dir = self._discover_test_dir()
        result: dict = {"test_dir": test_dir, "covered": False,
                        "test_count": 0, "detail": ""}
        if not os.path.isdir(test_dir):
            result["status"] = "skip"
            return result
        if importlib.util.find_spec("pytest") is None:
            result["status"] = "skip"
            result["detail"] = "pytest 未安装"
            return result
        result["status"] = "warn"
        if files:
            result["covered"] = self._probe_content_reference(
                test_dir, files)
        collect_status, count, detail = self._run_collect_only(
            test_dir, timeout)
        if collect_status == "pass":
            result["status"] = "pass"
            result["test_count"] = count
            return result
        result["status"] = collect_status
        result["detail"] = detail
        return result
    @staticmethod
    def _reference_patterns(files: list[str]) -> list[re.Pattern]:
        stems = [py_stem(os.path.basename(f)) for f in files]
        return [
            re.compile(rf'(?<![A-Za-z0-9_])(?:{re.escape(stem)})(?![A-Za-z0-9_])')
            for stem in stems if stem
        ]
    @staticmethod
    def _list_test_files(test_dir: str) -> list[str]:
        try:
            return [
                path for path in iter_py_files(test_dir)
                if is_py_source_file(path) and _is_collectable_test_file(path)
            ]
        except OSError as e:
            _log.debug(
                "[refactor_api_contract] 测试目录列举失败（按无测试处理）: %s: %s",
                test_dir, e)
            return []
    def _probe_content_reference(self, test_dir: str,
                                 files: list[str]) -> bool:
        patterns = self._reference_patterns(files)
        if not patterns:
            return False
        for tf in self._list_test_files(test_dir):
            content, _fingerprint = read_source_with_fingerprint(tf)
            if content is None:
                _log.debug(
                    "[refactor_api_contract] 测试文件读取失败（跳过）: %s", tf)
                continue
            if any(p.search(content) for p in patterns):
                return True
        return False
    def _run_collect_only(self, test_dir: str,
                         timeout: int) -> tuple[str, int, str]:
        proc, failure = self._spawn_collect(test_dir, timeout)
        if failure is not None:
            return failure
        if proc.returncode != 0:
            detail = ((proc.stdout or "").strip()
                      or (proc.stderr or "").strip())
            return "warn", 0, "收集失败: " + detail[:100]
        count = _count_collected(proc.stdout or "")
        if count == 0:
            return "warn", 0, "未收集到测试"
        return "pass", count, ""
    def _spawn_collect(self, test_dir: str, timeout: int):
        try:
            proc = subprocess.run(  # jwsgj:suppress SE-40 — 审计认可：测试收集验证调用点，目录参数内部构造、无外部输入面，非缺陷
                [sys.executable, "-B", "-m", "pytest", test_dir,
                 "--collect-only", "-q", "-p", "no:cacheprovider",
                 "-o", "addopts="],
                capture_output=True, text=True, encoding="utf-8",
                errors="replace", timeout=timeout, check=False,
                env=subprocess_noartifact_env(),
                cwd=self.skill_dir or None,
            )
            return proc, None
        except subprocess.TimeoutExpired:
            _log.debug("[refactor_api_contract] 测试收集超时（>%ss）", timeout)
            return None, ("warn", 0, "收集超时")
        except FileNotFoundError:
            _log.debug("[refactor_api_contract] pytest 未安装，负载性验证跳过")
            return None, ("skip", 0, "pytest 未安装")
        except OSError as e:
            _log.debug("[refactor_api_contract] 测试收集进程启动失败: %s", e)
            return None, ("warn", 0, "收集进程启动失败")
def _export_baseline_set(baseline_exports) -> set[str] | None:
    if baseline_exports is None:
        return None
    if isinstance(baseline_exports, (str, bytes)):
        return {os.fsdecode(baseline_exports)}
    try:
        return {name for name in baseline_exports
                if isinstance(name, str) and name}
    except TypeError:
        return set()
def validate_all_exports(skill_dir: str, baseline_exports: set[str] | None = None) -> tuple[bool, list[str]]:
    root_text = _text_dir(skill_dir)
    if not root_text:
        return False, ["skill_dir 缺失或非法"]
    if not os.path.isdir(root_text):
        return False, ["skill_dir 不存在或不是目录"]
    init_path = Path(root_text) / "__init__.py"
    baseline = _export_baseline_set(baseline_exports)
    if not init_path.exists():
        missing = sorted(baseline or ())
        return not missing, missing
    source, _fingerprint = read_source_with_fingerprint(str(init_path))
    if source is None:
        _log.warning("validate_all_exports: 源文件读取失败: %s", init_path)
        return False, ["__init__.py 解析失败"]
    try:
        tree = parse_cached(source, filename=str(init_path))
    except PARSE_DEGRADE_EXC as e:
        _log.warning("validate_all_exports: parse failed: %s", e)
        return False, ["__init__.py 解析失败"]
    current_exports: set[str] = set(
        collect_module_exports_ordered(tree)[0])
    if baseline is None:
        return True, []
    missing = baseline - current_exports
    return len(missing) == 0, sorted(missing)
INFRA_CONTRACT_FILENAME = "infra_contract.json"
INFRA_CONTRACT_SCHEMA = 2
INFRA_CONTRACT_ENV_VAR = "JWSGJ_INFRA_CONTRACT"
_INFRA_MODULE_WILDCARD = "*"
_INFRA_IMPACT_PERCENTILE = 0.90
@dataclass
class InfraContractReport:
    passed: bool = True
    modules_checked: int = 0
    symbols_checked: int = 0
    violations: list[dict] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    added: list[str] = field(default_factory=list)
    contract_path: str = ""
    def summary(self) -> str:
        return (
            f"INFRA 契约: {self.modules_checked} 模块 / "
            f"{self.symbols_checked} 符号, 破坏 {len(self.violations)} 项"
        )
def _infra_root_package(skill_dir: str) -> str:
    root = Path(skill_dir)
    try:
        if (root / "__init__.py").is_file():
            name = root.name
            return name if name.isidentifier() else ""
        for container in (root / name for name in _SOURCE_CONTAINER_DIRS):
            if not container.is_dir():
                continue
            packages = [child for child in sorted(container.iterdir())
                        if child.is_dir() and child.name.isidentifier()
                        and (child / "__init__.py").is_file()]
            if len(packages) == 1:
                return packages[0].name
        packages = [child for child in sorted(root.iterdir())
                    if child.is_dir() and child.name.isidentifier()
                    and not child.name.startswith(".")
                    and (child / "__init__.py").is_file()]
        if len(packages) == 1:
            return packages[0].name
    except OSError as exc:
        _log.debug("[refactor_api_contract] 根包探测失败: %s", exc)
    name = os.path.basename(os.path.normpath(str(skill_dir)))
    return name if name.isidentifier() else ""
def _infra_module_label(rel_path: str) -> str:
    name = rel_path.replace("\\", "/").replace("/", ".")
    if name.lower().endswith(".py"):
        name = name[:-3]
    if name.lower().endswith(".__init__"):
        name = name[: -len(".__init__")]
    return name or "__init__"
def _migration_import_label(root_dir: str, rel_path: str) -> str:
    label = _infra_module_label(rel_path)
    parts = label.split(".")
    if len(parts) > 1 and parts[0] in _SOURCE_CONTAINER_DIRS:
        label = ".".join(parts[1:])
    package = ""
    if root_dir:
        try:
            if (Path(root_dir) / "__init__.py").is_file():
                name = os.path.basename(os.path.normpath(root_dir))
                if name.isidentifier():
                    package = name
        except OSError as exc:
            _log.debug("[refactor_api_contract] 迁移根包探测失败: %s", exc)
    if not package:
        return label
    if label == "__init__":
        return package
    return f"{package}.{label}" if label else package
def _infra_resolve_from_target(module: str, node: ast.ImportFrom,
                               pkg: str,
                               is_package: bool) -> str | None:
    if node.level:
        parts = module.split(".") if module else []
        anchor = parts if is_package else parts[:-1]
        keep = len(anchor) - (node.level - 1)
        if keep < 0:
            return None
        base = list(anchor[:keep])
        if node.module:
            base += node.module.split(".")
        return ".".join(base)
    name = node.module or ""
    if name == pkg:
        return ""
    if name.startswith(pkg + "."):
        return name[len(pkg) + 1:]
    return None
def _infra_class_interface(node: ast.ClassDef) -> str:
    methods, attrs, method_signatures = _class_public_surface(node)
    method_text = ",".join(
        f"{name}{method_signatures[name]}" for name in methods)
    interface = f"methods={method_text};attrs={','.join(attrs)}"
    type_params = _type_params_text(node)
    if type_params:
        interface += f";type_params={type_params}"
    return interface
def _infra_const_interface(value: ast.AST | None) -> tuple[str, str]:
    if value is None:
        return "type=expr", ""
    try:
        literal = ast.literal_eval(value)
    except (ValueError, SyntaxError, TypeError) as _swallowed_exc:
        _log.debug("_infra_const_interface: 非常量表达式: %s",
                   _swallowed_exc, exc_info=True)
        return "type=expr", ""
    except (MemoryError, RecursionError) as _e:
        log_swallowed(__name__, _e, context="infra_contract:const_literal")
        return "type=expr", ""
    kind = type(literal).__name__
    if isinstance(literal, (str, int, float, bool)) or literal is None:
        return f"type={kind}", repr(literal)
    return f"type={kind}", ""
def _infra_const_entry(value: ast.AST | None) -> dict[str, str]:
    interface, const_value = _infra_const_interface(value)
    return {"kind": "const", "interface": interface, "const_value": const_value}
def _infra_definition_entry(node: ast.AST) -> dict[str, str]:
    if isinstance(node, ast.ClassDef):
        return {"kind": "class",
                "interface": _infra_class_interface(node),
                "const_value": "",
                "method_bindings": json.dumps(
                    _class_method_bindings(node), sort_keys=True,
                    separators=(",", ":"))}
    return {"kind": "function", "interface": _format_signature(node),
            "const_value": ""}
def _infra_record_target_const_bindings(
        target: ast.AST, value: ast.AST | None,
        table: dict[str, dict[str, str]], export_names: set[str]) -> None:
    if (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and not any(isinstance(element, ast.Starred)
                        for element in target.elts)):
        for subtarget, subvalue in zip(
                target.elts, value.elts, strict=True):
            _infra_record_target_const_bindings(
                subtarget, subvalue, table, export_names)
        return
    bound_value = value if isinstance(target, ast.Name) else None
    for name in binding_names_of(target):
        if _is_public_surface_name(name, export_names):
            table[name] = _infra_const_entry(bound_value)
def _infra_record_const_bindings(
        node: ast.stmt, table: dict[str, dict[str, str]],
        export_names: set[str]) -> None:
    assigned = assign_targets_value(node)
    if assigned is None:
        return
    targets, value = assigned
    for target in targets:
        _infra_record_target_const_bindings(target, value, table, export_names)
def _infra_record_import_bindings(
        node: ast.Import | ast.ImportFrom,
        table: dict[str, dict[str, str]], export_names: set[str]) -> None:
    for alias in node.names:
        if isinstance(node, ast.ImportFrom):
            if alias.name == "*":
                continue
            name = alias.asname or alias.name
        else:
            name = alias.asname or alias.name.split(".", 1)[0]
        if not name or not _is_public_surface_name(name, export_names):
            continue
        table[name] = {
            "kind": "import", "interface": "", "const_value": "",
        }
def _infra_public_symbol_table(tree: ast.Module) -> dict[str, dict[str, str]]:
    table: dict[str, dict[str, str]] = {}
    export_names = set(collect_module_exports_ordered(tree)[0])
    for node, _in_handler in iter_scope_statements(tree, include_defs=True):
        if isinstance(
                node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if _is_public_surface_name(node.name, export_names):
                table[node.name] = _infra_definition_entry(node)
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            _infra_record_import_bindings(node, table, export_names)
        else:
            _infra_record_const_bindings(node, table, export_names)
    return table
def _infra_module_selection(modules) -> tuple[str, ...]:
    if modules is None:
        return ()
    if isinstance(modules, bytes):
        modules = os.fsdecode(modules)
    if isinstance(modules, str):
        name = modules.strip()
        return (name,) if name else ()
    try:
        items = list(modules)
    except TypeError:
        return ()
    return tuple(name.strip() for name in items
                 if isinstance(name, str) and name.strip())
def _infra_scan_public_tables(
    skill_dir: str,
    modules: tuple[str, ...] | None = None,
) -> dict[str, dict[str, dict[str, str]]]:
    tables: dict[str, dict[str, dict[str, str]]] = {}
    selected = _infra_module_selection(modules) or discover_infra_modules(
        skill_dir)
    for module in selected:
        path, _is_package_init = _resolve_module_file(str(skill_dir), module)
        if path is None:
            continue
        _source, tree = parse_py_file(path, quiet=True)
        if tree is None:
            continue
        tables[module] = _infra_public_symbol_table(tree)
    return tables
def _infra_match_label(target: str, labels: set[str]) -> str | None:
    if target in labels:
        return target
    suffix = "." + target
    matched = [label for label in labels if label.endswith(suffix)]
    return matched[0] if len(matched) == 1 else None
def _infra_root_label(pkg: str, labels: set[str]) -> str | None:
    # 根包自身的文件标签: 平铺或 src/python/lib 容器布局取精确标签;
    # 技能根即包时文件标签不带包名, 无根包锚定标签, 返回 None.
    if not pkg or "__init__" in labels:
        return None
    candidates = [pkg, *(f"{container}.{pkg}"
                         for container in _SOURCE_CONTAINER_DIRS)]
    matched = [name for name in candidates if name in labels]
    return matched[0] if len(matched) == 1 else None
def _infra_rooted_label(pkg: str, target: str, labels: set[str]) -> str | None:
    # 根包锚定的绝对导入名 (pkg.target) 对应的文件标签; 未命中返回 None.
    root = _infra_root_label(pkg, labels)
    if not root or not target:
        return None
    label = f"{root}.{target}"
    return label if label in labels else None
def _infra_root_import_label(pkg: str, labels: set[str]) -> str | None:
    if pkg:
        rooted = _infra_root_label(pkg, labels)
        if rooted:
            return rooted
        matched = sorted(
            label for label in labels
            if label == pkg or label.endswith("." + pkg))
        if len(matched) == 1:
            return matched[0]
    return "__init__" if "__init__" in labels else None
def _infra_import_target(base_module: str, node: ast.ImportFrom, pkg: str,
                         labels: set[str], is_package: bool) -> str | None:
    target = _infra_resolve_from_target(
        base_module, node, pkg, is_package=is_package)
    if target == "":
        return _infra_root_import_label(pkg, labels)
    if target is None:
        if node.level or not node.module:
            return None
        return _infra_match_label(node.module, labels)
    return (_infra_rooted_label(pkg, target, labels)
            or _infra_match_label(target, labels) or target)
def _infra_imported_submodule(target: str, symbol: str,
                              labels: set[str]) -> str | None:
    if not symbol or symbol == "*":
        return None
    prefix = "" if target in ("", "__init__") else target
    candidate = f"{prefix}.{symbol}" if prefix else symbol
    return _infra_match_label(candidate, labels)
def _infra_plain_import_target(name: str, pkg: str,
                               labels: set[str]) -> str | None:
    if not name:
        return None
    if pkg and name == pkg:
        return _infra_root_import_label(pkg, labels)
    if pkg and name.startswith(pkg + "."):
        rooted = _infra_rooted_label(pkg, name[len(pkg) + 1:], labels)
        if rooted:
            return rooted
        name = name[len(pkg) + 1:]
    return _infra_match_label(name, labels) or name
def _infra_record_consumers(tree: ast.Module, module: str, base_module: str,
                            pkg: str, labels: set[str], is_package: bool,
                            consumers: dict[str, dict[str, set[str]]]) -> None:
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                target = _infra_plain_import_target(alias.name, pkg, labels)
                if target is not None:
                    consumers[target][_INFRA_MODULE_WILDCARD].add(module)
            continue
        if not isinstance(node, ast.ImportFrom):
            continue
        target = _infra_import_target(base_module, node, pkg, labels, is_package)
        if target is None:
            continue
        for alias in node.names:
            if alias.name != "*":
                submodule = _infra_imported_submodule(
                    target, alias.name, labels)
                if submodule is not None:
                    consumers[submodule][_INFRA_MODULE_WILDCARD].add(module)
            symbol = (_INFRA_MODULE_WILDCARD if alias.name == "*"
                      else alias.name)
            consumers[target][symbol].add(module)
def _infra_scan_contract_inputs(
    skill_dir: str,
) -> tuple[
    dict[str, dict[str, dict[str, str]]],
    dict[str, dict[str, set[str]]],
    list[str],
]:
    pkg = _infra_root_package(skill_dir)
    publics: dict[str, dict[str, dict[str, str]]] = {}
    consumers: dict[str, dict[str, set[str]]] = defaultdict(
        lambda: defaultdict(set))
    unreadable: list[str] = []
    files = list(iter_py_files(str(skill_dir)))
    labels = {_infra_module_label(os.path.relpath(path, str(skill_dir)))
              for path in files}
    for filepath in files:
        rel_path = os.path.relpath(filepath, str(skill_dir))
        module = _infra_module_label(rel_path)
        is_package = os.path.basename(rel_path).lower() == "__init__.py"
        base_module = ("" if is_package and module.lower() == "__init__"
                       else module)
        _source, tree = parse_py_file(filepath, quiet=True)
        if tree is None:
            unreadable.append(rel_path)
            continue
        publics[module] = _infra_public_symbol_table(tree)
        _infra_record_consumers(tree, module, base_module, pkg, labels,
                                is_package, consumers)
    return publics, consumers, unreadable
def _expand_module_wildcard(used: dict[str, set[str]],
                            public: dict[str, dict[str, str]]) -> dict[str, set[str]]:
    wildcard = used.pop(_INFRA_MODULE_WILDCARD, None)
    if not wildcard:
        return used
    expanded = {symbol: set(users) for symbol, users in used.items()}
    for symbol in public:
        expanded.setdefault(symbol, set()).update(wildcard)
    return expanded
def _infra_public_consumers(
    skill_dir: str,
    *,
    strict: bool = False,
) -> tuple[dict[str, dict[str, dict[str, str]]], dict[str, dict[str, set[str]]]]:
    public_map, consumers, unreadable = _infra_scan_contract_inputs(skill_dir)
    if strict and unreadable:
        preview = ", ".join(sorted(unreadable)[:5])
        suffix = ", ..." if len(unreadable) > 5 else ""
        raise ValueError(
            "INFRA 契约基线抓取失败："
            f"{len(unreadable)} 个 Python 文件不可读或不可解析 "
            f"({preview}{suffix})")
    kept: dict[str, dict[str, set[str]]] = {}
    for target, symbols in consumers.items():
        public = public_map.get(target)
        if not public:
            continue
        used = {symbol: users for symbol, users in symbols.items()
                if symbol in public or symbol == _INFRA_MODULE_WILDCARD}
        used = _expand_module_wildcard(used, public)
        used = {symbol: users for symbol, users in used.items() if users}
        if used:
            kept[target] = used
    return public_map, kept
def _infra_reverse_edges(
    consumers: dict[str, dict[str, set[str]]],
) -> dict[str, set[str]]:
    reverse: dict[str, set[str]] = defaultdict(set)
    for target, symbols in consumers.items():
        for users in symbols.values():
            reverse[target].update(users)
    return reverse
def _infra_impact_scores(reverse: dict[str, set[str]]) -> dict[str, int]:
    scores: dict[str, int] = {}
    for module in reverse:
        seen: set[str] = set()
        stack = list(reverse.get(module, ()))
        while stack:
            importer = stack.pop()
            if importer == module or importer in seen:
                continue
            seen.add(importer)
            stack.extend(reverse.get(importer, ()))
        scores[module] = len(seen)
    return scores
def _infra_percentile(values: list[int], ratio: float) -> int:
    if not values:
        return 0
    ordered = sorted(values)
    index = max(0, math.ceil(len(ordered) * ratio) - 1)
    return ordered[index]
def _infra_impact_floor(value, scores: dict[str, int]) -> int:
    default = max(1, _infra_percentile(
        list(scores.values()), _INFRA_IMPACT_PERCENTILE))
    if isinstance(value, bool) or not is_number(value):
        return default
    number = float(value)
    if not math.isfinite(number):
        return default
    return max(1, int(number))
def _infra_select_modules(
    consumers: dict[str, dict[str, set[str]]],
    impact_floor: int | None = None,
) -> tuple[str, ...]:
    scores = _infra_impact_scores(_infra_reverse_edges(consumers))
    impact_floor = _infra_impact_floor(impact_floor, scores)
    selected = [name for name, score in scores.items()
                if score >= impact_floor]
    return tuple(sorted(selected))
def discover_infra_modules(
    skill_dir: str,
    impact_floor: int | None = None,
) -> tuple[str, ...]:
    _, consumers = _infra_public_consumers(skill_dir)
    return _infra_select_modules(consumers, impact_floor)
def build_infra_contract(
    skill_dir: str,
    modules: tuple[str, ...] | None = None,
) -> dict:
    public_map, consumers = _infra_public_consumers(
        skill_dir, strict=True)
    selected = (_infra_module_selection(modules)
                or _infra_select_modules(consumers))
    contract: dict = {
        "schema": INFRA_CONTRACT_SCHEMA,
        "package": _infra_root_package(skill_dir),
        "modules": {},
    }
    for module in selected:
        symbols = public_map.get(module, {})
        used = consumers.get(module, {})
        entry: dict[str, dict] = {}
        for symbol in sorted(symbols):
            users = sorted(used.get(symbol, ()))
            if not users:
                continue
            meta = dict(symbols[symbol])
            meta["consumers"] = users
            entry[symbol] = meta
        if entry:
            contract["modules"][module] = entry
    return contract
def _infra_workspace_contract_path(skill_dir: str) -> str:
    if not is_workspace_root_available():
        return ""
    package = _infra_root_package(skill_dir) or os.path.basename(
        os.path.normpath(str(skill_dir)))
    try:
        base = get_workspace_output_dir(package)
    except (RuntimeError, OSError, ValueError) as _e:
        log_swallowed(__name__, _e, context="infra_contract:workspace")
        return ""
    return os.path.join(base, INFRA_CONTRACT_FILENAME)
def resolve_infra_contract_path(skill_dir: str, target_path: str | None = None,
                                *, for_write: bool = False) -> str:
    if target_path:
        path = os.path.abspath(os.fspath(target_path))
        if for_write and is_under_root(path, skill_dir):
            raise RuntimeError(
                f"INFRA 契约基线禁止落入技能根: {path}；"
                "请改用会话工作空间或显式目标路径")
        return path
    override = os.environ.get(INFRA_CONTRACT_ENV_VAR, "").strip()
    if override:
        if not os.path.isabs(override):
            raise RuntimeError(
                f"{INFRA_CONTRACT_ENV_VAR}={override!r} 必须是绝对路径")
        path = os.path.normpath(override)
        if for_write and is_under_root(path, skill_dir):
            raise RuntimeError(
                f"INFRA 契约基线禁止落入技能根: {path}；"
                "请把该环境变量指向会话工作空间")
        return path
    path = _infra_workspace_contract_path(skill_dir)
    if path:
        return path
    if for_write:
        raise RuntimeError(
            "INFRA 契约基线需要会话工作空间：未解析到 "
            f"{WORKSPACE_ENV_VAR} / 会话目录；请设置 {WORKSPACE_ENV_VAR}、"
            f"{INFRA_CONTRACT_ENV_VAR} 或显式 target_path")
    return ""
def _build_and_write_contract(skill_dir: str,
                              target_path: str | None = None
                              ) -> tuple[str, dict]:
    path = resolve_infra_contract_path(skill_dir, target_path, for_write=True)
    contract = build_infra_contract(skill_dir)
    parent = os.path.dirname(path)
    if parent:
        os.makedirs(parent, exist_ok=True)
    write_json_artifact(path, contract, indent=1)
    return path, contract
def _infra_load_contract(contract_path: str) -> dict | None:
    data, status, _error = read_json_artifact(contract_path)
    if status != "ok":
        return None
    return data if isinstance(data, dict) else None
def _infra_consumer_names(value) -> list[str]:
    if not isinstance(value, (list, tuple, set, frozenset)):
        return []
    return sorted(item for item in value if isinstance(item, str))
def _infra_module_violation(label: str, base_symbols: dict) -> dict:
    return {
        "module": label,
        "symbol": "<module>",
        "change": "module_missing",
        "consumers": sorted({
            user for base in base_symbols.values()
            if isinstance(base, dict)
            for user in _infra_consumer_names(base.get("consumers"))
        }),
        "detail": "INFRA 模块文件缺失或不可解析（符号级明细已折叠）",
    }
def _infra_symbol_violation(label: str, symbol: str, base: dict,
                           current: dict | None, users: list[str],
                           ) -> dict | None:
    if current is None:
        return {
            "module": label, "symbol": symbol, "change": "removed",
            "consumers": users,
            "detail": f"符号已不存在，{len(users)} 个模块受影响",
        }
    if current.get("kind") != base.get("kind"):
        return {
            "module": label, "symbol": symbol, "change": "modified",
            "consumers": users,
            "detail": (
                f"符号类型 {base.get('kind')} -> "
                f"{current.get('kind')}，{len(users)} 个模块受影响"
            ),
        }
    if current.get("interface") != base.get("interface"):
        return {
            "module": label, "symbol": symbol, "change": "modified",
            "consumers": users,
            "detail": (
                f"接口变更 {base.get('interface')} -> "
                f"{current.get('interface')}，{len(users)} 个模块受影响"
            ),
        }
    if "method_bindings" in base and current.get(
            "method_bindings") != base.get("method_bindings"):
        return {
            "module": label, "symbol": symbol, "change": "modified",
            "consumers": users,
            "detail": (
                f"方法 binding 变更 {base.get('method_bindings')} -> "
                f"{current.get('method_bindings')}，{len(users)} 个模块受影响"
            ),
        }
    return None
def _infra_const_value_warning(label: str, symbol: str, base: dict,
                               current: dict) -> str | None:
    if not base.get("const_value"):
        return None
    if current.get("const_value") == base.get("const_value"):
        return None
    return (f"{label}.{symbol} 常量值变化: "
            f"{base.get('const_value')} -> {current.get('const_value')}")
def _diff_infra_module(label: str, base_symbols: dict,
                       current_symbols: dict | None,
                       ) -> tuple[int, list[dict], list[str]]:
    if current_symbols is None:
        return 0, [_infra_module_violation(label, base_symbols)], []
    checked = 0
    violations: list[dict] = []
    warnings: list[str] = []
    for symbol, base in sorted(
            base_symbols.items(), key=lambda item: str(item[0])):
        checked += 1
        if not isinstance(symbol, str):
            violations.append(_infra_contract_shape_violation(
                label, f"INFRA 符号名格式异常: {symbol!r} 不是字符串",
                symbol=str(symbol)))
            continue
        if not isinstance(base, dict):
            violations.append(_infra_contract_shape_violation(
                label, f"INFRA 符号条目格式异常: {symbol} 不是映射",
                symbol=str(symbol)))
            continue
        users = _infra_consumer_names(base.get("consumers"))
        current = current_symbols.get(symbol)
        violation = _infra_symbol_violation(
            label, symbol, base, current, users)
        if violation is not None:
            violations.append(violation)
            continue
        warning = _infra_const_value_warning(label, symbol, base, current)
        if warning:
            warnings.append(warning)
    return checked, violations, warnings
def _infra_contract_shape_violation(
        label: str, detail: str, symbol: str = "<contract>") -> dict:
    return {
        "module": label, "symbol": symbol,
        "change": "invalid_contract", "consumers": [], "detail": detail,
    }
def diff_infra_contract(skill_dir: str, contract: dict) -> InfraContractReport:
    report = InfraContractReport()
    if not isinstance(contract, dict):
        report.passed = False
        report.violations.append(_infra_contract_shape_violation(
            "<contract>",
            f"INFRA 契约顶层非映射（{type(contract).__name__}），无法校验"))
        return report
    base_modules = contract.get("modules")
    if not isinstance(base_modules, dict):
        report.passed = False
        report.violations.append(_infra_contract_shape_violation(
            "<contract>", "INFRA 契约格式异常: modules 缺失或不是映射"))
        return report
    public_map = _infra_scan_public_tables(
        skill_dir, tuple(str(name) for name in base_modules))
    for module, base_symbols in sorted(
            base_modules.items(), key=lambda item: str(item[0])):
        if not isinstance(base_symbols, dict):
            report.modules_checked += 1
            report.violations.append(_infra_contract_shape_violation(
                str(module), "INFRA 模块条目格式异常: symbols 不是映射"))
            continue
        label = str(module)
        report.modules_checked += 1
        checked, violations, warnings = _diff_infra_module(
            label, base_symbols, public_map.get(label))
        report.symbols_checked += checked
        report.violations.extend(violations)
        report.warnings.extend(warnings)
    report.passed = not report.violations
    return report
def _infra_skipped_report(message: str, path: str = "") -> InfraContractReport:
    report = InfraContractReport(passed=False)
    report.contract_path = path
    report.warnings.append(message)
    return report
def check_infra_contract(skill_dir: str,
                         contract_path: str | None = None) -> InfraContractReport:
    path = resolve_infra_contract_path(skill_dir, contract_path)
    if not path:
        return _infra_skipped_report(
            "INFRA 契约缺失，已跳过校验: 未解析到会话工作空间基线"
            f"（设置 {WORKSPACE_ENV_VAR} 或 {INFRA_CONTRACT_ENV_VAR}）")
    if not os.path.isfile(path):
        return _infra_skipped_report(
            f"INFRA 契约缺失，已跳过校验: {path}", path)
    contract = _infra_load_contract(path)
    if contract is None:
        report = InfraContractReport(passed=False)
        report.contract_path = path
        report.violations.append(_infra_contract_shape_violation(
            "<contract>", f"INFRA 契约不可读，无法完成校验: {path}"))
        return report
    schema = contract.get("schema")
    if not is_number(schema) or schema != INFRA_CONTRACT_SCHEMA:
        report = InfraContractReport(passed=False)
        report.contract_path = path
        report.violations.append(_infra_contract_shape_violation(
            "<contract>",
            f"INFRA 契约 schema={schema} 与当前 "
            f"{INFRA_CONTRACT_SCHEMA} 不一致，无法完成校验"))
        return report
    report = diff_infra_contract(skill_dir, contract)
    report.contract_path = path
    return report
class InfraContractStage:
    def __init__(self, name: str = "infra_contract",
                 skill_dir: str | None = None) -> None:
        self.name = name
        self.description = "Check INFRA module contract (removed / narrowed symbols)"
        self.skill_dir = skill_dir
    def run(self, context: dict[str, Any]) -> dict[str, Any]:
        issues: list = []
        warnings: list = []
        if not isinstance(context, dict):
            context = {}
        skill_dir = self.skill_dir or context.get("skill_dir", "")
        target_declared = self.skill_dir is not None or "skill_dir" in context
        if not skill_dir:
            if target_declared:
                issues.append("Infra contract: skill_dir 必须为非空目录路径")
            return {
                "passed": not issues, "issues": issues, "warnings": warnings,
                "stage": self.name,
            }
        if not os.path.isdir(str(skill_dir)):
            issues.append(
                f"Infra contract: skill_dir 不存在或不是目录: {skill_dir}")
            return {
                "passed": False, "issues": issues, "warnings": warnings,
                "stage": self.name,
            }
        try:
            report = check_infra_contract(str(skill_dir))
        except Exception as exc:  # noqa: BLE001
            log_swallowed(__name__, exc,
                          context="infra_contract:stage")
            warnings.append(f"Infra contract check error (skipped): {exc}")
            issues.append(f"Infra contract check error (blocked): {exc}")
            return {
                "passed": False, "issues": issues, "warnings": warnings,
                "stage": self.name,
            }
        warnings.extend(report.warnings)
        for item in report.violations:
            issues.append(
                f"INFRA contract {item['change']}: "
                f"{item['module']}.{item['symbol']} "
                f"({len(item['consumers'])} consumers)"
            )
        if not report.passed and not issues:
            detail = "; ".join(report.warnings) or "未知校验失败"
            issues.append(f"Infra contract: 校验未完成，未度量不得判通过: {detail}")
        return {
            "passed": report.passed and not issues,
            "issues": issues,
            "warnings": warnings,
            "stage": self.name,
        }
def _contract_symbol_count(contract: dict) -> int:
    modules = contract.get("modules") or {}
    if not isinstance(modules, dict):
        return 0
    return sum(len(entry) for entry in modules.values()
               if isinstance(entry, dict))
def _print_contract_payload(payload: dict) -> None:
    if payload.get("ok"):
        if payload.get("action") == "capture":
            print(f"INFRA 契约基线已写入: {payload.get('path')}")
            print(f"  模块 {payload.get('modules', 0)} / "
                  f"符号 {payload.get('symbols', 0)}")
        else:
            print("INFRA 契约校验通过: "
                  f"{payload.get('modules', 0)} 模块 / "
                  f"{payload.get('symbols', 0)} 符号")
    else:
        print(f"[ERROR] {payload.get('error') or 'INFRA 契约校验失败'}")
        for item in payload.get("violations") or []:
            if not isinstance(item, dict):
                continue
            print(f"  [{item.get('change')}] "
                  f"{item.get('module')}.{item.get('symbol')}")
    for warning in payload.get("warnings") or []:
        print(f"  [WARN] {warning}")
def cmd_contract(args: argparse.Namespace) -> int:
    requested_dir = getattr(args, "skill_dir", "")
    skill_dir = os.path.abspath(
        requested_dir or resolve_search_root(os.getcwd()))
    target = getattr(args, "path", None)
    as_json = bool(getattr(args, "json", False))
    try:
        if not os.path.isdir(skill_dir):
            raise ValueError(f"技能/项目根不存在或不是目录: {skill_dir}")
        if getattr(args, "capture", False):
            path, contract = _build_and_write_contract(skill_dir, target)
            payload = {
                "ok": True,
                "command": "contract",
                "action": "capture",
                "path": path,
                "modules": len(contract.get("modules") or {}),
                "symbols": _contract_symbol_count(contract),
            }
        else:
            report = check_infra_contract(skill_dir, target)
            payload = {
                "ok": report.passed,
                "command": "contract",
                "action": "check",
                "path": report.contract_path,
                "passed": report.passed,
                "modules": report.modules_checked,
                "symbols": report.symbols_checked,
                "violations": report.violations[:20],
                "warnings": report.warnings,
            }
    except (RuntimeError, OSError, ValueError) as exc:
        _log.warning("contract 命令失败: %s", exc)
        payload = {
            "ok": False,
            "command": "contract",
            "action": "capture" if getattr(args, "capture", False) else "check",
            "error": str(exc),
            "error_type": type(exc).__name__,
        }
    if as_json:
        print(json.dumps(payload, ensure_ascii=False, indent=2, default=str))
    else:
        _print_contract_payload(payload)
    return 0 if payload.get("ok") else 1
def register_cli_contract(sub) -> None:
    parser = sub.add_parser(
        "contract",
        help="INFRA 底座契约基线（capture 抓基线 / check 复检，落会话工作空间）")
    parser.add_argument(
        "--skill-dir", default="",
        help="技能或 Python 项目根（默认从当前目录向上解析）")
    parser.add_argument("--path", default=None,
                        help="显式契约路径（默认会话工作空间）")
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--capture", action="store_true",
                        help="按当前源码重建基线")
    action.add_argument("--check", action="store_true",
                        help="对比基线（默认动作）")
    parser.add_argument("--json", action="store_true", help="输出 JSON")
CONTRACT_COMMANDS = {
    "contract": cmd_contract,
}

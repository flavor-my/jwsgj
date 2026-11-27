from __future__ import annotations  # noqa: I001
import ast
import logging
import os
import symtable
from dataclasses import dataclass, field
from os.path import abspath, normcase
from pathlib import Path
from typing import Any
from jwsgj.build_safe_write import commit_writes, is_syntax_valid
from jwsgj.diag_shared_ast_bindings import (
    import_bound_names,
    import_stmt_binds,
    module_scope_binds,
)
from jwsgj.diag_shared_ast_nodes import (
    BUILTIN_NAMES,
    build_parent_map,
    is_type_checking_guard,
    iter_import_time_nodes,
    module_postpones_annotations,
    parse_source_tree,
)
from jwsgj.diag_shared_ast_surface import (
    extract_all_names,
    is_all_assignment,
    is_all_target,
)
from jwsgj.diag_shared_source_core import (
    physical_lines_keepends,
    read_source_with_fingerprint,
)
from jwsgj.diag_types_vocab import INPLACE_MUTATING_METHODS
from jwsgj.log_config import log_swallowed
from jwsgj.refactor_migration_commit import commit_migrate_in
from jwsgj.refactor_migration_prepare import (
    _MODULE_CONTEXT_BUILTINS,
    _MODULE_CONTEXT_GLOBALS,
    _collect_scope_global_usage,
    _dynamic_context_import_aliases,
    _indirect_dynamic_context_refs,
    _package_chain,
    get_consumption_map,
    invalidate_consumption_cache,
    invalidate_zcc_cache,
    judge_migration,
    plan_post_merge_cleanup,
)
from jwsgj.refactor_migration_prepare import (
    assemble_merged_source as _assemble_merged_source,
)
from jwsgj.refactor_migration_prepare import (
    prepare_migrate_in as _prepare_migrate_in_impl,
)
from jwsgj.prevention_scope_facts import walk_nodes
_log = logging.getLogger(__name__)
DEFAULT_REFACTOR_DRY_RUN = True
def _as_source_list(value: object) -> list | None:
    if isinstance(value, str):
        return [value]
    if isinstance(value, (list, tuple)):
        return list(value)
    return None
def _first_non_path(*values: object) -> tuple[bool, object]:
    for value in values:
        if not isinstance(value, (str, os.PathLike)):
            return True, value
    return False, None
@dataclass
class ExecutorResult:
    action_type: str = ""
    status: str = "pending"
    source_files: list[str] = field(default_factory=list)
    target_files: list[str] = field(default_factory=list)
    changes_made: int = 0
    verification_passed: bool = False
    verification_details: list[str] = field(default_factory=list)
    error_message: str = ""
    details: list[str] = field(default_factory=list)
    extra: dict = field(default_factory=dict)
_ACTION_FIELD_MAP = {
    "source": "source_files",
    "sources": "source_files",
    "target": "target_files",
    "symbols": "code_elements",
}
class BaseExecutor:
    def __init__(self, skill_dir: str,
                 dry_run: bool = DEFAULT_REFACTOR_DRY_RUN,
                 cache: Any = None) -> None:
        self.skill_dir = Path(skill_dir)
        self.dry_run = bool(dry_run)
        self._cache = cache
        self.result = ExecutorResult()
    def _fail(self, message: str) -> None:
        self.result.status = "failed"
        self.result.error_message = message
    def _resolve_action_path(self, value: object) -> Path:
        try:
            raw = os.fspath(value)
            if not isinstance(raw, str) or not raw:
                raise TypeError("动作路径须为非空文本")
            root = self.skill_dir.resolve()
            candidate = Path(raw)
            resolved = (candidate if candidate.is_absolute()
                        else root / candidate).resolve()
            resolved.relative_to(root)
            return resolved
        except (OSError, RuntimeError, TypeError, ValueError) as exc:
            raise ValueError(
                f"动作路径非法或越出技能目录: {value!r}") from exc
    @staticmethod
    def _action_get(action: Any, key: str, default: Any = None) -> Any:
        candidates = [key, _ACTION_FIELD_MAP.get(key, key)]
        if key in ("source", "sources"):
            candidates.append("sources" if key == "source" else "source")
        val = None
        candidates = list(dict.fromkeys(candidates))
        if isinstance(action, dict):
            for candidate in candidates:
                val = action.get(candidate)
                if val is not None:
                    break
        else:
            for candidate in candidates:
                val = getattr(action, candidate, None)
                if val is not None:
                    break
        if val is None:
            return default
        if key in ("source", "target") and isinstance(val, (list, tuple)):
            return val[0] if val else (default if default is not None else "")
        return val
    def _finalize_commit(self, commit: dict, fail_default: str) -> bool:
        self.result.extra["commit"] = commit
        if commit.get("status") == "ok":
            self.result.verification_passed = True
            invalidate_zcc_cache(str(self.skill_dir))
            invalidate_consumption_cache(str(self.skill_dir))
            return True
        self.result.status = "failed"
        self.result.error_message = str(commit.get("message", fail_default))
        return False
    def _cached_source(
        self, fp: Path,
    ) -> tuple[str | None, ast.Module | None] | None:
        if self._cache is None:
            return None
        try:
            source = self._cache.get_source(str(fp))
            tree = self._cache.get_ast(str(fp))
        except Exception as _e:  # noqa: BLE001
            log_swallowed(__name__, _e,
                          context=f"_cached_source:{type(_e).__name__}")
            return None
        if source is not None and tree is not None:
            return source, tree
        return None
    def _read_source(self, filepath: str) -> tuple[str | None, ast.Module | None]:
        fp = Path(filepath)
        cached = self._cached_source(fp)
        if cached is not None:
            return cached
        if not fp.exists():
            return None, None
        source, _fingerprint = read_source_with_fingerprint(str(fp))
        if source is None:
            _log.warning("[Executor] 无法读取 %s", filepath)
            return None, None
        tree = parse_source_tree(source, str(fp))
        if tree is None:
            return None, None
        return source, tree
def _package_parts(module_path: str | Path, root: Path) -> tuple[str, ...]:
    try:
        resolved_root = Path(root).resolve()
        resolved_module = Path(module_path).resolve()
        rel = resolved_module.parent.relative_to(resolved_root)
        root_package = _package_chain(str(resolved_root))
        if (resolved_module.name == "__init__.py" and not rel.parts
                and not root_package and resolved_root.name):
            root_package = (resolved_root.name,)
    except (OSError, RuntimeError, ValueError) as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc,
                      context=f'_package_parts:{type(_swallowed_exc).__name__}')
        return ()
    return (*root_package, *rel.parts)
def _resolve_relative_module(package: tuple[str, ...], level: int,
                             module: str | None) -> tuple[str, ...] | None:
    if level <= 0:
        return None
    cut = max(0, len(package) - (level - 1))
    base = package[:cut]
    return base + tuple(module.split(".")) if module else base
def _dotted_module(parts: tuple[str, ...]) -> str:
    return ".".join(parts) if parts else "<顶层>"
class MergeExecutor(BaseExecutor):
    def execute(self, action: Any) -> ExecutorResult:
        self.result = ExecutorResult(action_type="merge")
        inputs = self._normalized_merge_inputs(action)
        if inputs is None:
            return self.result
        sources, target = inputs
        target_path = self.skill_dir / target
        self.result.source_files = [str(self.skill_dir / s) for s in sources]
        self.result.target_files = [str(target_path)]
        preview_detail = self._collect_pmc_plan(sources, target)
        if not self.dry_run:
            commit = self._write_merged_file(sources, str(target_path))
            if self._finalize_commit(commit, "合并落盘失败"):
                self.result.changes_made = 1
                self._discard_pmc_preview(preview_detail)
                self._collect_pmc_plan(sources, target, stage_note="落盘后实测")
            else:
                self._discard_pmc_preview(preview_detail)
        else:
            self._preview_merge(sources, str(target_path), preview_detail)
        if self.result.status != "failed":
            self.result.status = "success"
        return self.result
    def _normalized_merge_inputs(self, action: Any):
        sources = self._action_get(action, "sources", [])
        target = self._action_get(action, "target", "")
        if not sources or not target:
            self._fail("缺少 sources/target 参数")
            return None
        normalized = _as_source_list(sources)
        if normalized is None:
            self._fail(f"sources 参数形态非法: {type(sources).__name__}"
                "（须为文件清单或单文件字符串）")
            return None
        found_bad, bad = _first_non_path(*normalized, target)
        if found_bad:
            self._fail(f"sources/target 路径形态非法: {type(bad).__name__}"
                "（须为 str/PathLike）")
            return None
        try:
            resolved_sources = [
                str(self._resolve_action_path(source))
                for source in normalized]
            if len({normcase(abspath(source)) for source in resolved_sources}) != len(resolved_sources):
                self._fail("sources 含重复源文件：合并会重复执行顶层语句，请先去除重复路径")
                return None
            resolved_target = str(self._resolve_action_path(target))
        except ValueError as exc:
            log_swallowed(__name__, exc, context='_normalized_merge_inputs:ValueError')
            self._fail(str(exc))
            return None
        if not self._target_content_preserved(resolved_sources, resolved_target):
            return None
        return resolved_sources, resolved_target
    def _target_content_preserved(self, sources: list, target: str) -> bool:
        target_key = normcase(abspath(target))
        if any(normcase(abspath(source)) == target_key for source in sources):
            return True
        target_path = Path(target)
        if target_path.exists() and not target_path.is_file():
            self._fail(f"合并目标路径存在但不是普通文件，拒绝覆盖: {target}")
            return False
        existing, _fingerprint = read_source_with_fingerprint(target)
        if existing is None or not existing.strip():
            return True
        self._fail(
            "目标文件已存在且含实现，但不在 sources 中：合并只写入 sources 的"
            "装配结果，目标原有内容会被整篇覆盖丢失；请把目标文件一并加入 "
            "sources（合并顺序即 sources 顺序），或先清空目标文件")
        return False
    def _collect_pmc_plan(self, sources: list, target: str,
                          stage_note: str = "") -> str | None:
        try:
            pmc_plan = plan_post_merge_cleanup(
                str(self.skill_dir), sources, target)
        except Exception as pmc_err:  # noqa: BLE001
            _log.warning("[MergeExecutor] 合并后清理规划跳过(%s): %s",
                         stage_note or "预估", pmc_err)
            return None
        deletable, orphans_kept, stale = _cleanup_counts(pmc_plan)
        if not (deletable or orphans_kept or stale):
            return None
        self.result.extra["post_merge_cleanup"] = pmc_plan
        detail = _cleanup_detail(deletable, orphans_kept, stale, stage_note)
        self.result.details.append(detail)
        return detail
    def _discard_pmc_preview(self, preview_detail: str | None) -> None:
        self.result.extra.pop("post_merge_cleanup", None)
        if preview_detail and preview_detail in self.result.details:
            self.result.details.remove(preview_detail)
    def _preview_merge(self, sources: list, target_path: str,
                       preview_detail: str | None) -> None:
        _parts, merged, err = self._prepare_merged_content(sources, target_path)
        if err is None:
            if not is_syntax_valid(merged):
                self._fail("合并产物语法校验失败（预览与落盘同口径）")
                self._discard_pmc_preview(preview_detail)
            return
        self._fail(str(err.get("message", "合并预检失败")))
        self._discard_pmc_preview(preview_detail)
    def _read_merge_sources(self, sources: list):
        src_codes: list[tuple[str, str]] = []
        for s in sources:
            fp = self.skill_dir / s
            text, _fingerprint = read_source_with_fingerprint(str(fp))
            if text is None:
                return None, {"status": "error", "data": {},
                            "message": f"读取源文件失败: {fp}"}
            src_codes.append((str(fp), text))
        return src_codes, None
    def _prepare_merged_content(self, sources: list, target_path: str):
        src_codes, err = self._read_merge_sources(sources)
        if err is not None:
            return None, None, err
        parts, err = _collect_merge_parts(src_codes)
        if err is not None:
            return None, None, err
        merged_docstring = _primary_merge_docstring(
            parts, src_codes, target_path)
        gate_err = self._module_context_gate(
            parts.module_context_refs, target_path, len(src_codes),
            parts.indirect_context_ref_ids)
        if gate_err is not None:
            return None, None, gate_err
        gate_err = self._rel_import_gate(parts.rel_import_refs, target_path)
        if gate_err is not None:
            return None, None, gate_err
        merged = _assemble_merged_source(parts)
        if merged_docstring is not None:
            merged = repr(merged_docstring) + "\n\n" + merged
        gate_err = self._self_import_gate(merged, target_path)
        if gate_err is not None:
            return None, None, gate_err
        return parts, merged, None
    def _write_merged_file(self, sources: list, target_path: str) -> dict:
        target_existed = os.path.exists(target_path)
        base_target, _fingerprint = read_source_with_fingerprint(target_path)
        if target_existed and base_target is None:
            return {"status": "error", "data": {},
                    "message": f"合并目标文件 {target_path} 当前不可读，拒绝落盘"}
        _parts, merged, err = self._prepare_merged_content(sources, target_path)
        if err is not None:
            return err
        current_target, _fingerprint = read_source_with_fingerprint(target_path)
        if (os.path.exists(target_path) != target_existed
                or current_target != base_target):
            return {"status": "error",
                    "data": {"stale_target_file": target_path},
                    "message": (f"目标文件 {target_path} 在合并预览后已修改，"
                                "继续提交会覆盖并发变更；请重新生成预览")}
        return commit_writes([(target_path, merged)], str(self.skill_dir))
    def _module_context_gate(
            self, module_context_refs: list, target_path: str,
            source_count: int, indirect_ref_ids=frozenset()) -> dict | None:
        target_key = normcase(abspath(target_path))
        target_package = _package_parts(target_path, self.skill_dir)
        problems: list[str] = []
        for source_fp, node in module_context_refs:
            if (node.id in {"__doc__", "__annotations__"}
                    and source_count == 1):
                continue
            if node.id == "__package__":
                if _package_parts(source_fp, self.skill_dir) == target_package:
                    continue
            elif node.id in _MODULE_CONTEXT_GLOBALS:
                if normcase(abspath(source_fp)) == target_key:
                    continue
            elif ((node.id in _MODULE_CONTEXT_BUILTINS
                   or id(node) in indirect_ref_ids)
                  and source_count == 1
                  and normcase(abspath(source_fp)) == target_key):
                continue
            problems.append(
                f"{source_fp} 第 {node.lineno} 行读取 {node.id}")
        if not problems:
            return None
        return {"status": "error", "data": {},
                "message": ("合并会改变代码读取的模块身份、文档、注解、导出面"
                            "或动态命名空间，"
                            "拒绝落盘: " + "; ".join(problems)
                            + f"（目标 {target_path}）。请改为显式参数/依赖注入，"
                            "或保留原模块边界")}
    def _rel_import_gate(self, rel_import_refs: list,
                         target_path: str) -> dict | None:
        if not rel_import_refs:
            return None
        target = Path(target_path)
        if not target.is_absolute():
            target = self.skill_dir / target_path
        target_package = _package_parts(target, self.skill_dir)
        problems: list[str] = []
        for source_fp, node in rel_import_refs:
            source_package = _package_parts(source_fp, self.skill_dir)
            source_module = _resolve_relative_module(
                source_package, node.level, node.module)
            target_module = _resolve_relative_module(
                target_package, node.level, node.module)
            if source_module == target_module:
                continue
            problems.append(
                f"{_format_import_from(node)}（{source_fp} 第 {node.lineno} 行，"
                f"源解析 {_dotted_module(source_module)}，"
                f"目标解析 {_dotted_module(target_module)}）")
        if problems:
            return {"status": "error", "data": {},
                    "message": "合并源含相对导入且目标包改变其解析结果，"
                    "相对导入将断裂或绑定到不同模块，拒绝落盘: "
                    + "; ".join(problems)}
        return None
    def _target_module_path(self, target_path: str) -> tuple[str, str, str]:
        package = _package_parts(target_path, self.skill_dir)
        leaf = Path(target_path).stem
        if leaf == "__init__":
            return ".".join(package), ".".join(package[:-1]), ""
        return ".".join((*package, leaf)), ".".join(package), leaf
    def _self_import_gate(self, merged: str, target_path: str) -> dict | None:
        module, parent, leaf = self._target_module_path(target_path)
        if not module:
            return None
        tree = parse_source_tree(merged, target_path)
        if tree is None:
            return None
        package = _package_parts(target_path, self.skill_dir)
        for node in walk_nodes(tree):
            hit = _self_import_hit(
                node, package, module, parent, leaf, target_path)
            if hit:
                return {"status": "error", "data": {},
                        "message": ("合并产物会导入自身模块 "
                                    f"{module}（{hit}），落盘后形成循环导入并"
                                    "在导入期 ImportError；请先移除源文件对"
                                    "目标模块的导入，或改选其他合并目标")}
        return None
def _package_child_module_exists(package_dir: Path, name: str) -> bool:
    return (package_dir / f"{name}.py").is_file() or (package_dir / name).is_dir()
def _self_import_hit(node: ast.AST, package: tuple[str, ...], module: str,
                     parent: str, leaf: str, target_path: str = "") -> str:
    if isinstance(node, ast.Import):
        if any(alias.name == module for alias in node.names):
            return "import " + ", ".join(
                _format_alias(alias) for alias in node.names)
        return ""
    if not isinstance(node, ast.ImportFrom):
        return ""
    if node.level:
        resolved = _resolve_relative_module(package, node.level, node.module)
        imported = _dotted_module(resolved) if resolved else ""
    else:
        imported = node.module or ""
    if not imported:
        return ""
    if imported == module:
        if not leaf and target_path and all(
                _package_child_module_exists(
                    Path(target_path).parent, alias.name)
                for alias in node.names):
            return ""
        return _format_import_from(node)
    if parent and imported == parent and any(
            alias.name == leaf for alias in node.names):
        return _format_import_from(node)
    return ""
_MERGE_CONTEXT_NAMES = (
    _MODULE_CONTEXT_GLOBALS | _MODULE_CONTEXT_BUILTINS
    | frozenset({"__all__", "__annotations__", "__doc__"}))
@dataclass
class _MergeParts:
    exports_in_body: bool = False
    future_imports: list[str] = field(default_factory=list)
    imports: list[str] = field(default_factory=list)
    bodies: list[str] = field(default_factory=list)
    all_exports: list[str] = field(default_factory=list)
    exports_by_file: dict[str, list[str]] = field(default_factory=dict)
    dynamic_all_error: str = ""
    rel_import_refs: list[tuple[str, ast.ImportFrom]] = field(
        default_factory=list)
    module_context_refs: list[tuple[str, ast.Name]] = field(
        default_factory=list)
    indirect_context_ref_ids: set[int] = field(default_factory=set)
    docstrings: dict[str, str | None] = field(default_factory=dict)
    import_bindings: dict[str, dict[str, set[str]]] = field(
        default_factory=dict)
    import_binding_files: dict[str, set[str]] = field(default_factory=dict)
    definition_files: dict[str, set[str]] = field(default_factory=dict)
    source_files: set[str] = field(default_factory=set)
    from_import_refs: dict[str, list[tuple[str, str, str]]] = field(
        default_factory=dict)
def _primary_merge_docstring(
        acc: _MergeParts, src_codes: list, target_path: str) -> str | None:
    if not src_codes:
        return None
    target_key = normcase(abspath(target_path))
    for source_fp, _code in src_codes:
        if normcase(abspath(source_fp)) == target_key:
            return acc.docstrings.get(source_fp)
    return acc.docstrings.get(src_codes[0][0])
def _definition_conflict_message(acc: _MergeParts) -> str:
    conflicts = {
        symbol: sorted(files)
        for symbol, files in acc.definition_files.items()
        if len(files) > 1
    }
    if not conflicts:
        return ""
    return ("同名顶层绑定冲突(跨文件后定义覆盖前定义)，拒绝落盘: "
            + "; ".join(
                f"{symbol} <- {', '.join(files)}"
                for symbol, files in sorted(conflicts.items())))
def _stale_count(plan: dict) -> int:
    stale = plan.get("stale_references")
    return len(stale) if isinstance(stale, (list, tuple, set, frozenset)) else 0
def _cleanup_counts(pmc_plan: dict) -> tuple[Any, Any, int]:
    plan = pmc_plan.get("plan") or {}
    stats = plan.get("stats") or {}
    return (stats.get("deletable", 0), stats.get("orphans_kept", 0),
            _stale_count(plan))
def _cleanup_detail(deletable: Any, orphans_kept: Any, stale: int,
                    stage_note: str) -> str:
    label = f"({stage_note})" if stage_note else ""
    detail = (f"合并后清理{label}: {deletable} 死桩可删, "
              f"{orphans_kept} 孤儿保留")
    if stale:
        detail += f", {stale} 旧模块仍有消费者(须更新导入)"
    return detail + "(详见报告)"
def _collect_merge_parts(src_codes: list):
    acc = _MergeParts(exports_in_body=len(src_codes) == 1)
    hoist_trees: list[tuple[str, ast.Module]] = []
    for _fp, code in src_codes:
        acc.source_files.add(_fp)
        try:
            tree = ast.parse(code)
        except (SyntaxError, ValueError, RecursionError, MemoryError) as _e:
            log_swallowed(__name__, _e,
                          context=f'_collect_merge_parts:{type(_e).__name__}')
            return None, {"status": "error", "data": {},
                        "message": f"源文件语法异常，拒绝合并落盘: {_fp}"}
        hoist_trees.append((_fp, tree))
        err = _scan_merge_source(tree, code, _fp, acc)
        if err is not None:
            return None, err
    gate_err = _future_divergence_gate(hoist_trees)
    if gate_err is not None:
        return None, gate_err
    gate_err = _import_reorder_gate(hoist_trees)
    if gate_err is not None:
        return None, gate_err
    gate_err = _import_hoist_sequence_gate(hoist_trees)
    if gate_err is not None:
        return None, gate_err
    declared_files = set(acc.exports_by_file)
    if declared_files:
        for _fp, tree in hoist_trees:
            if _fp in declared_files:
                continue
            public_names, dynamic_line = _public_module_binds(tree)
            if dynamic_line is not None:
                return None, {"status": "error", "data": {},
                    "message": "合并源未显式声明 __all__，且含条件/循环/"
                    "异常分支、星号导入或条件解绑，无法静态确定最终 "
                    "import * 导出面，拒绝落盘（请先显式声明静态 "
                    f"__all__）: {_fp} 第 {dynamic_line} 行"}
            acc.exports_by_file[_fp] = public_names
    acc.all_exports = [
        name for _fp, _code in src_codes
        for name in acc.exports_by_file.get(_fp, ())]
    conflict_msg = (_definition_conflict_message(acc)
                    or _import_binding_conflict_message(acc)
                    or _import_definition_conflict_message(acc))
    if conflict_msg:
        return None, {"status": "error", "data": {},
                      "message": conflict_msg}
    return acc, None
def _deleted_binding_names(target: ast.AST) -> list[str]:
    if isinstance(target, ast.Name):
        return [target.id]
    if isinstance(target, (ast.Tuple, ast.List)):
        return [name for elt in target.elts
                for name in _deleted_binding_names(elt)]
    if isinstance(target, ast.Starred):
        return _deleted_binding_names(target.value)
    return []
def _dynamic_public_binding_line(node: ast.stmt) -> int | None:
    if isinstance(node, ast.ImportFrom):
        return (node.lineno if any(alias.name == "*" for alias in node.names)
                else None)
    if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                         ast.Import, ast.Expr) + _MODULE_SCOPE_DEF_TYPES):
        return None
    if module_scope_binds([node]):
        return node.lineno
    wrapper = ast.Module(body=[node], type_ignores=[])
    for sub in _exec_module_stmts(wrapper):
        if (isinstance(sub, ast.ImportFrom)
                and any(alias.name == "*" for alias in sub.names)):
            return sub.lineno
        if (isinstance(sub, ast.Delete) and any(
                _deleted_binding_names(target) for target in sub.targets)):
            return sub.lineno
    return None
def _public_module_binds(tree: ast.Module) -> tuple[list[str], int | None]:
    ordered: dict[str, None] = {}
    for node in tree.body:
        if isinstance(node, ast.ImportFrom) and node.module == "__future__":
            continue
        if isinstance(node, ast.Delete):
            for target in node.targets:
                for name in _deleted_binding_names(target):
                    ordered.pop(name, None)
            continue
        dynamic_line = _dynamic_public_binding_line(node)
        if dynamic_line is not None:
            return [], dynamic_line
        for name in module_scope_binds([node]):
            if not name.startswith("_"):
                ordered[name] = None
    return list(ordered), None
def _assigned_definition_names(node: ast.AST) -> list[str]:
    return sorted(
        module_scope_binds([node]) - import_bound_names([node]))
_MODULE_SCOPE_DEF_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef,
                           ast.ClassDef)
def _control_flow_child_bodies(node: ast.stmt) -> list[list[ast.stmt]]:
    bodies: list[list[ast.stmt]] = []
    if getattr(node, "body", None):
        bodies.append(node.body)
    if isinstance(node, (ast.If, ast.For, ast.While, ast.AsyncFor)):
        if node.orelse:
            bodies.append(node.orelse)
    elif _is_try_node(node):
        bodies.extend(_try_child_bodies(node))
    elif isinstance(node, ast.Match):
        bodies.extend(case.body for case in node.cases if case.body)
    return bodies
def _is_try_node(node: ast.stmt) -> bool:
    return isinstance(node, (ast.Try,) + ((ast.TryStar,)
                                          if hasattr(ast, "TryStar") else ()))
def _try_child_bodies(node: ast.stmt) -> list[list[ast.stmt]]:
    bodies = [handler.body for handler in node.handlers if handler.body]
    if node.orelse:
        bodies.append(node.orelse)
    if node.finalbody:
        bodies.append(node.finalbody)
    return bodies
def _exec_module_stmts(tree: ast.Module) -> list[ast.stmt]:
    ordered: list[ast.stmt] = []
    stack: list[ast.stmt] = list(reversed(tree.body))
    while stack:
        node = stack.pop()
        ordered.append(node)
        if isinstance(node, _MODULE_SCOPE_DEF_TYPES):
            continue
        if isinstance(node, ast.If) and is_type_checking_guard(node.test):
            stack.extend(reversed(node.orelse))
            continue
        for block in _control_flow_child_bodies(node):
            stack.extend(reversed(block))
    return ordered
def _register_definition_bindings(tree: ast.Module, _fp: str,
                                  acc: _MergeParts) -> None:
    for node in _exec_module_stmts(tree):
        for name in _assigned_definition_names(node):
            if name != "__all__":
                acc.definition_files.setdefault(name, set()).add(_fp)
def _merge_scope_reads(code: str) -> tuple[set[str], set[str]] | None:
    try:
        table = symtable.symtable(code, "<merge-source>", "exec")
    except (SyntaxError, ValueError, RecursionError, MemoryError) as exc:
        log_swallowed(__name__, exc,
                      context=f"_merge_scope_reads:{type(exc).__name__}")
        return None
    bound = {
        symbol.get_name() for symbol in table.get_symbols()
        if symbol.is_assigned() or symbol.is_imported()
        or symbol.is_namespace()}
    reads = {
        symbol.get_name() for symbol in table.get_symbols()
        if symbol.is_referenced()}
    for child in table.get_children():
        _collect_scope_global_usage(child, reads, None)
    return reads, bound
def _scan_merge_source(tree, code: str, _fp: str,
                       acc: _MergeParts) -> dict | None:
    acc.docstrings[_fp] = ast.get_docstring(tree, clean=False)
    dynamic_aliases, dynamic_modules = _dynamic_context_import_aliases(tree)
    scope_reads = _merge_scope_reads(code)
    visible_builtins = (BUILTIN_NAMES if scope_reads is None
                        else BUILTIN_NAMES - scope_reads[1])
    indirect_context = _indirect_dynamic_context_refs(
        tree, build_parent_map(tree), dynamic_aliases, dynamic_modules,
        visible_builtins)
    if scope_reads is None:
        context_names = _MERGE_CONTEXT_NAMES | indirect_context
    else:
        global_reads, module_bindings = scope_reads
        context_names = (
            global_reads & (_MERGE_CONTEXT_NAMES - _MODULE_CONTEXT_BUILTINS)
            | (global_reads - module_bindings) & _MODULE_CONTEXT_BUILTINS
            | indirect_context)
    _register_definition_bindings(tree, _fp, acc)
    _register_rel_imports(tree, _fp, acc)
    _register_import_bindings(tree, _fp, acc)
    drop: set[int] = set()
    handled: set[int] = set()
    _drop_module_docstring(tree, drop, handled)
    for node in tree.body:
        _ingest_merge_node(node, _fp, drop, handled, acc)
    for node in tree.body:
        if id(node) in handled:
            continue
        for sub in walk_nodes(node):
            if not (isinstance(sub, ast.Name)
                    and isinstance(sub.ctx, ast.Load)
                    and sub.id in context_names):
                continue
            acc.module_context_refs.append((_fp, sub))
            if sub.id in indirect_context:
                acc.indirect_context_ref_ids.add(id(sub))
    if acc.dynamic_all_error:
        return {"status": "error", "data": {},
                "message": acc.dynamic_all_error}
    gate_err = _single_line_stmt_gate(tree, drop, handled, _fp)
    if gate_err is not None:
        return gate_err
    gate_err = _all_usage_gate(tree, handled, _fp)
    if gate_err is not None:
        return gate_err
    acc.bodies.append(_body_after_drop(code, drop))
    return None
def _drop_module_docstring(tree, drop: set[int],
                           handled: set[int]) -> None:
    if not tree.body:
        return
    first = tree.body[0]
    if not (isinstance(first, ast.Expr)
            and isinstance(first.value, ast.Constant)
            and isinstance(first.value.value, str)):
        return
    drop.update(range(first.lineno - 1, first.end_lineno))
    handled.add(id(first))
def _single_line_stmt_gate(tree, drop: set[int], handled: set[int],
                           _fp: str) -> dict | None:
    for node in tree.body:
        if id(node) in handled:
            continue
        if any(ln in drop for ln in range(node.lineno - 1, node.end_lineno)):
            return {"status": "error", "data": {},
                    "message": "合并源含单行多语句（剔除节点与其他"
                    "语句同行），整行剔除将静默丢弃同行语句，拒绝落盘"
                    f"（请先归一为多行形态）: {_fp} 第 {node.lineno} 行"}
    return None
def _import_binding_pairs(node: ast.AST) -> list[tuple[str, str]]:
    pairs: list[tuple[str, str]] = []
    if isinstance(node, ast.Import):
        for alias in node.names:
            bound = alias.asname or alias.name.split(".")[0]
            origin = alias.name if alias.asname else alias.name.split(".")[0]
            pairs.append((bound, origin))
    elif isinstance(node, ast.ImportFrom):
        mod = "." * node.level + (node.module or "")
        for alias in node.names:
            if alias.name == "*":
                continue
            pairs.append((alias.asname or alias.name, f"{mod}.{alias.name}"))
    return pairs
def _register_import_bindings(tree, _fp: str, acc: _MergeParts) -> None:
    for node in _exec_module_stmts(tree):
        if isinstance(node, ast.ImportFrom) and node.module == "__future__":
            continue
        if isinstance(node, ast.ImportFrom):
            module = "." * node.level + (node.module or "")
            for alias in node.names:
                if alias.name != "*":
                    acc.from_import_refs.setdefault(
                        alias.asname or alias.name, []).append(
                            (_fp, module, alias.name))
        for bound, origin in _import_binding_pairs(node):
            acc.import_bindings.setdefault(bound, {}).setdefault(
                origin, set()).add(_fp)
            acc.import_binding_files.setdefault(bound, set()).add(_fp)
def _import_binding_conflict_message(acc: _MergeParts) -> str:
    conflicts: dict[str, dict[str, set[str]]] = {}
    for name, origins in acc.import_bindings.items():
        if len(origins) < 2:
            continue
        if len(set().union(*origins.values())) < 2:
            continue
        conflicts[name] = origins
    if not conflicts:
        return ""
    return ("合并源同名导入来自不同模块，合并后会重排求值顺序并只保留其一，"
            "引用方行为被静默改变，拒绝落盘（请先归一导入来源）: "
            + "; ".join(
                f"{name} <- " + ", ".join(
                    f"{origin}({', '.join(sorted(files))})"
                    for origin, files in sorted(origins.items()))
                for name, origins in sorted(conflicts.items())))
def _module_file_candidates(module: str) -> list[str]:
    return [module + ".py", os.path.join(module, "__init__.py")]
def _relative_import_source(acc: _MergeParts, import_fp: str,
                            module: str) -> str | None:
    dots = len(module) - len(module.lstrip("."))
    base = os.path.dirname(os.path.abspath(import_fp))
    for _ in range(max(dots - 1, 0)):
        base = os.path.dirname(base)
    tail = module[dots:]
    module_path = (os.path.join(base, *tail.split(".")) if tail else base)
    candidates = {os.path.normcase(os.path.abspath(path))
                  for path in _module_file_candidates(module_path)}
    matches = [fp for fp in acc.source_files
               if os.path.normcase(os.path.abspath(fp)) in candidates]
    return matches[0] if len(matches) == 1 else None
def _absolute_import_source(acc: _MergeParts, module: str) -> str | None:
    module_parts = tuple(os.path.normcase(part)
                         for part in module.split(".") if part)
    if not module_parts:
        return None
    matches: list[str] = []
    for fp in acc.source_files:
        parts = list(Path(os.path.normcase(os.path.abspath(fp))).parts)
        if parts and parts[-1].lower().endswith(".py"):
            parts[-1] = parts[-1][:-3]
        if parts and parts[-1] == "__init__":
            parts.pop()
        if len(parts) >= len(module_parts) and tuple(
                parts[-len(module_parts):]) == module_parts:
            matches.append(fp)
    return matches[0] if len(matches) == 1 else None
def _is_same_origin_definition(acc: _MergeParts, name: str,
                               import_fp: str, definition_fp: str) -> bool:
    for ref_fp, module, imported_name in acc.from_import_refs.get(name, ()):
        if ref_fp != import_fp or imported_name != name:
            continue
        source = (_relative_import_source(acc, ref_fp, module)
                  if module.startswith(".") else
                  _absolute_import_source(acc, module))
        if source is not None and os.path.normcase(os.path.abspath(
                source)) == os.path.normcase(os.path.abspath(definition_fp)):
            return True
    return False
def _import_definition_conflict_message(acc: _MergeParts) -> str:
    conflicts: list[str] = []
    for name, import_files in sorted(acc.import_binding_files.items()):
        definition_files = acc.definition_files.get(name, set())
        if not definition_files or not any(
                import_fp != definition_fp
                and not _is_same_origin_definition(
                    acc, name, import_fp, definition_fp)
                for import_fp in import_files
                for definition_fp in definition_files):
            continue
        conflicts.append(
            f"{name} <- import({', '.join(sorted(import_files))}) "
            f"vs definition({', '.join(sorted(definition_files))})")
    if not conflicts:
        return ""
    return ("合并源导入与顶层定义跨文件同名，合并后会覆盖绑定并改变引用方行为，"
            "拒绝落盘（请先归一命名）: " + "; ".join(conflicts))
def _register_rel_imports(tree, _fp: str, acc: _MergeParts) -> None:
    for node in walk_nodes(tree):
        if isinstance(node, ast.ImportFrom) and node.level > 0:
            acc.rel_import_refs.append((_fp, node))
_IMPORT_ENV_ATTRS = frozenset({
    ("sys", "path"), ("sys", "modules"), ("os", "environ"),
})
_IMPORT_ENV_DOTTED = frozenset(
    ".".join(pair) for pair in _IMPORT_ENV_ATTRS)
_IMPORT_HOIST_GATE_MSG = (
    "合并会把顶层 import 提升到导入环境变更（sys.path/sys.modules/"
    "os.environ）之前，改变导入解析顺序与结果，拒绝落盘（请先归一："
    "移除脚本自举改用显式包导入，或把环境变更后移）: %s 第 %d 行")
def _import_module_aliases(tree) -> dict[str, str]:
    aliases: dict[str, str] = {}
    for node in iter_import_time_nodes(tree):
        if not isinstance(node, ast.Import):
            continue
        for alias in node.names:
            aliases[alias.asname or alias.name.split(".")[0]] = alias.name
    return aliases
def _import_env_aliases(tree: ast.AST) -> dict[str, tuple[str, str]]:
    aliases: dict[str, tuple[str, str]] = {}
    for node in iter_import_time_nodes(tree):
        if not (isinstance(node, ast.ImportFrom) and not node.level
                and node.module):
            continue
        for alias in node.names:
            dotted = f"{node.module}.{alias.name}"
            if dotted not in _IMPORT_ENV_DOTTED:
                continue
            module, _, attr = dotted.partition(".")
            aliases[alias.asname or alias.name] = (module, attr)
    return aliases
_IMPORT_ENV_MUTATING_METHODS = frozenset({
    "append", "extend", "insert", "remove", "pop", "popitem", "clear",
    "update", "setdefault", "sort", "reverse", "__setitem__", "__delitem__",
})
def _import_env_object(
        node: ast.AST, aliases: dict[str, str],
        env_aliases: dict[str, tuple[str, str]]) -> tuple[str, str] | None:
    if isinstance(node, ast.Name):
        return env_aliases.get(node.id)
    if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
        root = aliases.get(node.value.id, node.value.id).split(".")[0]
        candidate = (root, node.attr)
        if candidate in _IMPORT_ENV_ATTRS:
            return candidate
    return None
def _import_env_line(
    node: ast.AST, aliases: dict[str, str],
    env_aliases: dict[str, tuple[str, str]], *,
    annotations_evaluated: bool = True,
) -> int | None:
    for sub in iter_import_time_nodes(
            node, annotations_evaluated=annotations_evaluated):
        lineno = getattr(sub, "lineno", getattr(node, "lineno", 0))
        if (isinstance(sub, (ast.Attribute, ast.Subscript))
                and isinstance(sub.ctx, (ast.Store, ast.Del))):
            target = sub if isinstance(sub, ast.Attribute) else sub.value
            if _import_env_object(target, aliases, env_aliases) is not None:
                return lineno
        if (isinstance(sub, ast.AugAssign)
                and isinstance(sub.target, ast.Name)
                and sub.target.id in env_aliases):
            return lineno
        if (isinstance(sub, ast.Call)
                and isinstance(sub.func, ast.Attribute)
                and sub.func.attr in _IMPORT_ENV_MUTATING_METHODS
                and _import_env_object(
                    sub.func.value, aliases, env_aliases) is not None):
            return lineno
    return None
def _future_features(tree: ast.Module) -> frozenset[str]:
    features: set[str] = set()
    for node in tree.body:
        if (isinstance(node, ast.ImportFrom) and node.level == 0
                and node.module == "__future__"):
            features.update(alias.name for alias in node.names)
    return frozenset(features)
def _future_divergence_gate(
        trees: list[tuple[str, ast.Module]]) -> dict | None:
    groups: dict[frozenset[str], list[str]] = {}
    for _fp, tree in trees:
        groups.setdefault(_future_features(tree), []).append(_fp)
    if len(groups) <= 1:
        return None
    details = "; ".join(
        f"{sorted(features) or '无 __future__ 特性'} <- "
        + ", ".join(sorted(files))
        for features, files in sorted(groups.items(),
                                     key=lambda item: sorted(item[1])))
    return {"status": "error", "data": {},
            "message": "合并源 __future__ 特性集不一致，单份 __future__ "
                       "声明无法同时保留各源语义（注解求值/语法特性会"
                       "被静默统一），拒绝落盘（请先归一 __future__ "
                       "声明）: " + details}
_IMPORT_REORDER_MSG = (
    "合并会把顶层 import 提升到其前面的语句之上，语句与导入的求值/绑定"
    "顺序改变（源文件不会发生），引用方将看到不同绑定，拒绝落盘（请先"
    "归一：把 import 前移到所有语句之前）: %s 第 %d 行 与 %s 第 %d 行"
    "重叠名 %s")
_IMPORT_SIDE_EFFECT_REORDER_MSG = (
    "合并会把顶层 import 提升到前序运行时语句之上，导入副作用与语句"
    "求值顺序改变（即使绑定名不重叠也无法保持外部行为），拒绝落盘"
    "（请先把顶层 import 前移到所有运行时语句之前）: %s 第 %d 行；"
    "前序运行时语句 %s 第 %d 行")
def _import_time_load_names(
    node: ast.AST, *, annotations_evaluated: bool = True,
) -> set[str]:
    return {
        sub.id
        for sub in iter_import_time_nodes(
            node, annotations_evaluated=annotations_evaluated)
        if isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load)
    }
def _import_time_touches(
    node: ast.AST, *, annotations_evaluated: bool = True,
) -> set[str]:
    if is_all_assignment(node) or _is_pure_all_annotation(node):
        return set()
    if (isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Constant)
            and isinstance(node.value.value, str)):
        return set()
    if isinstance(node, ast.If) and is_type_checking_guard(node.test):
        return module_scope_binds([node])
    return module_scope_binds([node]) | _import_time_load_names(
        node, annotations_evaluated=annotations_evaluated)
def _import_order_neutral(node: ast.stmt) -> bool:
    if isinstance(node, ast.Pass):
        return True
    if (isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Constant)
            and isinstance(node.value.value, str)):
        return True
    return (isinstance(node, ast.If)
            and is_type_checking_guard(node.test) and not node.orelse)
def _import_reorder_gate(
        trees: list[tuple[str, ast.Module]]) -> dict | None:
    touched: dict[str, tuple[str, int]] = {}
    prior_runtime: tuple[str, int] | None = None
    # 装配阶段按语句文本去重（assemble_merged_source → dict.fromkeys），
    # 后续文件里与之文本完全相同的 import 在产物中根本不会出现，也就不存在
    # "被提升到前序运行时语句之上"的副作用重排；只有首次出现（真正会落盘
    # 执行一次）的 import 才需要做提升位置校验。
    emitted_imports: set[str] = set()
    for fp, tree in trees:
        annotations_evaluated = not module_postpones_annotations(
            tree, require_absolute=True)
        for node in tree.body:
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                is_star = any(alias.name == "*" for alias in node.names)
                if is_star and touched:
                    src_fp, src_line = min(
                        touched.values(), key=lambda item: item[1])
                    return {"status": "error", "data": {},
                            "message": _IMPORT_REORDER_MSG % (
                                fp, node.lineno, src_fp, src_line,
                                "<星号导入绑定面不可枚举>")}
                overlap = import_stmt_binds(node) & touched.keys()
                if overlap:
                    name = min(overlap)
                    src_fp, src_line = touched[name]
                    return {"status": "error", "data": {},
                            "message": _IMPORT_REORDER_MSG % (
                                fp, node.lineno, src_fp, src_line, name)}
                statement_text = _import_statement_text(node)
                if statement_text in emitted_imports:
                    continue
                emitted_imports.add(statement_text)
                if prior_runtime is not None:
                    src_fp, src_line = prior_runtime
                    return {"status": "error", "data": {},
                            "message": _IMPORT_SIDE_EFFECT_REORDER_MSG % (
                                fp, node.lineno, src_fp, src_line)}
                continue
            if prior_runtime is None and not _import_order_neutral(node):
                prior_runtime = (fp, node.lineno)
            for name in _import_time_touches(
                    node, annotations_evaluated=annotations_evaluated):
                touched.setdefault(name, (fp, node.lineno))
    return None
def _import_hoist_sequence_gate(
        trees: list[tuple[str, ast.Module]]) -> dict | None:
    pending_env: tuple[str, int] | None = None
    for _fp, tree in trees:
        aliases = _import_module_aliases(tree)
        env_aliases = _import_env_aliases(tree)
        annotations_evaluated = not module_postpones_annotations(
            tree, require_absolute=True)
        for node in tree.body:
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                if pending_env is not None:
                    env_fp, env_line = pending_env
                    return {"status": "error", "data": {},
                            "message": _IMPORT_HOIST_GATE_MSG % (
                                env_fp, env_line)}
                continue
            if pending_env is None:
                env_line = _import_env_line(
                    node, aliases, env_aliases,
                    annotations_evaluated=annotations_evaluated)
                if env_line is not None:
                    pending_env = (_fp, env_line)
    return None
_ALL_USAGE_GATE_MSG = (
    "合并源在导入期引用 __all__（动态增改、条件增补或非静态参数"
    "无法静态折叠），合并产物会在 __all__ 赋值前求值而 NameError，"
    "拒绝落盘（请先归一为静态 __all__ 声明）: %s 第 %d 行")
def _is_pure_all_annotation(node: ast.AST) -> bool:
    return (isinstance(node, ast.AnnAssign) and node.value is None
            and isinstance(node.target, ast.Name)
            and node.target.id == "__all__")
def _all_rebind_line(
    node: ast.AST, *, annotations_evaluated: bool = True,
) -> int | None:
    for sub in iter_import_time_nodes(
            node, annotations_evaluated=annotations_evaluated):
        lineno = getattr(sub, "lineno", getattr(node, "lineno", 0))
        if (isinstance(sub, ast.Name) and sub.id == "__all__"
                and isinstance(sub.ctx, (ast.Store, ast.Del))):
            return lineno
        if isinstance(sub, ast.AugAssign) and is_all_target(sub.target):
            return lineno
        if isinstance(sub, ast.Delete) and any(
                is_all_target(target) for target in sub.targets):
            return lineno
        if (isinstance(sub, ast.Subscript) and is_all_target(sub.value)
                and isinstance(sub.ctx, (ast.Store, ast.Del))):
            return lineno
        if (isinstance(sub, ast.Call) and isinstance(sub.func, ast.Attribute)
                and is_all_target(sub.func.value)
                and sub.func.attr in INPLACE_MUTATING_METHODS):
            return lineno
    return None
def _all_load_line(
    node: ast.AST, *, annotations_evaluated: bool = True,
) -> int | None:
    for sub in iter_import_time_nodes(
            node, annotations_evaluated=annotations_evaluated):
        if (isinstance(sub, ast.Name) and sub.id == "__all__"
                and isinstance(sub.ctx, ast.Load)):
            return sub.lineno
    return None
def _all_usage_line(
    node: ast.AST, *, annotations_evaluated: bool = True,
) -> int | None:
    if _is_pure_all_annotation(node):
        return None
    line = _all_rebind_line(
        node, annotations_evaluated=annotations_evaluated)
    return line if line is not None else _all_load_line(
        node, annotations_evaluated=annotations_evaluated)
def _all_usage_gate(tree, handled: set[int], _fp: str) -> dict | None:
    annotations_evaluated = not module_postpones_annotations(
        tree, require_absolute=True)
    for node in tree.body:
        if id(node) in handled:
            continue
        lineno = _all_usage_line(
            node, annotations_evaluated=annotations_evaluated)
        if lineno is not None:
            return {"status": "error", "data": {},
                    "message": _ALL_USAGE_GATE_MSG % (_fp, lineno)}
    return None
def _body_after_drop(code: str, drop: set[int]) -> str:
    all_lines = physical_lines_keepends(code)
    body = "".join(ln for i, ln in enumerate(all_lines) if i not in drop)
    return body.strip("\r\n")
def _format_alias(alias: ast.alias) -> str:
    return f"{alias.name} as {alias.asname}" if alias.asname else alias.name
def _format_import_from(node: ast.ImportFrom) -> str:
    mod = "." * node.level + (node.module or "")
    return f"from {mod} import " + ", ".join(
        _format_alias(a) for a in node.names)
def _import_statement_text(node: ast.Import | ast.ImportFrom) -> str:
    """与装配阶段写入 imports 片段完全一致的语句文本（不含换行）。"""
    if isinstance(node, ast.Import):
        return "import " + ", ".join(_format_alias(a) for a in node.names)
    return _format_import_from(node)
def _ingest_merge_node(node, _fp: str, drop: set,
                       handled: set, acc: _MergeParts) -> None:
    if _ingest_all_declaration(node, _fp, drop, handled, acc):
        return
    if _ingest_all_mutation(node, _fp, drop, handled, acc):
        return
    if isinstance(node, ast.Import):
        acc.imports.append(_import_statement_text(node) + "\n")
        _mark_handled(node, drop, handled)
    elif isinstance(node, ast.ImportFrom):
        _ingest_import_from(node, drop, handled, acc)
_DYNAMIC_ALL_DECL_MSG = (
    "合并源的 __all__ 非静态字面量声明（推导式/条件/函数调用/星号展开或"
    "非常规增强运算符），无法静态折叠导出面：保留动态语句会被生成的静态 "
    "__all__ 覆盖，动态导出名静默丢失，拒绝落盘（请先归一为静态 "
    "__all__ 字面量）: %s 第 %d 行")
_MULTI_TARGET_ALL_DECL_MSG = (
    "合并源的 __all__ 采用多目标赋值（同一语句还绑定其他名字），静态"
    "折叠会把同一语句的其他绑定一起丢弃，合并产物将在引用处 NameError，"
    "拒绝落盘（请先归一为单目标 __all__ 声明）: %s 第 %d 行")
_ALL_WITHOUT_STATIC_BASE_MSG = (
    "合并源在本文件静态 __all__ 初始化前执行增改，初始导出面可能来自"
    "导入或动态绑定，且原语句可能原地修改其他模块的列表；静态折叠会"
    "丢失既有导出与副作用，拒绝落盘（请先改为静态字面量初始化后再增改）"
    ": %s 第 %d 行")
def _is_foldable_all_declaration(node: ast.AST) -> bool:
    if isinstance(node, ast.AugAssign):
        return isinstance(node.op, (ast.Add, ast.BitOr))
    return True
def _ingest_all_declaration(node, _fp: str, drop: set, handled: set,
                            acc: _MergeParts) -> bool:
    if not (isinstance(node, (ast.Assign, ast.AugAssign, ast.AnnAssign))
            and is_all_assignment(node)):
        return False
    if isinstance(node, ast.Assign) and len(node.targets) > 1:
        acc.dynamic_all_error = _MULTI_TARGET_ALL_DECL_MSG % (
            _fp, node.lineno)
        return True
    elems = extract_all_names(node)
    if elems is None or not _is_foldable_all_declaration(node):
        acc.dynamic_all_error = _DYNAMIC_ALL_DECL_MSG % (_fp, node.lineno)
        return True
    if isinstance(node, ast.AugAssign):
        if _fp not in acc.exports_by_file:
            acc.dynamic_all_error = _ALL_WITHOUT_STATIC_BASE_MSG % (
                _fp, node.lineno)
            return True
        acc.exports_by_file.setdefault(_fp, []).extend(elems)
    else:
        acc.exports_by_file[_fp] = list(elems)
    if acc.exports_in_body:
        handled.add(id(node))
    else:
        _mark_handled(node, drop, handled)
    return True
def _static_str_elems(value: object) -> list[str] | None:
    if not isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        return None
    elems: list[str] = []
    for elt in value.elts:
        if not (isinstance(elt, ast.Constant) and isinstance(elt.value, str)):
            return None
        elems.append(elt.value)
    return elems
def _folded_all_mutation(node) -> list[str] | None:
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)):
        return None
    call = node.value
    func = call.func
    if not (isinstance(func, ast.Attribute) and is_all_target(func.value)):
        return None
    if call.keywords or len(call.args) != 1:
        return None
    if func.attr == "append":
        arg = call.args[0]
        if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
            return [arg.value]
        return None
    if func.attr == "extend":
        return _static_str_elems(call.args[0])
    return None
def _ingest_all_mutation(node, _fp: str, drop: set, handled: set,
                         acc: _MergeParts) -> bool:
    elems = _folded_all_mutation(node)
    if elems is None:
        return False
    if _fp not in acc.exports_by_file:
        acc.dynamic_all_error = _ALL_WITHOUT_STATIC_BASE_MSG % (
            _fp, node.lineno)
        return True
    acc.exports_by_file.setdefault(_fp, []).extend(elems)
    if acc.exports_in_body:
        handled.add(id(node))
    else:
        _mark_handled(node, drop, handled)
    return True
def _ingest_import_from(node, drop: set, handled: set,
                        acc: _MergeParts) -> None:
    bucket = (acc.future_imports if node.module == "__future__"
              else acc.imports)
    bucket.append(_import_statement_text(node) + "\n")
    _mark_handled(node, drop, handled)
def _mark_handled(node, drop: set, handled: set) -> None:
    drop.update(range(node.lineno - 1, node.end_lineno))
    handled.add(id(node))
class MigrateExecutor(BaseExecutor):
    def execute(self, action: Any) -> ExecutorResult:
        self.result = ExecutorResult(action_type="migrate")
        validated = self._validate_migrate_inputs(action)
        if validated is None:
            return self.result
        symbols, source, target = validated
        source_path = self.skill_dir / source
        target_path = self.skill_dir / target
        self.result.source_files = [str(source_path)]
        self.result.target_files = [str(target_path)]
        consumption_map = self._build_migrate_evidence(
            symbols, source_path, target_path)
        risk_syms = self.result.extra.get("migration_risks", [])
        safe_syms = [s for s in symbols if s not in risk_syms]
        gate_reason = self._commit_gate_reason(
            consumption_map, source_path, target_path, safe_syms)
        if gate_reason:
            self.result.details.append(gate_reason)
            self._fail(gate_reason)
            return self.result
        prepared = self._preview_migrate_in(
            source_path, target_path, safe_syms)
        self._commit_migrate_writes(
            source_path, target_path, safe_syms, prepared)
        if self.result.status != "failed":
            self.result.status = "success"
        return self.result
    def _validate_migrate_inputs(self, action: Any):
        symbols = self._action_get(action, "symbols", [])
        source = self._action_get(action, "source", "")
        target = self._action_get(action, "target", "")
        if not symbols or not source or not target:
            self._fail("缺少 symbols/source/target 参数")
            return None
        raw_symbols = symbols
        symbols = _as_source_list(raw_symbols)
        if symbols is None:
            self._fail(f"symbols 参数形态非法: {type(raw_symbols).__name__}"
                "（须为符号清单或单符号字符串）")
            return None
        if any(not isinstance(symbol, str) or not symbol.strip()
               for symbol in symbols):
            self._fail("symbols 元素形态非法（须全部为非空 str）")
            return None
        symbols = list(dict.fromkeys(symbols))
        found_bad, _bad_path = _first_non_path(source, target)
        if found_bad:
            self._fail(f"source/target 路径形态非法: {type(_bad_path).__name__}"
                "（须为 str/PathLike）")
            return None
        try:
            source = str(self._resolve_action_path(source))
            target = str(self._resolve_action_path(target))
        except ValueError as exc:
            log_swallowed(__name__, exc, context='_validate_migrate_inputs:ValueError')
            self._fail(str(exc))
            return None
        return symbols, source, target
    def _build_migrate_evidence(self, symbols: list, source_path,
                                target_path) -> dict:
        consumption_map = self._load_consumption_map()
        if not consumption_map:
            return consumption_map
        try:
            evidence, risk_symbols = self._judge_symbols(
                symbols, source_path, target_path, consumption_map)
        except Exception as _jme:  # noqa: BLE001
            _log.warning("[MigrateExecutor] 迁移证据生成失败(降级为仅记录): %s",
                         _jme)
            self.result.details.append(
                f"迁移证据生成失败，降级为仅记录源/目标文件: {_jme}")
            return {}
        self.result.extra["migration_evidence"] = evidence
        if risk_symbols:
            self.result.extra["migration_risks"] = risk_symbols
        return consumption_map
    def _load_consumption_map(self) -> dict:
        try:
            return get_consumption_map(str(self.skill_dir), cache=self._cache)
        except Exception as _cme:  # noqa: BLE001
            _log.warning(
                "[MigrateExecutor] 消费图构建失败(降级为仅记录): %s", _cme)
            self.result.details.append(
                f"消费图构建失败，迁移证据降级为仅记录源/目标文件: {_cme}")
            return {}
    def _judge_symbols(self, symbols: list, source_path,
                       target_path, consumption_map: dict) -> tuple[list, list]:
        evidence: list[dict] = []
        risk_symbols: list[str] = []
        for sym in symbols:
            verdict = judge_migration(
                sym, str(source_path), str(target_path), consumption_map)
            evidence.append({
                "symbol": sym,
                "verdict": verdict.action,
                "priority": verdict.priority,
                "consumer_count": verdict.consumer_count,
                "reason": verdict.reason,
            })
            if verdict.action == "skip":
                risk_symbols.append(sym)
                _log.warning("[MigrateExecutor] 迁移风险 %s: %s",
                             sym, verdict.reason)
            else:
                self.result.details.append(
                    f"迁移证据 {sym}: {verdict.priority} "
                    f"({verdict.consumer_count} 消费者) — {verdict.reason}")
        return evidence, risk_symbols
    def _preview_migrate_in(self, source_path, target_path,
                            safe_syms: list):
        try:
            candidates, previews = _prepare_migrate_in_impl(
                source_path, target_path, safe_syms)
            self._record_preview(previews)
            failed = [preview for preview in previews if not preview.success]
            if failed:
                detail = "; ".join(
                    f"{preview.symbol}: {preview.reason}" for preview in failed)
                self._fail("迁入预览含失败项，已中止本次迁移: " + detail)
            return candidates, previews
        except Exception as _pe:  # noqa: BLE001
            _log.warning("[MigrateExecutor] 迁入预览生成失败(降级跳过): %s", _pe)
            if self.dry_run:
                self._fail(f"迁入预览生成失败: {_pe}")
            return None
    def _record_preview(self, previews: list) -> None:
        self.result.extra["migrate_in_preview"] = [
            {"symbol": p.symbol, "success": p.success, "reason": p.reason}
            for p in previews
        ]
        for preview in previews:
            if preview.success:
                self.result.details.append(
                    f"迁入预览 {preview.symbol}: {preview.reason}")
    def _commit_migrate_writes(self, source_path, target_path,
                               safe_syms: list, prepared) -> None:
        if self.dry_run or self.result.status == "failed":
            return
        try:
            self._migrate_commit_inner(
                source_path, target_path, safe_syms, prepared)
        except Exception as _ce:  # noqa: BLE001
            _log.warning("[MigrateExecutor] 落盘执行失败(降级记录): %s", _ce)
            self.result.extra["commit"] = {
                "status": "error", "data": {},
                "message": f"落盘执行异常: {_ce}"}
            self._fail(f"落盘执行异常: {_ce}")
    def _migrate_commit_inner(self, source_path, target_path,
                              safe_syms: list, prepared) -> None:
        if prepared is not None:
            candidates, previews = prepared
        else:
            candidates, previews = _prepare_migrate_in_impl(
                source_path, target_path, safe_syms)
        commit = commit_migrate_in(
            candidates, previews, str(target_path), str(self.skill_dir))
        if self._finalize_commit(commit, "迁移落盘失败"):
            self.result.changes_made = len(
                commit["data"].get("symbols_migrated", []))
    def _commit_gate_reason(self, consumption_map: dict, source_path,
                            target_path, safe_syms: list) -> str:
        if not (source_path.exists() and target_path.exists()):
            return ("源/目标文件不存在，跳过落盘: "
                    f"source={source_path}(exists={source_path.exists()}), "
                    f"target={target_path}(exists={target_path.exists()})")
        if not consumption_map:
            return ("消费图不可用（构建失败、空图或证据生成失败），"
                    "跳过落盘：迁移须消费证据支持，无证据不写盘")
        if not safe_syms:
            return "全部符号存在迁移风险，跳过落盘（需先解决风险）"
        return ""
def _rewrite_payload_error(new_code: Any) -> str:
    if not isinstance(new_code, str):
        return (f"重写载荷须为 str 源码文本，得到 {type(new_code).__name__}"
                "（落盘门禁会拒绝写入）")
    if not new_code.strip():
        return ("重写载荷为空或仅含空白字符，拒绝以空文件覆盖源文件"
                "（需提供重写后代码）")
    if not is_syntax_valid(new_code):
        return "重写载荷语法校验失败（落盘门禁会拒绝写入）"
    return ""
class RewriteExecutor(BaseExecutor):
    def execute(self, action: Any) -> ExecutorResult:
        self.result = ExecutorResult(action_type="rewrite")
        plan = self._plan_rewrite(action)
        if plan is None:
            return self.result
        source_path, new_code = plan
        if self.dry_run:
            self._preview_rewrite(source_path, new_code)
        else:
            payload_error = _rewrite_payload_error(new_code)
            if payload_error:
                self._fail(payload_error)
            else:
                commit = commit_writes([(str(source_path), new_code)],
                                        str(self.skill_dir))
                if self._finalize_commit(commit, "重写落盘失败"):
                    self.result.changes_made = 1
        if self.result.status != "failed":
            self.result.status = "success"
        return self.result
    def _preview_rewrite(self, source: Path, new_code: Any) -> None:
        error = _rewrite_payload_error(new_code)
        if error:
            self._fail(error)
            return
        self.result.details.append(
            f"重写候选（预览，待 AI 审核携带 new_code 以 dry_run=False 落盘）: "
            f"{source}")
    def _plan_rewrite(self, action: Any):
        resolved = self._resolve_source(action)
        if resolved is None:
            return None
        source_path = resolved
        new_code = self._action_get(action, "new_code", "")
        if self._needs_old_source(new_code) and not self._old_source_readable(
                source_path):
            self._fail(f"源文件读取/解析失败: {source_path}")
            return None
        return source_path, new_code
    def _resolve_source(self, action: Any) -> Path | None:
        source = self._action_get(action, "source", "")
        if not source:
            self._fail("缺少 source 参数")
            return None
        found_bad, bad = _first_non_path(source)
        if found_bad:
            self._fail(f"source 路径形态非法: {type(bad).__name__}"
                "（须为 str/PathLike）")
            return None
        source = os.fspath(source)
        try:
            source_path = self._resolve_action_path(source)
        except ValueError as exc:
            log_swallowed(__name__, exc, context='_resolve_source:ValueError')
            self._fail(str(exc))
            return None
        self.result.source_files = [str(source_path)]
        if not source_path.exists():
            self._fail(f"源文件不存在: {source_path}")
            return None
        if not source_path.is_file():
            self._fail(f"重写源路径存在但不是普通文件，拒绝覆盖: {source_path}")
            return None
        return source_path
    def _needs_old_source(self, new_code: Any) -> bool:
        return not new_code
    def _old_source_readable(self, source_path: Path) -> bool:
        src, _fingerprint = self._read_source(str(source_path))
        return src is not None
__all__ = [
    "DEFAULT_REFACTOR_DRY_RUN",
    "BaseExecutor",
    "ExecutorResult",
    "MergeExecutor",
    "MigrateExecutor",
    "RewriteExecutor",
]

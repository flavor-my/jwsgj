from __future__ import annotations

import ast
import logging
import os
import re
from typing import Any

from jwsgj.build_safe_write import commit_writes
from jwsgj.diag_shared_ast_bindings import (
    import_bound_names,
    import_stmt_binds,
    module_scope_binds,
)
from jwsgj.diag_shared_ast_nodes import (
    iter_def_site_nodes,
    iter_import_time_nodes,
    iter_module_level_stmts,
    iter_module_scope_nodes,
    parse_source_tree,
    symbol_start_line,
)
from jwsgj.diag_shared_ast_surface import (
    extract_all_names,
    is_all_assignment,
    replay_export_surface,
)
from jwsgj.diag_shared_source_core import (
    ast_split_lines,
    line_start_offset,
    read_source_with_fingerprint,
    utf8_span_to_char_span,
)
from jwsgj.diag_types_vocab import PARSE_DEGRADE_EXC
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.refactor_migration_prepare import (
    MigrateInResult,
    _candidate_identity,
    _package_chain,
    _path_text,
    _resolve_relative_target,
    _retained_source_refs,
    _source_eol,
    _symbol_global_usage,
    invalidate_consumption_cache,
    invalidate_zcc_cache,
    norm_cache_key,
    retained_source_reference_blocks,
)
from jwsgj.runtime_scope import (
    collect_migration_py_files,
    strip_stale_coding_declaration,
)

_log = logging.getLogger(__name__)
_EOL_KEEP_RE = re.compile(r"(\r\n|\r|\n)")
def _line_eols(code: str) -> list[str]:
    parts = _EOL_KEEP_RE.split(code)
    eols = parts[1::2]
    total = len(ast_split_lines(code))
    while len(eols) < total:
        eols.append("")
    return eols[:total]
def _removal_reference_blocks(source_code: str,
                              removed: list[str]) -> list[str]:
    tree = parse_source_tree(
        source_code, '_removal_reference_blocks:parse_source_tree')
    if tree is None:
        return []
    return retained_source_reference_blocks(tree, set(removed))
def _retained_symbol_bindings(code: str, removed: list[str]) -> list[str]:
    tree = parse_source_tree(
        code, '_retained_symbol_bindings:parse_source_tree')
    if tree is None:
        return list(removed)
    binds = module_scope_binds(tree.body)
    return sorted({name for name in removed if name in binds})
def _nested_scope_declares_global_all(node: ast.AST) -> bool:
    barriers = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)
    stack = list(getattr(node, "body", ()))
    while stack:
        child = stack.pop()
        if isinstance(child, barriers):
            continue
        if isinstance(child, ast.Global) and "__all__" in child.names:
            return True
        stack.extend(ast.iter_child_nodes(child))
    return False

def _nested_scope_mutates_all(node: ast.AST) -> bool:
    if not _nested_scope_declares_global_all(node):
        return False
    statements = [ast.Expr(value=expr) for expr in iter_def_site_nodes(node)]
    if isinstance(node, ast.Lambda):
        statements.append(ast.Expr(value=node.body))
    else:
        statements.extend(getattr(node, "body", ()))
    nested_module = ast.fix_missing_locations(
        ast.Module(body=statements, type_ignores=[]))
    return replay_export_surface(nested_module).declared
def _has_nested_all_mutation(tree: ast.Module) -> bool:
    barriers = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)
    return any(isinstance(node, barriers) and _nested_scope_mutates_all(node)
               for node in walk_nodes(tree))
def _all_export_literals(code: str) -> set[str] | None:
    tree = parse_source_tree(
        code, '_all_export_literals:parse_source_tree')
    if tree is None or _has_nested_all_mutation(tree):
        return None
    replay = replay_export_surface(tree)
    return set(replay.names) if replay.exact else None
def _reject_commit(message: str) -> tuple[list, dict]:
    return [], {"status": "error", "data": {}, "message": message}
def _validate_commit_inputs(candidates: list, results: list,
                            target_filepath: str) -> tuple[list, dict | None]:
    if not isinstance(candidates, (list, tuple)):
        return _reject_commit(
            f"candidates 须为清单，得到 {type(candidates).__name__}")
    if not isinstance(results, (list, tuple)):
        return _reject_commit(
            f"results 须为清单，得到 {type(results).__name__}")
    if not results:
        return _reject_commit("无可提交的迁入结果")
    bad_results = [r for r in results
                   if not isinstance(r, MigrateInResult)]
    if bad_results:
        return _reject_commit(
            "results 含非法条目"
            f"（{type(bad_results[0]).__name__}），须为 MigrateInResult 清单")
    bad_candidates = [c for c in candidates
                      if _candidate_identity(c) is None]
    if bad_candidates:
        return _reject_commit(
            "candidates 含非法条目"
            f"（{type(bad_candidates[0]).__name__}），"
            "须含非空 str 型 symbol/source_file")
    if len(candidates) != len(results):
        return _reject_commit(
            f"candidates({len(candidates)}) 与 results({len(results)}) "
            "长度不一致，拒绝落盘"
            "（results 须来自 batch_migrate_in 的顺序对应返回）")
    target_text = _path_text(target_filepath)
    if not target_text:
        return _reject_commit("target_filepath 须为非空路径")
    target_key = norm_cache_key(target_text)
    source_baselines: dict[str, str] = {}
    target_baseline = ""
    baseline_seen = False
    failed: list[MigrateInResult] = []
    for index, (candidate, result) in enumerate(
            zip(candidates, results, strict=True)):
        if result.symbol != candidate.symbol:
            return _reject_commit(
                f"第 {index} 项候选符号 {candidate.symbol!r} 与预览符号 "
                f"{result.symbol!r} 不一致，拒绝落盘"
                "（results 须来自 batch_migrate_in 的顺序对应返回）")
        candidate_target = _path_text(getattr(candidate, "target_file", ""))
        if (not candidate_target
                or norm_cache_key(candidate_target) != target_key):
            return _reject_commit(
                f"第 {index} 项候选目标 {candidate_target!r} 与提交目标 "
                f"{target_text!r} 不一致，拒绝落盘")
        if not result.success:
            failed.append(result)
            continue
        if not isinstance(result.target_code, str):
            return _reject_commit(
                f"第 {index} 项成功预览目标代码须为 str，"
                f"得到 {type(result.target_code).__name__}，拒绝落盘")
        if not result.target_code:
            return _reject_commit(
                f"第 {index} 项成功预览缺少目标代码，拒绝落盘")
        preview_source = _path_text(result.source_file)
        preview_target = _path_text(result.target_file)
        if (not preview_source
                or norm_cache_key(preview_source)
                != norm_cache_key(candidate.source_file)):
            return _reject_commit(
                f"第 {index} 项预览来源 {result.source_file!r} 与候选来源 "
                f"{candidate.source_file!r} 不一致，拒绝落盘")
        if (not preview_target
                or norm_cache_key(preview_target) != target_key):
            return _reject_commit(
                f"第 {index} 项预览目标 {result.target_file!r} 与提交目标 "
                f"{target_text!r} 不一致，拒绝落盘")
        if (not isinstance(result.source_code, str)
                or not isinstance(result.base_target_code, str)):
            return _reject_commit(
                f"第 {index} 项预览缺少源/目标基线文本，拒绝落盘")
        source_key = norm_cache_key(candidate.source_file)
        previous_source = source_baselines.setdefault(
            source_key, result.source_code)
        if previous_source != result.source_code:
            return _reject_commit(
                f"来源 {candidate.source_file!r} 的成功预览使用了不同源基线，"
                "不能组合为同一事务")
        if not baseline_seen:
            target_baseline = result.base_target_code
            baseline_seen = True
        elif target_baseline != result.base_target_code:
            return _reject_commit(
                "成功预览使用了不同目标基线，不能组合为同一事务")
    if failed:
        detail = "; ".join(f"{r.symbol}: {r.reason}" for r in failed)
        return _reject_commit(
            "迁入预览含失败项，为保证迁移原子性，拒绝部分落盘: " + detail)
    required_symbols = [result.symbol for result in results]
    final_segments = top_symbol_segments(results[-1].target_code,
                                         required_symbols)
    final_symbols = {name for _start, _end, name in final_segments}
    missing_symbols = sorted(set(required_symbols) - final_symbols)
    if missing_symbols:
        return _reject_commit(
            f"最终迁入预览缺少本事务符号 {missing_symbols}；"
            "results 须为 batch_migrate_in 生成的累积预览，"
            "不能组合相互独立的目标预览，拒绝落盘")
    return list(results), None
def _bucket_symbols_by_source(candidates: list,
                              results: list) -> dict[str, dict]:
    sym_by_src: dict[str, dict] = {}
    for cand, res in zip(candidates, results, strict=True):
        if not (res.success and res.target_code):
            continue
        bucket = sym_by_src.setdefault(
            norm_cache_key(cand.source_file),
            {"display": os.path.abspath(cand.source_file), "syms": [],
             "base_code": res.source_code})
        bucket["syms"].append(cand.symbol)
    return sym_by_src
def _same_file_error(sym_by_src: dict, target_key: str) -> dict | None:
    bucket = sym_by_src.get(target_key)
    if bucket is None:
        return None
    return {"status": "error", "data": {},
            "message": (f"迁入目标与迁出源为同一物理文件"
                        f"（{bucket['display']}），目标写入与"
                        "源删除写入互相覆盖会静默丢失迁入内容，"
                        "拒绝落盘，请人工裁决")}
def _shared_all_assignment_lines(source_code: str,
                                 symbols: Any) -> list[int]:
    wanted = set(_symbol_list(symbols))
    if not wanted:
        return []
    tree = parse_source_tree(
        source_code, '_shared_all_assignment_lines:parse_source_tree')
    if tree is None:
        return []
    lines: list[int] = []
    for node in iter_module_scope_nodes(tree, descend_classes=False):
        if not isinstance(node, ast.Assign) or len(node.targets) < 2:
            continue
        names = extract_all_names(node)
        if names is not None and wanted.intersection(names):
            lines.append(node.lineno)
    return lines
def _shared_all_assignment_error(source_code: str, symbols: Any,
                                 source_fp: str) -> dict | None:
    lines = _shared_all_assignment_lines(source_code, symbols)
    if not lines:
        return None
    return {
        "status": "error",
        "data": {"shared_all_assignment_lines": lines,
                 "source_file": source_fp},
        "message": (
            f"源文件 {source_fp} 第 {lines} 行通过多目标赋值共享 __all__ "
            "容器；清理待迁导出会同步改变其他绑定及保留代码行为，"
            "拒绝落盘。请先拆分共享赋值并明确各绑定的保留语义"),
    }
def _source_removal_writes(
        sym_by_src: dict) -> tuple[list, list, list, dict | None]:
    writes: list[tuple[str, str]] = []
    updated_sources: list[str] = []
    left_in_source: list[str] = []
    for bucket in sym_by_src.values():
        src_fp = bucket["display"]
        syms = bucket["syms"]
        code, _fingerprint = read_source_with_fingerprint(src_fp)
        if code is None:
            _log.warning("读取源文件失败: %s", src_fp)
            return (writes, updated_sources, left_in_source,
                    {"status": "error", "data": {},
                     "message": f"读取源文件失败: {src_fp}"})
        if code != bucket["base_code"]:
            _log.warning("源文件在迁入预览后已变化，拒绝过期提交: %s", src_fp)
            return (writes, updated_sources, left_in_source,
                    {"status": "error",
                     "data": {"stale_source_file": src_fp},
                     "message": (f"源文件 {src_fp} 在预览后已修改，"
                                 "继续提交会删除未纳入预览的新实现；"
                                 "请重新生成预览")})
        shared_all_error = _shared_all_assignment_error(code, syms, src_fp)
        if shared_all_error is not None:
            return (writes, updated_sources, left_in_source, shared_all_error)
        new_code, removed = remove_symbols_from_source(code, syms)
        if removed:
            ref_blocks = _removal_reference_blocks(code, removed)
            if ref_blocks:
                return (writes, updated_sources, left_in_source,
                        {"status": "error", "data": {},
                         "message": ("源文件删除符号后仍被保留代码引用，"
                                     "拒绝落盘: " + "; ".join(ref_blocks))})
            retained_bindings = _retained_symbol_bindings(new_code, removed)
            if retained_bindings:
                return (writes, updated_sources, left_in_source,
                        {"status": "error",
                         "data": {"retained_source_bindings": retained_bindings,
                                  "source_file": src_fp},
                         "message": (
                             f"源文件 {src_fp} 删除定义后仍绑定同名符号 "
                             f"{retained_bindings}（import/赋值/条件定义）；"
                             "旧导入会静默拿到另一份实现而非 ImportError，"
                             "请先处理该绑定或调整迁移边界")})
            export_literals = _all_export_literals(new_code)
            if export_literals is None:
                return (writes, updated_sources, left_in_source,
                        {"status": "error",
                         "data": {"unverifiable_source_exports": removed,
                                  "source_file": src_fp},
                         "message": (
                             f"源文件 {src_fp} 的 __all__ 含动态或不可解析形态，"
                             "无法证明删除符号后不会残留失效导出，拒绝落盘；"
                             "请先改为静态字面量容器或字面量追加")})
            retained_exports = sorted(export_literals & set(removed))
            if retained_exports:
                return (writes, updated_sources, left_in_source,
                        {"status": "error",
                         "data": {"retained_source_exports": retained_exports,
                                  "source_file": src_fp},
                         "message": (
                             f"源文件 {src_fp} 的 __all__ 仍含被迁符号 "
                             f"{retained_exports}（非字面量容器无法自动清理）；"
                             "from ... import * 会在导入期抛 AttributeError，"
                             "请先把 __all__ 改为可静态清理的字面量容器")})
            writes.append((src_fp, strip_stale_coding_declaration(new_code)))
            updated_sources.append(src_fp)
        left_in_source.extend(s for s in syms if s not in removed)
    return writes, updated_sources, left_in_source, None
def _target_freshness_error(target_text: str,
                            ok_results: list) -> dict | None:
    baseline = ok_results[0].base_target_code
    current, _fingerprint = read_source_with_fingerprint(target_text)
    if current is None:
        if not baseline and not os.path.exists(target_text):
            return None
        return {"status": "error",
                "data": {"stale_target_file": target_text},
                "message": f"目标文件 {target_text} 当前不可读，拒绝落盘"}
    if current != baseline:
        _log.warning("目标文件在迁入预览后已变化，拒绝过期提交: %s", target_text)
        return {"status": "error",
                "data": {"stale_target_file": target_text},
                "message": (f"目标文件 {target_text} 在预览后已修改，"
                            "继续提交会覆盖并发变更；请重新生成预览")}
    return None
def _migration_root(skill_dir: str, target_text: str,
                    sym_by_src: dict) -> str:
    explicit = _path_text(skill_dir)
    if explicit:
        root = os.path.abspath(explicit)
        real_root = os.path.realpath(root)
        root_key = norm_cache_key(real_root)
        paths = [target_text] + [
            bucket["display"] for bucket in sym_by_src.values()]
        for path in paths:
            real_path = os.path.realpath(os.path.abspath(path))
            try:
                common = os.path.commonpath([real_root, real_path])
            except ValueError:
                common = ""
            if not common or norm_cache_key(common) != root_key:
                _log.warning(
                    "迁移源/目标越过显式消费方扫描根，拒绝遗漏外部消费者: "
                    "root=%s path=%s", root, path)
                return ""
        return root
    target_dir = os.path.dirname(os.path.abspath(target_text))
    target_key = norm_cache_key(target_dir)
    for bucket in sym_by_src.values():
        source_dir = os.path.dirname(os.path.abspath(bucket["display"]))
        if norm_cache_key(source_dir) != target_key:
            _log.warning(
                "未提供 skill_dir 且源/目标跨目录，拒绝推导过宽扫描根: %s",
                source_dir)
            return ""
    package_root = target_dir
    for _ in _package_chain(target_dir):
        package_root = os.path.dirname(package_root)
    return package_root
def _migration_module_name(filepath: str) -> str:
    path = os.path.abspath(filepath)
    parts = list(_package_chain(os.path.dirname(path)))
    stem = os.path.splitext(os.path.basename(path))[0]
    if stem != "__init__":
        parts.append(stem)
    return ".".join(parts)
def _root_module_name(filepath: str, root: str,
                      *, include_root: bool) -> str:
    root_path = os.path.realpath(os.path.abspath(root))
    file_path = os.path.realpath(os.path.abspath(filepath))
    try:
        relative = os.path.relpath(file_path, root_path)
    except ValueError:
        return ""
    if relative == ".." or relative.startswith(".." + os.sep):
        return ""
    parts = relative.split(os.sep)
    parts[-1] = os.path.splitext(parts[-1])[0]
    if parts[-1] == "__init__":
        parts.pop()
    if include_root:
        parts.insert(0, os.path.basename(root_path))
    return ".".join(part for part in parts if part)
def _identity_pairs(source_fp: str, target_text: str,
                    root: str) -> list[tuple[str, str]]:
    pairs = [(_migration_module_name(source_fp),
              _migration_module_name(target_text))]
    pairs.extend(
        (_root_module_name(source_fp, root, include_root=include_root),
         _root_module_name(target_text, root, include_root=include_root))
        for include_root in (False, True)
    )
    return [
        (source, target) for source, target in dict.fromkeys(pairs)
        if source and target and source != target
    ]
def _move_specs(
    sym_by_src: dict, target_text: str, root: str,
) -> tuple[dict[str, dict], dict | None]:
    moves: dict[str, dict] = {}
    for source_key, bucket in sym_by_src.items():
        pairs = _identity_pairs(bucket["display"], target_text, root)
        if not pairs:
            return {}, {"status": "error", "data": {},
                        "message": (f"源/目标模块身份无法安全区分: "
                                    f"{bucket['display']} -> {target_text}")}
        for source_module, target_module in pairs:
            existing = moves.get(source_module)
            if existing is not None and existing["source_key"] != source_key:
                return {}, {"status": "error", "data": {},
                            "message": f"多个来源映射到同一模块身份: {source_module}"}
            moves[source_module] = {
                "source_key": source_key,
                "symbols": frozenset(bucket["syms"]),
                "target_module": target_module,
            }
    return moves, None
def _format_import_aliases(aliases: list[ast.alias]) -> str:
    return ", ".join(
        alias.name + (f" as {alias.asname}" if alias.asname else "")
        for alias in aliases)
def _format_import_statement(module: str, level: int,
                             aliases: list[ast.alias]) -> str:
    reference = "." * level + module
    return f"from {reference} import {_format_import_aliases(aliases)}"
def _target_rebound_imported_names(
    tree: ast.Module, imported_names: set[str],
    source_imports: set[ast.ImportFrom],
) -> set[str]:
    rebound: set[str] = set()
    for node in iter_module_scope_nodes(tree, descend_classes=False):
        if (isinstance(node, ast.Name)
                and isinstance(node.ctx, (ast.Store, ast.Del))
                and node.id in imported_names):
            rebound.add(node.id)
        elif (isinstance(node, ast.ExceptHandler)
              and node.name in imported_names):
            rebound.add(node.name)
    for node in iter_module_level_stmts(tree):
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef))
                and node.name in imported_names):
            rebound.add(node.name)
        elif (isinstance(node, (ast.Import, ast.ImportFrom))
              and node not in source_imports):
            rebound |= import_stmt_binds(node) & imported_names
    return rebound
def _import_time_transitive_reads(
    target_code: str, tree: ast.Module,
) -> set[str]:
    reads = {
        node.id for node in iter_import_time_nodes(tree)
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
    }
    definitions = {
        node.name: node for node in iter_module_level_stmts(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef))
    }
    pending = list(reads & definitions.keys())
    visited: set[str] = set()
    while pending:
        name = pending.pop()
        if name in visited:
            continue
        visited.add(name)
        usage = _symbol_global_usage(target_code, name)
        refs = (usage[0] if usage is not None
                else _retained_source_refs(definitions[name]))
        new_refs = refs - reads
        reads.update(new_refs)
        pending.extend(new_refs & definitions.keys())
    return reads
def _target_import_time_error(target_code: str, target_text: str,
                              moves: dict[str, dict]) -> dict | None:
    tree = parse_source_tree(
        target_code, '_target_import_time_error:parse_source_tree')
    if tree is None:
        return {"status": "error", "data": {},
                "message": f"目标文件无法解析，不能校验导入期依赖: {target_text}"}
    imported_names: set[str] = set()
    source_imports: set[ast.ImportFrom] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ImportFrom):
            continue
        move = moves.get(_resolve_relative_target(target_text, node))
        if move is None:
            continue
        moved_aliases = [alias for alias in node.names
                         if alias.name in move["symbols"]]
        if moved_aliases:
            source_imports.add(node)
        imported_names.update(
            alias.asname or alias.name for alias in moved_aliases)
    if not imported_names:
        return None
    rebound = sorted(_target_rebound_imported_names(
        tree, imported_names, source_imports))
    if rebound:
        return {"status": "error",
                "data": {"target_rebound_imports": rebound},
                "message": ("目标文件在源导入之外重新绑定待迁名字 "
                            f"{rebound}；迁入定义或别名赋值位于目标尾部，"
                            "会覆盖后续绑定并改变模块状态。请先调整绑定/"
                            "初始化顺序后重试")}
    import_time_reads = _import_time_transitive_reads(target_code, tree)
    early = sorted(imported_names & import_time_reads)
    if early:
        return {"status": "error",
                "data": {"target_import_time_dependencies": early},
                "message": ("目标文件在导入期读取待迁符号 "
                            f"{early}；迁入定义位于目标尾部，移除原导入后会在"
                            "定义前求值。请先调整目标初始化顺序后重试")}
    return None
def _dotted_expression(node: ast.AST) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        owner = _dotted_expression(node.value)
        return f"{owner}.{node.attr}" if owner else ""
    return ""
def _dynamic_import_module(
    node: ast.AST, importlib_aliases: set[str],
    import_module_aliases: set[str], builtins_aliases: set[str],
    dunder_import_aliases: set[str],
) -> str | None:
    if not isinstance(node, ast.Call):
        return None
    func = node.func
    direct = (isinstance(func, ast.Name)
              and (func.id in dunder_import_aliases
                   or func.id in import_module_aliases))
    via_importlib = (
        isinstance(func, ast.Attribute) and func.attr == "import_module"
        and isinstance(func.value, ast.Name)
        and func.value.id in importlib_aliases)
    via_builtins = (
        isinstance(func, ast.Attribute) and func.attr == "__import__"
        and isinstance(func.value, ast.Name)
        and func.value.id in builtins_aliases)
    if not (direct or via_importlib or via_builtins):
        return None
    name_node = node.args[0] if node.args else next(
        (keyword.value for keyword in node.keywords
         if keyword.arg == "name"), None)
    if not (isinstance(name_node, ast.Constant)
            and isinstance(name_node.value, str)):
        return ""
    return name_node.value
def _owner_matches_move(owner: str, source_module: str, move: dict,
                        module_aliases: dict[str, list[dict]]) -> bool:
    return owner == source_module or any(
        owner == alias and any(alias_move is move for alias_move in bindings)
        for alias, bindings in module_aliases.items())
def _dynamic_namespace_accessor(
    node: ast.AST, builtins_aliases: set[str],
    access_aliases: dict[str, str],
) -> str:
    if not isinstance(node, ast.Call):
        return ""
    func = node.func
    if isinstance(func, ast.Name):
        return access_aliases.get(func.id, "")
    if (isinstance(func, ast.Attribute)
            and func.attr in {"getattr", "hasattr", "vars"}
            and isinstance(func.value, ast.Name)
            and func.value.id in builtins_aliases):
        return func.attr
    return ""
def _module_attribute_blocks(
    tree: ast.AST, consumer_fp: str, moves: dict[str, dict],
) -> list[str]:
    module_aliases: dict[str, list[dict]] = {}
    importlib_aliases = {"importlib"}
    import_module_aliases: set[str] = set()
    builtins_aliases = {"builtins"}
    dunder_import_aliases = {"__import__"}
    access_aliases = {
        "getattr": "getattr", "hasattr": "hasattr", "vars": "vars"}
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name == "importlib":
                    importlib_aliases.add(alias.asname or alias.name)
                elif alias.name == "builtins":
                    builtins_aliases.add(alias.asname or alias.name)
                move = moves.get(alias.name)
                if move is not None:
                    module_aliases.setdefault(
                        alias.asname or alias.name, []).append(move)
            continue
        if not isinstance(node, ast.ImportFrom):
            continue
        if node.level == 0 and node.module == "importlib":
            import_module_aliases.update(
                alias.asname or alias.name for alias in node.names
                if alias.name == "import_module")
        elif node.level == 0 and node.module == "builtins":
            dunder_import_aliases.update(
                alias.asname or alias.name for alias in node.names
                if alias.name == "__import__")
            for alias in node.names:
                if alias.name in {"getattr", "hasattr", "vars"}:
                    access_aliases[alias.asname or alias.name] = alias.name
        resolved = _resolve_relative_target(consumer_fp, node)
        for alias in node.names:
            qualified = f"{resolved}.{alias.name}" if resolved else alias.name
            move = moves.get(qualified)
            if move is not None:
                module_aliases.setdefault(
                    alias.asname or alias.name, []).append(move)
    blocks: set[str] = set()
    for node in walk_nodes(tree):
        dynamic_module = _dynamic_import_module(
            node, importlib_aliases, import_module_aliases,
            builtins_aliases, dunder_import_aliases)
        if dynamic_module is not None and not dynamic_module:
            blocks.add(
                f"{consumer_fp} 第 {node.lineno} 行动态导入使用非字面量或空模块名；"
                "无法证明其不会消费待迁符号，请先改为显式 import 后再迁移")
        elif (dynamic_module is not None
              and dynamic_module.startswith(".")):
            blocks.add(
                f"{consumer_fp} 第 {node.lineno} 行使用相对动态导入 "
                f"{dynamic_module!r}；无法静态确认其完整模块身份及待迁符号"
                "消费面，请先改为显式 import 后再迁移")
        elif dynamic_module in moves:
            blocks.add(
                f"{consumer_fp} 第 {node.lineno} 行动态导入源模块 "
                f"{dynamic_module!r}；无法静态证明待迁符号的消费面，"
                "请先改为显式 import 后再迁移")
        if isinstance(node, ast.Attribute):
            owner = _dotted_expression(node.value)
            for source_module, move in moves.items():
                owner_hit = _owner_matches_move(
                    owner, source_module, move, module_aliases)
                if node.attr in {"__dict__", "__getattribute__"} and owner_hit:
                    blocks.add(
                        f"{consumer_fp} 第 {node.lineno} 行通过 {node.attr} 动态访问"
                        "源模块命名空间；无法证明待迁符号的消费面，请先改为"
                        "显式 from 导入后再迁移")
                for symbol in move["symbols"]:
                    if node.attr == symbol and owner_hit:
                        blocks.add(
                            f"{consumer_fp} 第 {node.lineno} 行通过模块属性消费 "
                            f"{symbol!r}；为避免影响同模块未迁符号，请先改为"
                            "显式 from 导入后再迁移")
        accessor = _dynamic_namespace_accessor(
            node, builtins_aliases, access_aliases)
        if accessor == "vars" and len(node.args) == 1:
            owner = _dotted_expression(node.args[0])
            for source_module, move in moves.items():
                if _owner_matches_move(
                        owner, source_module, move, module_aliases):
                    blocks.add(
                        f"{consumer_fp} 第 {node.lineno} 行通过 vars() 动态访问"
                        "源模块命名空间；无法证明待迁符号的消费面，请先改为"
                        "显式 from 导入后再迁移")
        elif accessor and len(node.args) >= 2:
            owner = _dotted_expression(node.args[0])
            name_node = node.args[1]
            literal_symbol = (name_node.value
                              if isinstance(name_node, ast.Constant)
                              and isinstance(name_node.value, str) else None)
            for source_module, move in moves.items():
                if not _owner_matches_move(
                        owner, source_module, move, module_aliases):
                    continue
                if literal_symbol is None:
                    blocks.add(
                        f"{consumer_fp} 第 {node.lineno} 行通过动态 {accessor} "
                        "以非字面量属性名访问源模块；无法证明待迁符号不会被"
                        "读取，请先改为显式 from 导入后再迁移")
                elif literal_symbol in move["symbols"]:
                    blocks.add(
                        f"{consumer_fp} 第 {node.lineno} 行通过 {accessor} 动态消费 "
                        f"{literal_symbol!r}；请先改为显式 from 导入后再迁移")
    return sorted(blocks)
def _rewrite_consumer_imports(
    code: str, consumer_fp: str, moves: dict[str, dict], target_key: str,
) -> tuple[str, list[tuple[str, str]], list[str]]:
    tree = parse_source_tree(code, '_rewrite_consumer_imports:parse_source_tree')
    if tree is None:
        message = (f"{consumer_fp} 无法解析，无法证明迁移后的导入关系；"
                   "为避免留下指向旧模块的导入，拒绝落盘")
        return code, [], [message]
    attribute_errors = _module_attribute_blocks(tree, consumer_fp, moves)
    if attribute_errors:
        return code, [], attribute_errors
    lines = ast_split_lines(code)
    edits: list[tuple[int, int, str]] = []
    target_aliases: list[tuple[str, str]] = []
    errors: list[str] = []
    is_target = norm_cache_key(consumer_fp) == target_key
    module_scope_stmts = set(iter_module_level_stmts(tree))
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ImportFrom):
            continue
        move = moves.get(_resolve_relative_target(consumer_fp, node))
        if move is None:
            continue
        package_parts = _package_chain(
            os.path.dirname(os.path.abspath(consumer_fp)))
        if node.level > 0 and (
                not package_parts
                or node.level - 1 >= len(package_parts)):
            errors.append(
                f"{consumer_fp} 第 {node.lineno} 行相对导入超出可验证的"
                f"包链（level={node.level}，包链={len(package_parts)}），"
                "请先改为显式绝对导入后再迁移")
            continue
        if any(alias.name == "*" for alias in node.names):
            errors.append(
                f"{consumer_fp} 第 {node.lineno} 行星号导入无法逐项证明"
                "迁移后的消费关系，请先改为显式导入")
            continue
        moved = [alias for alias in node.names
                 if alias.name in move["symbols"]]
        if not moved:
            continue
        if is_target and node not in module_scope_stmts:
            errors.append(
                f"{consumer_fp} 第 {node.lineno} 行存在函数/类局部自导入；"
                "删除导入并把待迁定义追加到模块尾部会丢失局部绑定，"
                "请先改为模块级导入或显式局部赋值后再迁移")
            continue
        kept = [alias for alias in node.names if alias not in moved]
        moved_bindings = {alias.asname or alias.name for alias in moved}
        kept_bindings = {alias.asname or alias.name for alias in kept}
        binding_conflicts = sorted(moved_bindings & kept_bindings)
        if binding_conflicts:
            errors.append(
                f"{consumer_fp} 第 {node.lineno} 行的本地别名 "
                f"{binding_conflicts} 同时绑定保留符号与待迁符号；"
                "拆分导入会改变最后绑定及求值顺序，请先去重或重命名后再迁移")
            continue
        replacements: list[str] = []
        if kept:
            replacements.append(_format_import_statement(
                node.module or "", node.level, kept))
        if is_target:
            target_aliases.extend(
                (alias.asname, alias.name) for alias in moved
                if alias.asname and alias.asname != alias.name)
        else:
            replacements.append(_format_import_statement(
                move["target_module"], 0, moved))
        if not replacements:
            replacements.append("pass")
        start = _ast_absolute_char_position(
            code, lines, node.lineno, node.col_offset)
        end = _ast_absolute_char_position(
            code, lines, node.end_lineno, node.end_col_offset)
        edits.append((start, end, "; ".join(replacements)))
    return _apply_source_edits(code, edits), target_aliases, errors
def _append_target_aliases(code: str,
                           aliases: list[tuple[str, str]]) -> str:
    ordered = list(dict.fromkeys(aliases))
    if not ordered:
        return code
    eol = _source_eol(code)
    assignments = eol.join(f"{alias} = {symbol}" for alias, symbol in ordered)
    return code.rstrip("\r\n") + eol + eol + assignments + eol
def _consumer_import_updates(
    writes_by_path: dict[str, tuple[str, str]], target_text: str,
    target_baseline: str, sym_by_src: dict, skill_dir: str,
) -> tuple[list[str], dict | None]:
    root = _migration_root(skill_dir, target_text, sym_by_src)
    if not root:
        return [], {"status": "error", "data": {},
                    "message": "无法确定消费方扫描根，请显式提供 skill_dir"}
    moves, move_error = _move_specs(sym_by_src, target_text, root)
    if move_error is not None:
        return [], move_error
    target_key = norm_cache_key(target_text)
    early_error = _target_import_time_error(
        target_baseline, target_text, moves)
    if early_error is not None:
        return [], early_error
    try:
        scan_files = set(collect_migration_py_files(
            root, include_tests=True))
    except (OSError, ValueError) as exc:
        return [], {"status": "error", "data": {},
                    "message": f"消费方扫描失败: {exc}"}
    scan_files.update(display for display, _code in writes_by_path.values())
    updated_consumers: list[str] = []
    target_aliases: list[tuple[str, str]] = []
    unreadable: list[str] = []
    for consumer_fp in sorted(scan_files, key=norm_cache_key):
        consumer_key = norm_cache_key(consumer_fp)
        existing = writes_by_path.get(consumer_key)
        if existing is not None:
            display, code = existing
        else:
            display = consumer_fp
            code, _fingerprint = read_source_with_fingerprint(consumer_fp)
            if code is None:
                unreadable.append(display)
                continue
        new_code, aliases, errors = _rewrite_consumer_imports(
            code, display, moves, target_key)
        if errors:
            return [], {"status": "error",
                        "data": {"consumer_blocks": errors},
                        "message": "；".join(errors)}
        if consumer_key == target_key:
            target_aliases.extend(aliases)
        if new_code != code:
            writes_by_path[consumer_key] = (display, new_code)
            if existing is None:
                updated_consumers.append(display)
    if unreadable:
        return [], {"status": "error",
                    "data": {"unreadable_consumers": sorted(unreadable)},
                    "message": ("下列消费者无法读取，无法证明迁移后导入关系；"
                                "拒绝落盘: " + "; ".join(sorted(unreadable)))}
    if target_aliases:
        migrated_symbols = {
            symbol for bucket in sym_by_src.values() for symbol in bucket["syms"]}
        alias_conflicts = sorted(
            {alias for alias, _symbol in target_aliases} & migrated_symbols)
        if alias_conflicts:
            return [], {
                "status": "error",
                "data": {"target_alias_conflicts": alias_conflicts},
                "message": (
                    f"目标文件导入别名 {alias_conflicts} 与本事务迁入符号同名；"
                    "尾部别名回填会覆盖迁入定义并改变调用结果，拒绝落盘；"
                    "请先重命名冲突别名或调整迁移边界"),
            }
        display, code = writes_by_path[target_key]
        writes_by_path[target_key] = (
            display, _append_target_aliases(code, target_aliases))
    return sorted(updated_consumers), None
def _annotate_commit_outcome(
    outcome: dict, ok_results: list, updated_sources: list,
    updated_consumers: list,
) -> dict:
    outcome["data"]["symbols_migrated"] = sorted(
        {r.symbol for r in ok_results})
    outcome["data"]["source_files_updated"] = sorted(updated_sources)
    outcome["data"]["consumer_files_updated"] = sorted(updated_consumers)
    invalidate_consumption_cache()
    invalidate_zcc_cache()
    return outcome
def commit_migrate_in(candidates: list, results: list,
                      target_filepath: str, skill_dir: str = "") -> dict:
    ok_results, input_err = _validate_commit_inputs(
        candidates, results, target_filepath)
    if input_err is not None:
        return input_err
    target_text = _path_text(target_filepath)
    target_baseline = ok_results[0].base_target_code
    final_target = strip_stale_coding_declaration(
        ok_results[-1].target_code)
    sym_by_src = _bucket_symbols_by_source(candidates, results)
    target_key = norm_cache_key(target_text)
    same_file_err = _same_file_error(sym_by_src, target_key)
    if same_file_err is not None:
        return same_file_err
    stale_target = _target_freshness_error(target_text, ok_results)
    if stale_target is not None:
        return stale_target
    src_writes, updated_sources, left_in_source, read_err = (
        _source_removal_writes(sym_by_src))
    if read_err is not None:
        return read_err
    if left_in_source:
        leftovers = sorted(set(left_in_source))
        return {
            "status": "error",
            "data": {"symbols_left_in_source": leftovers},
            "message": ("源文件未删除全部待迁符号，拒绝落盘: "
                        f"{leftovers}；请重新生成预览，避免目标/源重复定义"),
        }
    writes_by_path: dict[str, tuple[str, str]] = {
        target_key: (os.path.abspath(target_text), final_target),
    }
    for source_fp, source_code in src_writes:
        writes_by_path[norm_cache_key(source_fp)] = (source_fp, source_code)
    root = _migration_root(skill_dir, target_text, sym_by_src)
    if not root:
        return {"status": "error", "data": {},
                "message": "无法确定消费方扫描根，请显式提供 skill_dir"}
    updated_consumers, consumer_err = _consumer_import_updates(
        writes_by_path, target_text, target_baseline, sym_by_src, root)
    if consumer_err is not None:
        return consumer_err
    writes = list(writes_by_path.values())
    outcome = commit_writes(writes, root)
    if outcome["status"] == "ok":
        _annotate_commit_outcome(
            outcome, ok_results, updated_sources, updated_consumers)
        if updated_consumers:
            _log.info("[Migration] 已同步改写 %d 个消费者导入",
                      len(updated_consumers))
    return outcome
def _compress_seam_kept_indices(lines: list[str],
                                drop: set[int]) -> list[int]:
    if not drop:
        return list(range(len(lines)))
    intervals = _drop_intervals(drop)
    is_blank = [not ln.strip() for ln in lines]
    _merge_blank_joined_intervals(intervals, is_blank)
    seam_drop = _seam_extra_drops(lines, drop, is_blank, intervals)
    removed = drop | seam_drop
    return [i for i in range(len(lines)) if i not in removed]
def _seam_extra_drops(lines: list[str], drop: set[int],
                      is_blank: list[bool],
                      intervals: list[list[int]]) -> set[int]:
    _tail_is_artifact = bool(lines) and lines[-1] == ""
    _content_end = len(lines) - 1 if _tail_is_artifact else len(lines)
    seam_drop: set[int] = set()
    for a, b in intervals:
        lo = _seam_lead(drop, is_blank, a)
        hi = _seam_trail(lines, drop, is_blank, b, _tail_is_artifact)
        gap = [j for j in range(a, b) if j not in drop]
        seam = (a - lo) + len(gap) + (hi - b)
        allowance = _seam_blank_allowance(a, b, _content_end)
        if seam > allowance:
            seam_drop |= _seam_trim_plan(a, lo, b, gap, seam - allowance)
    return seam_drop
def _seam_blank_allowance(a: int, b: int, content_end: int) -> int:
    if a <= 0 or b >= content_end:
        return 0
    return 2
def _symbol_list(symbols: Any) -> list[str]:
    if isinstance(symbols, str):
        return [symbols]
    if isinstance(symbols, (list, tuple, set, frozenset)):
        return [s for s in symbols if isinstance(s, str)]
    _log.warning("symbols 形态非法(须为清单或单符号字符串), "
                 "按空清单处理: %s", type(symbols).__name__)
    return []
def top_symbol_segments(source_code: str, symbols: list[str]) -> list[tuple[int, int, str]]:
    wanted = set(_symbol_list(symbols))
    if not wanted:
        return []
    try:
        tree = ast.parse(source_code)
    except PARSE_DEGRADE_EXC as _e:
        log_swallowed(__name__, _e,
                      context=f'top_symbol_segments:{type(_e).__name__}')
        return []
    lines = ast_split_lines(source_code)
    out: list[tuple[int, int, str]] = []
    for node in tree.body:
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef)) and node.name in wanted):
            out.append((symbol_start_line(lines, node),
                        node.end_lineno, node.name))
    return out
def remove_symbols_from_source(source_code: str,
                               symbols: list[str]) -> tuple[str, list[str]]:
    segments = top_symbol_segments(source_code, symbols)
    if not segments:
        return source_code, []
    shared_lines = _shared_all_assignment_lines(source_code, symbols)
    if shared_lines:
        _log.warning(
            "源文件第 %s 行共享 __all__ 容器，无法在不改变其他绑定的情况下"
            "自动删除符号；返回未转换源码", shared_lines)
        return source_code, []
    lines = ast_split_lines(source_code)
    eols = _line_eols(source_code)
    drop = set()
    for start, end, _name in segments:
        drop.update(range(start - 1, end))
    kept = _compress_seam_kept_indices(lines, drop)
    eol = _source_eol(source_code)
    if len(eols) == len(lines):
        new_code = "".join(lines[i] + eols[i] for i in kept)
    else:
        new_code = eol.join(lines[i] for i in kept)
    new_code = _prune_all_names(
        new_code, [name for _s, _e, name in segments])
    if not new_code.endswith(("\r", "\n")):
        new_code += eol
    return new_code, [name for _s, _e, name in segments]
def _is_all_subscript(node: ast.AST) -> bool:
    return (isinstance(node, ast.Subscript)
            and isinstance(node.value, ast.Name)
            and node.value.id == "__all__")
def _has_all_removal_side_effects(tree: ast.Module) -> bool:
    for node in walk_nodes(tree):
        if _is_all_subscript(node):
            return True
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        if (isinstance(func, ast.Attribute)
                and isinstance(func.value, ast.Name)
                and func.value.id == "__all__"
                and func.attr in ("remove", "pop", "index")):
            return True
    return False
def _prune_all_names(code: str, removed: list[str]) -> str:
    removed_set = set(removed)
    if not removed_set:
        return code
    try:
        tree = ast.parse(code)
    except PARSE_DEGRADE_EXC as _e:
        log_swallowed(__name__, _e,
                      context=f'_prune_all_names:{type(_e).__name__}')
        return code
    if _has_all_removal_side_effects(tree):
        _log.warning("__all__ 含删除/位置型副作用，保留原导出容器并交由"
                     "提交校验阻断不安全的自动迁移")
        return code
    imported_names: set[str] = import_bound_names(tree.body)
    prunable = removed_set - imported_names
    if not prunable:
        return code
    edits = _all_prune_edits(
        tree, prunable, code, ast_split_lines(code))
    if not edits:
        return code
    return _apply_source_edits(code, edits)
def _all_prune_edits(tree: ast.Module, prunable: set[str],
                     code: str, lines: list[str]
                     ) -> list[tuple[int, int, str]]:
    edits: list[tuple[int, int, str]] = []
    for node in iter_module_scope_nodes(tree, descend_classes=False):
        edit = _prune_edit_for(node, prunable, code, lines)
        if edit is not None:
            edits.append(edit)
    return edits
def _ast_absolute_char_position(code: str, lines: list[str],
                                lineno: int, byte_col: int) -> int:
    row = lineno - 1
    char_col, _ = utf8_span_to_char_span(lines[row], byte_col, byte_col)
    return line_start_offset(code, lineno) + char_col
def _literal_container_text(value: ast.AST, names: list[str]) -> str:
    body = ", ".join(repr(name) for name in names)
    if isinstance(value, ast.Set):
        return "{" + body + "}" if names else "set()"
    if isinstance(value, ast.Tuple):
        return "(" + body + ("," if len(names) == 1 else "") + ")"
    return "[" + body + "]"
def _prune_edit_for(node: ast.AST, prunable: set[str], code: str,
                    lines: list[str]) -> tuple[int, int, str] | None:
    if not is_all_assignment(node):
        return None
    elems = extract_all_names(node)
    if elems is None:
        return None
    kept_names = [e for e in elems if e not in prunable]
    if len(kept_names) == len(elems):
        return None
    kept_literal = _literal_container_text(node.value, kept_names)
    start = _ast_absolute_char_position(
        code, lines, node.value.lineno, node.value.col_offset)
    end = _ast_absolute_char_position(
        code, lines, node.value.end_lineno, node.value.end_col_offset)
    return start, end, kept_literal
def _drop_intervals(drop: set[int]) -> list[list[int]]:
    intervals: list[list[int]] = []
    for i in sorted(drop):
        if intervals and intervals[-1][1] >= i:
            intervals[-1][1] = i + 1
        else:
            intervals.append([i, i + 1])
    return intervals
def _merge_blank_joined_intervals(intervals: list[list[int]],
                                  is_blank: list[bool]) -> None:
    merged = True
    while merged:
        merged = False
        for k in range(len(intervals) - 1):
            a, b = intervals[k]
            c, d = intervals[k + 1]
            if all(is_blank[j] for j in range(b, c)):
                intervals[k] = [a, d]
                del intervals[k + 1]
                merged = True
                break
def _seam_lead(drop: set[int], is_blank: list[bool], start: int) -> int:
    lo = start
    while lo - 1 >= 0 and lo - 1 not in drop and is_blank[lo - 1]:
        lo -= 1
    return lo
def _seam_trail(lines: list[str], drop: set[int], is_blank: list[bool],
                end: int, tail_is_artifact: bool) -> int:
    n = len(lines)
    hi = end
    while (hi < n and hi not in drop and is_blank[hi]
           and not (hi == n - 1 and tail_is_artifact)):
        hi += 1
    return hi
def _seam_trim_plan(a: int, lo: int, b: int,
                    gap: list[int], excess: int) -> set[int]:
    plan: set[int] = set()
    lead_cut = min(excess, a - lo)
    plan.update(range(a - lead_cut, a))
    excess -= lead_cut
    if excess > 0:
        gap_cut = min(excess, len(gap))
        plan.update(gap[:gap_cut])
        excess -= gap_cut
    if excess > 0:
        plan.update(range(b, b + excess))
    return plan
def _apply_source_edits(code: str, edits: list[tuple[int, int, str]]) -> str:
    for start, end, replacement in sorted(
            edits, key=lambda edit: edit[0], reverse=True):
        code = code[:start] + replacement + code[end:]
    return code
__all__ = [
    'commit_migrate_in',
    'remove_symbols_from_source',
    'top_symbol_segments',
]
_log.info(
    "refactor_migration_commit 迁移提交域已加载: %d 项导出",
    len(__all__))

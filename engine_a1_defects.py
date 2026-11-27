from __future__ import annotations

import ast
import logging
import os
import time
from collections import Counter, defaultdict
from typing import Any

from jwsgj.diag_shared_ast_nodes import TRY_NODE_TYPES, is_main_check
from jwsgj.diag_shared_source_core import (
    read_source_auto,
)
from jwsgj.diag_shared_source_scan import (
    comment_only_spans,
    is_suppressed,
    parse_suppressions,
    split_lines_lf,
)
from jwsgj.diag_types_vocab import Thresholds
from jwsgj.engine_a1_name_flow import (
    check_all_overwrite,
    check_undefined_names,
    exception_matches,
)
from jwsgj.engine_a1_structure import (
    SCOPE_BOUNDARY_NODES,
    DefectType,
    DomainCategory,
    FileBasicInfo,
    FileDefect,
    FileOverallProfile,
    behavioral_classes,
    check_duplicate_imports,
    check_import_override,
    check_line_limit,
    clear_complexity_memo,
    count_lines,
    extract_docstring,
    extract_key_entities,
    import_is_from,
    import_names,
    import_source,
    import_source_names,
    iter_scope_stmts,
    module_stem,
    parse_all,
    parse_structure,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    collect_scan_py_files,
    is_test_file_path,
)

logger = logging.getLogger(__name__)
__all__ = [
    'A1_METHOD_ID',
    'SCATTER_REPORT_MIN_FUNCS',
    'DefectEnhancer',
    'FileAnalyzerScanner',
    'collect_py_files',
    'detect_defects',
    'enhance_defects',
    'enhance_single_file_defects',
]
logger.info("engine_a1_defects A1 结构缺陷检测分发域已加载: %d 项导出", len(__all__))
_BIG_FILE_LINES = 1000
_MERGE_RESIDUE_LOOKAHEAD = 4
_BLOCK_CONTAINER_TYPES: frozenset = frozenset({
    ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef,
    ast.For, ast.AsyncFor, ast.While, ast.If, ast.With, ast.AsyncWith,
    *TRY_NODE_TYPES,
    ast.ExceptHandler, ast.match_case, ast.Match,
})
def _register_children(parent_map: dict[int, ast.AST], try_nodes: list,
                       stmts: list, parent: ast.AST) -> None:
    for st in stmts:
        parent_map[id(st)] = parent
        if isinstance(st, TRY_NODE_TYPES):
            try_nodes.append(st)
def _register_match_cases(parent_map: dict[int, ast.AST], try_nodes: list,
                           cases: list, parent: ast.AST) -> None:
    for mc in cases:
        parent_map[id(mc)] = parent
        mc_body = getattr(mc, "body", None)
        if isinstance(mc_body, list):
            _register_children(parent_map, try_nodes, mc_body, mc)
def _collect_block_edges(nodes) -> tuple[dict[int, ast.AST], list, list]:
    parent_map: dict[int, ast.AST] = {}
    try_nodes: list = []
    handler_nodes: list[ast.ExceptHandler] = []
    for parent in nodes:
        if type(parent) not in _BLOCK_CONTAINER_TYPES:
            continue
        if isinstance(parent, ast.ExceptHandler):
            handler_nodes.append(parent)
        for field in ("body", "orelse", "finalbody", "handlers"):
            stmts = getattr(parent, field, None)
            if isinstance(stmts, list):
                _register_children(parent_map, try_nodes, stmts, parent)
        cases = getattr(parent, "cases", None)
        if isinstance(cases, list):
            _register_match_cases(parent_map, try_nodes, cases, parent)
    return parent_map, try_nodes, handler_nodes
_BROAD_EXCEPT_SPECS = {
    "bare": ("P1", "裸 except: 捕获所有异常，可能掩盖错误",
             "指定具体的异常类型，如 except (ValueError, TypeError):", 0.9),
    "broad": ("P2", "except Exception/BaseException 捕获过于宽泛",
              "指定更具体的异常类型", 0.6),
}
_BROAD_EXCEPTION_NAMES = frozenset({"Exception", "BaseException"})
def _broad_except_kind(node: ast.ExceptHandler) -> str | None:
    if node.type is None:
        return "bare"
    return ("broad" if exception_matches(node.type, _BROAD_EXCEPTION_NAMES)
            else None)
def _broad_except_defect(node: ast.ExceptHandler, rel_path: str,
                         kind: str) -> FileDefect:
    severity, message, suggestion, confidence = _BROAD_EXCEPT_SPECS[kind]
    return FileDefect(
        defect_type=DefectType.BROAD_EXCEPT,
        severity=severity,
        filepath=rel_path,
        lineno=node.lineno,
        message=message,
        suggestion=suggestion,
        confidence=confidence,
        detail={"kind": "bare_except" if kind == "bare" else "broad_exception"},
    )
def _check_broad_except(rel_path: str, source: str,
                        nodes: list[ast.AST]) -> list[FileDefect]:
    defects: list[FileDefect] = []
    if is_test_file_path(rel_path):
        return defects
    suppressions = parse_suppressions(source) if source else {}
    parent_map, try_nodes, handler_nodes = _collect_block_edges(nodes)
    fallthrough_map: dict[int, bool] = {}
    for st in try_nodes:
        _fallthrough = _has_fallthrough(st, parent_map)
        for h in st.handlers:
            fallthrough_map[id(h)] = _fallthrough
    for node in handler_nodes:
        if is_suppressed(suppressions, node.lineno, DefectType.BROAD_EXCEPT):
            continue
        if _handler_is_defensive(node,
                                 fallthrough_map.get(id(node), False)):
            continue
        kind = _broad_except_kind(node)
        if kind is not None:
            defects.append(_broad_except_defect(node, rel_path, kind))
    return defects
def _clause_has_baseline_action(clause_stmts: list, strict: bool) -> bool:
    for _s in clause_stmts:
        if isinstance(_s, ast.Pass):
            continue
        if strict and isinstance(_s, TRY_NODE_TYPES):
            continue
        return True
    return False
def _sibling_tail_after(parent: ast.AST,
                        cur: ast.AST) -> tuple[str | None, bool]:
    for field in ("body", "orelse", "finalbody"):
        stmts = getattr(parent, field, None)
        if not isinstance(stmts, list):
            continue
        _idx = -1
        for _i, _s in enumerate(stmts):
            if _s is cur:
                _idx = _i
                break
        if _idx < 0:
            continue
        has_tail = any(not isinstance(_s, ast.Pass)
                       for _s in stmts[_idx + 1:])
        return field, has_tail
    return None, False
def _has_fallthrough(try_node: ast.Try,
                     parent_map: dict[int, ast.AST]) -> bool:
    if _clause_has_baseline_action(try_node.finalbody, strict=False):
        return True
    cur: ast.AST = try_node
    while True:
        p = parent_map.get(id(cur))
        if p is None:
            return False
        found_field, has_non_pass_tail = _sibling_tail_after(p, cur)
        if has_non_pass_tail:
            return True
        if isinstance(p, SCOPE_BOUNDARY_NODES):
            return False
        cur = p
        if isinstance(cur, TRY_NODE_TYPES):
            if (found_field != "finalbody"
                    and _clause_has_baseline_action(cur.finalbody, strict=True)):
                return True
            if (found_field == "body"
                    and _clause_has_baseline_action(cur.orelse, strict=True)):
                return True
def _has_observable_action(handler: ast.ExceptHandler) -> bool:
    _stack: list[ast.AST] = list(handler.body)
    while _stack:
        sub = _stack.pop()
        if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            continue
        if isinstance(sub, (ast.Raise, ast.Call, ast.Return, ast.Assert,
                            ast.Yield, ast.YieldFrom, ast.Await, ast.Delete)):
            return True
        if isinstance(sub, (ast.Assign, ast.AugAssign, ast.AnnAssign,
                            ast.NamedExpr)):
            return True
        _stack.extend(ast.iter_child_nodes(sub))
    return False
def _handler_is_defensive(handler: ast.ExceptHandler,
                           has_fallthrough: bool) -> bool:
    body = handler.body or []
    body_is_pure_passthrough = bool(body) and all(
        isinstance(st, (ast.Pass, ast.Continue, ast.Break)) for st in body)
    if _has_observable_action(handler):
        return True
    first_non_pass = next(
        (st for st in body if not isinstance(st, ast.Pass)), None)
    if isinstance(first_non_pass, ast.Continue):
        return True
    catches_base_exception = bool(
        handler.type is None
        or exception_matches(handler.type, ("BaseException",)))
    if catches_base_exception:
        return False
    return bool(body_is_pure_passthrough and has_fallthrough)
def _iter_public_top_symbols(tree: ast.Module):
    for node in iter_scope_stmts(tree):
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
                and not node.name.startswith("_")):
            yield node
def detect_defects(tree: ast.Module, rel_path: str,
                    source: str) -> list[FileDefect]:
    defects: list[FileDefect] = []
    nodes: list[ast.AST] = list(walk_nodes(tree))
    defects.extend(check_all_overwrite(tree, rel_path))
    defects.extend(check_undefined_names(tree, rel_path, nodes=nodes))
    defects.extend(check_import_override(tree, rel_path))
    defects.extend(_check_merge_residue(rel_path, source))
    defects.extend(check_line_limit(tree, rel_path, source, nodes=nodes))
    defects.extend(_check_missing_all(tree, rel_path, source))
    defects.extend(check_duplicate_imports(tree, rel_path, nodes=nodes))
    defects.extend(_check_broad_except(rel_path, source, nodes))
    defects.extend(_check_missing_docstring(tree, rel_path))
    if defects:
        logger.debug("A1 结构缺陷检出: file=%s defects=%d kinds=%s",
                     rel_path, len(defects),
                     sorted({d.defect_type for d in defects}))
    return defects
def _comment_rows(source: str) -> dict[int, int] | None:
    spans = comment_only_spans(source)
    if spans is None:
        return None
    return {row: items[0][0] for row, items in spans.items() if items}
def _is_comment_row(rows: dict[int, int] | None, index: int) -> bool:
    return rows is None or (index + 1) in rows
def _comment_block_end(lines: list[str], start: int,
                       rows: dict[int, int] | None) -> int:
    end = start
    while (end + 1 < len(lines) and lines[end + 1].strip().startswith("#")
           and _is_comment_row(rows, end + 1)):
        end += 1
    return end
def _has_code_in_window(lines: list[str], block_end: int,
                        rows: dict[int, int] | None) -> bool:
    window = lines[block_end + 1:block_end + 1 + _MERGE_RESIDUE_LOOKAHEAD]
    for _offset, line in enumerate(window):
        if not line.strip():
            continue
        _index = block_end + 1 + _offset
        if line.strip().startswith("#") and _is_comment_row(rows, _index):
            continue
        return True
    return False
_MERGE_RESIDUE_MARKERS = ("merged from", "merge from", "合并自", "合并来自")
def _is_merge_residue_comment(stripped: str) -> bool:
    if not stripped.startswith("#"):
        return False
    low = stripped.lower()
    return any(marker in low for marker in _MERGE_RESIDUE_MARKERS)
def _check_merge_residue(rel_path: str, source: str) -> list[FileDefect]:
    defects = []
    lines = split_lines_lf(source)
    rows: dict[int, int] | None = None
    _probed = False
    n = len(lines)
    i = 0
    while i < n:
        stripped = lines[i].strip()
        if not _is_merge_residue_comment(stripped):
            i += 1
            continue
        if not _probed:
            rows, _probed = _comment_rows(source), True
        if not _is_comment_row(rows, i):
            i += 1
            continue
        j = _comment_block_end(lines, i, rows)
        if not _has_code_in_window(lines, j, rows):
            defects.append(FileDefect(
                defect_type=DefectType.MERGE_RESIDUE,
                severity="P2",
                filepath=rel_path,
                lineno=i + 1,
                message=f"合并残留注释: '{stripped[:60]}' 后无对应代码",
                suggestion="删除该残留注释，或补充对应的实现代码",
                confidence=0.8,
                detail={"comment": stripped},
            ))
        i = j + 1
    return defects
def _check_missing_all(tree: ast.Module, rel_path: str,
                       source: str) -> list[FileDefect]:
    defects = []
    if is_test_file_path(rel_path):
        return defects
    has_all, _ = parse_all(tree)
    public_count = sum(1 for _ in _iter_public_top_symbols(tree))
    if not has_all and public_count > 0:
        total = len(split_lines_lf(source))
        _big = total > _BIG_FILE_LINES
        defects.append(FileDefect(
            defect_type=DefectType.MISSING_ALL,
            severity="P1" if _big else "P2",
            filepath=rel_path,
            lineno=1,
            message=(f"大文件 ({total} 行) 缺少 __all__ 定义" if _big
                     else f"文件有 {public_count} 个公开符号但缺少 __all__ 定义"),
            suggestion="添加 __all__ 列表，显式声明公开 API",
            confidence=0.7,
            detail={"public_count": public_count, "total_lines": total},
        ))
    return defects
def _docstring_defect(rel_path: str, lineno: int, message: str,
                      suggestion: str, detail: dict) -> FileDefect:
    return FileDefect(
        defect_type=DefectType.MISSING_DOCSTRING,
        severity="P2",
        filepath=rel_path,
        lineno=lineno,
        message=message,
        suggestion=suggestion,
        confidence=0.5,
        detail=detail,
    )
def _check_missing_docstring(tree: ast.Module, rel_path: str) -> list[FileDefect]:
    defects = []
    if is_test_file_path(rel_path):
        return defects
    if not extract_docstring(tree):
        defects.append(_docstring_defect(
            rel_path, 1, "模块缺少文档字符串",
            "在文件顶部添加模块级别的文档字符串", {"scope": "module"}))
    for node in _iter_public_top_symbols(tree):
        if extract_docstring(node):
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            defects.append(_docstring_defect(
                rel_path, node.lineno,
                f"公开函数 '{node.name}' 缺少文档字符串",
                "为函数添加文档字符串说明其功能和参数",
                {"scope": "function", "name": node.name}))
        else:
            defects.append(_docstring_defect(
                rel_path, node.lineno,
                f"公开类 '{node.name}' 缺少文档字符串",
                "为类添加文档字符串",
                {"scope": "class", "name": node.name}))
    return defects
def _dominant_naming_cluster(functions) -> float:
    if not functions:
        return 0.0
    counts: dict[str, int] = {}
    for f in functions:
        token = f.name.lstrip("_").split("_", 1)[0]
        if not token:
            token = f.name
        counts[token] = counts.get(token, 0) + 1
    return max(counts.values()) / len(functions)
SCATTER_REPORT_MIN_FUNCS = 60
_BEHAVIORAL_CLASS_ALERT_LIMIT = 15
_BIG_FUNC_LINES = Thresholds.FUNC_LINES_BLOCK
_AVG_FUNC_LEN_ALERT = Thresholds.FUNC_LINES_RECOMMEND
_BIG_FUNC_RATIO_ALERT = 0.2
_DOMINANT_CLUSTER_RATIO = 0.6
_OVER_LIMIT_SUGGESTION = (
    "治理候选：简化逻辑/消除重复/收敛依赖/迁移代码/"
    "提取同模块私有实现，不新增文件边界"
)
_OVER_LIMIT_SUPPRESSION_RULES: tuple[str, ...] = (
    DefectType.OVER_LIMIT, "A1-over_limit")
def _over_limit_defect(profile: FileOverallProfile, message: str,
                       detail: dict) -> FileDefect:
    return FileDefect(
        defect_type=DefectType.OVER_LIMIT,
        severity="P2",
        filepath=profile.filepath,
        lineno=1,
        message=message,
        suggestion=_OVER_LIMIT_SUGGESTION,
        confidence=0.6,
        detail=detail,
    )
def _func_len_metrics(functions) -> tuple[float, float]:
    if not functions:
        return 0.0, 0.0
    lens = [max(f.end_lineno - f.lineno + 1, 1) for f in functions]
    avg_len = sum(lens) / len(lens)
    big_ratio = sum(1 for ln in lens if ln > _BIG_FUNC_LINES) / len(lens)
    return avg_len, big_ratio
def _over_limit_suppressed(filepath) -> bool:
    path = str(filepath or "")
    if not path:
        return False
    try:
        source = read_source_auto(path)
    except OSError as _e:
        logger.debug("over_limit 抑制注解读取失败，按未抑制处理: %s (%s)",
                     path, _e)
        return False
    suppressions = parse_suppressions(source)
    if not suppressions:
        return False
    return any(is_suppressed(suppressions, line, rule)
               for line in (1, 2)
               for rule in _OVER_LIMIT_SUPPRESSION_RULES)
def _responsibility_scatter_suspected(basic: FileBasicInfo) -> bool:
    if basic.function_count <= SCATTER_REPORT_MIN_FUNCS:
        return False
    if _dominant_naming_cluster(basic.functions) >= _DOMINANT_CLUSTER_RATIO:
        return False
    avg_len, big_ratio = _func_len_metrics(basic.functions)
    return avg_len > _AVG_FUNC_LEN_ALERT or big_ratio > _BIG_FUNC_RATIO_ALERT
def _suppress_probe_path(basic: FileBasicInfo,
                         profile: FileOverallProfile) -> str:
    for candidate in (getattr(basic, "abspath", ""), profile.filepath):
        if isinstance(candidate, str) and os.path.isabs(candidate):
            return candidate
    return ""
def enhance_single_file_defects(profile: FileOverallProfile) -> list[FileDefect]:
    basic = profile.basic_info
    if (not basic
            or is_test_file_path(str(profile.filepath or ""))):
        return []
    _scatter_candidate = basic.function_count > SCATTER_REPORT_MIN_FUNCS
    behavioral_count = len(behavioral_classes(basic.classes))
    if not _scatter_candidate and behavioral_count <= _BEHAVIORAL_CLASS_ALERT_LIMIT:
        return []
    enhanced: list[FileDefect] = []
    _existing = {(d.defect_type, d.message) for d in profile.defects}
    _suppress_probe = _suppress_probe_path(basic, profile)
    _over_limit_off = (bool(_suppress_probe)
                       and _over_limit_suppressed(_suppress_probe))
    if not _over_limit_off and _responsibility_scatter_suspected(basic):
        _avg_len, _big_ratio = _func_len_metrics(basic.functions)
        enhanced.append(_over_limit_defect(
            profile,
            f"文件包含 {basic.function_count} 个函数，职责可能过于分散",
            {"function_count": basic.function_count,
             "avg_func_len": round(_avg_len, 1),
             "big_func_ratio": round(_big_ratio, 3)},
        ))
    if not _over_limit_off and behavioral_count > _BEHAVIORAL_CLASS_ALERT_LIMIT:
        enhanced.append(_over_limit_defect(
            profile,
            f"文件包含 {behavioral_count} 个行为类，职责可能过于分散",
            {"class_count": basic.class_count,
             "behavioral_class_count": behavioral_count},
        ))
    return [d for d in enhanced
            if (d.defect_type, d.message) not in _existing]
def _normalize_scan_root(skill_dir) -> str:
    raw = os.fspath(skill_dir) if isinstance(skill_dir, (str, os.PathLike)) else ""
    if not str(raw).strip():
        raise ValueError("A1 扫描根不能为空：请传入技能/项目目录")
    return os.path.abspath(raw)
def collect_py_files(skill_dir: str) -> list[str]:
    return sorted(collect_scan_py_files(_normalize_scan_root(skill_dir)))
class FileAnalyzerScanner:
    def __init__(self, skill_dir: str, cache=None):
        self.skill_dir = _normalize_scan_root(skill_dir)
        if not os.path.isdir(self.skill_dir):
            raise NotADirectoryError(
                f"A1 扫描根必须是目录: {self.skill_dir!r}")
        self._cache = cache
    @staticmethod
    def _resolve_filepath(filepath: str, base: str) -> str:
        path = os.fspath(filepath)
        return os.path.normpath(path if os.path.isabs(path)
                                else os.path.join(base, path))
    def scan_file(self, filepath: str,
                  base_dir: str | None = None) -> FileOverallProfile:
        start = time.perf_counter()
        clear_complexity_memo()
        base = (self.skill_dir if base_dir is None
                else _normalize_scan_root(base_dir))
        target = self._resolve_filepath(filepath, base)
        try:
            rel_path = os.path.relpath(target, base)
        except ValueError as _e:
            log_swallowed(__name__, _e, context='FileAnalyzerScanner.scan_file:ValueError')
            rel_path = target
        profile = FileOverallProfile(filepath=rel_path)
        _loaded = self._load_source_ast(target, profile, rel_path, start)
        if _loaded is None:
            return profile
        tree, source, size = _loaded
        total, code, comment, blank = count_lines(source, tree)
        functions, classes, imports, global_vars = parse_structure(tree)
        has_all, all_symbols = parse_all(tree)
        profile.basic_info = FileBasicInfo(
            filepath=rel_path,
            abspath=target,
            file_size=size,
            total_lines=total,
            code_lines=code,
            comment_lines=comment,
            blank_lines=blank,
            functions=functions,
            classes=classes,
            imports=imports,
            global_vars=global_vars,
            has_all=has_all,
            all_symbols=all_symbols,
        )
        profile.key_entities = extract_key_entities(tree, rel_path, all_symbols)
        if (any(isinstance(node, ast.If) and is_main_check(node.test)
                for node in tree.body)
                and "__main__" not in profile.key_entities.entry_points):
            profile.key_entities.entry_points.append("__main__")
        profile.defects = detect_defects(tree, rel_path, source)
        self._stamp_scan(profile, start)
        return profile
    @staticmethod
    def _stamp_scan(profile: FileOverallProfile, start: float) -> None:
        profile.scanned_at = time.strftime("%Y-%m-%dT%H:%M:%S")
        profile.elapsed_ms = round((time.perf_counter() - start) * 1000, 1)
    def _from_cache(self, getter: str, filepath: str) -> Any:
        if self._cache is None:
            return None
        try:
            return getattr(self._cache, getter)(filepath)
        except Exception as e:
            logger.debug("缓存通道 %s 读取失败，回退直读: %s", getter, e, exc_info=True)
            return None
    def _from_cache_pair(self, filepath: str) -> tuple[Any, Any] | None:
        getter = getattr(self._cache, "get_source_and_ast", None)
        if getter is None:
            return None
        try:
            pair = getter(filepath)
        except Exception as e:
            logger.debug("缓存通道 get_source_and_ast 读取失败，回退直读: %s",
                         e, exc_info=True)
            return None
        if not (isinstance(pair, tuple) and len(pair) == 2):
            logger.debug("缓存源码/AST 对形态非法（%s），回退直读",
                         type(pair).__name__)
            return None
        source, tree = pair
        if source is not None and not isinstance(source, str):
            logger.debug("缓存源码形态非法（%s），回退直读",
                         type(source).__name__)
            return None
        if tree is not None and not isinstance(tree, ast.Module):
            logger.debug("缓存 AST 形态非法（%s），回退解析",
                         type(tree).__name__)
            tree = None
        return source, tree
    def _load_source_ast(self, filepath: str, profile: FileOverallProfile,
                        rel_path: str,
                        start: float) -> tuple[ast.Module, str, int] | None:
        pair = self._from_cache_pair(filepath)
        if pair is not None and pair[0] is not None:
            source, tree = pair
            size = self._safe_getsize(filepath, source)
            if tree is not None:
                return tree, source, size
            return self._parse_ast(
                filepath, source, profile, rel_path, start, size,
            )
        loaded = self._load_source(filepath, profile, rel_path, start)
        if loaded is None:
            return None
        source, size = loaded
        return self._parse_ast(
            filepath, source, profile, rel_path, start, size,
        )
    def _load_source(self, filepath: str, profile: FileOverallProfile,
                     rel_path: str, start: float) -> tuple[str, int] | None:
        source = self._from_cache("get_source", filepath)
        if source is not None and not isinstance(source, str):
            logger.debug("缓存源码形态非法（%s），回退直读",
                         type(source).__name__)
            source = None
        if source is None:
            try:
                source = read_source_auto(filepath)
            except Exception as e:  # noqa: BLE001
                logger.warning("[A1] 读取文件失败 %s: %s", filepath, e)
                profile.basic_info = FileBasicInfo(
                    filepath=rel_path, abspath=filepath, total_lines=0)
                profile.defects.append(FileDefect(
                    defect_type=DefectType.READ_ERROR,
                    severity="P0",
                    filepath=rel_path,
                    lineno=1,
                    message=f"文件读取失败无法分析: {e}",
                    suggestion="检查文件权限/占用状态后重新诊断",
                    confidence=1.0,
                    detail={"error": str(e), "abspath": filepath},
                ))
                self._stamp_scan(profile, start)
                return None
        size = self._safe_getsize(filepath, source)
        return source, size
    def _parse_ast(self, filepath: str, source: str,
                   profile: FileOverallProfile, rel_path: str,
                   start: float, file_size: int,
                   ) -> tuple[ast.Module, str, int] | None:
        try:
            tree = ast.parse(source, filename=filepath)
        except (SyntaxError, ValueError, RecursionError) as e:
            log_swallowed(__name__, e,
                          context='FileAnalyzerScanner._parse_ast:SyntaxError+')
            return self._resolve_parse_failure(
                filepath, source, rel_path, profile, e, start, file_size,
            )
        return tree, source, file_size
    def _resolve_parse_failure(self, filepath: str, source: str,
                               rel_path: str, profile: FileOverallProfile,
                               e: Exception, start: float, file_size: int,
                               ) -> tuple[ast.Module, str, int] | None:
        retry = self._reread_and_parse(filepath)
        if retry is not None:
            tree, retry_source = retry
            return tree, retry_source, self._safe_getsize(
                filepath, retry_source,
            )
        logger.warning("[A1] 语法错误 %s: %s", filepath, e)
        _err_msg = getattr(e, "msg", None) or str(e)
        _err_line = getattr(e, "lineno", None) or 1
        total, code, comment, blank = count_lines(source)
        profile.basic_info = FileBasicInfo(
            filepath=rel_path,
            abspath=filepath,
            file_size=file_size,
            total_lines=total,
            code_lines=code,
            comment_lines=comment,
            blank_lines=blank,
        )
        profile.defects.append(FileDefect(
            defect_type=DefectType.SYNTAX_ERROR,
            severity="P0",
            filepath=rel_path,
            lineno=_err_line,
            message=f"文件存在语法错误无法解析: {_err_msg} (line {_err_line})",
            suggestion="修复语法错误后重新诊断",
            confidence=1.0,
            detail={"error": str(e), "line": _err_line},
        ))
        self._stamp_scan(profile, start)
        return None
    @staticmethod
    def _source_size(source: str) -> int:
        return len(source.encode("utf-8", errors="replace"))
    @staticmethod
    def _safe_getsize(filepath: str, source: str | None) -> int:
        try:
            return os.path.getsize(filepath)
        except OSError as _e:
            log_swallowed(__name__, _e, context='FileAnalyzerScanner._safe_getsize:OSError')
            return FileAnalyzerScanner._source_size(source) if source else 0
    @staticmethod
    def _reread_and_parse(filepath: str) -> tuple[ast.Module, str] | None:
        try:
            source = read_source_auto(filepath)
            tree = ast.parse(source, filename=filepath)
        except (OSError, SyntaxError, ValueError, RecursionError) as e:
            logger.debug("语法解析重试失败（跳过该文件）: %s: %s", filepath, e)
            return None
        logger.info("[A1] 语法错误瞬态复核恢复 %s（半写窗口）", filepath)
        return tree, source
    @staticmethod
    def _degraded_profile(filepath: str, base: str,
                          error: Exception) -> FileOverallProfile:
        try:
            rel_path = os.path.relpath(filepath, base)
        except ValueError as _swallow_e:
            log_swallowed(__name__, _swallow_e, context='FileAnalyzerScanner._degraded_profile:ValueError')
            rel_path = os.path.abspath(filepath)
        profile = FileOverallProfile(filepath=rel_path)
        profile.basic_info = FileBasicInfo(filepath=rel_path, abspath=filepath)
        profile.defects.append(FileDefect(
            defect_type=DefectType.READ_ERROR,
            severity="P0",
            filepath=rel_path,
            lineno=1,
            message=f"文件分析异常无法完成: {error}",
            suggestion="检查该文件分析链路后重新诊断",
            confidence=1.0,
            detail={"error": str(error), "abspath": filepath},
        ))
        profile.scanned_at = time.strftime("%Y-%m-%dT%H:%M:%S")
        return profile
    def scan_directory(self, skill_dir: str | None = None) -> list[FileOverallProfile]:
        target = self.skill_dir if skill_dir is None else skill_dir
        py_files = collect_py_files(target)
        profiles: list[FileOverallProfile] = []
        total = len(py_files)
        logger.info("[A1] 开始扫描 %d 个文件...", total)
        for i, fp in enumerate(py_files):
            if (i + 1) % 20 == 0:
                logger.info("[A1] 扫描进度: %d/%d", i + 1, total)
            _file_start = time.perf_counter()
            try:
                profile = self.scan_file(fp, base_dir=target)
                profiles.append(profile)
            except Exception as e:  # noqa: BLE001
                logger.warning("[A1] 扫描文件失败 %s: %s", fp, e)
                _degraded = self._degraded_profile(fp, target, e)
                _degraded.elapsed_ms = round(
                    (time.perf_counter() - _file_start) * 1000, 1)
                profiles.append(_degraded)
        logger.info("[A1] 扫描完成: %d/%d 个文件", len(profiles), total)
        clear_complexity_memo()
        return profiles
def _is_init_module(filepath) -> bool:
    name = str(filepath or "").rsplit("/", 1)[-1].rsplit("\\", 1)[-1]
    return name.lower() == "__init__.py"
def _entity_names(values) -> set[str]:
    if not isinstance(values, (list, tuple, set, frozenset)):
        return set()
    return {v for v in values if isinstance(v, str)}
def _str_tuple(values) -> tuple[str, ...]:
    if not isinstance(values, (list, tuple)):
        return ()
    return tuple(v for v in values if isinstance(v, str))
def _clean_doc(value) -> str:
    return value.strip() if isinstance(value, str) else ""
def _span_at_least(node, minimum: int) -> bool:
    start = getattr(node, "lineno", 0)
    end = getattr(node, "end_lineno", 0)
    return (isinstance(start, int) and isinstance(end, int)
            and (end - start + 1) >= minimum)
def _named_entity(items, symbol: str):
    for item in items or ():
        if getattr(item, "name", None) == symbol:
            return item
    return None
def _module_dotted_alias(filepath) -> str:
    text = str(filepath or "").replace("\\", "/").strip()
    while text.startswith("./"):
        text = text[2:]
    if not text or text.startswith("/") or os.path.splitdrive(text)[0]:
        return ""
    text = text.removesuffix(".py")
    parts = [p for p in text.split("/") if p not in ("", ".")]
    if not parts or any(p == ".." for p in parts):
        return ""
    if parts[-1] == "__init__":
        parts.pop()
    return ".".join(parts)
def _resolve_relative_import_source(filepath, source: str) -> str:
    text = str(source or "")
    if not text.startswith("."):
        return text
    dotted = _module_dotted_alias(filepath)
    if not dotted:
        return text
    package_parts = dotted.split(".")
    if not _is_init_module(filepath):
        package_parts.pop()
    level = len(text) - len(text.lstrip("."))
    parent_count = level - 1
    if parent_count >= len(package_parts):
        return text
    if parent_count:
        package_parts = package_parts[:-parent_count]
    module = text[level:]
    if module:
        package_parts.extend(p for p in module.split(".") if p)
    return ".".join(package_parts)
def _exact_high_layer_ref(mod: str, l0_modules: set[str],
                          known_non_l0: set[str]) -> str | None:
    dotted = ".".join(p for p in str(mod or "").split(".") if p)
    if not dotted or dotted in l0_modules or dotted not in known_non_l0:
        return None
    return dotted
def _high_layer_ref(mod: str, l0_modules: set[str],
                    known_non_l0: set[str]) -> str | None:
    parts = [p for p in str(mod or "").split(".") if p]
    while parts:
        stem = parts[-1]
        dotted = ".".join(parts)
        if dotted in known_non_l0 and dotted not in l0_modules:
            return dotted
        if dotted in l0_modules and dotted not in known_non_l0:
            return None
        if stem in l0_modules and stem in known_non_l0:
            dotted_l0 = dotted in l0_modules
            dotted_non_l0 = dotted in known_non_l0
            if dotted_l0 != dotted_non_l0:
                return dotted if dotted_non_l0 else None
        if stem in l0_modules:
            return None
        if stem in known_non_l0:
            return dotted
        parts.pop()
    return None
class DefectEnhancer:
    def __init__(self, profiles: list[FileOverallProfile]):
        self.profiles = profiles
        self._profile_map: dict[str, FileOverallProfile] = {
            p.filepath: p for p in profiles if p.filepath
        }
        self._global_symbols: dict[str, list[str]] = self._build_global_symbols()
    def _build_global_symbols(self) -> dict[str, list[str]]:
        symbols: dict[str, list[str]] = defaultdict(list)
        for profile in self.profiles:
            entities = profile.key_entities
            if not entities:
                continue
            fp = profile.filepath
            if not fp:
                continue
            imported = self._imported_names(profile)
            explicit = _entity_names(entities.public_api)
            implicit = _entity_names(entities.exported_symbols) - imported
            defined = explicit | {
                n for n in implicit if not n.startswith("_")}
            for name in sorted(defined):
                registered = symbols[name]
                if fp not in registered:
                    registered.append(fp)
        return dict(symbols)
    @staticmethod
    def _imported_names(profile: FileOverallProfile) -> set[str]:
        names: set[str] = set()
        basic = profile.basic_info
        if not basic:
            return names
        for imp in basic.imports:
            is_from = import_is_from(imp)
            for n in import_names(imp):
                if not n or n == "*":
                    continue
                names.add(n if is_from else n.split(".")[0])
        return names
    def _structure_signature(self, filepath: str, symbol: str):
        profile = self._profile_map.get(filepath)
        if not profile or not profile.basic_info:
            return None
        basic = profile.basic_info
        fn = _named_entity(basic.functions, symbol)
        if fn is not None:
            return ("func", _str_tuple(getattr(fn, "args", ())),
                    _span_at_least(fn, 10),
                    _clean_doc(getattr(fn, "docstring", "")))
        cls = _named_entity(basic.classes, symbol)
        if cls is None:
            return None
        methods = getattr(cls, "methods", ()) or ()
        return ("class",
                tuple(sorted(m.name for m in methods
                             if isinstance(getattr(m, "name", None), str))),
                tuple(sorted(_str_tuple(getattr(cls, "bases", ())))),
                _clean_doc(getattr(cls, "docstring", "")))
    def detect_cross_file_defects(self) -> list[FileDefect]:
        defects: list[FileDefect] = []
        defects.extend(self._check_symbol_conflicts())
        defects.extend(self._check_dead_modules())
        defects.extend(self._check_layer_violations())
        p1_plus = [d for d in defects if d.severity in ("P0", "P1")]
        if p1_plus:
            logger.warning(
                "跨文件缺陷检出 %d 项 P0/P1（共 %d 项）: %s",
                len(p1_plus), len(defects),
                "; ".join(f"{d.filepath}:{d.defect_type}" for d in p1_plus[:10]),
            )
        elif defects:
            logger.info("跨文件缺陷检出 %d 项（均为 P2/P3）", len(defects))
        return defects
    @staticmethod
    def _is_trivial_func_sig(sig: tuple) -> bool:
        return sig[0] == "func" and not sig[1] and not sig[2]
    def _conflict_report_files(self, real_files: list[str],
                               symbol: str) -> list[str] | None:
        sigs = [self._structure_signature(fp, symbol) for fp in real_files]
        if len(sigs) < 2 or any(sig is None for sig in sigs):
            return None
        if all(self._is_trivial_func_sig(sig) for sig in sigs):
            return []
        sig_counts = Counter(sigs)
        return [
            fp for fp, sig in zip(real_files, sigs, strict=True)
            if sig_counts.get(sig, 0) >= 2
            and not self._is_trivial_func_sig(sig)
        ]
    @staticmethod
    def _is_conventional_symbol(symbol: str) -> bool:
        return symbol in ("logger", "main") or symbol.upper() == symbol
    @staticmethod
    def _conflict_real_files(files: list[str]) -> list[str]:
        return [
            f for f in files
            if not _is_init_module(f)
            and not is_test_file_path(f)
        ]
    def _conflict_targets(self, symbol: str,
                          files: list[str]) -> tuple[list[str], int]:
        if len(files) < 2 or self._is_conventional_symbol(symbol):
            return [], 0
        real_files = self._conflict_real_files(files)
        if len(real_files) < 2:
            return [], 0
        report_files = self._conflict_report_files(real_files, symbol)
        targets = real_files if report_files is None else report_files
        return targets, len(real_files)
    def _check_symbol_conflicts(self) -> list[FileDefect]:
        defects = []
        for symbol, files in sorted(self._global_symbols.items()):
            targets, defined_count = self._conflict_targets(symbol, files)
            if not targets:
                continue
            for fp in targets:
                defects.append(FileDefect(
                    defect_type=DefectType.SYMBOL_CONFLICT,
                    severity="P2",
                    filepath=fp,
                    lineno=1,
                    message=(f"跨文件符号冲突: '{symbol}' 同时定义在 "
                             f"{defined_count} 个文件中"),
                    suggestion=f"考虑重命名或统一到一个模块: {', '.join(targets)}",
                    confidence=0.7,
                    detail={"symbol": symbol, "conflicting_files": targets,
                            "defined_file_count": defined_count},
                ))
        return defects
    @staticmethod
    def _looks_like_dead_module(filepath, basic, entities) -> bool:
        return (not entities.public_api
                and not entities.exported_symbols
                and not entities.entry_points
                and basic.function_count == 0
                and basic.class_count == 0
                and basic.import_count <= 2
                and not _is_init_module(filepath))
    def _is_dead_module(self, profile: FileOverallProfile,
                        consumed: set[str]) -> bool:
        basic = profile.basic_info
        entities = profile.key_entities
        if not basic or not entities:
            return False
        if is_test_file_path(str(profile.filepath or "")):
            return False
        stem = module_stem(profile.filepath)
        if stem in ("__main__", "conftest") or basic.global_vars:
            return False
        if stem in consumed:
            return False
        return self._looks_like_dead_module(profile.filepath, basic, entities)
    def _check_dead_modules(self) -> list[FileDefect]:
        defects = []
        consumed = self._consumed_modules()
        for profile in self.profiles:
            if not self._is_dead_module(profile, consumed):
                continue
            basic = profile.basic_info
            defects.append(FileDefect(
                defect_type=DefectType.DEAD_CODE,
                severity="P2",
                filepath=profile.filepath,
                lineno=1,
                message="模块无公开 API 且无函数定义，可能是死代码",
                suggestion="检查该文件是否被使用，考虑删除或补充实现",
                confidence=0.6,
                detail={"function_count": basic.function_count, "class_count": basic.class_count},
            ))
        return defects
    @staticmethod
    def _authoritative_layer(profile: FileOverallProfile) -> int | None:
        layer = profile.authoritative_layer
        return layer if isinstance(layer, int) else None
    def _is_l0(self, profile: FileOverallProfile) -> bool | None:
        domain = profile.functional_domain
        auth_layer = self._authoritative_layer(profile)
        if auth_layer is not None:
            return auth_layer == 0
        if not domain or domain.domain == DomainCategory.UNKNOWN:
            return None
        return domain.domain == DomainCategory.L0_BASE
    def _build_layer_evidence(self) -> tuple[set[str], set[str]]:
        l0_modules: set[str] = set()
        known_non_l0: set[str] = set()
        for profile in self.profiles:
            layer = self._is_l0(profile)
            if layer is None:
                continue
            aliases = {module_stem(profile.filepath),
                       _module_dotted_alias(profile.filepath)} - {""}
            (l0_modules if layer else known_non_l0).update(aliases)
        return l0_modules, known_non_l0
    @staticmethod
    def _import_consumption_terms(imp) -> set[str]:
        terms: set[str] = set()
        src = import_source(imp)
        if src:
            terms.update(src.replace("/", ".").split("."))
        if import_is_from(imp):
            terms.update(n for n in import_source_names(imp) if n and n != "*")
        return terms
    def _consumed_modules(self) -> set[str]:
        consumed: set[str] = set()
        for p in self.profiles:
            if not p.basic_info:
                continue
            for imp in p.basic_info.imports:
                consumed.update(self._import_consumption_terms(imp))
        return consumed
    @staticmethod
    def _high_layer_imports_of(basic, l0_modules: set[str],
                               known_non_l0: set[str]) -> list[str]:
        high_layer_imports: list[str] = []
        for imp in basic.imports:
            src = import_source(imp)
            is_relative = src.startswith(".")
            resolved_src = (_resolve_relative_import_source(basic.filepath, src)
                            if is_relative else src)
            matcher = _exact_high_layer_ref if is_relative else _high_layer_ref
            matched = matcher(resolved_src, l0_modules, known_non_l0)
            if matched:
                high_layer_imports.append(matched)
                continue
            if not import_is_from(imp):
                continue
            for name in import_source_names(imp):
                if not name or name == "*":
                    continue
                qualified_name = (f"{resolved_src}.{name}"
                                  if resolved_src else name)
                if not matcher(qualified_name, l0_modules, known_non_l0):
                    continue
                high_layer_imports.append(
                    f"{src}.{name}" if src and not is_relative else name)
        return high_layer_imports
    def _check_layer_violations(self) -> list[FileDefect]:
        defects = []
        _l0_modules, _known_non_l0 = self._build_layer_evidence()
        for profile in self.profiles:
            basic = profile.basic_info
            if not basic or is_test_file_path(str(profile.filepath or "")):
                continue
            if self._is_l0(profile) is not True:
                continue
            high_layer_imports = list(dict.fromkeys(
                self._high_layer_imports_of(basic, _l0_modules, _known_non_l0)))
            if high_layer_imports:
                defects.append(FileDefect(
                    defect_type=DefectType.LAYER_VIOLATION,
                    severity="P1",
                    filepath=profile.filepath,
                    lineno=1,
                    message=f"L0 模块依赖高层模块: {', '.join(high_layer_imports[:5])}",
                    suggestion="L0 模块不应依赖高层模块，提取共享定义到独立的 L0 模块",
                    confidence=0.8,
                    detail={"high_layer_imports": high_layer_imports},
                ))
        return defects
A1_METHOD_ID = "A1"
def enhance_defects(profiles: list[FileOverallProfile]) -> list[FileOverallProfile]:
    cross_defects = DefectEnhancer(profiles).detect_cross_file_defects()
    cross_by_file: dict[str, list[FileDefect]] = defaultdict(list)
    for d in cross_defects:
        cross_by_file[d.filepath].append(d)
    for profile in profiles:
        single_enhanced = enhance_single_file_defects(profile)
        profile.defects.extend(single_enhanced)
        _existing = {(d.defect_type, d.message) for d in profile.defects}
        cross = [d for d in cross_by_file.get(profile.filepath, [])
                 if (d.defect_type, d.message) not in _existing]
        profile.defects.extend(cross)
    return profiles

from __future__ import annotations  # noqa: I001
import ast
import difflib
import logging
import os
import re
from collections import Counter
from enum import Enum
from typing import Any
from jwsgj.diag_shared_ast_nodes import (
    TRY_NODE_TYPES,
    assign_targets_value,
    call_tail_name,
    iter_class_scope_methods,
    iter_module_level_stmts,
    iter_module_scope_entities,
    iter_scope_statements,
    iter_unpack_target_names,
)
from jwsgj.diag_shared_ast_surface import (
    collect_module_exports_state,
)
from jwsgj.diag_shared_source_core import (
    read_source_interpreter_encoding,
    scan_line_quote_state,
)
from jwsgj.diag_types_normalize import coerce_path_str, strip_bom
from jwsgj.diag_types_vocab import PARSE_DEGRADE_EXC
from jwsgj.runtime_scope import (
    SCAN_IGNORE_DIRS_LOWER,
    is_audit_skip_dir,
)
from jwsgj.prevention_scope_facts import walk_nodes
logger = logging.getLogger(__name__)
class FixRiskLevel(Enum):
    SAFE = "safe"
    CAUTION = "caution"
    DANGEROUS = "dangerous"
def normalize_risk_level(risk_level, original_source: str,
                          fixed_source: str, filepath: str):
    if risk_level is not None and not isinstance(risk_level, FixRiskLevel):
        try:
            risk_level = FixRiskLevel(risk_level)
        except ValueError:
            logger.warning(
                "verify: risk_level 形态不可识别(%r)，回退 classify_risk 自动分级",
                risk_level)
            risk_level = None
    if risk_level is None:
        risk_level = classify_risk(original_source, fixed_source, filepath)
    return risk_level
def scan_boundary_guard(original_source: str, fixed_source: str,
                         filepath: str) -> list:
    filepath = coerce_path_str(filepath)
    try:
        orig_tree_sb = ast.parse(strip_bom(original_source),
                                 filename=filepath or "<original>")
        fixed_tree_sb = ast.parse(strip_bom(fixed_source),
                                  filename=filepath or "<fixed>")
        return scan_side_effect_boundary(orig_tree_sb, fixed_tree_sb, filepath)
    except PARSE_DEGRADE_EXC as e:
        logger.debug("副作用边界扫描: 源码语法解析失败", exc_info=True)
        return [{"type": "parse_error", "symbol": filepath,
                 "kind": type(e).__name__, "file": filepath}]
def _is_deadcode_exempt(se: dict, filepath: str,
                        skill_dir: str | None) -> bool:
    if (se.get("type") not in ("removed", "global_removed")
            or se.get("symbol") == "__all__"):
        return False
    if (se.get("fixed_refs", 0) or se.get("export_unknown")
            or se.get("original_exported")
            or se.get("original_export_unknown")):
        return False
    return not symbol_referenced_externally(
        se.get("symbol", ""), filepath or "", skill_dir)
_BOUNDARY_TYPES = frozenset({
    "parse_error", "invalid_boundary",
    "except_removed", "except_added", "removed", "global_removed",
    "added", "modified", "signature_changed",
    "import_removed", "import_added", "import_reordered",
    "inheritance_changed", "class_keywords_changed",
    "class_decorator_changed", "class_type_params_changed",
    "class_attribute_removed", "class_attribute_added",
    "class_attribute_changed", "global_added", "global_value_changed",
})
def semantic_rejections(side_effects: list, filepath: str,
                         skill_dir: str | None) -> list:
    filepath = coerce_path_str(filepath)
    def _invalid_boundary(value: object, reason: str) -> dict:
        return {
            "type": "invalid_boundary", "symbol": "",
            "kind": type(value).__name__, "file": filepath,
            "detail": reason,
        }
    if side_effects is None:
        return [_invalid_boundary(side_effects, "边界列表缺失，无法证明语义安全")]
    if isinstance(side_effects, (str, bytes, dict)):
        logger.warning(
            "semantic_rejections: side_effects 形态异常(%s)，拒绝放行",
            type(side_effects).__name__)
        return [_invalid_boundary(side_effects, "边界列表必须是 dict 条目序列")]
    try:
        side_effects = list(side_effects)
    except Exception as exc:  # noqa: BLE001
        logger.warning(
            "semantic_rejections: 边界列表读取失败(%s: %s)，拒绝放行",
            type(exc).__name__, exc)
        return [_invalid_boundary(side_effects, "边界列表无法读取")]
    entries = []
    for index, entry in enumerate(side_effects):
        reason = ""
        normalized_type = ""
        if not isinstance(entry, dict):
            reason = "不是 dict"
        elif (not isinstance(entry.get("type"), str)
              or not entry["type"].strip()):
            reason = "缺少非空字符串 type"
        else:
            normalized_type = entry["type"].strip()
            if normalized_type not in _BOUNDARY_TYPES:
                reason = f"未知 type: {normalized_type}"
            elif (normalized_type in ("removed", "global_removed")
                  and not isinstance(entry.get("symbol"), str)):
                reason = "删除条目缺少字符串 symbol"
        if not reason:
            if normalized_type != entry["type"]:
                entry = {**entry, "type": normalized_type}
            entries.append(entry)
            continue
        logger.warning(
            "semantic_rejections: 第 %d 个边界条目%s(%s)，拒绝放行",
            index, reason, type(entry).__name__)
        entries.append(_invalid_boundary(
            entry, f"第 {index} 个边界条目{reason}"))
    rejections: list = []
    remaining_except_added: Counter[tuple[str, str]] = Counter(
        (se["migration_key"], se["symbol"]) for se in entries
        if se.get("type") == "except_added"
        and isinstance(se.get("migration_key"), str)
        and se["migration_key"]
        and isinstance(se.get("symbol"), str))
    remaining_legacy_except_added: Counter[str] = Counter(
        se["symbol"] for se in entries
        if se.get("type") == "except_added"
        and "migration_key" not in se
        and isinstance(se.get("symbol"), str))
    for se in entries:
        change_type = se.get("type", "")
        if change_type in ("parse_error", "invalid_boundary"):
            rejections.append(se)
            continue
        if change_type == "except_removed":
            migration_key = se.get("migration_key")
            symbol = se.get("symbol")
            if (isinstance(migration_key, str) and migration_key
                    and isinstance(symbol, str)):
                identity = (migration_key, symbol)
                if remaining_except_added[identity] > 0:
                    remaining_except_added[identity] -= 1
                    continue
            elif ("migration_key" not in se and isinstance(symbol, str)
                  and remaining_legacy_except_added[symbol] > 0):
                remaining_legacy_except_added[symbol] -= 1
                continue
            rejections.append(se)
            continue
        if change_type == "class_attribute_removed":
            rejections.append(se)
            continue
        if change_type in ("removed", "global_removed") and not _is_deadcode_exempt(
                se, filepath, skill_dir):
            rejections.append(se)
    return rejections
_DANGEROUS_NAMES: set[str] = {
    "__getattr__", "__all__", "__init__", "__init_subclass__",
    "globals", "locals", "vars",
}
_DANGEROUS_CALLS: set[str] = {
    "getattr", "setattr", "delattr", "hasattr",
    "exec", "eval", "compile",
    "import_module", "__import__",
}
_TEXT_DIFF_CAUTION_RATIO = 0.15
_MAGIC_CONTRACT_METHODS: tuple[str, ...] = (
    "__init__", "__getattr__", "__init_subclass__")
_MAGIC_BODY_CONTRACT_METHODS: tuple[str, ...] = (
    "__getattr__", "__init_subclass__")
_SEMANTIC_DIFF_CHECKERS: tuple = (
    (ast.Compare, "ops"),
    (ast.BoolOp, "op"),
    (ast.BinOp, "op"),
    (ast.UnaryOp, "op"),
    (ast.Constant, "value"),
    (ast.Name, "id"),
    (ast.Attribute, "attr"),
    (ast.keyword, "arg"),
)
_SEMANTIC_CHECKER_MAP: dict = dict(_SEMANTIC_DIFF_CHECKERS)
def _semantic_attr_spec(node: ast.AST, attr: str):
    value = getattr(node, attr, None)
    if isinstance(value, ast.AST):
        return ast.dump(value)
    if isinstance(value, list):
        return tuple(ast.dump(item) if isinstance(item, ast.AST) else item
                     for item in value)
    return value
def _check_pairwise_semantic_diff(
    orig_nodes: list[ast.AST], fixed_nodes: list[ast.AST]
) -> bool:
    for orig, fixed in zip(orig_nodes, fixed_nodes, strict=False):
        if type(orig) is not type(fixed):
            continue
        attr = _SEMANTIC_CHECKER_MAP.get(type(orig))
        if (attr is not None
                and _semantic_attr_spec(orig, attr) != _semantic_attr_spec(fixed, attr)):
            return True
    return False
def _strip_inline_comment(line):
    stripped = line.strip()
    cut, _state = scan_line_quote_state(stripped)
    return stripped if cut < 0 else stripped[:cut].rstrip()
def _strip_leading_string_literal(s: str) -> str | None:
    if not s or s[0] not in ("'", '"'):
        return None
    quote = s[0]
    close = quote * 3 if s.startswith(quote * 3) else quote
    n = len(s)
    i = len(close)
    while i < n:
        ch = s[i]
        if ch == "\\":
            i += 2
            continue
        if s.startswith(close, i):
            return s[i + len(close):]
        i += 1
    return ""
def _is_safe_diff_line(stripped):
    if not stripped:
        return True
    if stripped.startswith('#'):
        return True
    if stripped.startswith(('import ', 'from ')):
        return True
    if stripped.startswith(("'", '"')):
        return not (_strip_leading_string_literal(stripped) or "").strip(
            " \t,)]}")
    return False
def _parse_side_tree(source: str, filepath: str, side: str) -> ast.Module | None:
    try:
        return ast.parse(strip_bom(source), filename=filepath or f"<{side}>")
    except PARSE_DEGRADE_EXC:
        if side == "original":
            logger.warning("原始代码语法解析失败（语法错误/null byte/嵌套过深/解析器栈溢出），按 DANGEROUS 处理: %s", filepath)
        else:
            logger.debug("classify_risk: 修复后源码语法解析失败", exc_info=True)
        return None
def classify_risk(
    original_source: str,
    fixed_source: str,
    filepath: str = "",
) -> FixRiskLevel:
    early = _early_risk_level(original_source, fixed_source, filepath)
    if early is not None:
        return early
    orig_tree = _parse_side_tree(original_source, filepath, "original")
    if orig_tree is None:
        return FixRiskLevel.DANGEROUS
    fixed_tree = _parse_side_tree(fixed_source, filepath, "fixed")
    if fixed_tree is None:
        return FixRiskLevel.DANGEROUS
    orig_nodes = _collect_node_signatures(orig_tree)
    fixed_nodes = _collect_node_signatures(fixed_tree)
    if _has_dangerous_changes(orig_tree, fixed_tree, orig_nodes, fixed_nodes):
        return FixRiskLevel.DANGEROUS
    if _has_caution_changes(orig_tree, fixed_tree, orig_nodes, fixed_nodes):
        return FixRiskLevel.CAUTION
    return _post_ast_risk_level(
        original_source, fixed_source, orig_tree, fixed_tree)
def _early_risk_level(
    original_source: str,
    fixed_source: str,
    filepath: str,
) -> FixRiskLevel | None:
    if not isinstance(original_source, str) or not isinstance(fixed_source, str):
        logger.warning(
            "classify_risk: 源码输入非字符串（orig=%s, fixed=%s），按 DANGEROUS 处理: %s",
            type(original_source).__name__, type(fixed_source).__name__, filepath)
        return FixRiskLevel.DANGEROUS
    if original_source == fixed_source:
        return FixRiskLevel.SAFE
    return None
def _post_ast_risk_level(
    original_source: str,
    fixed_source: str,
    orig_tree: ast.Module,
    fixed_tree: ast.Module,
) -> FixRiskLevel:
    if _has_semantic_changes(orig_tree, fixed_tree):
        logger.debug("CAUTION: 语义级变更（运算符/字面量/变量名）")
        return FixRiskLevel.CAUTION
    if _is_safe_only_change(original_source, fixed_source):
        return FixRiskLevel.SAFE
    if ast.dump(orig_tree) == ast.dump(fixed_tree):
        return FixRiskLevel.SAFE
    if _has_text_level_caution(original_source, fixed_source):
        return FixRiskLevel.CAUTION
    if ast.dump(orig_tree) != ast.dump(fixed_tree):
        logger.debug("CAUTION: AST 非等价变更（表达式替换/重排等计数盲区）")
        return FixRiskLevel.CAUTION
    return FixRiskLevel.SAFE
def collect_import_keys(tree: ast.AST) -> Counter:
    result: Counter = Counter()
    for n in walk_nodes(tree):
        if isinstance(n, ast.Import):
            result.update(("Import", alias.name, alias.asname)
                          for alias in n.names)
        elif isinstance(n, ast.ImportFrom):
            result.update(("ImportFrom", n.level, n.module or "", alias.name,
                           alias.asname) for alias in n.names)
    return result
def _import_statement_specs(tree: ast.AST) -> tuple[tuple[str, str], ...]:
    collector = _ScopedImportCollector()
    collector.visit(tree)
    return tuple(collector.import_specs)
def _attribute_type_str(node: ast.Attribute) -> str:
    if isinstance(node.value, ast.Name):
        return f"{node.value.id}.{node.attr}"
    return ast.dump(node)
def stringify_exception_type(node: Any) -> Any:
    if node is None:
        return ""
    if isinstance(node, ast.Tuple):
        return ",".join(sorted(
            _single_exc_type_str(elt) for elt in node.elts))
    return _single_exc_type_str(node)
def _single_exc_type_str(node: ast.expr | None) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return _attribute_type_str(node)
    return ast.dump(node)
def _is_string_expression_stmt(node: ast.stmt) -> bool:
    return (isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Constant)
            and isinstance(node.value.value, str))
def collect_func_body_lens(tree: ast.AST) -> dict[str, list[int]]:
    lens: dict[str, list[int]] = {}
    for n in walk_nodes(tree):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            lens.setdefault(n.name, []).append(sum(
                not _is_string_expression_stmt(stmt) for stmt in n.body))
    return lens
def _count_top_level_defs(tree: ast.AST) -> dict[str, int]:
    counts: dict[str, int] = {}
    for node in iter_module_scope_entities(tree):
        counts[node.name] = counts.get(node.name, 0) + 1
    return counts
def _collect_dangerous_calls(tree: ast.AST) -> Counter:
    result: Counter = Counter()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Call):
            call_name = call_tail_name(node)
            if call_name in _DANGEROUS_CALLS:
                result[call_name] += 1
        if isinstance(node, ast.Name) and node.id in _DANGEROUS_NAMES:
            result[node.id] += 1
    return result
def _collect_except_types(tree: ast.AST) -> Counter:
    result: Counter = Counter()
    for node in walk_nodes(tree):
        if isinstance(node, ast.ExceptHandler):
            result[stringify_exception_type(node.type) or "bare"] += 1
    return result
def _parse_all_decl_value(value_node: ast.expr) -> tuple:
    try:
        value = ast.literal_eval(value_node)
    except (ValueError, TypeError, RecursionError):
        logger.debug("__all__ 含动态表达式，保留AST结构用于差分", exc_info=True)
        return "<non-literal>", ast.dump(value_node)
    if isinstance(value, (list, tuple)):
        return tuple(value)
    return "<non-container>", ast.dump(value_node)
def _assignment_target_value_pairs(
    target: ast.AST, value_node: ast.AST | None,
) -> list[tuple[ast.AST, ast.AST | None]]:
    if (value_node is not None
            and isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value_node, (ast.Tuple, ast.List))
            and len(target.elts) == len(value_node.elts)
            and not any(isinstance(item, ast.Starred) for item in target.elts)):
        return [
            pair
            for target_item, value_item in zip(
                target.elts, value_node.elts, strict=True)
            for pair in _assignment_target_value_pairs(target_item, value_item)
        ]
    return [(target, value_node)]
def _record_all_decl(
    targets: list[ast.expr],
    value_node: ast.expr | None,
    sigs: dict[str, Any],
) -> None:
    if value_node is None:
        return
    for target in targets:
        for target_item, assigned_value in _assignment_target_value_pairs(
                target, value_node):
            if (isinstance(target_item, ast.Name)
                    and target_item.id == "__all__"):
                sigs["__all__"] = {
                    "type": "all",
                    "value": _parse_all_decl_value(assigned_value),
                }
def _record_all_subscript_mutation(
    targets: list[ast.expr], sigs: dict[str, Any], operation: str,
    value_node: ast.expr | None = None,
) -> None:
    entries = [
        (operation, ast.dump(target_item),
         "" if assigned_value is None else ast.dump(assigned_value))
        for target in targets
        for target_item, assigned_value in _assignment_target_value_pairs(
            target, value_node)
        if (isinstance(target_item, ast.Subscript)
            and isinstance(target_item.value, ast.Name)
            and target_item.value.id == "__all__")
    ]
    if not entries:
        return
    sub = sigs.setdefault("__all___sub", {"type": "all_sub", "value": []})
    sub["value"].extend(entries)
def _record_all_assign_decl(node: ast.Assign, sigs: dict[str, Any]) -> None:
    _record_all_subscript_mutation(
        node.targets, sigs, "assign", node.value)
    _record_all_decl(node.targets, node.value, sigs)
def _record_all_annassign_decl(node: ast.AnnAssign, sigs: dict[str, Any]) -> None:
    _record_all_subscript_mutation(
        [node.target], sigs, "annassign", node.value)
    _record_all_decl(
        [node.target] if isinstance(node.target, ast.Name) else [],
        node.value, sigs)
def _record_all_augassign(node: ast.AugAssign, sigs: dict[str, Any]) -> None:
    operation = type(node.op).__name__
    _record_all_subscript_mutation(
        [node.target], sigs, operation, node.value)
    if not (isinstance(node.target, ast.Name) and node.target.id == "__all__"):
        return
    aug = sigs.setdefault("__all___aug", {"type": "all_aug", "value": []})
    aug["value"].append((operation, ast.dump(node.value)))
def _record_all_delete(node: ast.Delete, sigs: dict[str, Any]) -> None:
    _record_all_subscript_mutation(node.targets, sigs, "delete")
    if any(isinstance(target, ast.Name) and target.id == "__all__"
           for target in node.targets):
        sub = sigs.setdefault("__all___sub", {"type": "all_sub",
                                              "value": []})
        sub["value"].append("del __all__")
def _record_all_mutating_call(node: ast.Expr, sigs: dict[str, Any]) -> None:
    value = node.value
    if not (isinstance(value, ast.Call) and isinstance(value.func, ast.Attribute)
            and isinstance(value.func.value, ast.Name)
            and value.func.value.id == "__all__"):
        return
    mut = sigs.setdefault("__all___mut", {"type": "all_mut", "value": []})
    mut["value"].append(ast.dump(value))
_ALL_ENTRY_COLLECTORS: dict[type, Any] = {
    ast.Assign: _record_all_assign_decl,
    ast.AnnAssign: _record_all_annassign_decl,
    ast.AugAssign: _record_all_augassign,
    ast.Delete: _record_all_delete,
    ast.Expr: _record_all_mutating_call,
}
def _collect_all_signature_entry(node: ast.stmt, sigs: dict[str, Any]) -> None:
    handler = _ALL_ENTRY_COLLECTORS.get(type(node))
    if handler is not None:
        handler(node, sigs)
def _record_top_level_func_sig(
    node: ast.FunctionDef | ast.AsyncFunctionDef, sigs: dict[str, Any],
) -> None:
    sigs[node.name] = {"type": "func", "args": _function_signature_spec(node)}
def _class_method_sigs(class_node: ast.ClassDef) -> dict[str, dict]:
    return {
        item.name: {"args": _function_signature_spec(item)}
        for item in iter_class_scope_methods(class_node)
    }
def _record_class_sig(node: ast.ClassDef, sigs: dict[str, Any]) -> None:
    sigs[node.name] = {"type": "class", "methods": _class_method_sigs(node)}
_TOP_LEVEL_SIG_COLLECTORS: dict[type, Any] = {
    ast.FunctionDef: _record_top_level_func_sig,
    ast.AsyncFunctionDef: _record_top_level_func_sig,
    ast.ClassDef: _record_class_sig,
    ast.Assign: _collect_all_signature_entry,
    ast.AnnAssign: _collect_all_signature_entry,
    ast.AugAssign: _collect_all_signature_entry,
    ast.Delete: _collect_all_signature_entry,
    ast.Expr: _collect_all_signature_entry,
}
def _collect_node_signatures(tree: ast.AST) -> dict[str, Any]:
    sigs: dict[str, Any] = {}
    for node in iter_module_level_stmts(tree):
        collector = _TOP_LEVEL_SIG_COLLECTORS.get(type(node))
        if collector is not None:
            collector(node, sigs)
    return sigs
def _dangerous_fn_body_changed(
    orig_tree: ast.AST, fixed_tree: ast.AST
) -> bool:
    for _dangerous_fn in _MAGIC_BODY_CONTRACT_METHODS:
        if _function_body_changed(orig_tree, fixed_tree, _dangerous_fn):
            logger.debug("DANGEROUS: %s 函数体变更", _dangerous_fn)
            return True
    return False
def _has_dangerous_changes(
    orig_tree: ast.AST,
    fixed_tree: ast.AST,
    orig_sigs: dict[str, Any],
    fixed_sigs: dict[str, Any],
) -> bool:
    if _dangerous_fn_body_changed(orig_tree, fixed_tree):
        return True
    if _interface_contract_changed(orig_sigs, fixed_sigs):
        return True
    if _imports_changed(orig_tree, fixed_tree):
        logger.debug("DANGEROUS: import 变更（顶层/函数级）")
        return True
    if _top_level_symbols_changed(orig_sigs, fixed_sigs):
        return True
    if _top_level_definition_deletions_changed(
            orig_tree, fixed_tree, orig_sigs):
        logger.debug("DANGEROUS: 顶层函数/类定义被 del 删除")
        return True
    if _has_duplicate_definitions(orig_tree, fixed_tree):
        logger.debug("DANGEROUS: 同名函数重复定义")
        return True
    if _dangerous_calls_changed(orig_tree, fixed_tree):
        logger.debug("DANGEROUS: 动态调用变更")
        return True
    return False
def _interface_contract_changed(
    orig_sigs: dict[str, Any], fixed_sigs: dict[str, Any]
) -> bool:
    if any(orig_sigs.get(k) != fixed_sigs.get(k)
           for k in ("__all__", "__all___aug", "__all___mut",
                     "__all___sub")):
        logger.debug("DANGEROUS: __all__ 变更")
        return True
    for magic in _MAGIC_CONTRACT_METHODS:
        if _function_signature_changed(orig_sigs, fixed_sigs, magic):
            logger.debug("DANGEROUS: %s 签名变更", magic)
            return True
    return False
def _top_level_symbol_type_map(sigs: dict[str, Any]) -> dict[str, str]:
    return {name: info.get("type", "") for name, info in sigs.items()
            if info.get("type") in ("func", "class")}
def _top_level_symbols_changed(
    orig_sigs: dict[str, Any], fixed_sigs: dict[str, Any]
) -> bool:
    orig_types = _top_level_symbol_type_map(orig_sigs)
    fixed_types = _top_level_symbol_type_map(fixed_sigs)
    _changed = {name for name in set(orig_types) | set(fixed_types)
                if orig_types.get(name) != fixed_types.get(name)}
    if _changed:
        logger.debug("DANGEROUS: 顶层函数/类集合或类型变更: %s", sorted(_changed))
        return True
    return False
def _top_level_definition_deletions_changed(
    orig_tree: ast.AST, fixed_tree: ast.AST, orig_sigs: dict[str, Any],
) -> bool:
    orig_deleted = _collect_deleted_binding_names(orig_tree)
    fixed_deleted = _collect_deleted_binding_names(fixed_tree)
    deleted = ((fixed_deleted - orig_deleted)
               | (orig_deleted - fixed_deleted))
    return bool(set(deleted) & set(_top_level_symbol_type_map(orig_sigs)))
def _has_caution_changes(
    orig_tree: ast.AST,
    fixed_tree: ast.AST,
    orig_sigs: dict[str, Any],
    fixed_sigs: dict[str, Any],
) -> bool:
    if _docstring_contract_specs(orig_tree) != _docstring_contract_specs(fixed_tree):
        logger.debug("CAUTION: 模块/类/函数 docstring 契约变更")
        return True
    if _top_level_stmt_count_changed(orig_tree, fixed_tree):
        return True
    if _func_body_stmt_count_changed(orig_tree, fixed_tree):
        return True
    if _func_signatures_changed(orig_sigs, fixed_sigs):
        return True
    if _node_count_changed(
            orig_tree, fixed_tree, TRY_NODE_TYPES, "try/except"):
        return True
    if _exception_types_changed(orig_tree, fixed_tree):
        return True
    return _control_flow_changed(orig_tree, fixed_tree)
def _count_top_level_stmts(tree: ast.AST) -> int:
    return sum(1 for n in ast.iter_child_nodes(tree)
               if not isinstance(n, (ast.Import, ast.ImportFrom))
               and not _is_string_expression_stmt(n))
def _top_level_stmt_count_changed(
    orig_tree: ast.AST, fixed_tree: ast.AST
) -> bool:
    orig_stmts = _count_top_level_stmts(orig_tree)
    fixed_stmts = _count_top_level_stmts(fixed_tree)
    if orig_stmts != fixed_stmts:
        logger.debug("CAUTION: 顶层非导入语句数量变更 %d→%d", orig_stmts, fixed_stmts)
        return True
    return False
def _class_method_sigs_changed(
    orig_methods: dict[str, Any],
    fixed_methods: dict[str, Any],
    cls_name: str,
) -> bool:
    for m_name in sorted(set(orig_methods) | set(fixed_methods)):
        if m_name in _MAGIC_CONTRACT_METHODS:
            continue
        if (orig_methods.get(m_name, {}).get("args")
                != fixed_methods.get(m_name, {}).get("args")):
            logger.debug("CAUTION: 类 %s 方法 %s 签名变更", cls_name, m_name)
            return True
    return False
def _func_signatures_changed(
    orig_sigs: dict[str, Any], fixed_sigs: dict[str, Any]
) -> bool:
    for name, info in orig_sigs.items():
        if name in (*_MAGIC_CONTRACT_METHODS, "__all__", "__all___aug",
                    "__all___mut", "__all___sub"):
            continue
        kind = info.get("type")
        if (kind == "func"
                and _single_func_sig_changed(name, info, fixed_sigs.get(name))):
            return True
        if (kind == "class" and _class_methods_entry_changed(
                name, info, fixed_sigs.get(name))):
            return True
    return False
def _single_func_sig_changed(
    name: str, info: dict[str, Any], fixed_info: Any
) -> bool:
    if bool(fixed_info) and fixed_info.get("args") != info.get("args"):
        logger.debug("CAUTION: 函数 %s 签名变更", name)
        return True
    return False
def _class_methods_entry_changed(
    name: str, info: dict[str, Any], fixed_info: Any
) -> bool:
    if not fixed_info or fixed_info.get("type") != "class":
        return False
    return _class_method_sigs_changed(
        info.get("methods", {}), fixed_info.get("methods", {}), name)
_CONTROL_FLOW_COUNTERS = ((ast.If, "if"), (ast.For, "for"), (ast.While, "while"))
def _count_nodes(tree: ast.AST, node_type) -> int:
    return sum(1 for n in walk_nodes(tree) if isinstance(n, node_type))
def _node_count_changed(
    orig_tree: ast.AST, fixed_tree: ast.AST, node_type, label: str
) -> bool:
    orig_count = _count_nodes(orig_tree, node_type)
    fixed_count = _count_nodes(fixed_tree, node_type)
    if orig_count == fixed_count:
        return False
    logger.debug("CAUTION: %s 语句数量变更 %d→%d", label, orig_count, fixed_count)
    return True
def _control_flow_changed(
    orig_tree: ast.AST, fixed_tree: ast.AST
) -> bool:
    if any(_node_count_changed(orig_tree, fixed_tree, node_type, label)
           for node_type, label in _CONTROL_FLOW_COUNTERS):
        return True
    return _node_count_changed(orig_tree, fixed_tree, ast.Raise, "raise")
def _has_semantic_changes(
    orig_tree: ast.AST, fixed_tree: ast.AST
) -> bool:
    orig_nodes = list(walk_nodes(orig_tree))
    fixed_nodes = list(walk_nodes(fixed_tree))
    if len(orig_nodes) != len(fixed_nodes):
        return False
    return _check_pairwise_semantic_diff(orig_nodes, fixed_nodes)
def _is_safe_only_change(original: str, fixed: str) -> bool:
    orig_lines = original.splitlines()
    fixed_lines = fixed.splitlines()
    if _safe_line_signature(orig_lines) == _safe_line_signature(fixed_lines):
        return True
    diff_orig, diff_fixed = _diff_line_blocks(orig_lines, fixed_lines)
    if _diff_is_comment_only(diff_orig, diff_fixed):
        return True
    return all(_is_safe_diff_line(line.strip()) for line in diff_orig + diff_fixed)
def _safe_line_signature(lines: list[str]) -> tuple[list[str], list[str]]:
    tokens: list[str] = []
    indents: list[str] = []
    for ln in lines:
        if not ln.strip():
            continue
        tokens.extend(ln.split())
        indents.append(ln[: len(ln) - len(ln.lstrip())])
    return tokens, indents
def _diff_line_blocks(
    orig_lines: list[str], fixed_lines: list[str]
) -> tuple[list[str], list[str]]:
    diff_orig: list[str] = []
    diff_fixed: list[str] = []
    matcher = difflib.SequenceMatcher(None, orig_lines, fixed_lines)
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag == 'equal':
            continue
        diff_orig.extend(orig_lines[i1:i2])
        diff_fixed.extend(fixed_lines[j1:j2])
    return diff_orig, diff_fixed
def _diff_is_comment_only(
    diff_orig: list[str], diff_fixed: list[str]
) -> bool:
    def _code_with_indent(ln: str) -> str:
        body = _strip_inline_comment(ln)
        if not body:
            return ""
        return ln[: len(ln) - len(ln.lstrip())] + body
    return ([_code_with_indent(ln) for ln in diff_orig]
            == [_code_with_indent(ln) for ln in diff_fixed])
class _ScopedDefCollector(ast.NodeVisitor):
    def __init__(self) -> None:
        self.definitions: dict[tuple[str, str, int], ast.AST] = {}
        self._scope: list[str] = []
        self._occurrences: Counter = Counter()
    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._visit_definition(node)
    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self._visit_definition(node)
    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._visit_definition(node)
    def _visit_definition(self, node: ast.AST) -> None:
        kind = type(node).__name__
        qualname = ".".join((*self._scope, node.name))
        occurrence_key = (qualname, kind)
        occurrence = self._occurrences[occurrence_key]
        self._occurrences[occurrence_key] += 1
        self.definitions[(qualname, kind, occurrence)] = node
        self._scope.append(f"{node.name}#{occurrence}")
        self.generic_visit(node)
        self._scope.pop()
def _collect_scoped_def_nodes(tree: ast.AST) -> dict[tuple[str, str, int], ast.AST]:
    collector = _ScopedDefCollector()
    collector.visit(tree)
    return collector.definitions
def _docstring_contract_specs(tree: ast.AST) -> dict[tuple[str, str, int], str | None]:
    specs = {("<module>", "Module", 0): ast.get_docstring(tree, clean=False)}
    for identity, node in _collect_scoped_def_nodes(tree).items():
        specs[identity] = ast.get_docstring(node, clean=False)
    return specs
class _ScopedImportCollector(_ScopedDefCollector):
    def __init__(self) -> None:
        super().__init__()
        self.import_specs: list[tuple[str, str]] = []
    def visit_Import(self, node: ast.Import) -> None:
        scope = ".".join(self._scope) or "<module>"
        self.import_specs.append((scope, ast.dump(node)))
    visit_ImportFrom = visit_Import
def _function_body_spec(node: ast.FunctionDef | ast.AsyncFunctionDef) -> tuple[str, ...]:
    return tuple(ast.dump(stmt) for stmt in node.body)
def _collect_named_body_sigs(tree: ast.AST, func_name: str) -> dict:
    return {
        identity: _function_body_spec(node)
        for identity, node in _collect_scoped_def_nodes(tree).items()
        if node.name == func_name
        and isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }
def _function_body_changed(
    orig_tree: ast.AST, fixed_tree: ast.AST, func_name: str
) -> bool:
    orig_bodies = _collect_named_body_sigs(orig_tree, func_name)
    fixed_bodies = _collect_named_body_sigs(fixed_tree, func_name)
    if not orig_bodies and not fixed_bodies:
        return False
    return orig_bodies != fixed_bodies
def _has_duplicate_definitions(
    orig_tree: ast.AST, fixed_tree: ast.AST
) -> bool:
    orig_counts = _count_top_level_defs(orig_tree)
    fixed_counts = _count_top_level_defs(fixed_tree)
    for name in set(orig_counts) | set(fixed_counts):
        if orig_counts.get(name, 0) != fixed_counts.get(name, 0):
            return True
    return False
def _has_text_level_caution(original: str, fixed: str) -> bool:
    orig_lines = original.splitlines()
    fixed_lines = fixed.splitlines()
    diff = list(difflib.unified_diff(orig_lines, fixed_lines, n=0))
    changed = sum(1 for ln in diff[2:] if ln[:1] in ("+", "-"))
    total = max(len(orig_lines), len(fixed_lines), 1)
    if changed / total > _TEXT_DIFF_CAUTION_RATIO:
        logger.debug("CAUTION: diff占比 %.1f%% > %.0f%%",
                     changed / total * 100, _TEXT_DIFF_CAUTION_RATIO * 100)
        return True
    return False
def _class_method_signatures(
    sigs: dict[str, Any], method_name: str
) -> list[tuple[str, tuple]]:
    entries: list[tuple[str, tuple]] = []
    for cls_name, info in sigs.items():
        if info.get("type") != "class":
            continue
        for m_name, m_info in info.get("methods", {}).items():
            if m_name == method_name:
                entries.append((cls_name, tuple(m_info.get("args", ()))))
    return sorted(entries)
def _function_signature_changed(
    orig_sigs: dict[str, Any], fixed_sigs: dict[str, Any], name: str
) -> bool:
    orig = orig_sigs.get(name)
    fixed = fixed_sigs.get(name)
    class_changed = (_class_method_signatures(orig_sigs, name)
                     != _class_method_signatures(fixed_sigs, name))
    if orig is None and fixed is None:
        return class_changed
    if orig is None or fixed is None:
        return True
    if orig.get("type") != "func" or fixed.get("type") != "func":
        return orig != fixed or class_changed
    return orig.get("args") != fixed.get("args") or class_changed
def _imports_changed(orig_tree: ast.AST, fixed_tree: ast.AST) -> bool:
    return _import_statement_specs(orig_tree) != _import_statement_specs(fixed_tree)
def _dangerous_calls_changed(orig_tree: ast.AST, fixed_tree: ast.AST) -> bool:
    return _collect_dangerous_calls(orig_tree) != _collect_dangerous_calls(fixed_tree)
def _func_body_stmt_count_changed(
    orig_tree: ast.AST, fixed_tree: ast.AST
) -> bool:
    orig_counts = collect_func_body_lens(orig_tree)
    fixed_counts = collect_func_body_lens(fixed_tree)
    for name in set(orig_counts) | set(fixed_counts):
        if sorted(orig_counts.get(name, [])) != sorted(fixed_counts.get(name, [])):
            return True
    return False
def _exception_types_changed(orig_tree: ast.AST, fixed_tree: ast.AST) -> bool:
    return _collect_except_types(orig_tree) != _collect_except_types(fixed_tree)
def _kw_default_specs(a: ast.arguments) -> tuple[str, ...]:
    return tuple("" if d is None else ast.dump(d)
                 for d in (getattr(a, "kw_defaults", None) or []))
def _default_specs(a: ast.arguments) -> tuple[str, ...]:
    return (tuple(ast.dump(d) for d in (a.defaults or ()))
            + _kw_default_specs(a))
def _decorator_specs(
        n: ast.FunctionDef | ast.AsyncFunctionDef) -> tuple[str, ...]:
    return tuple(ast.dump(d) for d in n.decorator_list)
def _annotation_spec(node: ast.expr | None) -> str:
    return "" if node is None else ast.dump(node)
def _parameter_specs(a: ast.arguments) -> tuple[tuple[str, str, str], ...]:
    specs = [
        ("posonly", p.arg, _annotation_spec(p.annotation))
        for p in (getattr(a, "posonlyargs", None) or [])
    ]
    specs.extend(("arg", p.arg, _annotation_spec(p.annotation)) for p in a.args)
    if getattr(a, "vararg", None):
        specs.append(("vararg", a.vararg.arg, _annotation_spec(a.vararg.annotation)))
    elif getattr(a, "kwonlyargs", None):
        specs.append(("kwonly_separator", "*", ""))
    specs.extend(
        ("kwonly", p.arg, _annotation_spec(p.annotation))
        for p in (getattr(a, "kwonlyargs", None) or [])
    )
    if getattr(a, "kwarg", None):
        specs.append(("kwarg", a.kwarg.arg, _annotation_spec(a.kwarg.annotation)))
    return tuple(specs)
def _type_param_specs(
    node: ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef,
) -> tuple[str, ...]:
    return tuple(ast.dump(item) for item in getattr(node, "type_params", ()))
def _function_signature_spec(
    node: ast.FunctionDef | ast.AsyncFunctionDef,
) -> tuple:
    return (
        _parameter_specs(node.args),
        _default_specs(node.args),
        _decorator_specs(node),
        _annotation_spec(node.returns),
        _type_param_specs(node),
    )
def _boundary_entry(change_type: str, symbol: str, kind: str,
                    filepath: str) -> dict:
    return {"type": change_type, "symbol": symbol,
            "kind": kind, "file": filepath}
def _removed_symbol_entry(
    change_type: str, symbol: str, kind: str, filepath: str,
    fixed_refs: Counter, fixed_export_names: set[str] | None,
) -> dict:
    entry = _boundary_entry(change_type, symbol, kind, filepath)
    entry["fixed_refs"] = fixed_refs.get(symbol, 0) + (
        1 if fixed_export_names is not None and symbol in fixed_export_names
        else 0)
    if fixed_export_names is None:
        entry["export_unknown"] = True
    return entry
def _mark_original_export_state(
    entry: dict, symbol: str, original_export_names: set[str] | None,
) -> dict:
    if original_export_names is None:
        entry["original_export_unknown"] = True
    elif symbol in original_export_names:
        entry["original_exported"] = True
    return entry

def _diff_function_signatures(orig_tree, fixed_tree, filepath):
    orig_defs = _collect_scoped_def_nodes(orig_tree)
    fixed_defs = _collect_scoped_def_nodes(fixed_tree)
    affected = []
    for identity in sorted(set(orig_defs) & set(fixed_defs)):
        orig_node = orig_defs[identity]
        fixed_node = fixed_defs[identity]
        if not isinstance(orig_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        orig_spec = _function_signature_spec(orig_node)
        fixed_spec = _function_signature_spec(fixed_node)
        if orig_spec == fixed_spec:
            continue
        affected.append({
            **_boundary_entry(
                "signature_changed", orig_node.name, type(orig_node).__name__, filepath),
            "detail": f"orig={orig_spec} -> fixed={fixed_spec}",
        })
    return affected
def _diff_imports(orig_tree, fixed_tree, filepath):
    orig_imports = collect_import_keys(orig_tree)
    fixed_imports = collect_import_keys(fixed_tree)
    affected = (
        [_boundary_entry("import_removed", str(imp), "Import", filepath)
         for imp in orig_imports - fixed_imports]
        + [_boundary_entry("import_added", str(imp), "Import", filepath)
           for imp in fixed_imports - orig_imports]
    )
    if (not affected
            and _import_statement_specs(orig_tree)
            != _import_statement_specs(fixed_tree)):
        affected.append(_boundary_entry(
            "import_reordered", "<order>", "Import", filepath))
    return affected
def _class_method_binding_state(
    class_node: ast.ClassDef,
) -> tuple[dict[str, ast.AST], set[str]]:
    methods: dict[str, ast.AST] = {}
    present: set[str] = set()
    for stmt, _in_handler in iter_scope_statements(
            class_node, include_defs=True):
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
            methods[stmt.name] = stmt
            present.add(stmt.name)
        elif isinstance(stmt, ast.Delete):
            for target in stmt.targets:
                present.difference_update(iter_unpack_target_names(target))
    return methods, present
def _diff_class_contracts(
    orig_tree, fixed_tree, filepath, fixed_refs: Counter,
    fixed_export_names: set[str] | None,
):
    orig_defs = _collect_scoped_def_nodes(orig_tree)
    fixed_defs = _collect_scoped_def_nodes(fixed_tree)
    affected = []
    for identity in sorted(set(orig_defs) & set(fixed_defs)):
        orig_node = orig_defs[identity]
        fixed_node = fixed_defs[identity]
        if not isinstance(orig_node, ast.ClassDef):
            continue
        orig_bases = tuple(ast.dump(base) for base in orig_node.bases)
        fixed_bases = tuple(ast.dump(base) for base in fixed_node.bases)
        if orig_bases != fixed_bases:
            affected.append(_boundary_entry(
                "inheritance_changed", orig_node.name, "ClassDef", filepath))
        contract_specs = (
            ("class_keywords_changed", orig_node.keywords, fixed_node.keywords),
            ("class_decorator_changed",
             orig_node.decorator_list, fixed_node.decorator_list),
            ("class_type_params_changed",
             getattr(orig_node, "type_params", ()),
             getattr(fixed_node, "type_params", ())),
        )
        for change_type, orig_items, fixed_items in contract_specs:
            orig_spec = tuple(ast.dump(item) for item in orig_items)
            fixed_spec = tuple(ast.dump(item) for item in fixed_items)
            if orig_spec != fixed_spec:
                affected.append(_boundary_entry(
                    change_type, orig_node.name, "ClassDef", filepath))
        orig_methods, orig_method_present = _class_method_binding_state(orig_node)
        fixed_methods, fixed_method_present = _class_method_binding_state(fixed_node)
        for name in sorted(orig_methods.keys() & fixed_methods.keys()):
            if name in orig_method_present and name not in fixed_method_present:
                affected.append(_removed_symbol_entry(
                    "removed", name, type(orig_methods[name]).__name__, filepath,
                    fixed_refs, fixed_export_names))
            elif name not in orig_method_present and name in fixed_method_present:
                affected.append(_boundary_entry(
                    "added", name, type(fixed_methods[name]).__name__, filepath))
        orig_attrs, orig_present = _collect_assignment_state(orig_node)
        fixed_attrs, fixed_present = _collect_assignment_state(fixed_node)
        removed = orig_present - fixed_present
        added = fixed_present - orig_present
        for name in sorted(orig_present | fixed_present):
            if (name not in removed and name not in added
                    and orig_attrs.get(name) == fixed_attrs.get(name)):
                continue
            if name in removed:
                change_type = "class_attribute_removed"
            elif name in added:
                change_type = "class_attribute_added"
            else:
                change_type = "class_attribute_changed"
            affected.append(_boundary_entry(
                change_type, f"{orig_node.name}.{name}", "ClassAssign", filepath))
    return affected
def _normalize_literal_repr(val) -> str:
    if isinstance(val, (set, frozenset)):
        return f"{type(val).__name__}({sorted(map(repr, val))!r})"
    if isinstance(val, dict):
        return "dict(" + repr(sorted(val.items(), key=lambda kv: repr(kv[0]))) + ")"
    return repr(val)
def _global_value_spec(name: str, value_node: ast.AST) -> str:
    try:
        return _normalize_literal_repr(ast.literal_eval(value_node))
    except (ValueError, TypeError, RecursionError):
        logger.debug("全局赋值为非字面量，保留AST结构用于差分: %s", name)
        return "<non-literal>:" + ast.dump(value_node)
def _assignment_name_value_pairs(
    target: ast.AST, value_node: ast.AST,
) -> list[tuple[str, ast.AST]]:
    return [
        (name, assigned_value)
        for target_item, assigned_value in _assignment_target_value_pairs(
            target, value_node)
        for name in iter_unpack_target_names(target_item)
    ]
def _collect_deleted_binding_names(scope: ast.AST) -> Counter[str]:
    deleted: Counter[str] = Counter()
    for stmt in iter_module_level_stmts(scope):
        if not isinstance(stmt, ast.Delete):
            continue
        for target in stmt.targets:
            deleted.update(iter_unpack_target_names(target))
    return deleted
def _collect_assignment_state(
    scope: ast.AST,
) -> tuple[dict[str, tuple[str, ...]], set[str]]:
    values: dict[str, list[str]] = {}
    present: set[str] = set()
    for stmt, _in_handler in iter_scope_statements(scope):
        binding = assign_targets_value(stmt)
        if binding is not None:
            targets, value_node = binding
            operation = type(stmt).__name__
        elif (isinstance(stmt, ast.AugAssign)
              and isinstance(stmt.target, ast.Name)):
            targets, value_node = [stmt.target], stmt.value
            operation = f"AugAssign:{type(stmt.op).__name__}"
        elif isinstance(stmt, ast.Delete):
            for target in stmt.targets:
                present.difference_update(iter_unpack_target_names(target))
            continue
        else:
            continue
        for target in targets:
            for name, assigned_value in _assignment_name_value_pairs(
                    target, value_node):
                present.add(name)
                spec = f"{operation}:{_global_value_spec(name, assigned_value)}"
                values.setdefault(name, []).append(spec)
    return {name: tuple(specs) for name, specs in values.items()}, present
def _diff_global_assigns(
    orig_tree, fixed_tree, filepath, fixed_refs: Counter,
    fixed_export_names: set[str] | None,
):
    orig_globals, orig_present = _collect_assignment_state(orig_tree)
    fixed_globals, fixed_present = _collect_assignment_state(fixed_tree)
    orig_deleted = _collect_deleted_binding_names(orig_tree)
    fixed_deleted = _collect_deleted_binding_names(fixed_tree)
    removed_names = ((orig_present - fixed_present)
                     | (set(fixed_deleted - orig_deleted) - fixed_present))
    added_names = fixed_present - orig_present
    removed = []
    for name in sorted(removed_names):
        removed.append(_removed_symbol_entry(
            "global_removed", name, "Assign", filepath,
            fixed_refs, fixed_export_names))
    return (
        removed
        + [_boundary_entry("global_added", g_name, "Assign", filepath)
           for g_name in sorted(added_names)]
        + [_boundary_entry("global_value_changed", g_name, "Assign", filepath)
           for g_name in sorted(orig_present & fixed_present)
           if orig_globals[g_name] != fixed_globals[g_name]]
    )
class _ScopedExceptCollector(_ScopedDefCollector):
    def __init__(self) -> None:
        super().__init__()
        self.pairs: Counter = Counter()
        self._try_occurrences: Counter = Counter()
    def visit_Try(self, node: ast.Try) -> None:
        scope = tuple(self._scope)
        occurrence = self._try_occurrences[scope]
        self._try_occurrences[scope] += 1
        scope_name = ".".join(self._scope) or "<module>"
        for index, handler in enumerate(node.handlers):
            migration_key = (
                f"{scope_name}::try{occurrence}::handler{index}")
            exc_name = (stringify_exception_type(handler.type)
                        if handler.type else "")
            self.pairs[(migration_key, exc_name, handler.name or "")] += 1
        self.generic_visit(node)
    visit_TryStar = visit_Try
def _collect_except_pairs(tree: ast.AST) -> Counter:
    collector = _ScopedExceptCollector()
    collector.visit(tree)
    return collector.pairs
def _diff_exception_handlers(orig_tree, fixed_tree, filepath):
    orig_excepts = _collect_except_pairs(orig_tree)
    fixed_excepts = _collect_except_pairs(fixed_tree)
    def _entries(items, change_type: str) -> list[dict]:
        entries = []
        for migration_key, exc_name, alias in items:
            entry = _boundary_entry(
                change_type, str((exc_name, alias)), "ExceptHandler", filepath)
            entry["migration_key"] = migration_key
            entries.append(entry)
        return entries
    return (_entries(orig_excepts - fixed_excepts, "except_removed")
            + _entries(fixed_excepts - orig_excepts, "except_added"))
def _diff_restored_definitions(
    orig_tree: ast.AST, fixed_tree: ast.AST,
    orig_defs: dict, fixed_defs: dict, filepath: str,
) -> list:
    restored = (_collect_deleted_binding_names(orig_tree)
                - _collect_deleted_binding_names(fixed_tree))
    if not restored:
        return []
    nodes: dict[str, ast.AST] = {}
    for identity in sorted(set(orig_defs) & set(fixed_defs)):
        node = fixed_defs[identity]
        if identity[0] == node.name and node.name in restored:
            nodes[node.name] = node
    return [_boundary_entry("added", name, type(node).__name__, filepath)
            for name, node in sorted(nodes.items())]
def _scan_file_for_symbol(target_path: str, pat) -> bool | None:
    try:
        return pat.search(read_source_interpreter_encoding(target_path)) is not None
    except (OSError, UnicodeError, LookupError, SyntaxError) as scan_err:
        logger.warning("symbol_referenced_externally: 扫描文件读取失败(跳过): %s: %s",
                       target_path, scan_err)
        return None
def _normcase_key(path: str) -> str:
    return os.path.normcase(os.path.normpath(os.path.abspath(path)))
def _resolve_definition_key(filepath: str, root: str) -> str:
    if not filepath:
        return ""
    if not os.path.isabs(filepath):
        root_rel = os.path.join(root, filepath)
        if os.path.isfile(root_rel):
            return _normcase_key(root_rel)
    def_path = os.path.abspath(filepath)
    return _normcase_key(def_path) if os.path.isfile(def_path) else ""
def _raise_walk_error(err: OSError) -> None:
    raise err
def _is_pruned_scan_dir(name: str) -> bool:
    return is_audit_skip_dir(name) or name.lower() in SCAN_IGNORE_DIRS_LOWER
def _iter_scan_files(root: str):
    for dirpath, dirnames, filenames in os.walk(root, onerror=_raise_walk_error):
        dirnames[:] = [d for d in dirnames if not _is_pruned_scan_dir(d)]
        for fn in filenames:
            if fn.lower().endswith(".py"):
                yield os.path.join(dirpath, fn)
def _scan_tree_for_pattern(root: str, pat, def_key: str) -> bool:
    undetermined = False
    for target_path in _iter_scan_files(root):
        if def_key and _normcase_key(target_path) == def_key:
            continue
        hit = _scan_file_for_symbol(target_path, pat)
        if hit:
            return True
        if hit is None:
            undetermined = True
    return undetermined
def symbol_referenced_externally(symbol: str, filepath: str, skill_dir: str = "") -> bool:
    if not symbol:
        return True
    filepath = coerce_path_str(filepath)
    root = coerce_path_str(skill_dir)
    if not root or not os.path.isdir(root):
        return True
    pat = re.compile(r"\b" + re.escape(symbol) + r"\b")
    def_key = _resolve_definition_key(filepath, root)
    try:
        return _scan_tree_for_pattern(root, pat, def_key)
    except OSError as walk_err:
        logger.warning("symbol_referenced_externally: 全库扫描异常，保守返回 True(不豁免): %s: %s",
                       root, walk_err)
        return True
def _diff_function_bodies(
    orig_defs: dict, fixed_defs: dict, common: set, filepath: str,
) -> list:
    changed = []
    for identity in sorted(common):
        orig_node = orig_defs[identity]
        fixed_node = fixed_defs[identity]
        if not isinstance(orig_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if _function_body_spec(orig_node) != _function_body_spec(fixed_node):
            changed.append(_boundary_entry(
                "modified", orig_node.name, type(orig_node).__name__, filepath))
    return changed
def _module_export_names(tree: ast.AST) -> set[str] | None:
    if not isinstance(tree, ast.Module):
        return None
    try:
        names, exact = collect_module_exports_state(tree)
    except (AttributeError, TypeError, ValueError, RecursionError) as export_err:
        logger.warning(
            "副作用边界: __all__ 收集异常，导出集合按未知处理: %s", export_err)
        return None
    if not exact:
        logger.warning("副作用边界: 动态 __all__ 的导出集合不完整，按未知处理")
        return None
    return names
def _collect_tree_symbol_refs(tree: ast.AST) -> Counter:
    references: Counter = Counter()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
            references[node.id] += 1
        elif (isinstance(node, ast.Attribute)
              and isinstance(node.ctx, ast.Load)):
            references[node.attr] += 1
    return references
def scan_side_effect_boundary(orig_tree, fixed_tree, filepath: str = "") -> list:
    affected = []
    orig_defs = _collect_scoped_def_nodes(orig_tree)
    fixed_defs = _collect_scoped_def_nodes(fixed_tree)
    orig_identities = set(orig_defs)
    fixed_identities = set(fixed_defs)
    original_export_names = _module_export_names(orig_tree)
    fixed_export_names = _module_export_names(fixed_tree)
    fixed_refs = _collect_tree_symbol_refs(fixed_tree)
    for identity in sorted(orig_identities - fixed_identities):
        node = orig_defs[identity]
        entry = _removed_symbol_entry(
            "removed", node.name, type(node).__name__, filepath,
            fixed_refs, fixed_export_names)
        if identity[0] == node.name:
            _mark_original_export_state(
                entry, node.name, original_export_names)
        affected.append(entry)
    for identity in sorted(fixed_identities - orig_identities):
        node = fixed_defs[identity]
        affected.append(_boundary_entry(
            "added", node.name, type(node).__name__, filepath))
    affected.extend(_diff_restored_definitions(
        orig_tree, fixed_tree, orig_defs, fixed_defs, filepath))
    affected.extend(_diff_function_bodies(
        orig_defs, fixed_defs, orig_identities & fixed_identities, filepath))
    affected.extend(_diff_function_signatures(orig_tree, fixed_tree, filepath))
    affected.extend(_diff_imports(orig_tree, fixed_tree, filepath))
    affected.extend(_diff_class_contracts(
        orig_tree, fixed_tree, filepath, fixed_refs, fixed_export_names))
    global_effects = _diff_global_assigns(
        orig_tree, fixed_tree, filepath, fixed_refs, fixed_export_names)
    for entry in global_effects:
        if entry.get("type") == "global_removed":
            _mark_original_export_state(
                entry, entry.get("symbol", ""), original_export_names)
    affected.extend(global_effects)
    affected.extend(_diff_exception_handlers(orig_tree, fixed_tree, filepath))
    return affected
__all__ = [
    'FixRiskLevel',
    'classify_risk',
    'normalize_risk_level',
    'scan_boundary_guard',
    'semantic_rejections',
]
logger.info("fix_safety_boundary 风险分级与副作用边界已加载: %d 项导出", len(__all__))

from __future__ import annotations

import ast
import builtins
import logging
import math
from collections import Counter
from collections.abc import Iterator
from dataclasses import dataclass

from jwsgj.diag_guard_source import (
    _CODE_WRITE_OPS,
    _METADATA_TYPE_FIX,
    _as_name_list,
    _before_after_type_gate,
    _code_guard_verdict,
    _file_issues,
    _GuardVerdictSpec,
    _iter_valid_targets,
    _pending_write_source,
    _read_source_optional,
    _result_identity,
    content_label,
    iter_scan_sources,
    iter_scan_sources_with_ast,
    parse_safe,
)
from jwsgj.diag_shared_ast_nodes import (
    annassign_target_names,
    argument_param_names,
    augassign_target_names,
    build_parent_map,
    definition_time_exprs,
    iter_class_scope_methods,
    iter_def_site_nodes,
    iter_module_level_stmts,
    iter_module_stmt_blocks,
    iter_unpack_target_names,
    module_postpones_annotations,
)
from jwsgj.diag_shared_ast_nodes import (
    definition_site_walrus_names as _definition_site_walrus_names,
)
from jwsgj.diag_types_defs import (
    GuardResult,
    OperationContext,
    code_to_write_str,
    issues_guard_result,
)
from jwsgj.diag_types_vocab import GuardLevel, OperationType
from jwsgj.prevention_scope_facts import walk_nodes

_log = logging.getLogger(__name__)
__all__ = [
    'count_pass_statements',
    'get_function_tree',
    'guard_ast',
    'guard_concurrent_state',
    'guard_dictret',
    'guard_funcbody',
    'guard_mro',
    'guard_recursion_depth',
    'guard_slots',
]
_log.info("diag_guard_quality 已加载：%d 项导出", len(__all__))
def _definition_inventory(
        tree: ast.Module) -> tuple[dict[str, int], dict[str, Counter[str]]]:
    counts = {"functions": 0, "classes": 0, "imports": 0}
    names: dict[str, Counter[str]] = {
        "functions": Counter(), "classes": Counter(), "imports": Counter()}
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            counts["functions"] += 1
            names["functions"][node.name] += 1
        elif isinstance(node, ast.ClassDef):
            counts["classes"] += 1
            names["classes"][node.name] += 1
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            counts["imports"] += len(node.names)
            names["imports"].update(_import_definition_names(node))
    return counts, names
def _import_alias_binding(node: ast.Import | ast.ImportFrom, alias,
                          *, include_star: bool) -> str | None:
    if alias.name == "*":
        return "*" if include_star else None
    if alias.asname:
        return alias.asname
    if isinstance(node, ast.Import):
        return alias.name.split(".")[0]
    return alias.name
def _import_binding_names(node: ast.Import | ast.ImportFrom) -> set[str]:
    names: set[str] = set()
    for alias in node.names:
        name = _import_alias_binding(node, alias, include_star=False)
        if name is not None:
            names.add(name)
    return names
def _import_definition_names(node: ast.Import | ast.ImportFrom) -> list[str]:
    names: list[str] = []
    for alias in node.names:
        name = _import_alias_binding(node, alias, include_star=True)
        if name is not None:
            names.append(name)
    return names
def _diff_definition_counts(
    before_counts: dict[str, int], after_counts: dict[str, int],
    before_names: dict[str, Counter[str]],
    after_names: dict[str, Counter[str]],
    declared_names: dict[str, Counter[str]],
) -> list[str]:
    issues: list[str] = []
    _dim_label = {"functions": "函数", "classes": "类",
                  "imports": "import 导入名"}
    _before_names = before_names or {}
    _after_names = after_names or {}
    _declared_names = declared_names or {}
    for _dim in ("functions", "classes", "imports"):
        _b, _a = before_counts[_dim], after_counts[_dim]
        _net = _b - _a
        _before_occurrences = _before_names.get(_dim, Counter())
        _after_occurrences = _after_names.get(_dim, Counter())
        _lost = _before_occurrences - _after_occurrences
        _declared = _declared_names.get(_dim, Counter())
        _matched_occurrences = _lost & _declared
        _undeclared = _lost - _declared
        if _dim == "imports":
            _undeclared.pop("*", None)
        _matched = sum(_matched_occurrences.values())
        _undeclared_count = sum(_undeclared.values())
        _unmatched_net = max(_net - _matched, 0)
        if _unmatched_net <= 0 and not _undeclared:
            continue
        if _unmatched_net > 0:
            _declared_note = (f"，已豁免声明删除 {_matched} 个"
                              if _matched else "")
            issues.append(
                f"{_dim_label[_dim]}数量净减少 {_net} 个"
                f"（{_b} → {_a}{_declared_note}），"
                f"未声明减少 {_unmatched_net} 个,"
                f"请确认是否为预期行为."
            )
        if _undeclared_count > _unmatched_net:
            _names = ", ".join(
                f"{name}×{count}" if count > 1 else name
                for name, count in sorted(_undeclared.items()))
            issues.append(
                f"{_dim_label[_dim]}存在未声明丢失名称: "
                f"{_names}（净变化 {_net:+d} 个），"
                f"请确认是否为预期行为."
            )
    return issues
def _append_split_merge_hint(ctx: OperationContext, issues: list[str]) -> None:
    if (ctx.operation in (OperationType.SPLIT, OperationType.MERGE)
            and any("净减少" in _d for _d in issues)):
        issues.append(
            "拆分/合并场景提示: before_code/after_code 须为同一逻辑"
            "单元的全集形态（拆分后各产物拼接 / 合并前各源文件拼接）,"
            "单产物对比会把定义搬运误判为减少."
        )
def _guard_ast_suggestion(method: str, after_broken: bool,
                          bad_types: list[str]) -> str:
    if method == "regex":
        return "使用 ast.NodeTransformer 进行代码结构修改,避免正则替换."
    if after_broken:
        return "先修复语法错误（可用 compile() 定位），再重新执行结构对比."
    if bad_types:
        return _METADATA_TYPE_FIX
    return ("确认定义减少是否为预期行为（预期删除请在 metadata 的 "
            "deleted_functions/deleted_classes/deleted_imports 中声明），"
            "意外丢失时回滚修改或补回定义.")
def _compare_code_structures(ctx: OperationContext, before_code: str,
                             after_code: str, issues: list[str]) -> bool:
    before_tree = parse_safe(before_code)
    after_tree = parse_safe(after_code)
    if before_tree is None or after_tree is None:
        _bad_side = []
        if before_tree is None:
            _bad_side.append("before_code")
        if after_tree is None:
            _bad_side.append("after_code")
        issues.append(f"{' 与 '.join(_bad_side)} 无法解析（语法损坏），"
                      f"结构数量对比无法执行，请先修复语法")
        return after_tree is None
    before_counts, before_names = _definition_inventory(before_tree)
    after_counts, after_names = _definition_inventory(after_tree)
    _declared_names = {
        "functions": Counter(_as_name_list(
            ctx.metadata.get("deleted_functions"))),
        "classes": Counter(_as_name_list(
            ctx.metadata.get("deleted_classes"))),
        "imports": Counter(_as_name_list(
            ctx.metadata.get("deleted_imports"))),
    }
    issues.extend(_diff_definition_counts(
        before_counts, after_counts, before_names, after_names,
        _declared_names))
    _append_split_merge_hint(ctx, issues)
    return False
def guard_ast(ctx: OperationContext) -> GuardResult:
    if ctx.operation not in _CODE_WRITE_OPS:
        return GuardResult(guard_name="G2", passed=True,
                           message="非代码修改操作,跳过 AST 检查")
    issues: list[str] = []
    after_broken = False
    method = ctx.metadata.get("method", "")
    if method == "regex":
        issues.append("检测到使用正则替换修改代码结构.正则无法正确处理 Python 语法,"
                      "建议改用 AST 遍历 + ast.NodeTransformer.")
    _gate_notes, _before, _after = _before_after_type_gate(ctx, "结构数量对比")
    if _before is not None:
        after_broken = _compare_code_structures(ctx, _before, _after, issues)
    return _code_guard_verdict(
        _GuardVerdictSpec(
            "G2", "AST 结构检查通过", "AST 结构检查",
            _guard_ast_suggestion(method, after_broken, _gate_notes),
            block_level=(method == "regex" or after_broken)),
        issues, _gate_notes)
def _iter_function_nodes(tree: ast.AST, *,
                         reset_class_depth: bool):
    stack: list[tuple[ast.AST, int]] = [
        (child, 0) for child in reversed(list(ast.iter_child_nodes(tree)))
    ]
    while stack:
        node, depth = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield node, depth
            child_depth = depth + 1
        elif isinstance(node, ast.ClassDef):
            child_depth = 0 if reset_class_depth else depth + 1
        else:
            child_depth = depth
        for child in reversed(list(ast.iter_child_nodes(node))):
            stack.append((child, child_depth))
def _function_inventory(source: str, *,
                        reset_class_depth: bool) -> dict[str, list[int]]:
    inventory: dict[str, list[int]] = {}
    tree = parse_safe(source)
    if tree is None:
        return inventory
    for node, depth in _iter_function_nodes(
            tree, reset_class_depth=reset_class_depth):
        inventory.setdefault(node.name, []).append(depth)
    return inventory
def get_function_tree(source: str) -> dict[str, int]:
    return {name: depths[-1]
            for name, depths in _function_inventory(
                source, reset_class_depth=False).items()}
def _push_pass_child(stack: list, child: ast.AST, owner: ast.AST | None,
                     per_func: dict[ast.AST, int]) -> None:
    if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
        per_func[child] = 0
        stack.append((child, child))
        return
    if isinstance(child, ast.ClassDef):
        stack.append((child, None))
        return
    if isinstance(child, ast.Pass) and owner is not None:
        per_func[owner] += 1
        return
    stack.append((child, owner))
def count_pass_statements(source: str | ast.Module) -> dict[str, int]:
    pass_counts: dict[str, int] = {}
    tree = parse_safe(source)
    if tree is None:
        return pass_counts
    per_func: dict[ast.AST, int] = {}
    stack: list[tuple[ast.AST, ast.AST | None]] = [(tree, None)]
    while stack:
        node, owner = stack.pop()
        for child in ast.iter_child_nodes(node):
            _push_pass_child(stack, child, owner, per_func)
    for func_node, count in per_func.items():
        if count > pass_counts.get(func_node.name, -1):
            pass_counts[func_node.name] = count
    return pass_counts
def _check_func_nesting(source: str | ast.Module) -> list[str]:
    issues: list[str] = []
    tree = parse_safe(source)
    if tree is None:
        return issues
    module_funcs = {
        node.name for node in iter_module_level_stmts(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }
    for node, depth in _iter_function_nodes(tree, reset_class_depth=True):
        if depth >= 1 and node.name in module_funcs:
            issues.append(
                f"函数 {node.name}(第 {node.lineno} 行) 被嵌套在其他函数内部,"
                f"且与模块级函数同名,可能是 pass 语句破坏了缩进结构"
            )
    return issues
def _lost_function_notes(before_inv: dict[str, list[int]],
                         after_inv: dict[str, list[int]],
                         deleted_functions) -> list[str]:
    before_counts = Counter({n: len(d) for n, d in before_inv.items()})
    after_counts = Counter({n: len(d) for n, d in after_inv.items()})
    lost = before_counts - after_counts
    if not lost:
        return []
    declared = Counter(_as_name_list(deleted_functions))
    undeclared = lost - declared
    if not undeclared:
        return []
    parts = [f"{n}×{c}"
             if (c > 1 or before_counts.get(n, 0) > 1) else n
             for n, c in sorted(undeclared.items())]
    return [(f"以下函数意外丢失（未在 metadata 中声明删除）: "
             f"{', '.join(parts)}")]
def _nesting_jump_notes(before_inv: dict[str, list[int]],
                        after_inv: dict[str, list[int]]) -> list[str]:
    issues: list[str] = []
    for name, before_depths in before_inv.items():
        after_depths = after_inv.get(name)
        if not after_depths:
            continue
        new_depths = Counter(after_depths) - Counter(before_depths)
        deepest_new = max(new_depths.elements(), default=None)
        if deepest_new is None or deepest_new <= 0:
            continue
        before_top = Counter(before_depths)[0]
        after_top = Counter(after_depths)[0]
        if after_top >= before_top:
            continue
        issues.append(
            f"函数 {name} 嵌套深度跃迁: 顶层实例 {before_top} → "
            f"{after_top} 个,新增嵌套形态(深度 {deepest_new}),"
            f"可能被意外嵌套"
        )
    return issues
def _diff_function_inventory(before_code: str, after_code: str,
                             deleted_functions) -> list[str]:
    before_inv = _function_inventory(before_code, reset_class_depth=True)
    after_inv = _function_inventory(after_code, reset_class_depth=True)
    issues: list[str] = []
    issues.extend(_lost_function_notes(before_inv, after_inv,
                                       deleted_functions))
    issues.extend(_nesting_jump_notes(before_inv, after_inv))
    return issues
def _scan_funcbody_issues(parse_arg) -> list[str]:
    issues: list[str] = []
    pass_counts = count_pass_statements(parse_arg)
    heavy_pass = {k: v for k, v in pass_counts.items() if v >= 5}
    if heavy_pass:
        issues.append(
            "以下函数包含大量 pass 语句 "
            "（可能是 cleanup 残留）: "
            f"{', '.join(f'{k}({v})' for k, v in heavy_pass.items())}"
        )
    issues.extend(_check_func_nesting(parse_arg))
    return issues
def guard_funcbody(ctx: OperationContext) -> GuardResult:
    if ctx.operation not in _CODE_WRITE_OPS:
        return GuardResult(guard_name="G6", passed=True,
                           message="非代码修改操作,跳过函数体检查")
    issues: list[str] = []
    type_notes, _before, _after = _before_after_type_gate(ctx, "函数清单对比")
    if _before is not None:
        issues.extend(_diff_function_inventory(
            _before, _after, ctx.metadata.get("deleted_functions")))
    for fpath, source, _tree in iter_scan_sources_with_ast(ctx):
        _parse_arg = _tree if _tree is not None else source
        issues.extend(_file_issues(fpath, _scan_funcbody_issues(_parse_arg)))
    return _code_guard_verdict(
        _GuardVerdictSpec(
            "G6", "函数体完整性检查通过", "函数体完整性检查",
            "使用 AST 解析验证函数定义层级,修复被破坏的缩进结构."),
        issues, type_notes)
def _slots_assignment(child: ast.stmt
                      ) -> tuple[list[ast.expr], ast.expr] | None:
    if isinstance(child, ast.Assign):
        return list(child.targets), child.value
    if isinstance(child, ast.AnnAssign) and child.value is not None:
        targets = [child.target] if isinstance(child.target, ast.Name) else []
        return targets, child.value
    return None
def _class_own_slots(node: ast.ClassDef) -> set[str] | None:
    last_names: set[str] | None = None
    for child in node.body:
        if (isinstance(child, ast.AugAssign)
                and isinstance(child.target, ast.Name)
                and child.target.id == "__slots__"):
            added = (_slots_value_names(child.value)
                     if isinstance(child.op, ast.Add) else None)
            last_names = (last_names | added
                          if last_names is not None and added is not None
                          else None)
            continue
        assignment = _slots_assignment(child)
        if assignment is None:
            continue
        targets, value = assignment
        if any(isinstance(target, ast.Name) and target.id == "__slots__"
               for target in targets):
            last_names = _slots_value_names(value)
    return last_names
def _slots_value_names(value: ast.expr) -> set[str] | None:
    names: set[str] = set()
    if isinstance(value, (ast.Tuple, ast.List, ast.Set)):
        elements = value.elts
    elif isinstance(value, ast.Dict):
        if any(key is None for key in value.keys):
            return None
        elements = value.keys
    elif isinstance(value, ast.Constant):
        elements = [value]
    else:
        return None
    for element in elements:
        if not isinstance(element, ast.Constant):
            return None
        if isinstance(element.value, str):
            names.add(element.value)
    return names
def _has_method_decorator(node, name: str) -> bool:
    return any(
        (isinstance(decorator, ast.Name) and decorator.id == name)
        or (isinstance(decorator, ast.Attribute) and decorator.attr == name)
        for decorator in node.decorator_list)
def _first_positional_param_name(node) -> str | None:
    positional = [*node.args.posonlyargs, *node.args.args]
    return positional[0].arg if positional else None
def _instance_receiver_name(node) -> str | None:
    if (_has_method_decorator(node, "staticmethod")
            or _has_method_decorator(node, "classmethod")):
        return None
    return _first_positional_param_name(node)
_DEFAULT_RECEIVER = "self"
def _self_attr(node: ast.AST,
              receiver: str = _DEFAULT_RECEIVER) -> ast.Attribute | None:
    if (isinstance(node, ast.Attribute)
            and isinstance(node.value, ast.Name)
            and node.value.id == receiver):
        return node
    return None
def _iter_self_attr_targets(targets, receiver: str = _DEFAULT_RECEIVER
                            ) -> Iterator[ast.Attribute]:
    for target in targets:
        yield from _iter_unpack_self_targets(target, receiver)
def _iter_unpack_self_targets(target, receiver: str = _DEFAULT_RECEIVER
                              ) -> Iterator[ast.Attribute]:
    stack = [target]
    while stack:
        cur = stack.pop()
        if isinstance(cur, (ast.Tuple, ast.List)):
            stack.extend(cur.elts)
            continue
        if isinstance(cur, ast.Starred):
            stack.append(cur.value)
            continue
        attr = _self_attr(cur, receiver)
        if attr is not None:
            yield attr
def _iter_with_item_vars(node) -> Iterator:
    for item in node.items:
        if item.optional_vars is not None:
            yield item.optional_vars
def _iter_self_attr_binds(node: ast.AST, receiver: str = _DEFAULT_RECEIVER
                          ) -> Iterator[ast.Attribute]:
    if isinstance(node, ast.Assign):
        yield from _iter_self_attr_targets(node.targets, receiver)
    elif isinstance(node, (ast.AnnAssign, ast.AugAssign, ast.For,
                           ast.AsyncFor, ast.comprehension)):
        if isinstance(node, ast.AnnAssign) and node.value is None:
            return
        yield from _iter_self_attr_targets([node.target], receiver)
    elif isinstance(node, (ast.With, ast.AsyncWith)):
        yield from _iter_self_attr_targets(
            list(_iter_with_item_vars(node)), receiver)
def _params_bind_name(args: ast.arguments, name: str) -> bool:
    params = [*args.posonlyargs, *args.args, *args.kwonlyargs]
    if args.vararg is not None:
        params.append(args.vararg)
    if args.kwarg is not None:
        params.append(args.kwarg)
    return any(param.arg == name for param in params)
def _collect_self_attrs(node: ast.AST, attrs: set,
                        receiver: str = _DEFAULT_RECEIVER) -> None:
    stack = [node]
    while stack:
        cur = stack.pop()
        for sub in ast.iter_child_nodes(cur):
            if isinstance(sub, ast.ClassDef):
                continue
            if (isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef))
                    and _params_bind_name(sub.args, receiver)):
                continue
            for attr_node in _iter_self_attr_binds(sub, receiver):
                attrs.add(attr_node.attr)
            stack.append(sub)
def _collect_class_body_self_binds(stmt: ast.AST, attrs: set) -> None:
    stack = [stmt]
    while stack:
        cur = stack.pop()
        for sub in ast.iter_child_nodes(cur):
            if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef)):
                receiver = _instance_receiver_name(sub)
                if receiver is not None:
                    _collect_self_attrs(sub, attrs, receiver)
                continue
            if isinstance(sub, ast.ClassDef):
                continue
            stack.append(sub)
_SCOPE_CLASS = "class"
_SCOPE_PLAIN = "plain"
_ScopeChain = tuple[tuple[str, dict[str, ast.ClassDef | None]], ...]
def _walk_scope_block(index: dict[int, _ScopeChain], stmts: list[ast.stmt],
                      outer: _ScopeChain, kind: str) -> None:
    local: dict[str, ast.ClassDef | None] = {}
    _walk_scope_stmts(index, stmts, (*outer, (kind, local)), local)
def _walk_scope_stmts(index: dict[int, _ScopeChain], stmts: list[ast.stmt],
                      chain: _ScopeChain,
                      local: dict[str, ast.ClassDef | None]) -> None:
    for stmt in stmts:
        if isinstance(stmt, ast.ClassDef):
            index[id(stmt)] = tuple(
                (kind, dict(scope_names)) for kind, scope_names in chain)
            _walk_scope_block(index, stmt.body, chain, _SCOPE_CLASS)
            local[stmt.name] = (None if stmt.name in local else stmt)
        elif isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_chain = tuple(
                entry for entry in chain if entry[0] != _SCOPE_CLASS)
            _walk_scope_block(index, stmt.body, func_chain, _SCOPE_PLAIN)
            local[stmt.name] = None
        else:
            shadowed_names = _stmt_writing_bound_names(stmt)
            if shadowed_names is not None:
                for name in shadowed_names:
                    local[name] = None
            elif isinstance(stmt, ast.NamedExpr):
                local[stmt.target.id] = None
            for block in iter_module_stmt_blocks(stmt):
                _walk_scope_stmts(index, block, chain, local)
def _index_class_scopes(tree: ast.Module) -> dict[int, _ScopeChain]:
    index: dict[int, _ScopeChain] = {}
    _walk_scope_block(index, tree.body, (), _SCOPE_PLAIN)
    return index
def _lookup_class(name: str, chain: _ScopeChain) -> ast.ClassDef | None:
    for _kind, classes in reversed(chain):
        if name in classes:
            return classes[name]
    return None
def _inherited_slots(cls: ast.ClassDef, base: ast.expr,
                     scopes: _ScopeChain,
                     scopes_by_class: dict[int, _ScopeChain],
                     visiting: tuple[int, ...]) -> set[str] | None:
    if not isinstance(base, ast.Name):
        return None
    if base.id == "object":
        return set()
    base_cls = _lookup_class(base.id, scopes)
    if base_cls is None:
        return set() if base.id == cls.name else None
    if id(base_cls) in visiting or base_cls is cls:
        return set()
    if _class_own_slots(base_cls) is None:
        return None
    return _effective_slots(base_cls, scopes_by_class, (*visiting, id(cls)))
def _effective_slots(cls: ast.ClassDef, scopes_by_class: dict[int, _ScopeChain],
                     _visiting: tuple[int, ...] = ()) -> set[str] | None:
    eff = set(_class_own_slots(cls) or ())
    scopes = scopes_by_class.get(id(cls), ())
    for base in cls.bases:
        parent_eff = _inherited_slots(
            cls, base, scopes, scopes_by_class, _visiting)
        if parent_eff is None:
            return None
        eff |= parent_eff
    return eff
def _collect_instance_attrs(node: ast.ClassDef) -> set[str]:
    attrs: set[str] = set()
    for child in node.body:
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
            receiver = _instance_receiver_name(child)
            if receiver is not None:
                _collect_self_attrs(child, attrs, receiver)
            continue
        if isinstance(child, ast.ClassDef):
            continue
        _collect_class_body_self_binds(child, attrs)
    return attrs
def _slots_missing_issue(node: ast.ClassDef,
                         scopes_by_class: dict[int, _ScopeChain]) -> list[str]:
    effective = _effective_slots(node, scopes_by_class)
    if effective is None or "__dict__" in effective:
        return []
    missing = _collect_instance_attrs(node) - effective
    if not missing:
        return []
    return [(f"Class {node.name} sets attrs {sorted(missing)} "
             f"in methods but not in __slots__")]
def _extract_slots_info(source: str) -> list[dict]:
    results = []
    tree = parse_safe(source)
    if tree is None:
        return results
    scopes_by_class = _index_class_scopes(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        if _class_own_slots(node) is None:
            continue
        issues = _slots_missing_issue(node, scopes_by_class)
        if issues:
            results.append({"class": node.name, "issues": issues})
    return results
def guard_slots(ctx: OperationContext) -> GuardResult:
    if ctx.operation not in _CODE_WRITE_OPS:
        return GuardResult(guard_name="G11", passed=True,
                           message="非代码修改操作,跳过 __slots__ 检查")
    issues: list[str] = []
    for fpath, source in iter_scan_sources(ctx):
        for info in _extract_slots_info(source):
            issues.extend(_file_issues(fpath, info["issues"]))
    return _code_guard_verdict(
        _GuardVerdictSpec(
            "G11", "__slots__ 检查通过", "__slots__检查",
            "在 __slots__ 中显式声明所有方法中设置的实例属性."),
        issues, [])
def _base_display_names(node: ast.ClassDef) -> list[str]:
    return [b.id if isinstance(b, ast.Name) else ast.unparse(b)
            for b in node.bases
            if isinstance(b, (ast.Name, ast.Attribute))]
def _duplicate_base_issues(node: ast.ClassDef,
                           base_names: list[str]) -> list[str]:
    comparable = [*base_names, *(ast.unparse(base.value) for base in node.bases
                                if isinstance(base, ast.Subscript))]
    counts = Counter(comparable)
    return [f"Class {node.name} has duplicate base class {bn}"
            for bn in sorted(counts) if counts[bn] > 1]
def _merge_class_entry(class_info: dict[str, dict], name: str,
                       mro_issues: list[str]) -> None:
    entry = class_info.get(name)
    if entry is None:
        class_info[name] = {"mro_issues": list(mro_issues)}
        return
    entry["mro_issues"].extend(mro_issues)
def _extract_class_info(source: str | ast.Module) -> dict[str, dict]:
    class_info: dict[str, dict] = {}
    tree = parse_safe(source)
    if tree is None:
        return class_info
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        base_names = _base_display_names(node)
        _merge_class_entry(class_info, node.name,
                           _duplicate_base_issues(node, base_names))
    return class_info
def _check_mixin_super(source: str | ast.Module) -> list[str]:
    issues = []
    tree = parse_safe(source)
    if tree is None:
        return issues
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        if "Mixin" not in node.name:
            continue
        if _mixin_calls_super_init(node):
            continue
        issues.append(
            f"Mixin 类 {node.name} 定义了 __init__ 但未调用 "
            f"super().__init__(),违反协作式多重继承规范"
        )
    return issues
def _mixin_calls_super_init(class_node: ast.ClassDef) -> bool:
    effective_init = None
    for method in iter_class_scope_methods(class_node):
        if method.name == "__init__":
            effective_init = method
    return effective_init is None or _init_calls_super(effective_init)
def _is_super_init_call(node: ast.AST) -> bool:
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "__init__"):
        return False
    recv = node.func.value
    return (isinstance(recv, ast.Call)
            and isinstance(recv.func, ast.Name)
            and recv.func.id == "super")
def _init_calls_super(init_node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    return any(_is_super_init_call(child)
               for child in _iter_own_nodes(init_node))
def _mro_issues_for_file(fpath: str, source: str) -> list[str]:
    tree = parse_safe(source)
    if tree is None:
        return []
    messages = [
        message
        for info in _extract_class_info(tree).values()
        for message in info["mro_issues"]
    ]
    messages.extend(_check_mixin_super(tree))
    return _file_issues(fpath, messages)
def _mro_fix_suggestion(issues: list[str]) -> str:
    if not issues:
        return ""
    has_dup = any("has duplicate base class" in i for i in issues)
    has_mixin = any("未调用 super().__init__()" in i for i in issues)
    if has_dup and has_mixin:
        return ("移除重复的基类声明(如 class X(A, A) 改为 class X(A));"
                "在 Mixin 类的 __init__ 末尾添加 "
                "super().__init__(*args, **kwargs),"
                "确保协作式多重继承的 MRO 链完整.")
    if has_dup:
        return ("移除重复的基类声明(如 class X(A, A) 改为 class X(A));"
                "重复基类会在类定义执行时触发 "
                "TypeError: duplicate base class.")
    return ("在 Mixin 类的 __init__ 末尾添加 "
            "super().__init__(*args, **kwargs),"
            "确保协作式多重继承的 MRO 链完整.")
def guard_mro(ctx: OperationContext) -> GuardResult:
    if ctx.operation not in _CODE_WRITE_OPS:
        return GuardResult(guard_name="G10", passed=True,
                           message="非代码修改操作,跳过 MRO 检查")
    issues = [
        issue
        for fpath, source in iter_scan_sources(ctx)
        for issue in _mro_issues_for_file(fpath, source)
    ]
    return _code_guard_verdict(
        _GuardVerdictSpec(
            "G10", "MRO 链检查通过", "MRO 链检查",
            _mro_fix_suggestion(issues),
            block_level=any("has duplicate base class" in issue
                            for issue in issues)),
        issues, [])
_MATCH_STMT_TYPE = getattr(ast, "Match", None)
def _iter_own_nodes(func_node, *, annotations_evaluated: bool = False):
    body = getattr(func_node, "body", ())
    items = list(body) if isinstance(body, list) else [body]
    stack = list(items)
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda, ast.ClassDef)):
            sites = (iter_def_site_nodes(node)
                     if annotations_evaluated or isinstance(node, ast.ClassDef)
                     else definition_time_exprs(node))
            stack.extend(sites)
            continue
        yield node
        stack.extend(ast.iter_child_nodes(node))
def _all_direct_returns_empty_dict(func_node) -> bool:
    returns = [c for c in _iter_own_nodes(func_node)
               if isinstance(c, ast.Return)]
    if not returns:
        return False
    return all(
        r.value is not None and isinstance(r.value, ast.Dict)
        and len(r.value.keys) == 0
        for r in returns
    )
def _assigned_result_names(func_node) -> set[str]:
    names: set[str] = set()
    for child in _iter_own_nodes(func_node):
        if not isinstance(child, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
            continue
        if isinstance(child, ast.AnnAssign) and child.value is None:
            continue
        targets = (child.targets if isinstance(child, ast.Assign)
                   else (child.target,))
        for target in targets:
            names.update(iter_unpack_target_names(target))
    return {n for n in names if n.strip("_")}
def _loaded_names(func_node) -> set[str]:
    parent_map = build_parent_map(func_node)
    scope_bindings = {
        id(scope): _collect_scope_bindings(scope, True)
        for scope in walk_nodes(func_node)
        if isinstance(scope, _SCOPE_NODE_TYPES)
    }
    names: set[str] = set()
    for node in walk_nodes(func_node):
        if not isinstance(node, ast.Name) or not isinstance(node.ctx, ast.Load):
            continue
        chain: list[tuple[ast.AST, ast.AST | None, ast.AST | None]] = []
        current = parent_map.get(id(node))
        child: ast.AST | None = node
        below: ast.AST | None = None
        while current is not None:
            if isinstance(current, _SCOPE_NODE_TYPES):
                chain.append((current, child, below))
            if current is func_node:
                break
            below = child
            child = current
            current = parent_map.get(id(current))
        first = True
        for scope, scope_child, scope_below in chain:
            if not _scope_owns_child(scope, scope_child):
                continue
            bound, g_decls, nl_decls = scope_bindings[id(scope)]
            if scope is func_node:
                if node.id in bound:
                    names.add(node.id)
                break
            if node.id in g_decls:
                break
            if node.id in nl_decls:
                first = False
                continue
            if not first and isinstance(scope, ast.ClassDef):
                continue
            if (isinstance(scope, _COMP_SCOPE_NODES)
                    and _is_first_comprehension_iter(
                        scope, scope_child, scope_below)):
                continue
            visible = (bound if not isinstance(scope, _COMP_SCOPE_NODES)
                       else _comprehension_visible_bindings(
                           scope, scope_child, scope_below))
            if node.id in visible:
                break
            first = False
    return names
def _has_discarded_computation(func_node) -> bool:
    return bool(_assigned_result_names(func_node) - _loaded_names(func_node))
def _find_empty_dict_return(source: str) -> list[str]:
    issues: list[str] = []
    tree = parse_safe(source)
    if tree is None:
        return issues
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if (_all_direct_returns_empty_dict(node)
                and _has_discarded_computation(node)):
            issues.append(
                f"函数 {node.name} 计算了变量但所有出口均返回空字典 {{}},"
                f"计算结果被整体丢弃"
            )
    return issues
@dataclass(frozen=True)
class _DictKeySurface:
    keys: frozenset[object]
    dynamic: bool


_UNKNOWN_DICT_KEY = object()
def _literal_dict_key(node: ast.AST | None) -> object:
    if node is None:
        return _UNKNOWN_DICT_KEY
    try:
        value = ast.literal_eval(node)
        hash(value)
    except (ValueError, TypeError, SyntaxError):
        return _UNKNOWN_DICT_KEY
    return value

def _direct_return_dict_key_sets(func_node) -> list[_DictKeySurface]:
    returns = sorted(
        (child for child in _iter_own_nodes(func_node)
         if isinstance(child, ast.Return)),
        key=lambda child: (child.lineno, child.col_offset))
    surfaces: list[_DictKeySurface] = []
    for child in returns:
        if child.value is None or not isinstance(child.value, ast.Dict):
            surfaces.append(_DictKeySurface(frozenset(), False))
            continue
        literal_keys = [_literal_dict_key(key) for key in child.value.keys]
        surfaces.append(_DictKeySurface(
            frozenset(key for key in literal_keys
                      if key is not _UNKNOWN_DICT_KEY),
            any(key is _UNKNOWN_DICT_KEY for key in literal_keys)))
    return surfaces
def _extract_return_dict_key_sets(
        code_str: str, func_name: str) -> list[_DictKeySurface] | None:
    tree = parse_safe(code_str)
    if tree is None:
        return None
    module_matches = [
        node for node in iter_module_level_stmts(tree)
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            and node.name == func_name)
    ]
    if module_matches:
        return _direct_return_dict_key_sets(module_matches[-1])
    for node in walk_nodes(tree):
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                and node.name == func_name):
            return _direct_return_dict_key_sets(node)
    return None
def _scan_affected_files_empty_dict(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    pending = _pending_write_source(ctx)
    pending_key = _result_identity(pending[0]) if pending else ""
    for fpath in _iter_valid_targets(ctx):
        if pending and _result_identity(fpath) == pending_key:
            continue
        source = _read_source_optional(ctx, fpath)
        if source is None:
            continue
        issues.extend(_file_issues(fpath, _find_empty_dict_return(source)))
    return issues
def _scan_code_to_write_empty_dict(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    code_to_write = code_to_write_str(ctx)
    if code_to_write:
        label = content_label(ctx)
        for desc in _find_empty_dict_return(code_to_write):
            issues.append(f"{label}: {desc}")
    return issues
def _minimum_cost_return_assignment(
        before_returns: list[_DictKeySurface],
        after_returns: list[_DictKeySurface]) -> list[int | None]:
    active = [index for index, surface in enumerate(before_returns)
              if surface.keys]
    assignment: list[int | None] = [None] * len(before_returns)
    if not active:
        return assignment
    row_count = len(active)
    real_columns = len(after_returns)
    column_count = real_columns + row_count
    costs = [
        [(len(before_returns[row].keys - after_surface.keys)
          if not after_surface.dynamic else 0)
         for after_surface in after_returns]
        + [len(before_returns[row].keys)] * row_count
        for row in active
    ]
    u = [0] * (row_count + 1)
    v = [0] * (column_count + 1)
    matched_row = [0] * (column_count + 1)
    previous = [0] * (column_count + 1)
    for row in range(1, row_count + 1):
        matched_row[0] = row
        column = 0
        min_values = [10 ** 9] * (column_count + 1)
        used = [False] * (column_count + 1)
        while True:
            used[column] = True
            current_row = matched_row[column]
            delta = 10 ** 9
            next_column = 0
            for candidate in range(1, column_count + 1):
                if used[candidate]:
                    continue
                current = (costs[current_row - 1][candidate - 1]
                           - u[current_row] - v[candidate])
                if current < min_values[candidate]:
                    min_values[candidate] = current
                    previous[candidate] = column
                if min_values[candidate] < delta:
                    delta = min_values[candidate]
                    next_column = candidate
            for candidate in range(column_count + 1):
                if used[candidate]:
                    u[matched_row[candidate]] += delta
                    v[candidate] -= delta
                else:
                    min_values[candidate] -= delta
            column = next_column
            if matched_row[column] == 0:
                break
        while True:
            next_column = previous[column]
            matched_row[column] = matched_row[next_column]
            column = next_column
            if column == 0:
                break
    for column, row in enumerate(matched_row):
        if row and 0 < column <= real_columns:
            assignment[active[row - 1]] = column - 1
    return assignment
def _check_before_after_key_loss(before_code: str, after_code: str,
                                 func_name: str) -> list[str]:
    before_returns = _extract_return_dict_key_sets(before_code, func_name)
    after_returns = _extract_return_dict_key_sets(after_code, func_name)
    if before_returns is None or after_returns is None:
        return []
    matched = _minimum_cost_return_assignment(before_returns, after_returns)
    issues: list[str] = []
    for index, before_surface in enumerate(before_returns, 1):
        if not before_surface.keys:
            continue
        after_index = matched[index - 1]
        after_surface = (after_returns[after_index]
                         if after_index is not None
                         else _DictKeySurface(frozenset(), False))
        lost_keys = (before_surface.keys - after_surface.keys
                     if not after_surface.dynamic else set())
        if lost_keys:
            issues.append(
                f"函数 {func_name} 第 {index} 个 return 字典丢失键: "
                f"{', '.join(sorted(str(key) for key in lost_keys))}")
    return issues
def _collect_dictret_issues(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    issues.extend(_scan_affected_files_empty_dict(ctx))
    issues.extend(_scan_code_to_write_empty_dict(ctx))
    before_code = ctx.metadata.get("before_code", "")
    after_code = ctx.metadata.get("after_code", "")
    func_name = ctx.metadata.get("function_name", "")
    if (isinstance(before_code, str) and isinstance(after_code, str)
            and isinstance(func_name, str)
            and before_code and after_code and func_name):
        issues.extend(
            _check_before_after_key_loss(before_code, after_code, func_name))
    return issues
def guard_dictret(ctx: OperationContext) -> GuardResult:
    if ctx.operation not in _CODE_WRITE_OPS:
        return GuardResult(guard_name="G9", passed=True,
                           message="非代码修改操作,跳过字典返回值检查")
    return issues_guard_result(
        "G9", "字典返回值检查", "问题", _collect_dictret_issues(ctx),
        "空字典返回:请将计算结果放入返回字典;重构丢键:请补回 return 字典中丢失的键.",
        "字典返回值检查通过",
        level=GuardLevel.WARN)
_MUTABLE_CALLS = {
    "add", "append", "extend", "update", "insert", "discard",
    "remove", "pop", "setdefault", "clear", "sort", "reverse",
    "popitem", "intersection_update", "difference_update",
    "symmetric_difference_update", "__setitem__", "__delitem__",
    "__iadd__", "__imul__", "__ior__", "__iand__", "__isub__",
    "__ixor__",
}
_COMP_SCOPE_NODES = (ast.ListComp, ast.SetComp, ast.DictComp,
                     ast.GeneratorExp)
_SCOPE_NODE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda,
                     ast.ClassDef, *_COMP_SCOPE_NODES)
_MATCH_CAPTURE_NODE_TYPES = tuple(
    t for t in (getattr(ast, "MatchAs", None),
                getattr(ast, "MatchStar", None),
                getattr(ast, "MatchMapping", None))
    if t is not None)
def _iter_match_capture_names(pattern: ast.AST) -> set[str]:
    names: set[str] = set()
    stack: list[ast.AST] = [pattern]
    while stack:
        node = stack.pop()
        if isinstance(node, _MATCH_CAPTURE_NODE_TYPES):
            _nm = getattr(node, "name", None) or getattr(node, "rest", None)
            if _nm:
                names.add(_nm)
        stack.extend(ast.iter_child_nodes(node))
    return names
def _annotations_evaluated(tree: ast.Module) -> bool:
    return not module_postpones_annotations(tree, require_absolute=True)
def _collect_scope_bindings(
        scope: ast.AST, annotations_evaluated: bool
) -> tuple[set, set, set]:
    bound: set[str] = set()
    g_decls: set[str] = set()
    nl_decls: set[str] = set()
    body = _init_scope_body(scope, bound)
    stack: list[ast.AST] = list(body)
    while stack:
        n = stack.pop()
        if _bind_nested_def(n, bound, annotations_evaluated):
            continue
        if (isinstance(n, ast.AnnAssign)
                and isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef))):
            bound.update(annassign_target_names(
                n, include_unassigned=True))
        else:
            _bind_stmt_scope_names(n, bound, g_decls, nl_decls)
        stack.extend(ast.iter_child_nodes(n))
    return bound, g_decls, nl_decls
def _collect_scope_binding_sets(
        tree: ast.Module) -> dict[int, tuple[set, set, set]]:
    result: dict[int, tuple[set, set, set]] = {}
    annotations_evaluated = _annotations_evaluated(tree)
    for scope in walk_nodes(tree):
        if isinstance(scope, _SCOPE_NODE_TYPES):
            result[id(scope)] = _collect_scope_bindings(
                scope, annotations_evaluated)
    return result
def _init_scope_body(scope: ast.AST, bound: set) -> list:
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                          ast.Lambda)):
        args = scope.args
        for arg in (*args.posonlyargs, *args.args, *args.kwonlyargs):
            bound.add(arg.arg)
        if args.vararg is not None:
            bound.add(args.vararg.arg)
        if args.kwarg is not None:
            bound.add(args.kwarg.arg)
        return ([scope.body] if isinstance(scope, ast.Lambda)
                else list(scope.body))
    if isinstance(scope, (ast.ListComp, ast.SetComp, ast.DictComp,
                          ast.GeneratorExp)):
        for gen in scope.generators:
            bound.update(iter_unpack_target_names(gen.target))
        return []
    return list(scope.body)
def _bind_nested_def(
        n: ast.AST, bound: set, annotations_evaluated: bool) -> bool:
    if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef,
                      ast.Lambda, ast.ClassDef)):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            bound.add(n.name)
        bound.update(_definition_site_walrus_names(
            n, annotations_evaluated))
        return True
    return False
def _assign_target_names(
        node: ast.Assign | ast.For | ast.AsyncFor) -> set[str]:
    names: set[str] = set()
    targets = node.targets if isinstance(node, ast.Assign) else (node.target,)
    for target in targets:
        names.update(iter_unpack_target_names(target))
    return names
def _delete_target_names(node: ast.Delete) -> set[str]:
    names: set[str] = set()
    for target in node.targets:
        names.update(iter_unpack_target_names(target))
    return names
def _with_target_names(node) -> set[str]:
    names: set[str] = set()
    for item in node.items:
        if item.optional_vars is not None:
            names.update(iter_unpack_target_names(item.optional_vars))
    return names
def _match_capture_names_of(node) -> set[str]:
    names: set[str] = set()
    for case in node.cases:
        names.update(_iter_match_capture_names(case.pattern))
    return names
def _except_target_names(n: ast.ExceptHandler) -> set[str]:
    return {n.name} if n.name else set()
_WRITING_BOUND_NAME_HANDLERS = (
    ((ast.Assign, ast.For, ast.AsyncFor), _assign_target_names),
    ((ast.Delete,), _delete_target_names),
    ((ast.AnnAssign,), annassign_target_names),
    ((ast.AugAssign,), augassign_target_names),
    ((ast.With, ast.AsyncWith), _with_target_names),
    ((ast.ExceptHandler,), _except_target_names),
    ((ast.Import, ast.ImportFrom), _import_binding_names),
)
def _stmt_writing_bound_names(n: ast.AST) -> set[str] | None:
    for node_types, handler in _WRITING_BOUND_NAME_HANDLERS:
        if isinstance(n, node_types):
            return handler(n)
    if _MATCH_STMT_TYPE is not None and isinstance(n, _MATCH_STMT_TYPE):
        return _match_capture_names_of(n)
    return None
def _bind_stmt_scope_names(n: ast.AST, bound: set, g_decls: set,
                           nl_decls: set) -> None:
    stmt_names = _stmt_writing_bound_names(n)
    if stmt_names is not None:
        bound.update(stmt_names)
        return
    if isinstance(n, ast.Global):
        g_decls.update(n.names)
    elif isinstance(n, ast.Nonlocal):
        nl_decls.update(n.names)
    elif isinstance(n, ast.NamedExpr):
        bound.add(n.target.id)
def _parse_guarded_code(ctx: OperationContext, guard_name: str,
                        op_skip_msg: str) -> tuple:
    if ctx.operation not in _CODE_WRITE_OPS:
        return None, GuardResult(guard_name=guard_name, passed=True,
                                 message=op_skip_msg)
    code = code_to_write_str(ctx)
    if not code:
        return None, GuardResult(guard_name=guard_name, passed=True,
                                 message="无待写入代码,跳过")
    tree = parse_safe(code)
    if tree is None:
        return None, GuardResult(guard_name=guard_name, passed=True,
                                 message="代码无法解析,跳过")
    return tree, None
_MODULE_SCOPE_DEFINITIONS = (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)
def _module_binding_inventory(tree: ast.Module) -> tuple[set[str], set[str]]:
    imported: set[str] = set()
    state: set[str] = set()
    annotations_evaluated = _annotations_evaluated(tree)
    stack: list[ast.AST] = list(tree.body)
    while stack:
        node = stack.pop()
        if isinstance(node, _MODULE_SCOPE_DEFINITIONS):
            state.add(node.name)
            state.update(_definition_site_walrus_names(
                node, annotations_evaluated))
            continue
        if isinstance(node, ast.Lambda):
            state.update(_definition_site_walrus_names(
                node, annotations_evaluated))
            continue
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            imported.update(_import_binding_names(node))
            continue
        names = _stmt_writing_bound_names(node)
        if names is not None:
            state.update(names)
        elif isinstance(node, ast.NamedExpr):
            state.add(node.target.id)
        stack.extend(ast.iter_child_nodes(node))
    builtin_names = set(dir(builtins))
    for declared in walk_nodes(tree):
        if not isinstance(declared, ast.Global):
            continue
        for global_name in declared.names:
            if global_name not in imported and global_name not in builtin_names:
                state.add(global_name)
    return imported, state
def _module_state_names(tree: ast.Module) -> frozenset[str]:
    _imported, state = _module_binding_inventory(tree)
    return frozenset(state)
def _prepare_scope_maps(tree: ast.Module) -> tuple:
    return (build_parent_map(tree), _collect_scope_binding_sets(tree),
            _module_state_names(tree))
def _scope_owns_child(scope: ast.AST, child: ast.AST | None) -> bool:
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                          ast.ClassDef)):
        return child in scope.body
    if isinstance(scope, ast.Lambda):
        return child is scope.body
    return True
def _is_first_comprehension_iter(scope: ast.AST,
                                 child: ast.AST | None,
                                 below: ast.AST | None) -> bool:
    generators = getattr(scope, "generators", ()) or ()
    return (bool(generators) and child is generators[0]
            and below is generators[0].iter)
def _comprehension_visible_bindings(scope: ast.AST, child: ast.AST | None,
                                   below: ast.AST | None) -> set[str]:
    generators = getattr(scope, "generators", ()) or ()
    elt = getattr(scope, "elt", None)
    def _targets(items) -> set[str]:
        names: set[str] = set()
        for item in items:
            names.update(iter_unpack_target_names(item.target))
        return names
    if child is elt:
        return _targets(generators)
    for index, generator in enumerate(generators):
        if child is not generator:
            continue
        if below is generator.iter:
            return _targets(generators[:index])
        return _targets(generators[:index + 1])
    return _targets(generators)
def _class_binding_precedes(scope: ast.ClassDef, name: str,
                            node: ast.AST, parent_map: dict) -> bool:
    root: ast.AST = scope
    while parent_map.get(id(root)) is not None:
        root = parent_map[id(root)]
    annotations_evaluated = (_annotations_evaluated(root)
                             if isinstance(root, ast.Module) else True)
    target_position = (node.lineno, node.col_offset)
    stack: list[ast.AST] = list(scope.body)
    while stack:
        current = stack.pop()
        current_line = getattr(current, "lineno", None)
        if current_line is not None:
            current_position = (current_line, current.col_offset)
            if current_position >= target_position:
                continue
        bound: set[str] = set()
        g_decls: set[str] = set()
        nl_decls: set[str] = set()
        if _bind_nested_def(current, bound, annotations_evaluated):
            if name in bound:
                return True
            continue
        _bind_stmt_scope_names(current, bound, g_decls, nl_decls)
        if name in bound:
            return True
        stack.extend(ast.iter_child_nodes(current))
    return False
def _is_module_global_ref(node: ast.AST, name: str, parent_map: dict,
                          scope_bindings: dict,
                          state_names: frozenset[str]) -> bool:
    chain: list[tuple[ast.AST, ast.AST | None, ast.AST | None]] = []
    cur = parent_map.get(id(node))
    child: ast.AST | None = node
    below: ast.AST | None = None
    while cur is not None:
        if isinstance(cur, _SCOPE_NODE_TYPES):
            chain.append((cur, child, below))
        below = child
        child = cur
        cur = parent_map.get(id(cur))
    first = True
    for scope, scope_child, scope_below in chain:
        if not _scope_owns_child(scope, scope_child):
            continue
        bound, g_decls, nl_decls = scope_bindings[id(scope)]
        if name in g_decls:
            return name in state_names
        if name in nl_decls:
            return False
        if not first and isinstance(scope, ast.ClassDef):
            continue
        if (isinstance(scope, _COMP_SCOPE_NODES)
                and _is_first_comprehension_iter(
                    scope, scope_child, scope_below)):
            continue
        visible = (bound if not isinstance(scope, _COMP_SCOPE_NODES)
                   else _comprehension_visible_bindings(
                       scope, scope_child, scope_below))
        if name in visible:
            if (first and isinstance(scope, ast.ClassDef)
                    and not _class_binding_precedes(
                        scope, name, node, parent_map)):
                first = False
                continue
            return False
        first = False
    return name in state_names
def _root_global_name(node) -> ast.Name | None:
    while isinstance(node, (ast.Subscript, ast.Attribute, ast.Starred,
                            ast.NamedExpr)):
        node = node.target if isinstance(node, ast.NamedExpr) else node.value
    return node if isinstance(node, ast.Name) else None
def _global_access_label(target) -> str:
    parts: list[str] = []
    cur = target
    while True:
        if isinstance(cur, ast.Name):
            parts.append(cur.id)
            break
        if isinstance(cur, ast.Subscript):
            parts.append("[...]")
            cur = cur.value
            continue
        if isinstance(cur, ast.Attribute):
            parts.append("." + cur.attr)
            cur = cur.value
            continue
        if isinstance(cur, ast.Starred):
            cur = cur.value
            continue
        if isinstance(cur, ast.NamedExpr):
            cur = cur.target
            continue
        parts.append("[...]")
        break
    return "".join(reversed(parts))
def _global_mutation_target(node, target, parent_map: dict,
                            scope_bindings: dict,
                            state_names: frozenset[str]) -> str | None:
    root = _root_global_name(target)
    if root is None:
        return None
    if not _is_module_global_ref(
            node, root.id, parent_map, scope_bindings, state_names):
        return None
    return _global_access_label(target)
def _mutable_call_issue(node: ast.Call, parent_map: dict,
                        scope_bindings: dict,
                        state_names: frozenset[str]) -> str | None:
    attr_name = node.func.attr
    if attr_name not in _MUTABLE_CALLS:
        return None
    label = _global_mutation_target(
        node, node.func.value, parent_map, scope_bindings, state_names)
    if label is None:
        return None
    return (f"行 {getattr(node, 'lineno', '?')}: 模块级全局 "
            f"'{label}.{attr_name}()' 可能无锁保护")
def _declares_global(node: ast.AST, name: str, parent_map: dict,
                     scope_bindings: dict) -> bool:
    cur = parent_map.get(id(node))
    child: ast.AST | None = node
    while cur is not None:
        if (isinstance(cur, _SCOPE_NODE_TYPES)
                and _scope_owns_child(cur, child)):
            _bound, g_decls, nl_decls = scope_bindings[id(cur)]
            if name in g_decls:
                return True
            if name in nl_decls or name in _bound:
                return False
        child = cur
        cur = parent_map.get(id(cur))
    return False
def _assign_target_issue(node, tgt, parent_map: dict,
                         scope_bindings: dict,
                         state_names: frozenset[str]) -> str | None:
    label = _global_mutation_target(
        node, tgt, parent_map, scope_bindings, state_names)
    if label is None:
        return None
    if isinstance(tgt, ast.Name):
        if isinstance(node, ast.AugAssign):
            return (f"行 {getattr(node, 'lineno', '?')}: 模块级全局 "
                    f"'{label}' 增强赋值（读-改-写）可能无锁保护")
        if not _declares_global(node, tgt.id, parent_map, scope_bindings):
            return None
        return (f"行 {getattr(node, 'lineno', '?')}: 模块级全局 "
                f"'{label}' 赋值可能无锁保护")
    action = "增强赋值（读-改-写）" if isinstance(node, ast.AugAssign) else "赋值"
    return (f"行 {getattr(node, 'lineno', '?')}: 模块级全局 "
            f"'{label}' {action}可能无锁保护")
def _iter_target_leaves(target: ast.expr) -> Iterator[ast.expr]:
    if isinstance(target, (ast.Tuple, ast.List)):
        for elt in target.elts:
            yield from _iter_target_leaves(elt)
    elif isinstance(target, ast.Starred):
        yield from _iter_target_leaves(target.value)
    else:
        yield target
def _mutation_target_exprs(node: ast.AST) -> tuple[ast.expr, ...] | None:
    if isinstance(node, ast.Assign):
        return tuple(node.targets)
    if isinstance(node, ast.AnnAssign):
        return None if node.value is None else (node.target,)
    if isinstance(node, (ast.AugAssign, ast.For, ast.AsyncFor,
                         ast.comprehension, ast.NamedExpr)):
        return (node.target,)
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return tuple(item.optional_vars for item in node.items
                     if item.optional_vars is not None)
    if isinstance(node, ast.Delete):
        return tuple(node.targets)
    return None
def _iter_mutation_targets(node: ast.AST) -> Iterator[ast.expr]:
    for target in _mutation_target_exprs(node) or ():
        yield from _iter_target_leaves(target)
def _mutation_target_issues(node: ast.AST, parent_map: dict,
                            scope_bindings: dict,
                            state_names: frozenset[str]) -> list[str]:
    issues: list[str] = []
    for target in _iter_mutation_targets(node):
        if isinstance(node, ast.Delete):
            label = _global_mutation_target(
                node, target, parent_map, scope_bindings, state_names)
            if label is not None:
                issues.append(
                    f"行 {getattr(node, 'lineno', '?')}: 模块级全局 "
                    f"'{label}' 删除操作可能无锁保护")
            continue
        issue = _assign_target_issue(
            node, target, parent_map, scope_bindings, state_names)
        if issue is not None:
            issues.append(issue)
    return issues
_MUTATION_TARGET_NODE_TYPES = (
    ast.Assign, ast.AnnAssign, ast.AugAssign, ast.Delete,
    ast.For, ast.AsyncFor, ast.With, ast.AsyncWith, ast.comprehension,
    ast.NamedExpr,
)
def _is_lock_context_expr(node: ast.AST) -> bool:
    if isinstance(node, ast.Call):
        node = node.func
    if isinstance(node, ast.Name):
        name = node.id
    elif isinstance(node, ast.Attribute):
        name = node.attr
    else:
        return False
    normalized = name.casefold()
    return (normalized == "lock" or normalized.endswith("_lock")
            or name.endswith("Lock"))
def _has_enclosing_lock(node: ast.AST, parent_map: dict) -> bool:
    current: ast.AST | None = node
    child: ast.AST | None = None
    below: ast.AST | None = None
    while current is not None:
        if isinstance(current, (ast.With, ast.AsyncWith)):
            acquired = current.items
            if child not in current.body:
                item_index = next((i for i, item in enumerate(current.items)
                                   if item is child), None)
                acquired = (current.items[:item_index]
                            if item_index is not None else ())
                if (item_index is not None
                        and below is current.items[item_index].optional_vars):
                    acquired = current.items[:item_index + 1]
            if any(_is_lock_context_expr(item.context_expr)
                   for item in acquired):
                return True
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if child in current.body:
                return False
        elif ((isinstance(current, ast.Lambda) and child is current.body)
                or (isinstance(current, ast.GeneratorExp)
                    and not _is_first_comprehension_iter(
                        current, child, below))):
            return False
        below, child, current = child, current, parent_map.get(id(current))
    return False
def _find_unlocked_global_writes(tree: ast.Module) -> list:
    parent_map, scope_bindings, state_names = _prepare_scope_maps(tree)
    issues: list[str] = []
    for node in walk_nodes(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            _msg = _mutable_call_issue(
                node, parent_map, scope_bindings, state_names)
            if (_msg is not None
                    and not _has_enclosing_lock(node, parent_map)):
                issues.append(_msg)
        if isinstance(node, _MUTATION_TARGET_NODE_TYPES):
            mutation_issues = _mutation_target_issues(
                node, parent_map, scope_bindings, state_names)
            if mutation_issues and not _has_enclosing_lock(node, parent_map):
                issues.extend(mutation_issues)
    return issues
def guard_concurrent_state(ctx: OperationContext) -> GuardResult:
    tree, _skip = _parse_guarded_code(ctx, "G25", "非代码修改,跳过并发检查")
    if tree is None:
        return _skip
    return issues_guard_result(
        "G25", "并发状态检查", "无锁全局修改",
        _find_unlocked_global_writes(tree),
        "用 threading.Lock() 保护模块级可变全局的读写，"
        "或改用局部容器后一次性赋值",
        "并发状态检查通过",
        level=GuardLevel.WARN)
def _except_handler_names(type_node) -> list[str]:
    if isinstance(type_node, ast.Name):
        return [type_node.id]
    if isinstance(type_node, ast.Attribute):
        return [type_node.attr]
    if isinstance(type_node, ast.Tuple):
        return [name for elt in type_node.elts
                for name in _except_handler_names(elt)]
    if (isinstance(type_node, ast.BinOp)
            and isinstance(type_node.op, ast.BitOr)):
        return [*_except_handler_names(type_node.left),
                *_except_handler_names(type_node.right)]
    return []
def _is_class_scope_function(node, parent_map: dict) -> bool:
    current = parent_map.get(id(node))
    while current is not None:
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda)):
            return False
        if isinstance(current, ast.ClassDef):
            return True
        current = parent_map.get(id(current))
    return False
def _is_static_method(node) -> bool:
    return _has_method_decorator(node, "staticmethod")
@dataclass(frozen=True)
class _RecursionMethodContext:
    receiver_param: str | None
    class_name: str | None
    class_name_shadowed: bool
    @property
    def receiver_names(self) -> tuple[str, ...]:
        return ((self.receiver_param,) if self.receiver_param is not None
                else ())
def _is_recursive_call(node: ast.Call, fname: str, is_method: bool,
                       name_shadowed: bool,
                       method: _RecursionMethodContext | None = None) -> bool:
    if (not is_method and not name_shadowed
            and isinstance(node.func, ast.Name) and node.func.id == fname):
        return True
    if not (is_method and isinstance(node.func, ast.Attribute)
            and node.func.attr == fname
            and isinstance(node.func.value, ast.Name)):
        return False
    receiver = node.func.value.id
    if method is None:
        return receiver in ("self", "cls")
    if receiver in method.receiver_names:
        return True
    return (not method.class_name_shadowed
            and receiver == method.class_name)
def _recursive_calls(node, fname: str, is_method: bool,
                     name_shadowed: bool,
                     annotations_evaluated: bool = False,
                     method: _RecursionMethodContext | None = None
                     ) -> list[ast.Call]:
    return [
        child for child in _iter_own_nodes(
            node, annotations_evaluated=annotations_evaluated)
        if isinstance(child, ast.Call) and _is_recursive_call(
            child, fname, is_method, name_shadowed, method)
    ]
_TRY_NODE_TYPES = tuple(
    node_type for node_type in (ast.Try, getattr(ast, "TryStar", None))
    if node_type is not None)
def _call_has_recursion_handler(call: ast.Call, function_node,
                                parent_map: dict) -> bool:
    current: ast.AST = call
    while current is not function_node:
        parent = parent_map.get(id(current))
        if parent is None:
            break
        if isinstance(parent, _TRY_NODE_TYPES) and current in parent.body:
            for handler in parent.handlers:
                if (handler.type is not None
                        and "RecursionError" in _except_handler_names(
                            handler.type)):
                    return True
        current = parent
    return False
_DEPTH_GUARD_PARAM_NAMES = frozenset({
    "depth", "max_depth", "remaining_depth", "current_depth",
    "recursion_depth", "max_recursion_depth", "depth_limit",
    "max_depth_limit", "depth_budget", "maxdepth",
})
def _is_depth_guard_param(name: str) -> bool:
    lowered = name.lower()
    return (lowered in _DEPTH_GUARD_PARAM_NAMES
            or lowered.endswith(("_depth", "_depth_limit", "_depth_budget")))
def _is_nonrecursive_base_exit(statement: ast.stmt, fname: str,
                               is_method: bool, name_shadowed: bool,
                               method: _RecursionMethodContext | None = None
                               ) -> bool:
    if not isinstance(statement, (ast.Return, ast.Raise)):
        return False
    return not any(
        isinstance(child, ast.Call) and _is_recursive_call(
            child, fname, is_method, name_shadowed, method)
        for child in _iter_test_nodes(statement))
def _iter_test_nodes(test: ast.AST) -> Iterator[ast.AST]:
    stack = [test]
    while stack:
        current = stack.pop()
        if isinstance(current, ast.Lambda):
            stack.extend(current.args.defaults)
            stack.extend(default for default in current.args.kw_defaults
                         if default is not None)
            continue
        yield current
        stack.extend(ast.iter_child_nodes(current))
def _iter_sufficient_base_tests(test: ast.AST) -> Iterator[ast.AST]:
    if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.Or):
        for value in test.values:
            yield from _iter_sufficient_base_tests(value)
        return
    yield test
def _numeric_argument_defaults(node) -> dict[str, int | float]:
    defaults: dict[str, int | float] = {}
    positional = [*node.args.posonlyargs, *node.args.args]
    if node.args.defaults:
        for parameter, expression in zip(
                positional[-len(node.args.defaults):], node.args.defaults):
            value = _signed_numeric_constant(expression)
            if value is not None:
                defaults[parameter.arg] = value
    for parameter, expression in zip(
            node.args.kwonlyargs, node.args.kw_defaults):
        if expression is None:
            continue
        value = _signed_numeric_constant(expression)
        if value is not None:
            defaults[parameter.arg] = value
    return defaults
def _recursive_call_arguments(
        node, call: ast.Call,
        method: _RecursionMethodContext | None = None
        ) -> dict[str, ast.expr] | None:
    if (any(isinstance(value, ast.Starred) for value in call.args)
            or any(keyword.arg is None for keyword in call.keywords)):
        return None
    positional = [*node.args.posonlyargs, *node.args.args]
    positional_names = [parameter.arg for parameter in positional]
    call_args = call.args
    if isinstance(call.func, ast.Attribute) and positional_names:
        if method is None:
            drop_receiver = (
                isinstance(call.func.value, ast.Name)
                and call.func.value.id in ("self", "cls")
                and positional_names[0] == call.func.value.id)
        else:
            drop_receiver = (
                method.receiver_param is not None
                and positional_names[0] == method.receiver_param)
        if drop_receiver:
            positional_names = positional_names[1:]
            if (method is not None
                    and isinstance(call.func.value, ast.Name)
                    and call.func.value.id == method.class_name
                    and call.func.value.id not in method.receiver_names):
                call_args = call_args[1:]
    arguments = dict(zip(positional_names, call_args))
    arguments.update({
        keyword.arg: keyword.value for keyword in call.keywords
        if keyword.arg is not None
    })
    return arguments
def _depth_base_guards(
        node, depth_names: set[str], fname: str,
        is_method: bool, name_shadowed: bool, target_call: ast.Call,
        annotations_evaluated: bool = False,
        method: _RecursionMethodContext | None = None) -> list[tuple]:
    guards: list[tuple] = []
    defaults = _numeric_argument_defaults(node)
    all_calls = [target_call]
    parent_map = build_parent_map(node)
    for candidate in _iter_own_nodes(
            node, annotations_evaluated=annotations_evaluated):
        if not isinstance(candidate, ast.If):
            continue
        candidate_position = (candidate.lineno, candidate.col_offset)
        if any((call.lineno, call.col_offset) < candidate_position
               and (_depth_update_dominates_node(
                       call, candidate, node, parent_map)
                    or _constant_recursion_blocks_later_base(
                        call, candidate, node, parent_map))
               for call in all_calls):
            continue
        if any(not _depth_update_dominates_node(
                candidate, call, node, parent_map) for call in all_calls):
            continue
        guard_defaults = dict(defaults)
        candidate_updates = _depth_updates_before_node(
            node, candidate, depth_names)
        for name, step in candidate_updates.items():
            if step is None:
                guard_defaults.pop(name, None)
            elif name in guard_defaults:
                guard_defaults[name] += step
        base_exits = [
            statement for statement in candidate.body
            if _is_nonrecursive_base_exit(
                statement, fname, is_method, name_shadowed, method)
        ]
        if not base_exits:
            continue
        first_exit = min(
            (statement.lineno, statement.col_offset)
            for statement in base_exits)
        if any((call.lineno, call.col_offset) < first_exit
               for call in _recursive_calls(
                   candidate, fname, is_method, name_shadowed,
                   annotations_evaluated, method)):
            continue
        test_calls = [
            current for current in _iter_test_nodes(candidate.test)
            if isinstance(current, ast.Call) and _is_recursive_call(
                current, fname, is_method, name_shadowed, method)
        ]
        for test in _iter_sufficient_base_tests(candidate.test):
            test_position = (test.lineno, test.col_offset)
            if any((call.lineno, call.col_offset) < test_position
                   for call in test_calls):
                continue
            if any(isinstance(current, ast.Call) and _is_recursive_call(
                    current, fname, is_method, name_shadowed, method)
                   for current in _iter_test_nodes(test)):
                continue
            guards.append((
                test, dict(defaults), dict(guard_defaults),
                dict(candidate_updates)))
    return guards

def _signed_numeric_constant(node) -> int | float | None:
    sign = 1
    if isinstance(node, ast.UnaryOp) and isinstance(
            node.op, (ast.UAdd, ast.USub)):
        sign = -1 if isinstance(node.op, ast.USub) else 1
        node = node.operand
    if (not isinstance(node, ast.Constant)
            or isinstance(node.value, bool)
            or not isinstance(node.value, (int, float))
            or not math.isfinite(node.value)):
        return None
    return sign * node.value
def _depth_expression_step(expression, name: str) -> int | float | None:
    if isinstance(expression, ast.Name) and expression.id == name:
        return 0
    if not isinstance(expression, ast.BinOp):
        return None
    left_name = (isinstance(expression.left, ast.Name)
                 and expression.left.id == name)
    right_name = (isinstance(expression.right, ast.Name)
                  and expression.right.id == name)
    if left_name and isinstance(expression.op, (ast.Add, ast.Sub)):
        step = _signed_numeric_constant(expression.right)
        if step is not None and isinstance(expression.op, ast.Sub):
            step = -step
        return step
    if right_name and isinstance(expression.op, ast.Add):
        return _signed_numeric_constant(expression.left)
    return None
def _same_statement_block(owner: ast.AST, update_child: ast.AST,
                          call: ast.AST, parent_map: dict) -> bool:
    call_child: ast.AST | None = call
    while call_child is not None and parent_map.get(
            id(call_child)) is not owner:
        call_child = parent_map.get(id(call_child))
    if call_child is None:
        return False
    for _field_name, field_value in ast.iter_fields(owner):
        if (isinstance(field_value, list)
                and any(item is update_child for item in field_value)
                and any(item is call_child for item in field_value)):
            return True
    return False
def _depth_update_dominates_node(update: ast.AST, target: ast.AST,
                                 function_node: ast.AST,
                                 parent_map: dict) -> bool:
    if ((update.lineno, update.col_offset)
            >= (target.lineno, target.col_offset)):
        return False
    conditional_ancestors = (
        ast.If, ast.For, ast.AsyncFor, ast.While, ast.Match,
        ast.ExceptHandler, ast.With, ast.AsyncWith, *_TRY_NODE_TYPES,
    )
    current = update
    while current is not function_node:
        owner = parent_map.get(id(current))
        if owner is None:
            return False
        if owner is function_node:
            return True
        if (isinstance(owner, conditional_ancestors)
                and not _same_statement_block(
                    owner, current, target, parent_map)):
            return False
        current = owner
    return False
def _loop_has_own_break(loop_node: ast.While, call: ast.Call) -> bool:
    call_position = (call.lineno, call.col_offset)
    stack = list(loop_node.body)
    while stack:
        current = stack.pop()
        if isinstance(current, ast.Break):
            if (current.lineno, current.col_offset) < call_position:
                return True
            continue
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda, ast.ClassDef, ast.For,
                                ast.AsyncFor, ast.While)):
            continue
        stack.extend(ast.iter_child_nodes(current))
    return False
def _constant_recursion_blocks_later_base(
        call: ast.Call, candidate: ast.If, function_node: ast.AST,
        parent_map: dict) -> bool:
    current: ast.AST = call
    conditional_call = False
    while current is not function_node:
        owner = parent_map.get(id(current))
        if owner is None:
            return False
        constant_body = (
            isinstance(owner, (ast.If, ast.While))
            and current in owner.body
            and isinstance(owner.test, ast.Constant)
            and bool(owner.test.value))
        if constant_body:
            unconditional_block = isinstance(owner, ast.While) or not conditional_call
            if (unconditional_block
                    and not (isinstance(owner, ast.While)
                             and _loop_has_own_break(owner, call))
                    and _depth_update_dominates_node(
                        owner, candidate, function_node, parent_map)):
                return True
        elif isinstance(owner, (ast.If, ast.For, ast.AsyncFor, ast.While,
                                ast.Match)):
            conditional_call = True
        current = owner
    return False
def _depth_updates_before_node(node, target: ast.AST,
                               depth_names: set[str]) -> dict:
    target_position = (target.lineno, target.col_offset)
    parent_map = build_parent_map(node)
    updates: dict[str, int | float | None] = {}
    def _record(name: str, step: float | None) -> None:
        previous = updates.get(name, 0)
        if previous is None or step is None:
            updates[name] = None
        else:
            updates[name] = previous + step
    for child in _iter_own_nodes(node):
        if not isinstance(child, (ast.AugAssign, ast.Assign, ast.AnnAssign)):
            continue
        if (child.lineno, child.col_offset) >= target_position:
            continue
        if not _depth_update_dominates_node(
                child, target, node, parent_map):
            continue
        if (isinstance(child, ast.AugAssign)
                and isinstance(child.target, ast.Name)
                and child.target.id in depth_names):
            step = _signed_numeric_constant(child.value)
            if step is not None and isinstance(child.op, ast.Sub):
                step = -step
            elif not isinstance(child.op, (ast.Add, ast.Sub)):
                step = None
            _record(child.target.id, step)
            continue
        if not isinstance(child, (ast.Assign, ast.AnnAssign)):
            continue
        value = child.value
        targets = child.targets if isinstance(child, ast.Assign) else [child.target]
        for assign_target in targets:
            if (isinstance(assign_target, ast.Name)
                    and assign_target.id in depth_names):
                _record(
                    assign_target.id,
                    _depth_expression_step(value, assign_target.id))
    return updates
class _DepthProgressProbe:
    """递归深度守卫的「是否向哨兵推进」判定器。

    ``_call_has_depth_progress`` 原本把 9 个闭包塞在一个 222 行的函数体里，
    按「取值 → 比较 → 单守卫判定 → 合取判定」四段拆成方法后每段都可独立
    阅读，语义与原闭包实现逐字等价（``call_arguments`` / ``depth_names`` /
    ``updates`` 三个捕获变量下沉为实例属性）。
    """

    __slots__ = ('call_arguments', 'depth_names', 'updates')

    def __init__(self, call_arguments: dict, depth_names: set,
                 updates: dict) -> None:
        self.call_arguments = call_arguments
        self.depth_names = depth_names
        self.updates = updates

    def _argument_step(self, name: str) -> tuple[bool, int | float | None]:
        value = self.call_arguments.get(name)
        if value is None:
            return False, None
        update_step = self.updates.get(name, 0)
        if update_step is None:
            return True, None
        if isinstance(value, ast.Name) and value.id == name:
            return True, update_step
        expression_step = _depth_expression_step(value, name)
        if expression_step is None:
            return True, None
        return True, update_step + expression_step

    def _comparison_value(self, expression, values):
        if (isinstance(expression, ast.Name)
                and expression.id in self.depth_names):
            return values.get(expression.id)
        return _signed_numeric_constant(expression)

    def _comparison_holds(self, left, operator, right, values) -> bool:
        left_value = self._comparison_value(left, values)
        right_value = self._comparison_value(right, values)
        if left_value is None or right_value is None:
            return False
        if isinstance(operator, ast.Gt):
            return left_value > right_value
        if isinstance(operator, ast.GtE):
            return left_value >= right_value
        if isinstance(operator, ast.Lt):
            return left_value < right_value
        if isinstance(operator, ast.LtE):
            return left_value <= right_value
        if isinstance(operator, ast.Eq):
            return left_value == right_value
        if isinstance(operator, ast.NotEq):
            return left_value != right_value
        return False

    def _holds(self, test, values) -> bool:
        if isinstance(test, ast.BoolOp):
            results = (self._holds(value, values) for value in test.values)
            return (all(results) if isinstance(test.op, ast.And)
                    else any(results))
        if (isinstance(test, ast.UnaryOp)
                and isinstance(test.op, ast.Not)
                and isinstance(test.operand, ast.Name)
                and test.operand.id in self.depth_names):
            return values.get(test.operand.id) == 0
        return (isinstance(test, ast.Compare) and len(test.ops) == 1
                and len(test.comparators) == 1
                and self._comparison_holds(
                    test.left, test.ops[0], test.comparators[0], values))

    def _next_guard_values(self, defaults, guard_defaults,
                           candidate_updates) -> dict[str, int | float]:
        values: dict[str, int | float] = {}
        for name in self.depth_names:
            argument = self.call_arguments.get(name)
            if argument is None:
                value = defaults.get(name)
                step = candidate_updates.get(name, 0)
                if value is not None and step is not None:
                    values[name] = value + step
                continue
            constant = _signed_numeric_constant(argument)
            if constant is not None:
                step = candidate_updates.get(name, 0)
                if step is not None:
                    values[name] = constant + step
                continue
            supplied, step = self._argument_step(name)
            start = guard_defaults.get(name)
            if supplied and step is not None and start is not None:
                values[name] = start + step
        return values

    def _side_step(self, expression):
        if (isinstance(expression, ast.Name)
                and expression.id in self.depth_names):
            supplied, step = self._argument_step(expression.id)
            return step if supplied else None
        if _signed_numeric_constant(expression) is not None:
            return 0
        return None

    def _relative_step(self, left, right):
        left_step = self._side_step(left)
        right_step = self._side_step(right)
        if left_step is None or right_step is None:
            return None
        return left_step - right_step

    def _single_progress(self, test, values, guard_defaults) -> bool:
        if self._holds(test, values):
            return True
        if (isinstance(test, ast.UnaryOp)
                and isinstance(test.op, ast.Not)
                and isinstance(test.operand, ast.Name)
                and test.operand.id in self.depth_names):
            name = test.operand.id
            supplied, step = self._argument_step(name)
            return (supplied and _reaches_sentinel(
                guard_defaults.get(name), 0, step))
        if not (isinstance(test, ast.Compare) and len(test.ops) == 1
                and len(test.comparators) == 1):
            return False
        return self._compare_progress(
            test.left, test.ops[0], test.comparators[0], guard_defaults)

    def _compare_progress(self, left, operator, right, guard_defaults) -> bool:
        left_name = (left.id if isinstance(left, ast.Name)
                     and left.id in self.depth_names else None)
        right_name = (right.id if isinstance(right, ast.Name)
                      and right.id in self.depth_names else None)
        if left_name is None and right_name is None:
            return False
        if isinstance(operator, (ast.Eq, ast.NotEq)):
            return self._equality_progress(
                left, left_name, operator, right, right_name, guard_defaults)
        if not isinstance(operator, (ast.Gt, ast.GtE, ast.Lt, ast.LtE)):
            return False
        relative_step = self._relative_step(left, right)
        if relative_step is None:
            return False
        required_direction = (1 if isinstance(operator, (ast.Gt, ast.GtE))
                              else -1)
        return relative_step * required_direction > 0

    def _equality_progress(self, left, left_name, operator, right, right_name,
                           guard_defaults) -> bool:
        if left_name is not None and right_name is not None:
            left_supplied, left_step = self._argument_step(left_name)
            right_supplied, right_step = self._argument_step(right_name)
            if not (left_supplied and right_supplied):
                return False
            if left_step is None or right_step is None:
                return False
            relative_step = left_step - right_step
            if isinstance(operator, ast.NotEq):
                return relative_step != 0
            return _reaches_sentinel(
                guard_defaults.get(left_name),
                guard_defaults.get(right_name), relative_step)
        name = left_name if left_name is not None else right_name
        target_expression = right if left_name is not None else left
        target = _signed_numeric_constant(target_expression)
        if target is None:
            return False
        supplied, step = self._argument_step(name)
        if not supplied:
            return False
        if isinstance(operator, ast.NotEq):
            return step is not None and step != 0
        return _reaches_sentinel(guard_defaults.get(name), target, step)

    def _conjunct_progress(self, test, values) -> bool:
        if not (isinstance(test, ast.Compare) and len(test.ops) == 1
                and len(test.comparators) == 1
                and isinstance(test.ops[0],
                               (ast.Gt, ast.GtE, ast.Lt, ast.LtE))):
            return False
        left, right = test.left, test.comparators[0]
        if not any(isinstance(expression, ast.Name)
                   and expression.id in self.depth_names
                   for expression in (left, right)):
            return False
        relative_step = self._relative_step(left, right)
        required_direction = (1 if isinstance(
            test.ops[0], (ast.Gt, ast.GtE)) else -1)
        if relative_step is not None:
            return (relative_step * required_direction > 0
                    or (relative_step == 0 and self._holds(test, values)))
        if not self._holds(test, values):
            return False
        for expression in (left, right):
            if not (isinstance(expression, ast.Name)
                    and expression.id in self.depth_names):
                if _signed_numeric_constant(expression) is None:
                    return False
                continue
            argument = self.call_arguments.get(expression.id)
            if (argument is not None
                    and _signed_numeric_constant(argument) is None):
                return False
        return True

    def evaluate(self, base_guards: list[tuple]) -> bool:
        for test, defaults, guard_defaults, candidate_updates in base_guards:
            values = self._next_guard_values(
                defaults, guard_defaults, candidate_updates)
            if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And):
                if self._holds(test, values) or all(
                        self._conjunct_progress(value, values)
                        for value in test.values):
                    return True
            elif self._single_progress(test, values, guard_defaults):
                return True
        return False


def _reaches_sentinel(start, target, step) -> bool:
    """从 ``start`` 按 ``step`` 至少步进一步，能否恰好落在 ``target``。"""
    if step is None or step == 0:
        return False
    if start is None:
        return False
    if target is None:
        return False
    distance = target - start
    if distance * step < 0:
        return False
    if isinstance(distance, int) and isinstance(step, int):
        return distance // step >= 1 and distance % step == 0
    quotient = distance / step
    nearest = round(quotient)
    return (nearest >= 1 and math.isclose(
        quotient, nearest, rel_tol=1e-9, abs_tol=1e-12))


def _budget_names_from_guards(
        base_guards: list[tuple], param_names: set[str]) -> set[str]:
    """基础出口条件中实际参与比较的形参名。

    G27 原先只承认名字像 depth 的形参为预算（``_is_depth_guard_param``），
    于是 ``def f(n): if n <= 0: return; f(n - 1)`` 这种标准递减递归被判
    无保护。基础出口 test 里出现的形参本身就是该路径的预算变量，应加入
    推进判定；树遍历等非数值守卫（``node is None``）仍走相对步进判定而
    不会被误放行。
    """
    names: set[str] = set()
    for test, *_rest in base_guards:
        for node in _iter_test_nodes(test):
            if isinstance(node, ast.Name) and node.id in param_names:
                names.add(node.id)
    return names

def _call_has_depth_progress(
        node, call: ast.Call, base_guards: list[tuple],
        method: _RecursionMethodContext | None = None,
        budget_names: set[str] | None = None) -> bool:
    if not base_guards:
        return False
    call_arguments = _recursive_call_arguments(node, call, method)
    if call_arguments is None:
        return False
    if budget_names is None:
        budget_names = {
            name for name in argument_param_names(node.args)
            if _is_depth_guard_param(name)
        }
    updates = _depth_updates_before_node(node, call, budget_names)
    return _DepthProgressProbe(call_arguments, budget_names, updates).evaluate(
        base_guards)

def _find_unguarded_recursion(tree: ast.Module) -> list:
    issues = []
    annotations_evaluated = _annotations_evaluated(tree)
    parent_map = build_parent_map(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        fname = node.name
        is_method = _is_class_scope_function(node, parent_map)
        bound, _g_decls, nl_decls = _collect_scope_bindings(
            node, annotations_evaluated)
        method = None
        if is_method:
            class_node = parent_map.get(id(node))
            while class_node is not None and not isinstance(
                    class_node, ast.ClassDef):
                class_node = parent_map.get(id(class_node))
            class_name = class_node.name if class_node is not None else None
            receiver_param = (None if _is_static_method(node)
                              else _first_positional_param_name(node))
            method = _RecursionMethodContext(
                receiver_param, class_name,
                class_name in bound or class_name in nl_decls)
        name_shadowed = fname in bound or fname in nl_decls
        calls = _recursive_calls(
            node, fname, is_method, name_shadowed, annotations_evaluated,
            method)
        if not calls:
            continue
        param_names = set(argument_param_names(node.args))
        depth_names = {
            name for name in param_names if _is_depth_guard_param(name)
        }
        unprotected = []
        for call in calls:
            if _call_has_recursion_handler(call, node, parent_map):
                continue
            base_guards = _depth_base_guards(
                node, depth_names, fname, is_method, name_shadowed,
                call, annotations_evaluated, method)
            budget_names = depth_names | _budget_names_from_guards(
                base_guards, param_names)
            if budget_names != depth_names:
                base_guards = _depth_base_guards(
                    node, budget_names, fname, is_method, name_shadowed,
                    call, annotations_evaluated, method)
            if not _call_has_depth_progress(
                    node, call, base_guards, method, budget_names):
                unprotected.append(call)
        if unprotected:
            issues.append(
                f"行 {node.lineno}: 递归函数 '{fname}' 存在无保护递归路径"
                f"（缺有效深度预算终止/推进，或该路径的 RecursionError 捕获）"
            )
    return issues
def guard_recursion_depth(ctx: OperationContext) -> GuardResult:
    tree, _skip = _parse_guarded_code(ctx, "G27", "非代码修改,跳过递归检查")
    if tree is None:
        return _skip
    return issues_guard_result(
        "G27", "递归深度检查", "无保护递归",
        _find_unguarded_recursion(tree),
        "为递归路径设置深度预算，在递归前检查终止条件并推进预算；"
        "或在实际递归调用所在 try 中捕获 RecursionError",
        "递归深度检查通过",
        level=GuardLevel.WARN)

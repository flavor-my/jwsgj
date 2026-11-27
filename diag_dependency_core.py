from __future__ import annotations

__all__ = [
    "FAN_CRITICAL_RATIO",
    "FAN_IN_DEFAULT_FLOOR",
    "FAN_IN_LAYER_FLOORS",
    "FAN_LAYER_MIN_SAMPLE",
    "FAN_OUT_DEFAULT_FLOOR",
    "FAN_OUT_LAYER_FLOORS",
    "FAN_THRESHOLD_SIGMA",
    "TUKEY_OUTLIER_FACTOR",
    "Finding",
    "PackageRootResolver",
    "build_symbol_universe",
    "collect_import_guarded_ids",
    "fan_severity",
    "import_chain_findings",
    "import_target_exists",
    "namespace_has_symbol",
    "relative_target_dir",
    "resolve_global_fan_threshold",
    "resolve_import_symbol",
    "resolve_layer_fan_thresholds",
    "resolve_outlier_limit",
    "symbol_exists_in_module",
]
import ast
import os
import sys
from collections.abc import Iterable, Iterator
from dataclasses import dataclass
from importlib.machinery import SOURCE_SUFFIXES, all_suffixes
from pathlib import Path
from typing import Any, NamedTuple

from jwsgj.diag_module_surface import (
    _GUARD_TRY_TYPES,
    _IMPORT_FALLBACK_NAMES,
    _MATCH_TYPES,
    _AstCache,
    _declared_package_dir,
    _extract_all,
    _importable_package_dir,
    _iter_import_time_nodes,
    _module_name,
    _pkg_root_base_dir,
    _StaticAll,
    _top_level_symbols,
    _tree_and_getattr,
    _tree_global_names,
    _tree_import_time_scopes,
    _tree_walrus_names,
    dynamic_module_binding_names,
    iter_match_capture_names,
    iter_module_level_nodes,
    iter_walrus_expr_bindings,
    layout_of,
    package_roots_for,
    project_package_root,
    prune_target_dirs,
    relative_import_base,
    strip_root_prefix,
)
from jwsgj.diag_shared_ast_nodes import (
    TYPE_ALIAS_NODES,
    is_star_import,
    iter_unpack_target_names,
)
from jwsgj.diag_shared_ast_views import (
    tree_nodes,
)
from jwsgj.diag_shared_source_core import (
    is_memory_source,
    parse_with_compile,
    read_source,
)
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
)
from jwsgj.log_config import (
    get_module_logger,
    log_swallowed,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    import_key,
    is_runtime_temp_path,
)

logger = get_module_logger(__name__)
FAN_OUT_LAYER_FLOORS: dict[int, float] = {
    0: 10.0, 1: 12.0, 2: 14.0, 3: 16.0, 4: 22.0, 5: 30.0,
}
FAN_OUT_DEFAULT_FLOOR = 16.0
FAN_IN_LAYER_FLOORS: dict[int, float] = {
    0: 60.0, 1: 40.0, 2: 24.0, 3: 18.0, 4: 12.0, 5: 8.0,
}
FAN_IN_DEFAULT_FLOOR = 24.0
FAN_THRESHOLD_SIGMA = 2.0
FAN_LAYER_MIN_SAMPLE = 10
FAN_CRITICAL_RATIO = 1.5
TUKEY_OUTLIER_FACTOR = 1.5
_DEFAULT_FAN_KIND = "out"
def _layer_fan_floor(kind: str, layer: int) -> float:
    if kind == "out":
        return FAN_OUT_LAYER_FLOORS.get(layer, FAN_OUT_DEFAULT_FLOOR)
    return FAN_IN_LAYER_FLOORS.get(layer, FAN_IN_DEFAULT_FLOOR)
def _sigma_cutoff(values: list[int]) -> float:
    vals = values or [0]
    mean = sum(vals) / len(vals)
    std = (sum((v - mean) ** 2 for v in vals) / len(vals)) ** 0.5
    return mean + FAN_THRESHOLD_SIGMA * std
def resolve_layer_fan_thresholds(degrees: dict[str, int],
                                 layer_of: dict[str, int], *,
                                 kind: str = _DEFAULT_FAN_KIND) -> dict[int, float]:
    grouped: dict[int, list[int]] = {}
    for module, degree in degrees.items():
        grouped.setdefault(layer_of.get(module, -1), []).append(degree)
    global_cutoff = _sigma_cutoff(list(degrees.values()))
    thresholds: dict[int, float] = {}
    for layer, values in grouped.items():
        cutoff = (_sigma_cutoff(values)
                  if len(values) >= FAN_LAYER_MIN_SAMPLE
                  else global_cutoff)
        thresholds[layer] = max(_layer_fan_floor(kind, layer), cutoff)
    return thresholds
def resolve_global_fan_threshold(degrees: dict[str, int], *,
                                 kind: str = _DEFAULT_FAN_KIND) -> float:
    return max(_layer_fan_floor(kind, -1),
               _sigma_cutoff(list(degrees.values())))
def _quartiles(values: list[int]) -> tuple[float, float, float]:
    """线性插值四分位（与 ``statistics.quantiles`` 的 inclusive 口径一致）。"""
    sample = sorted(values)
    last = len(sample) - 1
    def cut(ratio: float) -> float:
        position = ratio * last
        low = int(position)
        high = min(low + 1, last)
        return sample[low] + (sample[high] - sample[low]) * (position - low)
    return cut(0.25), cut(0.50), cut(0.75)
def resolve_outlier_limit(values, *, floor: float) -> float:
    """按项目自身分布派生离群阈值（Tukey 上栅栏），并以绝对下限兜底。

    绝对常量阈值只对固定规模的小技能成立：模块总数从十几个涨到几百个时，
    同一常量会把「正常的编排枢纽」和「真正的职责过宽」一起判为违规。
    这里改为以本项目分布的四分位距（IQR）为标尺，只把显著离群的个体拿出来，
    下限 ``floor`` 保证小项目不会因样本太少而把阈值拉低到噪声区。
    """
    sample = [int(value) for value in values]
    if not sample:
        return floor
    _q1, _median, q3 = _quartiles(sample)
    return max(floor, q3 + TUKEY_OUTLIER_FACTOR * (q3 - _q1))
def fan_severity(degree: int, threshold: float) -> str:
    return "P1" if degree >= threshold * FAN_CRITICAL_RATIO else "P2"
@dataclass
class Finding:
    rule_id: str
    severity: str
    message: str
    source: str = "D1"
    file: str = ""
    line: int = 0
    confidence: float = 0.8
    detail: str = ""
    def to_dict(self) -> dict:
        return {
            "rule_id": self.rule_id,
            "severity": self.severity,
            "message": self.message,
            "source": self.source,
            "sources": [self.source] if self.source else [],
            "file": self.file,
            "line": self.line,
            "confidence": self.confidence,
            "detail": self.detail,
        }
def _is_self_import(node: ast.AST, module_path: str | os.PathLike | None,
                    project_root: str | os.PathLike | None) -> bool:
    if module_path is None or not isinstance(node, ast.ImportFrom):
        return False
    current = Path(module_path)
    if node.level > 0:
        source = current.parent
        for _ in range(node.level - 1):
            source = source.parent
        if node.module:
            source = source / node.module.replace(".", "/")
    else:
        if node.module is None:
            return False
        if project_root is None:
            parts = [] if current.name == "__init__.py" else [current.stem]
            package_dir = current.parent
            while (package_dir / "__init__.py").is_file():
                parts.insert(0, package_dir.name)
                package_dir = package_dir.parent
            return node.module == ".".join(parts)
        root = Path(project_root)
        parts = strip_root_prefix(root, node.module)
        source = Path(project_package_root(root)).joinpath(*parts)
    candidates = ((source / "__init__.py",) if not node.module else
                  (source / "__init__.py", source.with_suffix(".py")))
    # 绝对分支的 source 来自 project_package_root（realpath），current 来自调用方
    # 传入的模块路径：经符号链接访问技能根时两者口径不同，须统一按 realpath 比较，
    # 否则绝对自导入识别失效，模块内“先自导入后定义”的断链被当成可解析。
    current_key = os.path.normcase(os.path.realpath(os.path.abspath(str(current))))
    for candidate in candidates:
        if not _source_path_exists(candidate):
            continue
        candidate_key = os.path.normcase(
            os.path.realpath(os.path.abspath(str(candidate))))
        return candidate_key == current_key
    return False
def _self_import_source_symbol(node: ast.ImportFrom, symbol: str) -> str | None:
    for alias in node.names:
        if (alias.asname or alias.name) == symbol:
            return alias.name
    return None
def _self_package_import_exists(node: ast.ImportFrom, module_path,
                                symbol: str) -> bool:
    source_symbol = _self_import_source_symbol(node, symbol)
    return (source_symbol is not None
            and namespace_has_symbol(Path(module_path).parent, source_symbol))
def _matching_self_import(tree: ast.AST, symbol: str, module_path,
                          project_root) -> ast.ImportFrom | None:
    guarded: set[int] | None = None
    for node in _iter_import_time_nodes(tree):
        if not isinstance(node, ast.ImportFrom):
            continue
        if not (_import_from_binds_symbol(node, symbol)
                and _is_self_import(node, module_path, project_root)):
            continue
        if guarded is None:
            guarded = collect_import_guarded_ids(tree)
        if id(node) not in guarded:
            return node
    return None
def _symbol_in_tree(tree: ast.AST, symbol: str, module_path=None,
                    project_root=None) -> bool:
    if symbol in _tree_walrus_names(tree):
        return True
    for node in _iter_import_time_nodes(tree):
        if not _statement_binds_symbol(node, symbol):
            continue
        if _is_self_import(node, module_path, project_root):
            if (Path(module_path).name == "__init__.py"
                    and _self_package_import_exists(node, module_path, symbol)):
                return True
            continue
        return True
    return _global_declares_symbol(tree, symbol)
def _statement_binds_symbol(node: ast.AST, symbol: str) -> bool:
    # ``globals()['x'] = v`` / ``globals().update({...})`` 运行期真实绑定模块属性，
    # 但 AST 上不是 ``Name`` 目标，须先于结构性检查识别，否则被当作断链。
    if symbol in dynamic_module_binding_names(node):
        return True
    for node_types, check in _SYMBOL_BIND_CHECKS:
        if isinstance(node, node_types):
            return check(node, symbol)
    return False
def _def_binds_symbol(node: ast.AST, symbol: str) -> bool:
    return node.name == symbol
def _assign_binds_symbol(node: ast.AST, symbol: str) -> bool:
    return any(symbol in iter_unpack_target_names(t) for t in node.targets)
def _annassign_binds_symbol(node: ast.AST, symbol: str) -> bool:
    return (node.value is not None
            and isinstance(node.target, ast.Name)
            and node.target.id == symbol)
def _for_binds_symbol(node: ast.AST, symbol: str) -> bool:
    return (_getattr_static_iteration(node.iter) is not False
            and symbol in iter_unpack_target_names(node.target))
def _with_binds_symbol(node: ast.AST, symbol: str) -> bool:
    return any(
        item.optional_vars is not None
        and symbol in iter_unpack_target_names(item.optional_vars)
        for item in node.items)
def _import_from_binds_symbol(node: ast.AST, symbol: str) -> bool:
    return any((a.asname or a.name) == symbol for a in node.names)
def _import_binds_symbol(node: ast.AST, symbol: str) -> bool:
    return any((a.asname or a.name.split(".")[0]) == symbol
               for a in node.names)
def _match_binds_symbol(node: ast.AST, symbol: str) -> bool:
    return any(symbol in iter_match_capture_names(case.pattern)
               for case in node.cases)
def _typealias_binds_symbol(node: ast.AST, symbol: str) -> bool:
    return (isinstance(node.name, ast.Name)
            and node.name.id == symbol)
def _global_declares_symbol(tree: ast.AST, symbol: str,
                            before: ast.AST | None = None) -> bool:
    if symbol not in _tree_global_names(tree):
        return False
    for scope in _tree_import_time_scopes(tree):
        if (before is not None
                and getattr(scope, "lineno", 0) >= getattr(before, "lineno", 0)):
            continue
        statements = list(iter_module_level_nodes(scope.body))
        if not any(isinstance(node, ast.Global) and symbol in node.names
                   for node in statements):
            continue
        if any(_statement_binds_symbol(node, symbol)
               or symbol in iter_walrus_expr_bindings(node)
               for node in statements):
            return True
    return False
_SYMBOL_BIND_CHECKS = (
    ((ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef), _def_binds_symbol),
    ((ast.Assign,), _assign_binds_symbol),
    ((ast.AnnAssign,), _annassign_binds_symbol),
    ((ast.For, ast.AsyncFor), _for_binds_symbol),
    ((ast.With, ast.AsyncWith), _with_binds_symbol),
    ((ast.ImportFrom,), _import_from_binds_symbol),
    ((ast.Import,), _import_binds_symbol),
)
if _MATCH_TYPES:
    _SYMBOL_BIND_CHECKS += ((_MATCH_TYPES, _match_binds_symbol),)
if TYPE_ALIAS_NODES:
    _SYMBOL_BIND_CHECKS += ((TYPE_ALIAS_NODES, _typealias_binds_symbol),)
def _symbol_bound_before(tree: ast.AST, symbol: str,
                         before: ast.AST) -> bool:
    for node in _iter_import_time_nodes(tree):
        if node is before:
            break
        if (_statement_binds_symbol(node, symbol)
                or symbol in iter_walrus_expr_bindings(node)):
            return True
    return _global_declares_symbol(tree, symbol, before=before)
def _symbol_in_module_tree(tree: ast.AST, symbol: str,
                           module_path=None, project_root=None, *,
                           allow_getattr: bool = True) -> bool:
    self_import = _matching_self_import(
        tree, symbol, module_path, project_root)
    if self_import is not None:
        if (Path(module_path).name == "__init__.py"
                and _self_package_import_exists(
                    self_import, module_path, symbol)):
            return True
        source_symbol = _self_import_source_symbol(self_import, symbol)
        if source_symbol is None:
            return False
        return (_symbol_bound_before(tree, source_symbol, self_import)
                or (allow_getattr and _getattr_provides_symbol(
                    tree, source_symbol, before=self_import)))
    if _symbol_in_tree(tree, symbol, module_path, project_root):
        return True
    return allow_getattr and _getattr_provides_symbol(tree, symbol)
_UNKNOWN_GETATTR = object()
_UNKNOWN_GETATTR_OPERAND = object()
def _module_getattr_event(node: ast.AST) -> tuple[bool, object]:
    if isinstance(node, ast.Delete):
        deleted = any("__getattr__" in iter_unpack_target_names(target)
                      for target in node.targets)
        return deleted, None
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return node.name == "__getattr__", node
    if isinstance(node, (ast.Assign, ast.AnnAssign)):
        if isinstance(node, ast.AnnAssign) and node.value is None:
            return False, None
        targets = node.targets if isinstance(node, ast.Assign) else [node.target]
        if not any("__getattr__" in iter_unpack_target_names(target)
                   for target in targets):
            return False, None
        simple_names = all(isinstance(target, ast.Name) for target in targets)
        if simple_names and isinstance(node.value, ast.Lambda):
            return True, node.value
        if simple_names and isinstance(node.value, (
                ast.Constant, ast.JoinedStr, ast.List, ast.Tuple,
                ast.Set, ast.Dict)):
            return True, None
        return True, _UNKNOWN_GETATTR
    if not _statement_binds_symbol(node, "__getattr__"):
        return False, None
    if isinstance(node, ast.Import):
        return True, None
    return True, _UNKNOWN_GETATTR
def _module_getattr_states(tree: ast.AST,
                           before: ast.AST | None = None) -> set:
    visible = {id(node) for node in _iter_import_time_nodes(tree)}
    stopped = False
    def visit(statements, incoming):
        nonlocal stopped
        current = set(incoming)
        for node in statements:
            if stopped:
                break
            if node is before:
                stopped = True
                break
            if id(node) not in visible:
                continue
            if isinstance(node, ast.If):
                if isinstance(node.test, ast.Constant):
                    branch = node.body if bool(node.test.value) else node.orelse
                    current = visit(branch, current)
                    continue
                body_visible = any(id(stmt) in visible for stmt in node.body)
                else_visible = any(id(stmt) in visible for stmt in node.orelse)
                if not body_visible:
                    current = visit(node.orelse, current)
                    continue
                if node.orelse and not else_visible:
                    current = visit(node.body, current)
                    continue
                body_states = visit(node.body, set(current))
                if stopped:
                    return body_states
                else_states = (visit(node.orelse, set(current))
                               if node.orelse else set(current))
                current = body_states | else_states
                continue
            if isinstance(node, _GUARD_TRY_TYPES):
                before_try = set(current)
                body_states = visit(node.body, set(current))
                if stopped:
                    return body_states
                handler_states: set = set()
                if any(not isinstance(stmt, ast.Pass) for stmt in node.body):
                    for handler in node.handlers:
                        handler_states |= visit(handler.body, set(before_try))
                        if stopped:
                            return handler_states
                normal_states = (visit(node.orelse, body_states)
                                 if node.orelse else body_states)
                current = normal_states | handler_states
                if node.finalbody:
                    current = visit(node.finalbody, current)
                continue
            if isinstance(node, (ast.For, ast.AsyncFor)):
                execution = _getattr_static_iteration(node.iter)
                if execution is False:
                    current = (visit(node.orelse, current)
                               if node.orelse else current)
                    continue
                if execution is True:
                    control = _getattr_block_outcomes(node.body, "", "")
                    body_states = visit(node.body, set(current))
                    if stopped:
                        return body_states
                    if not control.breaks and not control.continues:
                        current = (visit(node.orelse, body_states)
                                   if node.orelse else body_states)
                    else:
                        current |= body_states
                        if node.orelse:
                            current |= visit(node.orelse, body_states)
                    continue
            if (isinstance(node, ast.While)
                    and isinstance(node.test, ast.Constant)
                    and not node.test.value):
                current = (visit(node.orelse, current)
                           if node.orelse else current)
                continue
            if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
                body_states = visit(node.body, set(current))
                if stopped:
                    return body_states
                else_states = visit(node.orelse, body_states)
                current |= body_states | else_states
                continue
            if isinstance(node, (ast.With, ast.AsyncWith)):
                current = visit(node.body, current)
                continue
            if _MATCH_TYPES and isinstance(node, _MATCH_TYPES):
                for case in node.cases:
                    current |= visit(case.body, set(current))
                    if stopped:
                        return current
                continue
            changed, state = _module_getattr_event(node)
            if changed:
                current = {state}
        return current
    return visit(tree.body, {None})
def _getattr_hashable(value: object) -> bool:
    if isinstance(value, (list, set, dict)):
        return False
    if isinstance(value, tuple):
        return all(_getattr_hashable(item) for item in value)
    return True

def _getattr_operand(node: ast.AST, param: str, symbol: str):
    if isinstance(node, ast.Name) and node.id == param:
        return symbol
    if isinstance(node, ast.Constant):
        return node.value
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        values = [_getattr_operand(element, param, symbol)
                  for element in node.elts]
        if any(value is _UNKNOWN_GETATTR_OPERAND for value in values):
            return _UNKNOWN_GETATTR_OPERAND
        if isinstance(node, ast.List):
            return values
        if isinstance(node, ast.Tuple):
            return tuple(values)
        if not all(_getattr_hashable(value) for value in values):
            return _UNKNOWN_GETATTR_OPERAND
        return set(values)
    if isinstance(node, ast.Dict):
        keys = [_getattr_operand(key, param, symbol) if key is not None
                else _UNKNOWN_GETATTR_OPERAND for key in node.keys]
        values = [_getattr_operand(value, param, symbol)
                  for value in node.values]
        if (any(key is _UNKNOWN_GETATTR_OPERAND for key in keys)
                or any(value is _UNKNOWN_GETATTR_OPERAND for value in values)
                or not all(_getattr_hashable(key) for key in keys)):
            return _UNKNOWN_GETATTR_OPERAND
        return dict(zip(keys, values, strict=True))
    return _UNKNOWN_GETATTR_OPERAND
def _getattr_test_value(node: ast.AST, param: str, symbol: str) -> bool | None:
    if isinstance(node, ast.Constant):
        return bool(node.value)
    if isinstance(node, ast.Name) and node.id == param:
        return bool(symbol)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        value = _getattr_test_value(node.operand, param, symbol)
        return None if value is None else not value
    if isinstance(node, ast.BoolOp):
        values = [_getattr_test_value(value, param, symbol)
                  for value in node.values]
        if isinstance(node.op, ast.And):
            if any(value is False for value in values):
                return False
            return True if all(value is True for value in values) else None
        if isinstance(node.op, ast.Or):
            if any(value is True for value in values):
                return True
            return False if all(value is False for value in values) else None
    if not isinstance(node, ast.Compare):
        return None
    results = []
    left = node.left
    for op, comparator in zip(node.ops, node.comparators, strict=False):
        left_value = _getattr_operand(left, param, symbol)
        right_value = _getattr_operand(comparator, param, symbol)
        if (left_value is _UNKNOWN_GETATTR_OPERAND
                or right_value is _UNKNOWN_GETATTR_OPERAND):
            results.append(None)
        elif isinstance(op, ast.Eq):
            results.append(left_value == right_value)
        elif isinstance(op, ast.NotEq):
            results.append(left_value != right_value)
        elif isinstance(op, (ast.In, ast.NotIn)):
            try:
                contained = left_value in right_value
            except TypeError:
                results.append(None)
            else:
                results.append(not contained if isinstance(op, ast.NotIn)
                               else contained)
        else:
            results.append(None)
        left = comparator
    if any(result is False for result in results):
        return False
    return True if all(result is True for result in results) else None
class _GetattrOutcome(NamedTuple):
    succeeds: bool = False
    falls_through: bool = False
    breaks: bool = False
    continues: bool = False


def _getattr_outcome_union(outcomes) -> _GetattrOutcome:
    outcomes = tuple(outcomes)
    return _GetattrOutcome(
        succeeds=any(result.succeeds for result in outcomes),
        falls_through=any(result.falls_through for result in outcomes),
        breaks=any(result.breaks for result in outcomes),
        continues=any(result.continues for result in outcomes),
    )


def _getattr_static_iteration(iterable: ast.AST) -> bool | None:
    if isinstance(iterable, (ast.List, ast.Tuple, ast.Set)):
        if any(isinstance(element, ast.Starred) for element in iterable.elts):
            return None
        return bool(iterable.elts)
    if isinstance(iterable, ast.Dict):
        if any(key is None for key in iterable.keys):
            return None
        return bool(iterable.keys)
    if (isinstance(iterable, ast.Constant)
            and isinstance(iterable.value, (str, bytes))):
        return bool(iterable.value)
    return None


def _getattr_loop_outcome(node: ast.AST, param: str,
                          symbol: str) -> _GetattrOutcome:
    execution = (_getattr_test_value(node.test, param, symbol)
                 if isinstance(node, ast.While)
                 else _getattr_static_iteration(node.iter))
    body = (_GetattrOutcome() if execution is False else
            _getattr_block_outcomes(node.body, param, symbol))
    if isinstance(node, ast.While):
        else_reachable = execution is not True
    elif execution is True:
        # 非空字面量迭代只有正常耗尽才进入 else，break 会跳过它。
        else_reachable = body.falls_through or body.continues
    else:
        # 空迭代必进 else；未知迭代保留零次迭代路径。
        else_reachable = True
    if node.orelse and else_reachable:
        otherwise = _getattr_block_outcomes(node.orelse, param, symbol)
        normal_exit = otherwise.falls_through
    else:
        otherwise = _GetattrOutcome()
        normal_exit = else_reachable
    return _GetattrOutcome(
        succeeds=body.succeeds or otherwise.succeeds,
        falls_through=body.breaks or normal_exit,
    )


def _getattr_finally_outcome(current: _GetattrOutcome,
                             final: _GetattrOutcome) -> _GetattrOutcome:
    if not any(final):
        return final
    return _GetattrOutcome(
        succeeds=(current.succeeds and final.falls_through) or final.succeeds,
        falls_through=current.falls_through and final.falls_through,
        breaks=(current.breaks and final.falls_through) or final.breaks,
        continues=((current.continues and final.falls_through)
                   or final.continues),
    )


def _getattr_block_outcomes(statements, param: str,
                            symbol: str) -> _GetattrOutcome:
    current = _GetattrOutcome(falls_through=True)
    for node in statements:
        if not current.falls_through:
            break
        if isinstance(node, ast.Return):
            outcome = _GetattrOutcome(succeeds=True)
        elif isinstance(node, ast.Raise):
            outcome = _GetattrOutcome()
        elif isinstance(node, ast.Break):
            outcome = _GetattrOutcome(breaks=True)
        elif isinstance(node, ast.Continue):
            outcome = _GetattrOutcome(continues=True)
        elif isinstance(node, ast.If):
            test = _getattr_test_value(node.test, param, symbol)
            branches = ((node.body, node.orelse) if test is None else
                        (node.body if test else node.orelse,))
            outcome = _getattr_outcome_union(
                _getattr_block_outcomes(branch, param, symbol)
                for branch in branches)
        elif isinstance(node, _GUARD_TRY_TYPES):
            body = _getattr_block_outcomes(node.body, param, symbol)
            normal = body
            if node.orelse and body.falls_through:
                otherwise = _getattr_block_outcomes(
                    node.orelse, param, symbol)
                normal = _GetattrOutcome(
                    succeeds=body.succeeds or otherwise.succeeds,
                    falls_through=otherwise.falls_through,
                    breaks=body.breaks or otherwise.breaks,
                    continues=body.continues or otherwise.continues,
                )
            outcome = _getattr_outcome_union(
                (normal, *(_getattr_block_outcomes(
                    handler.body, param, symbol)
                    for handler in node.handlers)))
            if node.finalbody:
                final = _getattr_block_outcomes(
                    node.finalbody, param, symbol)
                outcome = _getattr_finally_outcome(outcome, final)
        elif isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
            outcome = _getattr_loop_outcome(node, param, symbol)
        elif isinstance(node, (ast.With, ast.AsyncWith)):
            outcome = _getattr_block_outcomes(node.body, param, symbol)
        elif _MATCH_TYPES and isinstance(node, _MATCH_TYPES):
            cases = _getattr_outcome_union(
                _getattr_block_outcomes(case.body, param, symbol)
                for case in node.cases)
            exhaustive = any(
                case.guard is None and isinstance(case.pattern, ast.MatchAs)
                and case.pattern.pattern is None for case in node.cases)
            outcome = cases if exhaustive else cases._replace(falls_through=True)
        else:
            continue
        current = _GetattrOutcome(
            succeeds=current.succeeds or outcome.succeeds,
            falls_through=outcome.falls_through,
            breaks=current.breaks or outcome.breaks,
            continues=current.continues or outcome.continues,
        )
    return current
def _getattr_accepts_name(state: object) -> bool:
    if state is _UNKNOWN_GETATTR:
        return True
    if not isinstance(state, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        return False
    args = state.args
    positional = [*args.posonlyargs, *args.args]
    if not positional and args.vararg is None:
        return False
    required_positional = len(positional) - len(args.defaults)
    return (required_positional <= 1
            and all(default is not None for default in args.kw_defaults))
def _getattr_provides_symbol(tree: ast.AST, symbol: str,
                             before: ast.AST | None = None) -> bool:
    for state in _module_getattr_states(tree, before):
        if not _getattr_accepts_name(state):
            continue
        if state is _UNKNOWN_GETATTR or isinstance(state, ast.Lambda):
            return True
        args = [*state.args.posonlyargs, *state.args.args]
        if not args:
            return True
        outcome = _getattr_block_outcomes(
            state.body, args[0].arg, symbol)
        if outcome.succeeds or outcome.falls_through:
            return True
    return False
def _symbol_project_root(module_path: str) -> str | None:
    current = Path(os.path.abspath(module_path)).parent
    project_root = None
    while (current / "__init__.py").is_file():
        parent = current.parent
        project_root = str(parent)
        if parent == current:
            break
        current = parent
    return project_root
def symbol_exists_in_module(module_path: str | None, symbol: str,
                            cache: _AstCache | None = None) -> bool:
    tree, _has_getattr = _tree_and_getattr(module_path, cache)
    if tree is None:
        return True
    return resolve_import_symbol(
        _symbol_project_root(module_path), module_path, symbol, cache=cache,
        _parsed_tree=tree)
class _WildcardSource(NamedTuple):
    path: Path
    allow_mod_py: bool
def _source_path_exists(path: Path) -> bool:
    return path.is_file() or is_memory_source(str(path))
def _probe_wildcard_source(src: _WildcardSource, symbol: str,
                           project_root, visited: set[tuple[str, str, bool, bool]],
                           cache: _AstCache | None) -> bool:
    pkg_init = src.path / "__init__.py"
    module_file = src.path.with_suffix(".py")
    if _source_path_exists(pkg_init):
        source_path = pkg_init
    elif src.allow_mod_py and _source_path_exists(module_file):
        source_path = module_file
    else:
        return False
    tree, _has_getattr = _tree_and_getattr(source_path, cache)
    allow_package_member = False
    allow_getattr = True
    if tree is not None:
        all_surface = _extract_all(tree)
        allow_getattr = all_surface is not None
        if all_surface is None and symbol.startswith("_"):
            return False
        if (all_surface is not None and all_surface.complete
                and symbol not in all_surface.names):
            return False
        allow_package_member = (
            all_surface is not None and all_surface.complete)
    return resolve_import_symbol(
        project_root, source_path, symbol, cache=cache, _visited=visited,
        _allow_package_member=allow_package_member,
        _allow_getattr=allow_getattr)
def namespace_has_symbol(ns_dir: Path, symbol: str) -> bool:
    return (any((ns_dir / f"{symbol}{suffix}").is_file()
                for suffix in all_suffixes())
            or (ns_dir / symbol).is_dir())
def _within_project_root(base: Path, project_root) -> bool:
    try:
        base_abs = os.path.normcase(os.path.abspath(str(base)))
        root_abs = os.path.normcase(os.path.abspath(str(project_root)))
        return os.path.commonpath([base_abs, root_abs]) == root_abs
    except (ValueError, OSError) as _e:
        log_swallowed(__name__, _e,
                      context='_within_project_root:OSError')
        return False
def _relative_wildcard_source(node: ast.ImportFrom,
                              module_path: Path,
                              project_root) -> _WildcardSource | None:
    base = module_path.parent
    for _ in range(node.level - 1):
        base = base.parent
    if project_root is not None and not _within_project_root(base, project_root):
        return None
    if node.module:
        return _WildcardSource(base / node.module.replace(".", "/"), True)
    return _WildcardSource(base, False)
def _absolute_wildcard_source(node: ast.ImportFrom,
                              project_root) -> _WildcardSource | None:
    if project_root is None or node.module is None:
        return None
    root = Path(project_root)
    parts = strip_root_prefix(root, node.module)
    return _WildcardSource(
        Path(project_package_root(root)) / "/".join(parts), bool(parts))
def _track_wildcard_reexports(tree: ast.Module, module_path: Path,
                               symbol: str, project_root,
                               visited: set[tuple[str, str, bool, bool]],
                               cache: _AstCache | None) -> bool:
    self_import = _matching_self_import(
        tree, symbol, module_path, project_root)
    for node in _iter_import_time_nodes(tree):
        if node is self_import:
            break
        if not is_star_import(node):
            continue
        resolved = _wildcard_source(node, module_path, project_root)
        if resolved is None:
            continue
        if _probe_wildcard_source(resolved, symbol, project_root, visited, cache):
            return True
    return False
def _wildcard_source(node: ast.ImportFrom, module_path: Path,
                     project_root) -> _WildcardSource | None:
    if node.level > 0:
        return _relative_wildcard_source(node, module_path, project_root)
    return _absolute_wildcard_source(node, project_root)
def resolve_import_symbol(project_root: str | os.PathLike | None,
                          module_path: str | os.PathLike | None,
                          symbol: str, cache: _AstCache | None = None, *,
                          _visited: set[tuple[str, str, bool, bool]] | None = None,
                          _allow_package_member: bool = True,
                          _allow_getattr: bool = True,
                          _parsed_tree: ast.AST | None = None) -> bool:
    if module_path is None:
        return False
    module_path = Path(module_path)
    if _parsed_tree is None and not _source_path_exists(module_path):
        return False
    visited = set() if _visited is None else _visited
    source_key = (os.path.normcase(os.path.abspath(str(module_path))), symbol,
                  _allow_package_member, _allow_getattr)
    if source_key in visited:
        return False
    visited.add(source_key)
    tree = _parsed_tree
    if tree is None:
        tree, _has_getattr = _tree_and_getattr(module_path, cache)
    if tree is None:
        return True
    if _symbol_in_module_tree(
            tree, symbol, module_path, project_root,
            allow_getattr=_allow_getattr):
        return True
    return (_track_wildcard_reexports(
                tree, module_path, symbol, project_root, visited, cache)
            or (_allow_package_member
                and _symbol_is_package_member(module_path, symbol)))
def _symbol_is_package_member(module_path: Path, symbol: str) -> bool:
    return (module_path.name == "__init__.py"
            and namespace_has_symbol(module_path.parent, symbol))
def _handler_catches_fallback(handler: ast.ExceptHandler) -> bool:
    if handler.type is None:
        catches = True
    else:
        catches = any(name in _IMPORT_FALLBACK_NAMES
                      for name in _exception_handler_names(handler.type))
    # 无条件重抛的 handler 不提供回退：导入失败仍会向上传播，断链须照常上报。
    return catches and not _body_always_raises(handler.body)


def _body_always_raises(body: list[ast.stmt]) -> bool:
    """语句序列是否在所有路径上以 raise 结束；无法定论时返回 False（维持守卫语义）。"""
    for index, stmt in enumerate(body):
        if isinstance(stmt, ast.Raise):
            return True
        if isinstance(stmt, (ast.Return, ast.Break, ast.Continue)):
            return False
        if index == len(body) - 1:
            return _stmt_always_raises(stmt)
    return False


def _stmt_always_raises(stmt: ast.stmt) -> bool:
    if isinstance(stmt, ast.Raise):
        return True
    if isinstance(stmt, ast.If):
        return (bool(stmt.orelse) and _body_always_raises(stmt.body)
                and _body_always_raises(stmt.orelse))
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        return _body_always_raises(stmt.body)
    if isinstance(stmt, _GUARD_TRY_TYPES):
        finally_exits = any(
            isinstance(node, (ast.Return, ast.Break, ast.Continue))
            for node in stmt.finalbody)
        return (not finally_exits and _body_always_raises(stmt.body)
                and all(_body_always_raises(h.body) for h in stmt.handlers))
    return False
def _exception_handler_names(handler_type: ast.AST) -> tuple[str, ...]:
    if isinstance(handler_type, ast.Name):
        return (handler_type.id,)
    if isinstance(handler_type, ast.Attribute):
        return (handler_type.attr,)
    if isinstance(handler_type, ast.Tuple):
        return tuple(name for element in handler_type.elts
                     for name in _exception_handler_names(element))
    return ()
def collect_import_guarded_ids(tree: ast.AST) -> set[int]:
    guarded: set[int] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, _GUARD_TRY_TYPES):
            continue
        if not any(_handler_catches_fallback(h) for h in node.handlers):
            continue
        guarded.update(id(n) for n in iter_module_level_nodes(node.body))
    return guarded
def _iter_absolute_import_paths(tree: ast.AST) -> Iterator[str]:
    for node in iter_module_level_nodes(tree):
        if (isinstance(node, ast.ImportFrom) and node.level == 0
                and node.module):
            yield node.module
            if "." not in node.module:
                for alias in node.names:
                    if alias.name != "*":
                        yield f"{node.module}.{alias.name}"
        elif isinstance(node, ast.Import):
            for alias in node.names:
                yield alias.name
def _collect_dotted_imports(
        py_files: Iterable[str],
        parsed: dict[str, tuple[ast.AST, str]] | None = None) -> list[str]:
    dotted: list[str] = []
    for fpath in py_files:
        tree = _load_source_tree(fpath, tag="dotted_imports", parsed=parsed)
        if tree is None:
            continue
        dotted.extend(_iter_absolute_import_paths(tree))
    return dotted
class PackageRootResolver:
    __slots__ = ("_importable", "_layout", "_probe_dirs", "root_name",
                 "roots", "skill_dir")
    def __init__(self, skill_dir: str) -> None:
        self.skill_dir = skill_dir
        self.root_name = import_key(os.path.basename(
            os.path.normpath(os.path.abspath(skill_dir))))
        self.roots: set[str] = set()
        self._probe_dirs: dict[str, str] = {}
        self._importable: dict[str, bool] = {}
        self._layout: Any = None
    def _layout_info(self):
        if self._layout is None:
            self._layout = layout_of(self.skill_dir)
        return self._layout
    def resolve(self, py_files: Iterable[str], *,
                parsed: dict[str, tuple[ast.AST, str]] | None = None
                ) -> set[str]:
        local_roots = package_roots_for(self.skill_dir)
        dotted_imports = _collect_dotted_imports(py_files, parsed)
        namespace_roots = self._namespace_roots(dotted_imports)
        external_roots = self._external_roots(
            dotted_imports, local_roots | namespace_roots)
        self.roots = local_roots | namespace_roots | external_roots
        return self.roots
    def is_importable(self, root: str) -> bool:
        if root in self.roots:
            return True
        cached = self._importable.get(root)
        if cached is None:
            cached = self._external_dir(root) is not None
            self._importable[root] = cached
        return cached
    def probe_dir(self, root: str) -> str:
        cached = self._probe_dirs.get(root)
        if cached is not None:
            return cached
        if root == self.root_name:
            if os.path.isfile(os.path.join(self.skill_dir, "__init__.py")):
                resolved = self.skill_dir
            else:
                resolved = _pkg_root_base_dir(
                    root, self.root_name, self.skill_dir,
                    layout=self._layout_info())
        else:
            sub = os.path.join(self.skill_dir, root)
            if os.path.isdir(sub):
                resolved = sub
            else:
                declared = _declared_package_dir(
                    self.skill_dir, root, self._layout_info())
                resolved = declared if declared is not None else (
                    self._external_dir(root) or sub)
        self._probe_dirs[root] = resolved
        return resolved
    def _namespace_roots(self, dotted_imports: Iterable[str]) -> set[str]:
        pairs: set[tuple[str, str]] = set()
        for dotted in dotted_imports:
            parts = dotted.split(".")
            if len(parts) >= 2:
                pairs.add((parts[0], parts[1]))
        if not pairs:
            return set()
        try:
            top = set(os.listdir(self.skill_dir))
        except OSError as exc:
            log_swallowed(__name__, exc, context='_namespace_roots:listdir')
            return set()
        dirs_by_root: dict[str, set[str]] = {}
        files_by_root: dict[str, set[str]] = {}
        roots: set[str] = set()
        for root, second in sorted(pairs):
            if root not in top or (root + ".py") in top:
                continue
            dirs = dirs_by_root.get(root)
            if dirs is None:
                dirs, files = set(), set()
                root_dir = os.path.join(self.skill_dir, root)
                try:
                    with os.scandir(root_dir) as entries:
                        for entry in entries:
                            (dirs if entry.is_dir() else files).add(
                                entry.name)
                except OSError as exc:
                    log_swallowed(
                        __name__, exc, context='_namespace_roots:scandir')
                dirs_by_root[root] = dirs
                files_by_root[root] = files
            has_module_file = any(
                second + suffix in files_by_root[root]
                for suffix in all_suffixes())
            if (second in dirs or has_module_file) \
                    and "__init__.py" not in files_by_root[root]:
                roots.add(root)
        return roots
    def _external_roots(self, dotted_imports: Iterable[str],
                        known_roots: set[str]) -> set[str]:
        candidates = {dotted.split(".", 1)[0] for dotted in dotted_imports}
        return {root for root in candidates - known_roots
                if self._external_dir(root) is not None}
    def _is_local(self, root: str) -> bool:
        return (os.path.isfile(os.path.join(self.skill_dir, root + ".py"))
                or os.path.isdir(os.path.join(self.skill_dir, root)))
    def _external_dir(self, root: str) -> str | None:
        if not root or self._is_local(root) or root in sys.stdlib_module_names:
            return None
        return _importable_package_dir(root)
def import_target_exists(path_noext: str) -> bool:
    return (any(os.path.isfile(path_noext + suffix)
                for suffix in all_suffixes())
            or os.path.isfile(os.path.join(path_noext, "__init__.py"))
            or os.path.isdir(path_noext))
class _ImportScanScope:
    __slots__ = ("_base_dirs", "cache", "parsed", "pkg_roots",
                 "real_pkg_root", "skill_dir")
    def __init__(self, skill_dir: str, pkg_roots: frozenset[str],
                 real_pkg_root: str, cache: Any = None,
                 parsed: dict[str, tuple[ast.AST, str]] | None = None
                 ) -> None:
        self.skill_dir = skill_dir
        self.pkg_roots = pkg_roots
        self.real_pkg_root = real_pkg_root
        self.cache = cache
        self.parsed = parsed
        self._base_dirs: dict[str, str | None] = {}
    def base_dir(self, root_name: str) -> str | None:
        if root_name in self._base_dirs:
            return self._base_dirs[root_name]
        resolved = _pkg_root_base_dir(
            root_name, self.real_pkg_root, self.skill_dir)
        self._base_dirs[root_name] = resolved
        return resolved
    def check_symbols(self, node: ast.ImportFrom, imported: str,
                      target_file: str, site: _ImportSite,
                      base_dir: str | None = None) -> list[Finding]:
        results: list[Finding] = []
        symbol_root = self.skill_dir if base_dir is None else base_dir
        for alias in node.names:
            symbol = alias.name
            if not _is_checkable_symbol(symbol):
                continue
            if resolve_import_symbol(
                    symbol_root, target_file, symbol, cache=self.cache):
                continue
            results.append(_broken_finding(
                "D9-BROKEN-SYMBOL", site,
                f"符号级导入断链: {site.module_name} 从 {imported} 导入 "
                f"{symbol}，但该符号不可解析",
                f"模块 {imported} 存在但符号 {symbol} 缺失"
                f"（可能已改名/迁移），五层符号解析均失败",
                line=node.lineno,
            ))
        return results
class _ImportSite(NamedTuple):
    module_name: str
    fpath: str
def _broken_finding(rule_id: str, site: _ImportSite,
                    message: str, detail: str, *,
                    line: int = 0) -> Finding:
    return Finding(rule_id=rule_id, severity="P1", message=message,
                   detail=detail, file=site.fpath, line=line)
def _broken_module_finding(site: _ImportSite, imported: str, *,
                           line: int = 0) -> Finding:
    return _broken_finding(
        "D9-BROKEN-IMPORT", site,
        f"断裂的 import 路径: {site.module_name} 导入 {imported}，"
        f"但该模块不存在",
        f"引用了不存在的模块 {imported}",
        line=line,
    )
def _check_import_form_broken(node: ast.Import, site: _ImportSite,
                              scope: _ImportScanScope) -> list[Finding]:
    results: list[Finding] = []
    for alias in node.names:
        parts = alias.name.split(".")
        if len(parts) < 2 or parts[0] not in scope.pkg_roots:
            continue
        base_dir = scope.base_dir(parts[0])
        target_module = ".".join(parts)
        if base_dir is None:
            results.append(_broken_module_finding(
                site, target_module, line=node.lineno))
            continue
        rel_parts = os.path.join(*parts[1:])
        if import_target_exists(os.path.join(base_dir, rel_parts)):
            continue
        results.append(_broken_module_finding(
            site, target_module, line=node.lineno))
    return results
def _package_first_anchor(mod_base: str, mod_pkg: str) -> str | None:
    if os.path.isfile(mod_pkg):
        return mod_pkg
    return next(
        (mod_base + suffix for suffix in SOURCE_SUFFIXES
         if os.path.isfile(mod_base + suffix)),
        None,
    )
def _is_checkable_symbol(symbol: str) -> bool:
    return bool(symbol) and symbol != "*"
def _check_relative_module_channel(node: ast.ImportFrom, target_dir: str,
                                   dots: str, site: _ImportSite,
                                   scope: _ImportScanScope) -> list[Finding]:
    mod_rel = node.module.replace(".", os.sep)
    mod_base = os.path.join(target_dir, mod_rel)
    mod_pkg = os.path.join(mod_base, "__init__.py")
    anchor = _package_first_anchor(mod_base, mod_pkg)
    if anchor is not None:
        return scope.check_symbols(
            node, dots + node.module, anchor, site)
    mod_dir = os.path.join(target_dir, mod_rel)
    if os.path.isdir(mod_dir):
        return _namespace_symbol_findings(
            node, mod_dir, f"{dots}{node.module}", site)
    if import_target_exists(mod_base):
        return []
    return [_broken_finding(
        "D9-BROKEN-IMPORT", site,
        f"断裂的相对导入: {site.module_name} 导入 {dots}{node.module}，"
        f"但该模块不存在",
        f"引用了不存在的模块 {dots}{node.module}",
        line=node.lineno,
    )]
def _namespace_symbol_findings(node: ast.ImportFrom, ns_dir: str,
                               imported: str, site: _ImportSite
                               ) -> list[Finding]:
    results: list[Finding] = []
    for alias in node.names:
        symbol = alias.name
        if not _is_checkable_symbol(symbol):
            continue
        if import_target_exists(os.path.join(ns_dir, symbol)):
            continue
        results.append(_broken_finding(
            "D9-BROKEN-SYMBOL", site,
            f"符号级导入断链: {site.module_name} 从 {imported} 导入 "
            f"{symbol}，但该符号非 namespace 子模块/子包",
            f"模块 {imported} 为 PEP 420 命名空间目录（无 __init__.py），"
            f"符号 {symbol} 既非其子模块也非其子包"
            "（namespace 形态不可解析）",
            line=node.lineno,
        ))
    return results
def _check_relative_symbols_channel(node: ast.ImportFrom, target_dir: str,
                                    dots: str, site: _ImportSite,
                                    cache: Any = None,
                                    project_root: str | None = None
                                    ) -> list[Finding]:
    results: list[Finding] = []
    for alias in node.names:
        symbol = alias.name
        if not _is_checkable_symbol(symbol):
            continue
        if _package_symbol_resolvable(
                target_dir, symbol, cache, project_root):
            continue
        results.append(_broken_finding(
            "D9-BROKEN-SYMBOL", site,
            f"相对导入断链: from {dots} import {symbol}"
            "，既非同级子模块也非包门面导出",
            f"符号 {symbol} 不可解析（可能已改名/迁移），"
            "同级文件与包 __init__.py 五层解析均失败",
            line=node.lineno,
        ))
    return results
def _package_symbol_resolvable(base_dir: str, symbol: str, cache=None,
                               project_root: str | None = None) -> bool:
    if import_target_exists(os.path.join(base_dir, symbol)):
        return True
    pkg_init = os.path.join(base_dir, "__init__.py")
    if not os.path.isfile(pkg_init):
        return False
    return resolve_import_symbol(
        project_root if project_root is not None else base_dir,
        pkg_init, symbol, cache=cache)
def _relative_import_owner_root(site: _ImportSite,
                                scope: _ImportScanScope) -> str:
    source_dir = Path(os.path.abspath(site.fpath)).parent
    candidates: list[str] = []
    for root_name in scope.pkg_roots:
        base_dir = scope.base_dir(root_name)
        if base_dir is not None and _within_project_root(source_dir, base_dir):
            candidates.append(base_dir)
    if candidates:
        # 内层包边界已由 relative_import_base 校验；此处须容纳外层合法上下文。
        return min(candidates, key=lambda value: len(Path(value).parts))
    return scope.skill_dir
def _check_relative_import(node: ast.ImportFrom, site: _ImportSite,
                           scope: _ImportScanScope) -> list[Finding]:
    target_dir = relative_target_dir(site.fpath, node.level, scope.skill_dir)
    owner_root = _relative_import_owner_root(site, scope)
    dots = "." * node.level
    imported = f"{dots}{node.module or ''}"
    if (target_dir is None
            or not _within_project_root(Path(target_dir), owner_root)):
        return [_broken_finding(
            "D9-BROKEN-IMPORT", site,
            f"断裂的相对导入: {site.module_name} 导入 {imported}，"
            "但相对级别越出顶层包或目标目录不存在",
            f"相对导入 {imported} 超出当前顶层包边界，或目标目录不存在",
            line=node.lineno,
        )]
    if node.module:
        return _check_relative_module_channel(
            node, target_dir, dots, site, scope)
    return _check_relative_symbols_channel(
        node, target_dir, dots, site, scope.cache, scope.skill_dir)
def relative_target_dir(fpath: str, level: int,
                         skill_dir: str) -> str | None:
    base = relative_import_base(fpath, level, skill_dir)
    return str(base) if base is not None and base.is_dir() else None
class _ParsedSourceCache:
    __slots__ = ("_parsed",)
    def __init__(self, parsed: dict[str, tuple[ast.AST, str]]) -> None:
        self._parsed = parsed
    def get_ast(self, filepath: str) -> ast.AST | None:
        entry = self._parsed.get(filepath)
        return entry[0] if entry is not None else None
    def get_source(self, filepath: str) -> str | None:
        entry = self._parsed.get(filepath)
        return entry[1] if entry is not None else None
def _load_source_tree(path: str, cache=None, tag: str = "import_chain",
                      parsed: dict[str, tuple[ast.AST, str]] | None = None
                      ) -> ast.AST | None:
    if parsed is not None:
        entry = parsed.get(path)
        if entry is not None:
            return entry[0]
    if cache is not None:
        tree = _cached_ast(cache, path, tag)
        if tree is not None:
            return tree
    try:
        content = read_source(path, cache)
    except OSError as e:
        logger.warning("[%s] 读取 %s 失败，跳过该文件: %s", tag, path, e)
        return None
    if content is None:
        logger.warning("[%s] 读取 %s 失败，跳过该文件", tag, path)
        return None
    try:
        tree = compile(content, path, "exec", ast.PyCF_ONLY_AST)
    except PARSE_DEGRADE_EXC as e:
        logger.warning("[%s] 解析 %s 失败，跳过该文件: %s", tag, path, e)
        return None
    if parsed is not None:
        parsed[path] = (tree, content)
    return tree
def _cached_ast(ctx, path: str, tag: str) -> ast.AST | None:
    try:
        return ctx.get_ast(path)
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e, context=f'_cached_ast:{tag}')
        return None
def _self_import_prefixes(init_path: str, skill_dir: str,
                          real_pkg_root: str) -> tuple[str, ...]:
    prefixes: list[str] = []
    # SkillLayout.package_root 经 realpath 归一（符号链接技能根会解析到真实目录），
    # 入口路径与技能根必须同样归一，否则经符号链接访问时嵌套包入口算不出带层级的
    # 前缀，退化为顶层包名：兄弟包的绝对导入被误判为自导入，整改建议也指错层级。
    abs_init = os.path.realpath(os.path.abspath(init_path))
    layout = layout_of(skill_dir)
    if layout.is_package and layout.package_root:
        package_root = os.path.realpath(os.path.abspath(layout.package_root))
        rel_to_package = os.path.relpath(
            abs_init, package_root).replace("\\", "/")
        if rel_to_package != ".." and not rel_to_package.startswith("../"):
            pkg_parts = rel_to_package.split("/")[:-1]
            suffix = ".".join(pkg_parts)
            prefixes.append(layout.package_name + (
                "." + suffix if suffix else ""))
    else:
        abs_skill = os.path.realpath(os.path.abspath(skill_dir))
        rel = os.path.relpath(abs_init, abs_skill).replace("\\", "/")
        parts = rel.split("/")
        for idx in range(len(parts) - 1, 0, -1):
            pkg_dir = os.path.join(abs_skill, *parts[:idx])
            if os.path.isfile(os.path.join(pkg_dir, "__init__.py")):
                prefixes.append(".".join(parts[:idx]))
                break
    if not prefixes and real_pkg_root:
        prefixes.append(real_pkg_root)
    return tuple(dict.fromkeys(p for p in prefixes if p))
def _find_self_import(
        init_tree: ast.AST, pkg_prefixes: tuple[str, ...],
) -> tuple[ast.ImportFrom, str, str] | None:
    for node in tree_nodes(init_tree):
        if not (isinstance(node, ast.ImportFrom) and node.level == 0
                and node.module is not None):
            continue
        for prefix in pkg_prefixes:
            if _is_self_pkg_name(node.module, prefix):
                return node, node.module, prefix
    return None
def _is_self_pkg_name(module: str, pkg_prefix: str) -> bool:
    return module == pkg_prefix or module.startswith(pkg_prefix + ".")
def _scan_init_self_imports(init_path: str,
                            scope: _ImportScanScope) -> Finding | None:
    init_tree = _load_source_tree(
        init_path, scope.cache, tag="self_import_scan", parsed=scope.parsed)
    if init_tree is None:
        return None
    pkg_prefixes = _self_import_prefixes(
        init_path, scope.skill_dir, scope.real_pkg_root)
    matched = _find_self_import(init_tree, pkg_prefixes)
    if matched is None:
        return None
    node, module, pkg_prefix = matched
    rel = os.path.relpath(init_path, scope.skill_dir).replace("\\", "/")
    return Finding(
        rule_id="D9-SELF-IMPORT",
        severity="P2",
        message=f"自导入反模式: {rel} 应使用相对导入 from . import",
        file=init_path,
        line=node.lineno,
        detail=(f"__init__.py 中绝对导入自身子包 {module}，"
                f"改为 'from .{module[len(pkg_prefix):].lstrip('.')}"
                " import ...'"),
    )
def _iter_init_paths(skill_dir: str):
    for dirpath, dirnames, filenames in os.walk(skill_dir):
        prune_target_dirs(dirnames, include_tests=False)
        init_path = _scannable_init_path(dirpath, filenames)
        if init_path is not None:
            yield init_path
def _scannable_init_path(dirpath: str, filenames) -> str | None:
    init_name = next(
        (f for f in filenames if f.lower() == "__init__.py"), None)
    if init_name is None:
        return None
    init_path = os.path.join(dirpath, init_name)
    return None if is_runtime_temp_path(init_path) else init_path
def _self_import_findings(scope: _ImportScanScope) -> list[Finding]:
    findings: list[Finding] = []
    for init_path in _iter_init_paths(scope.skill_dir):
        finding = _scan_init_self_imports(init_path, scope)
        if finding is not None:
            findings.append(finding)
    return findings
def _check_dotted_from_import(node: ast.ImportFrom, parts: list[str],
                              site: _ImportSite, scope: _ImportScanScope
                              ) -> list[Finding]:
    findings: list[Finding] = []
    base_dir = scope.base_dir(parts[0])
    target_module = ".".join(parts)
    if base_dir is None:
        return [_broken_module_finding(
            site, target_module, line=node.lineno)]
    rel_parts = os.path.join(*parts[1:])
    mod_base = os.path.join(base_dir, rel_parts)
    mod_pkg = os.path.join(mod_base, "__init__.py")
    anchor = _package_first_anchor(mod_base, mod_pkg)
    if anchor is None:
        ns_dir = Path(base_dir).joinpath(*parts[1:])
        if ns_dir.is_dir() and not (ns_dir / "__init__.py").exists():
            findings.extend(_namespace_symbol_findings(
                node, str(ns_dir), target_module, site))
            return findings
        if import_target_exists(mod_base):
            return findings
        findings.append(_broken_module_finding(
            site, target_module, line=node.lineno))
        return findings
    findings.extend(scope.check_symbols(
        node, target_module, anchor, site, base_dir=base_dir))
    return findings
def _check_root_reexport(node: ast.ImportFrom, parts: list[str],
                         site: _ImportSite, scope: _ImportScanScope
                         ) -> list[Finding]:
    findings: list[Finding] = []
    base_dir = scope.base_dir(parts[0])
    if base_dir is None:
        return [_broken_module_finding(
            site, parts[0], line=node.lineno)]
    for alias in node.names:
        symbol = alias.name
        if not _is_checkable_symbol(symbol):
            continue
        if _package_symbol_resolvable(
                base_dir, symbol, scope.cache, base_dir):
            continue
        findings.append(_broken_finding(
            "D9-BROKEN-SYMBOL", site,
            f"根包重导出断链: from {parts[0]} import {symbol}，"
            "该符号既非根子模块也非根 __init__.py 导出",
            f"根包门面未导出符号 {symbol}（可能已改名/迁移），"
            "检查 __init__.py 静态导出或动态导出映射",
            line=node.lineno,
        ))
    return findings
def _file_import_findings(file_tree, site: _ImportSite,
                          scope: _ImportScanScope) -> list[Finding]:
    guarded = collect_import_guarded_ids(file_tree)
    findings: list[Finding] = []
    for node in tree_nodes(file_tree):
        if id(node) in guarded:
            continue
        if isinstance(node, ast.ImportFrom):
            findings.extend(_import_from_findings(node, site, scope))
        elif isinstance(node, ast.Import):
            findings.extend(_check_import_form_broken(node, site, scope))
    return findings
def _import_from_findings(node: ast.ImportFrom, site: _ImportSite,
                          scope: _ImportScanScope) -> list[Finding]:
    if node.level > 0:
        return _check_relative_import(node, site, scope)
    if not node.module:
        return []
    parts = node.module.split(".")
    if parts[0] not in scope.pkg_roots:
        return []
    if len(parts) >= 2:
        return _check_dotted_from_import(node, parts, site, scope)
    if len(parts) == 1:
        return _check_root_reexport(node, parts, site, scope)
    return []
def _module_path_label(fpath: str, skill_dir: str) -> str:
    try:
        rel = os.path.relpath(fpath, skill_dir)
    except ValueError as _e:
        log_swallowed(__name__, _e, context='_module_path_label:ValueError')
        rel = os.path.basename(fpath)
    if rel == '..' or rel.startswith('..' + os.sep):
        rel = os.path.basename(fpath)
    return _module_name(Path(rel))
def import_chain_findings(
        skill_dir: str, py_files: list[str], pkg_roots: set[str], ctx=None,
        *, parsed: dict[str, tuple[ast.AST, str]] | None = None
) -> list[Finding]:
    findings: list[Finding] = []
    real_pkg_root = import_key(os.path.basename(
        os.path.normpath(os.path.abspath(skill_dir))))
    scope = _ImportScanScope(skill_dir, frozenset(pkg_roots),
                            real_pkg_root, ctx, parsed)
    for fpath in py_files:
        file_tree = _load_source_tree(fpath, ctx, parsed=parsed)
        if file_tree is None:
            continue
        site = _ImportSite(
            module_name=_module_path_label(fpath, skill_dir),
            fpath=fpath,
        )
        findings.extend(_file_import_findings(file_tree, site, scope))
    findings.extend(_self_import_findings(scope))
    return findings
def _iter_project_py_files(
        root: Path) -> tuple[list[Path], list[str], set[str], bool]:
    files: list[Path] = []
    walk_errors: list[str] = []
    failed_dirs: set[str] = set()
    root_failed = False
    def _on_walk_error(err: OSError) -> None:
        nonlocal root_failed
        walk_errors.append(str(err))
        failed = getattr(err, "filename", None)
        if not failed:
            return
        try:
            rel = Path(failed).relative_to(root)
        except (TypeError, ValueError) as _swallow_e:
            log_swallowed(
                __name__, _swallow_e,
                context='_iter_project_py_files._on_walk_error:TypeError+')
            return
        if not rel.parts:
            root_failed = True
            return
        failed_dirs.add(_module_name(rel / "__init__.py"))
    for dirpath, dirnames, filenames in os.walk(root, onerror=_on_walk_error):
        prune_target_dirs(dirnames, include_tests=True)
        files.extend(Path(dirpath) / n for n in filenames
                     if not n.startswith(".") and n.lower().endswith(".py"))
    return sorted(files), walk_errors, failed_dirs, root_failed
class _UniverseScan(NamedTuple):
    modules: dict[str, dict]
    parse_errors: list[str]
    unparsed_modules: set[str]
    root_failed: bool = False
class _ModuleLoad(NamedTuple):
    module: str
    entry: dict | None
    error: str
def _universe_result(status: str, scan: _UniverseScan, message: str) -> dict:
    return {
        "status": status,
        "data": {
            "modules": scan.modules,
            "module_count": len(scan.modules),
            "parse_errors": scan.parse_errors,
            "unparsed_modules": sorted(scan.unparsed_modules),
        },
        "message": message,
    }
def _load_module_entry(py: Path, root: Path) -> _ModuleLoad:
    rel = py.relative_to(root)
    module = _module_name(rel)
    source = read_source(str(py))
    if source is None:
        return _failed_load(module, rel, OSError(f"无法读取 {rel}"), "不可读")
    try:
        tree = parse_with_compile(source, filename=str(rel))
    except PARSE_DEGRADE_EXC as e:
        log_swallowed(__name__, e, context='_load_module_entry:PARSE_DEGRADE_EXC')
        return _failed_load(module, rel, e, "不可解析")
    symbols = _top_level_symbols(tree)
    all_surface = _extract_all(tree)
    return _ModuleLoad(module, {
        "symbols": sorted(symbols),
        "all": list(all_surface.names)
        if all_surface is not None and all_surface.complete else None,
        "export_open": _export_surface_open(tree, all_surface),
        "star_reexport": _has_star_reexport(tree),
        "path": str(rel).replace(os.sep, "/"),
    }, "")
def _has_star_reexport(tree: ast.Module) -> bool:
    return any(isinstance(node, ast.ImportFrom)
               and any(alias.name == "*" for alias in node.names)
               for node in _iter_import_time_nodes(tree))
def _universe_has_module_getattr(tree: ast.Module) -> bool:
    return any(_getattr_accepts_name(state)
               for state in _module_getattr_states(tree))
def _export_surface_open(tree: ast.Module,
                         all_surface: _StaticAll | None) -> bool:
    if _universe_has_module_getattr(tree):
        return True
    if all_surface is not None:
        return not all_surface.complete
    return _has_star_reexport(tree)
def _failed_load(module: str, rel: Path, error: Exception,
                 label: str) -> _ModuleLoad:
    logger.warning("[symbol_grounding] 跳过%s文件 %s: %s", label, rel, error)
    return _ModuleLoad(module, None, f"{rel}: {error}")
def _resolve_project_root(project_dir: object) -> Path | None:
    if not project_dir or not isinstance(project_dir, (str, os.PathLike)):
        return None
    try:
        candidate = Path(project_dir)
        return candidate if candidate.is_dir() else None
    except (TypeError, ValueError, OSError) as e:
        log_swallowed(__name__, e, context='build_symbol_universe:TypeError')
        return None
def _scan_project(root: Path) -> _UniverseScan:
    py_files, walk_errors, failed_dirs, root_failed = _iter_project_py_files(root)
    modules: dict[str, dict] = {}
    parse_errors = list(walk_errors)
    unparsed_modules: set[str] = set(failed_dirs)
    for py in py_files:
        loaded = _load_module_entry(py, root)
        if loaded.entry is None:
            parse_errors.append(loaded.error)
            unparsed_modules.add(loaded.module)
            continue
        modules[loaded.module] = loaded.entry
    return _UniverseScan(modules, parse_errors, unparsed_modules, root_failed)
def build_symbol_universe(project_dir: str) -> dict:
    root = _resolve_project_root(project_dir)
    if root is None:
        return _universe_result(
            "error", _UniverseScan({}, [], set()),
            f"项目目录无效: {project_dir!r}")
    scan = _scan_project(root)
    if scan.root_failed:
        return _universe_result(
            "error", scan, f"项目根不可枚举: {project_dir!r}")
    return _universe_result("ok", scan, f"已扫描 {len(scan.modules)} 个模块")

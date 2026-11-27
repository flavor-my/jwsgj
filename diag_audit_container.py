from __future__ import annotations  # noqa: I001
import ast
import logging
from collections.abc import Callable
from dataclasses import dataclass, field
from functools import partial
from itertools import islice
from typing import ClassVar
from jwsgj.diag_shared_ast_bindings import (
    build_scope_index,
    collect_shadow_bindings,
)
from jwsgj.diag_shared_ast_nodes import (
    assign_targets_value,
    block_may_fall_through,
    collect_param_names,
    definition_time_exprs,
    is_constant_expr_stmt,
    iter_def_site_nodes,
    iter_own_scope,
    iter_scope_nodes_with_shadow,
    iter_target_bindings,
    loop_body_has_break,
    module_postpones_annotations,
    split_identifier,
    subtree_node_ids,
)
from jwsgj.diag_shared_ast_views import (
    parent_map as shared_parent_map,
)
from jwsgj.diag_shared_ast_views import (
    tree_nodes,
)
from jwsgj.diag_shared_source_core import (
    TRY_TYPES,
    aligned_source_lines,
    parse_py_file,
    safe_source_line,
    suggest,
)
from jwsgj.diag_types_defs import (
    PatternFinding,
    dedupe_findings,
)
from jwsgj.diag_types_vocab import SEVERITY_RANK
from jwsgj.prevention_scope_facts import walk_nodes
__all__ = [
    "DictInPlaceMutationDetector",
    "EmptyDictStubDetector",
    "ListDictMethodMisuseDetector",
    "LocalVarNotWrittenBackDetector",
    "NoOpExpressionDetector",
    "StringMaxMinComparisonDetector",
]
logger = logging.getLogger(__name__)
logger.info("diag_audit_container 已加载：%d 项导出", len(__all__))
_QUALITY_ROOT_CAUSE = '代码实现中存在代码质量方面的问题, 需要规范化处理。'
def _parse_source(filepath: str,
                  detector_id: str) -> tuple[str, ast.AST] | None:
    source, tree = parse_py_file(filepath, quiet=True)
    if tree is None:
        logger.warning("[AuditPatterns] %s 源文件解析失败，检测跳过: %s",
                       detector_id, filepath)
        return None
    return source, tree
class EmptyDictStubDetector:
    DETECTOR_ID = "D40"
    PATTERN_NAME = "空字典桩检测"
    MIN_RETURN_PATHS = 2
    MAX_DECORATED_BODY = 2
    @staticmethod
    def _own_nodes(func_node: ast.AST,
                   node_types: tuple[type, ...]) -> list[ast.AST]:
        return [node for node in iter_own_scope(func_node, skip_lambda=True)
                if isinstance(node, node_types)]
    def _empty_dict_stub_returns(
            self,
            node: ast.FunctionDef | ast.AsyncFunctionDef) -> list[ast.Return] | None:
        if self._own_nodes(node, (ast.Yield, ast.YieldFrom)):
            return None
        returns = self._own_nodes(node, (ast.Return,))
        if len(returns) < self.MIN_RETURN_PATHS:
            return None
        if block_may_fall_through(node.body):
            return None
        if not self._all_empty_dict_returns(returns):
            return None
        if self._decorator_exempt(node):
            return None
        return returns
    @staticmethod
    def _all_empty_dict_returns(returns: list[ast.Return]) -> bool:
        return all(isinstance(ret.value, ast.Dict) and not ret.value.keys
                   for ret in returns)
    @classmethod
    def _decorator_exempt(cls, node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
        if not node.decorator_list:
            return False
        effective_body = [stmt for stmt in node.body
                          if not is_constant_expr_stmt(stmt)]
        return len(effective_body) <= cls.MAX_DECORATED_BODY
    def detect_file(self, filepath: str) -> list[PatternFinding]:
        parsed = _parse_source(filepath, self.DETECTOR_ID)
        if parsed is None:
            return []
        _source, tree = parsed
        findings: list[PatternFinding] = []
        for node in tree_nodes(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            returns = self._empty_dict_stub_returns(node)
            if returns is None:
                continue
            findings.append(PatternFinding(
                detector_id=self.DETECTOR_ID,
                pattern_name=self.PATTERN_NAME,
                severity="WARN",
                filepath=filepath,
                line=node.lineno,
                snippet=f"{node.name}(...) -> {{}} x{len(returns)}",
                message=f"函数 {node.name} 所有 {len(returns)} 个返回路径均为空 dict",
                suggestion="至少一个分支应返回有意义的键值对",
            ))
        return findings
def _dynamic_binding_events(tree: ast.AST,
                            scope_index: dict[int, str],
                            names: set[str]) -> dict:
    events = {"": _collect_key_binding_events(tree, names)}
    for node in walk_nodes(tree):
        if isinstance(node, ast.ClassDef):
            events[_scope_name(node, scope_index)] = (
                _collect_key_binding_events(node, names))
    return events
def _dynamic_binding_is_active(events, position: tuple[int, int]) -> bool:
    latest_pos = None
    latest_bound = False
    for pos, bound in events:
        if pos > position:
            continue
        if latest_pos is None or pos >= latest_pos:
            latest_pos = pos
            latest_bound = bound
    return latest_bound
def _builtin_shadowed(
        call: ast.Call, name: str, local_bindings: dict, global_names: dict,
        class_scopes: frozenset, scope_index: dict[int, str],
        dynamic_events: dict) -> bool:
    current = scope_index.get(id(call), "")
    position = (call.lineno, call.col_offset)
    first = True
    crossed_function = False
    while True:
        is_class = current in class_scopes
        if not (is_class and not first):
            if name in global_names.get(current, frozenset()):
                if current:
                    if name in local_bindings.get(current, frozenset()):
                        return True
                    crossed_function = crossed_function or not is_class
                    current, first = "", False
                    continue
            elif name in local_bindings.get(current, frozenset()):
                if current and not is_class:
                    return True
                if crossed_function:
                    return True
                events = dynamic_events.get(current, {}).get(name, ())
                if _dynamic_binding_is_active(events, position):
                    return True
        if not current:
            return False
        crossed_function = crossed_function or not is_class
        current = current.rpartition(".")[0]
        first = False
class StringMaxMinComparisonDetector:
    DETECTOR_ID = "D46"
    PATTERN_NAME = "字符串max/min语义错误"
    SEVERITY_ORDER: ClassVar[dict[str, int]] = {
        **{text: -rank for text, rank in SEVERITY_RANK.items()},
        'TRACE': -8, 'DEBUG': -7, 'NOTICE': -3, 'ERR': -1, 'CRIT': 0,
    }
    SEVERITY_LEVELS = frozenset(SEVERITY_ORDER)
    def detect_file(self, filepath: str) -> list[PatternFinding]:
        findings: list[PatternFinding] = []
        parsed = _parse_source(filepath, self.DETECTOR_ID)
        if parsed is None:
            return findings
        source, tree = parsed
        lines = aligned_source_lines(source)
        local_bindings, global_names, class_scopes = collect_shadow_bindings(tree)
        scope_index = build_scope_index(tree)
        dynamic_events = _dynamic_binding_events(
            tree, scope_index, {"max", "min"})
        shadowed_ids = _shadowed_call_ids(tree, _extreme_call_name)
        for node in walk_nodes(tree):
            candidate = self._candidate_call(node)
            if (candidate is None or id(node) in shadowed_ids
                    or _builtin_shadowed(
                        node, node.func.id, local_bindings, global_names,
                        class_scopes, scope_index, dynamic_events)):
                continue
            str_args, lex_result = candidate
            semantic_result = self._semantic_extreme(str_args, node.func.id == 'max')
            lex_order = self.SEVERITY_ORDER.get(lex_result.upper())
            sem_order = self.SEVERITY_ORDER.get(semantic_result.upper())
            if lex_order is None or sem_order is None:
                continue
            if lex_order != sem_order:
                findings.append(self._make_finding(
                    node, str_args, filepath,
                    lex_result=lex_result,
                    semantic_result=semantic_result,
                    source_line=safe_source_line(lines, node.lineno)))
        return findings
    def _candidate_call(self, node: ast.AST) -> tuple[list[str], str] | None:
        if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id in ('max', 'min') and not node.keywords):
            return None
        str_args = self._severity_str_args(node)
        if len(str_args) < 2 or len(str_args) != len(node.args):
            return None
        lex_result = max(str_args) if node.func.id == 'max' else min(str_args)
        return str_args, lex_result
    def _severity_str_args(self, node: ast.Call) -> list[str]:
        str_args: list[str] = []
        for arg in node.args:
            if (isinstance(arg, ast.Constant) and isinstance(arg.value, str)
                    and arg.value.upper() in self.SEVERITY_LEVELS):
                str_args.append(arg.value)
        return str_args
    def _make_finding(self, node: ast.Call, str_args: list[str],
                      filepath: str, *, lex_result: str,
                      semantic_result: str,
                      source_line: str) -> PatternFinding:
        return PatternFinding(
            detector_id=self.DETECTOR_ID,
            pattern_name=self.PATTERN_NAME,
            severity="ERROR",
            filepath=filepath,
            line=node.lineno,
            snippet=source_line[:120],
            message=f"{node.func.id}({', '.join(repr(a) for a in str_args)}) → 字典序结果 '{lex_result}' ≠ 语义结果 '{semantic_result}'",
            suggestion=suggest('代码使用了不规范或有风险的实现方式。该问题属于代码质量类别。', '使用语义排序映射比较,而非字符串 max()/min()')
        )
    def _semantic_extreme(self, values: list[str], want_max: bool) -> str:
        scored = [(v, self.SEVERITY_ORDER.get(v.upper(), -1)) for v in values]
        pick = max if want_max else min
        return pick(scored, key=lambda x: x[1])[0]
def _target_names(nodes) -> set:
    return {name
            for node in nodes
            for name, _lineno, _col_offset in iter_target_bindings(node)}
def _iter_target_leaves(target: ast.AST):
    if isinstance(target, (ast.Tuple, ast.List)):
        for child in target.elts:
            yield from _iter_target_leaves(child)
    elif isinstance(target, ast.Starred):
        yield from _iter_target_leaves(target.value)
    else:
        yield target
def _is_list_construction(
        value: ast.AST,
        list_shadowed: Callable[[ast.Call], bool]) -> bool:
    return isinstance(value, (ast.List, ast.ListComp)) or (
        isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
        and value.func.id == 'list' and not list_shadowed(value))
def _list_binding_pos(target: ast.AST,
                      fallback: tuple[int, int]) -> tuple[int, int]:
    lineno = getattr(target, 'lineno', None)
    col = getattr(target, 'col_offset', None)
    if lineno is None or col is None:
        return fallback
    return (lineno, col)
def _binding_end_pos(value: ast.AST | None,
                     fallback: tuple[int, int]) -> tuple[int, int]:
    end_line = getattr(value, 'end_lineno', None)
    end_col = getattr(value, 'end_col_offset', None)
    if end_line is None or end_col is None:
        return fallback
    return (end_line, end_col)
@dataclass(frozen=True)
class _ListState:
    position: tuple[int, int]
    is_list: bool
    path: frozenset[tuple[int, int]]
    guaranteed_loops: frozenset[int] = frozenset()
def _record_list_state(states: dict, names: set, is_list: bool,
                       pos: tuple[int, int],
                       path: frozenset[tuple[int, int]]) -> None:
    for name in names:
        states.setdefault(name, []).append(_ListState(pos, is_list, path))
def _in_branch(current: ast.AST, branch) -> bool:
    return current is branch if isinstance(branch, ast.AST) else current in branch
def _parent_branch_decisions(parent: ast.AST,
                             current: ast.AST) -> set[tuple[int, int]]:
    if isinstance(parent, (ast.If, ast.IfExp)):
        if _in_branch(current, parent.body):
            return {(id(parent), 1)}
        if _in_branch(current, parent.orelse):
            return {(id(parent), 0)}
    if isinstance(parent, (ast.For, ast.AsyncFor, ast.While)):
        if current in parent.body:
            return {(id(parent), 1)}
        if current in parent.orelse and loop_body_has_break(parent.body):
            return {(id(parent.orelse), 1)}
        return set()
    if isinstance(parent, TRY_TYPES):
        if current in parent.body or current in parent.orelse:
            return {(id(parent), 0)}
        for index, handler in enumerate(parent.handlers, start=1):
            if current is handler:
                return {(id(parent), index)}
    if isinstance(parent, ast.Match):
        for index, case in enumerate(parent.cases):
            if current is case:
                return {(id(parent), index)}
    if isinstance(parent, ast.BoolOp):
        return ({(id(parent), 1)}
                if any(value is current for value in parent.values[1:]) else set())
    return set()
def _branch_path(node: ast.AST, parents: dict[ast.AST, ast.AST],
                 scope: ast.AST) -> frozenset[tuple[int, int]]:
    decisions: set[tuple[int, int]] = set()
    current = node
    while current is not scope:
        parent = parents.get(current)
        if parent is None:
            break
        decisions.update(_parent_branch_decisions(parent, current))
        current = parent
    return frozenset(decisions)
def _paths_compatible(first: frozenset[tuple[int, int]],
                      second: frozenset[tuple[int, int]]) -> bool:
    decisions = dict(first)
    return all(decision not in decisions or decisions[decision] == value
               for decision, value in second)
def _branch_worlds(base: frozenset[tuple[int, int]], decisions: list[int],
                   arity: dict[int, int]):
    stack = [(base, 0)]
    while stack:
        world, index = stack.pop()
        if index == len(decisions):
            yield world
            continue
        decision = decisions[index]
        if decision in dict(world):
            stack.append((world, index + 1))
            continue
        values = range(max(arity.get(decision, 2), 2))
        for value in reversed(values):
            stack.append((world | {(decision, value)}, index + 1))
def _loop_has_known_nonempty_iter(node: ast.AST) -> bool:
    return (isinstance(node, (ast.For, ast.AsyncFor))
            and isinstance(node.iter, (ast.List, ast.Tuple, ast.Set))
            and bool(node.iter.elts))


def _state_guaranteed_loops(
        record: _ListState, loop_nodes: dict[int, ast.AST]) -> frozenset[int]:
    guaranteed: set[int] = set()
    for decision, value in record.path:
        loop = loop_nodes.get(decision)
        if value != 1 or not _loop_has_known_nonempty_iter(loop) or not loop.body:
            continue
        first = loop.body[0]
        start = (first.lineno, first.col_offset)
        end = (first.end_lineno, first.end_col_offset)
        if start <= record.position <= end:
            guaranteed.add(decision)
    return frozenset(guaranteed)


def _is_trivially_nonraising(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant):
        return True
    if isinstance(node, ast.Name):
        return not isinstance(node.ctx, ast.Load)
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return all(_is_trivially_nonraising(elt) for elt in node.elts)
    if isinstance(node, ast.Dict):
        return all(key is not None and _is_trivially_nonraising(key)
                   for key in node.keys) and all(
                       _is_trivially_nonraising(value) for value in node.values)
    return False
def _potential_exception_events(
        scope: ast.AST, parents: dict[ast.AST, ast.AST],
        scope_nodes: tuple[ast.AST, ...]) -> tuple:
    events = []
    for node in scope_nodes:
        is_exception_source = isinstance(
            node, (ast.Raise, ast.Assert, ast.Import, ast.ImportFrom)) or (
                isinstance(node, ast.expr) and not _is_trivially_nonraising(node))
        if not is_exception_source:
            continue
        end_line = getattr(node, 'end_lineno', None)
        end_col = getattr(node, 'end_col_offset', None)
        if end_line is None or end_col is None:
            continue
        events.append(((end_line, end_col), _branch_path(node, parents, scope)))
    return tuple(events)
def _exception_transition_path(
        candidate: _ListState, killers: list[_ListState],
        operation_path: frozenset[tuple[int, int]],
        try_ids: frozenset[int], exception_events: tuple,
        ) -> frozenset[tuple[int, int]] | None:
    candidate_decisions = dict(candidate.path)
    operation_decisions = dict(operation_path)
    transitions = {
        decision for decision in try_ids
        if candidate_decisions.get(decision) == 0
        and operation_decisions.get(decision) != 0
    }
    if not transitions:
        return candidate.path
    for killer in killers:
        killer_decisions = dict(killer.path)
        direct_killer = killer.path <= candidate.path and any(
            killer_decisions.get(decision) == 0 for decision in transitions)
        if not direct_killer:
            continue
        interrupted = any(
            candidate.position < event_pos <= killer.position
            and _paths_compatible(event_path, candidate.path)
            and _paths_compatible(event_path, killer.path)
            for event_pos, event_path in exception_events)
        if not interrupted:
            return None
    return frozenset(
        (decision, value) for decision, value in candidate.path
        if decision not in transitions)
def _killer_blocks_world(
        candidate: _ListState, killer: _ListState,
        world: frozenset[tuple[int, int]], try_ids: frozenset[int],
        exception_events: tuple) -> bool:
    if _paths_compatible(world, killer.path):
        return True
    world_decisions = dict(world)
    killer_decisions = dict(killer.path)
    phantom_skips = {
        decision for decision in killer.guaranteed_loops
        if killer_decisions.get(decision) == 1
        and world_decisions.get(decision, 0) == 0
    }
    if phantom_skips:
        guaranteed_path = frozenset(
            (decision, value) for decision, value in killer.path
            if decision not in phantom_skips)
        if _paths_compatible(world, guaranteed_path):
            return True
    transitions = {
        decision for decision in try_ids
        if killer_decisions.get(decision) == 0
        and world_decisions.get(decision, 0) > 0
    }
    if not transitions:
        return False
    stripped_killer = frozenset(
        (decision, value) for decision, value in killer.path
        if decision not in transitions)
    if not _paths_compatible(world, stripped_killer):
        return False
    for event_pos, event_path in exception_events:
        if not candidate.position < event_pos <= killer.position:
            continue
        event_decisions = dict(event_path)
        if not any(event_decisions.get(decision) == 0
                   for decision in transitions):
            continue
        stripped_event = frozenset(
            (decision, value) for decision, value in event_path
            if decision not in transitions)
        if (_paths_compatible(stripped_event, world)
                and _paths_compatible(stripped_event, stripped_killer)):
            return False
    return True
def _list_state_reaches(candidate: _ListState, later: list[_ListState],
                        operation_path: frozenset[tuple[int, int]],
                        operation_pos: tuple[int, int],
                        try_ids: frozenset[int], exception_events: tuple) -> bool:
    if candidate.position >= operation_pos:
        return False
    killers = [record for record in later
               if candidate.position <= record.position < operation_pos]
    candidate_path = _exception_transition_path(
        candidate, killers, operation_path, try_ids, exception_events)
    if candidate_path is None or not _paths_compatible(
            candidate_path, operation_path):
        return False
    base = candidate_path | operation_path
    paths = (base, *(record.path for record in killers))
    decisions = sorted({decision for path in paths for decision, _ in path})
    arity: dict[int, int] = {}
    for path in paths:
        for decision, value in path:
            arity[decision] = max(arity.get(decision, 0), value + 1)
    world_count = 1
    for decision in decisions:
        world_count *= max(arity.get(decision, 2), 2)
    worlds = _branch_worlds(base, decisions, arity)
    if world_count > 1024:
        worlds = islice(worlds, 1024)
    return any(
        not any(_killer_blocks_world(
            candidate, killer, world, try_ids, exception_events)
                for killer in killers)
        for world in worlds)
_COMP_TYPES = (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
_DICT_ONLY_METHODS = frozenset({
    'keys', 'values', 'items', 'get', 'setdefault', 'update',
    'fromkeys', 'popitem',
})
def _comp_result_nodes(comp: ast.AST) -> tuple[ast.AST, ...]:
    if isinstance(comp, ast.DictComp):
        return comp.key, comp.value
    return comp.elt,
def _lambda_default_ids(lam: ast.Lambda) -> frozenset[int]:
    defaults = [
        *(lam.args.defaults or ()),
        *(d for d in (lam.args.kw_defaults or ()) if d is not None),
    ]
    return frozenset(
        node_id
        for default in defaults
        for node_id in subtree_node_ids([default]))
def _shadowed_calls_in(scope_node: ast.AST, names: set[str],
                       name_of: Callable[[ast.AST], str | None],
                       outer_scope_ids: frozenset[int] = frozenset(),
                       ) -> set[int]:
    if not names:
        return set()
    shadowed: set[int] = set()
    for sub in walk_nodes(scope_node):
        if id(sub) in outer_scope_ids:
            continue
        name = name_of(sub)
        if name is not None and name in names:
            shadowed.add(id(sub))
    return shadowed
def _lambda_assignment_names(lam: ast.Lambda) -> set[str]:
    names: set[str] = set()
    stack: list[ast.AST] = [lam.body]
    while stack:
        cur = stack.pop()
        if isinstance(cur, ast.Lambda):
            _push_lambda_defaults(stack, cur.args)
            continue
        if isinstance(cur, ast.NamedExpr) and isinstance(cur.target, ast.Name):
            names.add(cur.target.id)
        stack.extend(ast.iter_child_nodes(cur))
    return names
def _shadowed_call_ids(root: ast.AST,
                       name_of: Callable[[ast.AST], str | None]) -> set[int]:
    shadowed: set[int] = set()
    for node in walk_nodes(root):
        if isinstance(node, _COMP_TYPES):
            visible: set[str] = set()
            for generator in node.generators:
                shadowed |= _shadowed_calls_in(
                    generator.iter, visible, name_of)
                visible |= _target_names([generator.target])
                for condition in generator.ifs:
                    shadowed |= _shadowed_calls_in(condition, visible, name_of)
            for result_node in _comp_result_nodes(node):
                shadowed |= _shadowed_calls_in(result_node, visible, name_of)
        elif isinstance(node, ast.Lambda):
            local_names = (collect_param_names(node)
                           | _lambda_assignment_names(node))
            if local_names:
                shadowed |= _shadowed_calls_in(
                    node, local_names, name_of, _lambda_default_ids(node))
    return shadowed
def _scope_nodes(tree: ast.AST) -> list[ast.AST]:
    return [tree, *[node for node in walk_nodes(tree)
                     if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                          ast.ClassDef))]]
def _scope_name(node: ast.AST, scope_index: dict[int, str]) -> str:
    name = getattr(node, "name", "")
    if not name:
        return ""
    if isinstance(node, ast.ClassDef) and node.body:
        class_scope = scope_index.get(id(node.body[0]))
        if class_scope is not None:
            return class_scope
    outer = scope_index.get(id(node), "")
    return f"{outer}.{name}" if outer else name
def _definition_runtime_exprs(
        node: ast.AST, annotations_evaluated: bool) -> list[ast.AST]:
    if (not annotations_evaluated
            and isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))):
        return _definition_outer_exprs(node)
    return list(iter_def_site_nodes(node))
def _list_scope_nodes(
        scope: ast.AST, annotations_evaluated: bool) -> tuple[ast.AST, ...]:
    current_outer_ids = frozenset(
        node_id
        for expr in _definition_runtime_exprs(scope, annotations_evaluated)
        for node_id in subtree_node_ids([expr]))
    own_nodes = [node for node in iter_own_scope(scope)
                 if id(node) not in current_outer_ids]
    outer_nodes: list[ast.AST] = []
    for node in own_nodes:
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef)):
            continue
        for expr in _definition_runtime_exprs(node, annotations_evaluated):
            outer_nodes.extend(iter_own_scope(expr, include_self=True))
    return (*own_nodes, *outer_nodes)
def _dict_method_call_name(node: ast.AST) -> str | None:
    if (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in _DICT_ONLY_METHODS
            and isinstance(node.func.value, ast.Name)):
        return node.func.value.id
    return None
def _extreme_call_name(node: ast.AST) -> str | None:
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in ('max', 'min')):
        return node.func.id
    return None
def _dict_literal_written_keys(mapping: ast.AST) -> set[str] | None:
    if not isinstance(mapping, ast.Dict):
        return None
    keys: set[str] = set()
    for key in mapping.keys:
        if not isinstance(key, ast.Name):
            return None
        keys.add(key.id)
    return keys
def _call_written_keys(call: ast.Call) -> set[str] | None:
    attr = call.func.attr
    if attr in {'setdefault', '__setitem__'}:
        expected_args = 2 if attr == '__setitem__' else (1, 2)
        arg_count_ok = (len(call.args) == expected_args
                        if isinstance(expected_args, int)
                        else len(call.args) in expected_args)
        if call.keywords or not arg_count_ok:
            return None
        key = call.args[0]
        return {key.id} if isinstance(key, ast.Name) else None
    if attr == 'update' and not call.args and not call.keywords:
        return set()
    if attr in {'update', '__ior__'}:
        if call.keywords or len(call.args) != 1:
            return None
        return _dict_literal_written_keys(call.args[0])
    return None
class ListDictMethodMisuseDetector:
    DETECTOR_ID = "D47"
    PATTERN_NAME = "对list调用dict方法"
    def _exclude_binding_names(
            self, states: dict, pos: tuple[int, int],
            path: frozenset[tuple[int, int]], *targets) -> None:
        for tgt in targets:
            _record_list_state(states, _target_names([tgt]), False, pos, path)
    def _make_finding(self, child: ast.Call, filepath: str) -> PatternFinding:
        var_name = child.func.value.id
        return PatternFinding(
            detector_id=self.DETECTOR_ID,
            pattern_name=self.PATTERN_NAME,
            severity="ERROR",
            filepath=filepath,
            line=child.lineno,
            snippet=f"{var_name}.{child.func.attr}(...)",
            message=f"变量 {var_name} 是 list,调用 .{child.func.attr}() 将抛 AttributeError",
            suggestion=suggest('数据结构与调用方法类型不匹配。该问题属于代码质量类别。',
                        f"改用列表方法(如 in/索引/append),或把 {var_name} 改为 dict 后再调用 .{child.func.attr}()")
        )
    def _classify_unknown_unpack_target(
            self, target: ast.AST, states: dict, pos: tuple[int, int],
            path: frozenset[tuple[int, int]]) -> None:
        if isinstance(target, ast.Starred):
            _record_list_state(
                states, _target_names([target]), True, pos, path)
            return
        if isinstance(target, (ast.Tuple, ast.List)):
            for child in target.elts:
                self._classify_unknown_unpack_target(child, states, pos, path)
            return
        self._exclude_binding_names(states, pos, path, target)
    def _classify_unpack_target(
            self, target: ast.AST, value: ast.AST, states: dict,
            pos: tuple[int, int], path: frozenset[tuple[int, int]],
            list_shadowed: Callable[[ast.Call], bool]) -> None:
        if isinstance(target, ast.Starred):
            _record_list_state(
                states, _target_names([target]), True, pos, path)
            return
        if isinstance(target, ast.Name):
            _record_list_state(
                states, {target.id},
                _is_list_construction(value, list_shadowed), pos, path)
            return
        if not isinstance(target, (ast.Tuple, ast.List)):
            self._exclude_binding_names(states, pos, path, target)
            return
        if not (isinstance(value, (ast.Tuple, ast.List))
                and len(target.elts) == len(value.elts)):
            self._classify_unknown_unpack_target(target, states, pos, path)
            return
        for child_target, child_value in zip(
                target.elts, value.elts, strict=True):
            self._classify_unpack_target(
                child_target, child_value, states, pos, path, list_shadowed)
    def _classify_assign(
            self, node: ast.Assign, states: dict, pos: tuple[int, int],
            path: frozenset[tuple[int, int]],
            list_shadowed: Callable[[ast.Call], bool]) -> None:
        is_list = _is_list_construction(node.value, list_shadowed)
        bind_pos = _binding_end_pos(node.value, pos)
        for target in node.targets:
            if isinstance(target, ast.Name):
                _record_list_state(states, {target.id}, is_list, bind_pos, path)
            elif isinstance(target, (ast.Tuple, ast.List)):
                self._classify_unpack_target(
                    target, node.value, states, bind_pos, path, list_shadowed)
    def _classify_annassign_or_loop(
            self, node, states: dict, pos: tuple[int, int],
            path: frozenset[tuple[int, int]],
            list_shadowed: Callable[[ast.Call], bool]) -> None:
        if isinstance(node, ast.AnnAssign):
            if node.value is None:
                return
            bind_pos = _binding_end_pos(node.value, pos)
            if (isinstance(node.target, ast.Name)
                    and _is_list_construction(node.value, list_shadowed)):
                _record_list_state(states, {node.target.id}, True, bind_pos, path)
            else:
                self._exclude_binding_names(states, bind_pos, path, node.target)
            return
        nonempty_literal = _loop_has_known_nonempty_iter(node)
        loop_path = path if nonempty_literal else path | {(id(node), 1)}
        self._classify_unknown_unpack_target(
            node.target, states, _binding_end_pos(node.iter, pos), loop_path)
    def _exclude_value_bindings(
            self, node: ast.AST, states: dict, pos: tuple[int, int],
            path: frozenset[tuple[int, int]],
            list_shadowed: Callable[[ast.Call], bool]) -> None:
        if isinstance(node, ast.NamedExpr):
            _record_list_state(
                states, _target_names([node.target]),
                _is_list_construction(node.value, list_shadowed),
                _binding_end_pos(node.value,
                                 _list_binding_pos(node.target, pos)), path)
        if isinstance(node, ast.withitem) and node.optional_vars is not None:
            self._classify_unknown_unpack_target(
                node.optional_vars, states,
                _list_binding_pos(node.optional_vars, pos), path)
        if isinstance(node, ast.MatchStar) and node.name:
            _record_list_state(states, {node.name}, True, pos, path)
        elif (isinstance(node, (ast.ExceptHandler, ast.MatchAs))
              and node.name):
            _record_list_state(states, {node.name}, False, pos, path)
        if isinstance(node, ast.Delete):
            self._exclude_binding_names(states, pos, path, *node.targets)
    def _exclude_decl_bindings(
            self, node: ast.AST, states: dict, pos: tuple[int, int],
            path: frozenset[tuple[int, int]]) -> None:
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            for alias in node.names:
                _record_list_state(
                    states, {alias.asname or alias.name.split('.')[0]},
                    False, pos, path)
        if isinstance(node, ast.MatchMapping) and node.rest:
            _record_list_state(states, {node.rest}, False, pos, path)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            _record_list_state(
                states, {node.name}, False, _binding_end_pos(node, pos), path)
    def _collect_list_states(
            self, func_node: ast.AST, *,
            list_shadowed: Callable[[ast.Call], bool],
            parents: dict[ast.AST, ast.AST],
            scope_nodes: tuple[ast.AST, ...]) -> dict:
        states: dict[str, list[_ListState]] = {}
        for node in scope_nodes:
            pos = (getattr(node, 'lineno', 0) or 0,
                   getattr(node, 'col_offset', 0) or 0)
            path = _branch_path(node, parents, func_node)
            if isinstance(node, ast.Assign):
                self._classify_assign(node, states, pos, path, list_shadowed)
            if isinstance(node, (ast.AnnAssign, ast.For, ast.AsyncFor)):
                self._classify_annassign_or_loop(
                    node, states, pos, path, list_shadowed)
            self._exclude_value_bindings(
                node, states, pos, path, list_shadowed)
            self._exclude_decl_bindings(node, states, pos, path)
        for records in states.values():
            records.sort(key=lambda record: record.position)
        return states
    @staticmethod
    def _is_list_at(
            states: dict, name: str, operation: ast.Call,
            parents: dict[ast.AST, ast.AST], scope: ast.AST,
            scope_nodes: tuple[ast.AST, ...]) -> bool:
        operation_pos = (operation.lineno, operation.col_offset)
        operation_path = _branch_path(operation, parents, scope)
        loop_nodes = {
            id(parent): parent for parent in parents.values()
            if isinstance(parent, (ast.For, ast.AsyncFor))}
        records = [
            _ListState(record.position, record.is_list, record.path,
                       _state_guaranteed_loops(record, loop_nodes))
            for record in states.get(name, ())]
        try_ids = frozenset(
            id(parent) for parent in parents.values()
            if isinstance(parent, TRY_TYPES))
        exception_events = (
            _potential_exception_events(scope, parents, scope_nodes)
            if try_ids else ())
        return any(
            candidate.is_list and _list_state_reaches(
                candidate, list(records[index + 1:]),
                operation_path, operation_pos, try_ids, exception_events)
            for index, candidate in enumerate(records))
    def detect_file(self, filepath: str) -> list[PatternFinding]:
        findings: list[PatternFinding] = []
        parsed = _parse_source(filepath, self.DETECTOR_ID)
        if parsed is None:
            return findings
        _source, tree = parsed
        local_bindings, global_names, class_scopes = collect_shadow_bindings(tree)
        scope_index = build_scope_index(tree)
        dynamic_events = _dynamic_binding_events(tree, scope_index, {"list"})
        list_shadowed = partial(
            _builtin_shadowed, name="list", local_bindings=local_bindings,
            global_names=global_names, class_scopes=class_scopes,
            scope_index=scope_index, dynamic_events=dynamic_events)
        annotations_evaluated = not module_postpones_annotations(tree)
        for scope_node in _scope_nodes(tree):
            findings.extend(self._scan_scope(
                scope_node, filepath, list_shadowed=list_shadowed,
                annotations_evaluated=annotations_evaluated))
        return dedupe_findings(findings)
    def _scan_scope(
            self, node: ast.AST, filepath: str, *,
            list_shadowed: Callable[[ast.Call], bool],
            annotations_evaluated: bool) -> list[PatternFinding]:
        parents = shared_parent_map(node)
        scope_nodes = _list_scope_nodes(node, annotations_evaluated)
        states = self._collect_list_states(
            node, list_shadowed=list_shadowed, parents=parents,
            scope_nodes=scope_nodes)
        if not states:
            return []
        shadowed_ids = _shadowed_call_ids(node, _dict_method_call_name)
        findings: list[PatternFinding] = []
        for child in scope_nodes:
            if id(child) in shadowed_ids:
                continue
            name = _dict_method_call_name(child)
            if name not in states:
                continue
            if self._is_list_at(
                    states, name, child, parents, node, scope_nodes):
                findings.append(self._make_finding(child, filepath))
        return findings
@dataclass(frozen=True)
class _UnwrittenWriteHit:
    var: str
    container: str
    method: str
    lineno: int
class LocalVarNotWrittenBackDetector:
    DETECTOR_ID = "D44"
    PATTERN_NAME = "局部变量未写回容器"
    STRING_METHODS = frozenset({
        'replace', 'strip', 'lstrip', 'rstrip', 'upper', 'lower',
        'title', 'capitalize', 'swapcase', 'expandtabs',
        'center', 'ljust', 'rjust', 'zfill',
        'split', 'rsplit', 'splitlines', 'partition', 'rpartition',
        'format', 'format_map', 'join', 'casefold', 'translate',
        'encode', 'removeprefix', 'removesuffix',
    })
    @staticmethod
    def _collect_container_writes(targets: list, func_writes: list,
                                  value: ast.AST) -> None:
        def collect(target: ast.AST, assigned_value: ast.AST) -> None:
            if (isinstance(target, ast.Subscript)
                    and isinstance(target.value, ast.Name)):
                func_writes.append((target, assigned_value))
                return
            if not isinstance(target, (ast.Tuple, ast.List)):
                return
            if (not isinstance(assigned_value, (ast.Tuple, ast.List))
                    or len(target.elts) != len(assigned_value.elts)
                    or any(isinstance(node, ast.Starred)
                           for node in (*target.elts, *assigned_value.elts))):
                return
            for child_target, child_value in zip(
                    target.elts, assigned_value.elts, strict=True):
                collect(child_target, child_value)
        for w_tgt in targets:
            collect(w_tgt, value)
    @staticmethod
    def _collect_scope_writes_and_candidates(
            func_node: ast.AST) -> tuple[list[ast.Subscript], list[tuple]]:
        func_writes: list[tuple[ast.Subscript, ast.AST]] = []
        candidate_stmts: list[tuple] = []
        for w_node in iter_own_scope(func_node, skip_lambda=True):
            assigned = assign_targets_value(w_node)
            if assigned is not None:
                targets, value = assigned
                LocalVarNotWrittenBackDetector._collect_container_writes(
                    targets, func_writes, value)
                candidate_stmts.append((targets, value,
                                        w_node.lineno, w_node.col_offset))
            elif isinstance(w_node, ast.AugAssign):
                LocalVarNotWrittenBackDetector._collect_container_writes(
                    [w_node.target], func_writes, w_node.value)
        return func_writes, candidate_stmts
    @staticmethod
    def _read_modify_subscript(value: ast.AST) -> ast.Subscript | None:
        if (isinstance(value, ast.Call)
                and isinstance(value.func, ast.Attribute)
                and value.func.attr in LocalVarNotWrittenBackDetector.STRING_METHODS
                and isinstance(value.func.value, ast.Subscript)
                and isinstance(value.func.value.value, ast.Name)):
            return value.func.value
        return None
    @staticmethod
    def _value_uses_name(value: ast.AST, var_name: str) -> bool:
        lambda_body_ids = {
            node_id
            for node in walk_nodes(value) if isinstance(node, ast.Lambda)
            for node_id in subtree_node_ids([node.body])
        }
        if (isinstance(value, ast.Name) and isinstance(value.ctx, ast.Load)
                and value.id == var_name):
            return True
        return any(
            isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
            and node.id == var_name and var_name not in shadowed
            and id(node) not in lambda_body_ids
            for node, shadowed in iter_scope_nodes_with_shadow(value)
        )
    @classmethod
    def _derived_rebind_positions(
            cls, func_node: ast.AST, var_name: str) -> set[tuple[int, int]]:
        positions: set[tuple[int, int]] = set()
        for node in iter_own_scope(func_node, skip_lambda=True):
            if isinstance(node, (ast.AugAssign, ast.NamedExpr)):
                targets, value = [node.target], node.value
            else:
                assigned = assign_targets_value(node)
                if assigned is None:
                    continue
                targets, value = assigned
            if (len(targets) == 1 and isinstance(targets[0], ast.Name)
                    and targets[0].id == var_name
                    and (isinstance(node, ast.AugAssign)
                         or cls._value_uses_name(value, var_name))):
                positions.add((targets[0].lineno, targets[0].col_offset))
        return positions
    @classmethod
    def _binding_reaches_writeback(
            cls, func_node: ast.AST, source: ast.Subscript, var_name: str,
            stmt_pos: tuple[int, int], target: ast.Subscript, *,
            for_read_dependency: bool = False) -> bool:
        parents = shared_parent_map(func_node)
        source_path = _branch_path(source, parents, func_node)
        target_path = _branch_path(target, parents, func_node)
        if not _paths_compatible(source_path, target_path):
            return False
        target_pos = (target.lineno, target.col_offset)
        derived = (set() if for_read_dependency else
                   cls._derived_rebind_positions(func_node, var_name))
        source_positions = (
            {(getattr(node, 'lineno', 0), getattr(node, 'col_offset', 0))
             for node in walk_nodes(source)}
            if for_read_dependency else set())
        events = _collect_key_binding_events(
            func_node, {var_name}).get(var_name, ())
        between = [
            pos for pos, _bound in events
            if (stmt_pos <= pos if for_read_dependency else stmt_pos < pos)
            and pos < target_pos and pos not in derived
            and pos not in source_positions
        ]
        if not between:
            return True
        position_nodes = {
            (getattr(node, 'lineno', 0), getattr(node, 'col_offset', 0)): node
            for node in iter_own_scope(func_node, skip_lambda=True)
        }
        for pos in between:
            event_node = position_nodes.get(pos)
            if event_node is None:
                return False
            event_path = _branch_path(event_node, parents, func_node)
            if (_paths_compatible(source_path, event_path)
                    and _paths_compatible(event_path, target_path)):
                return False
        return True
    @classmethod
    def _read_dependencies_reach_writeback(
            cls, func_node: ast.AST, source: ast.Subscript,
            stmt_pos: tuple[int, int], target: ast.Subscript) -> bool:
        dependency_names = {source.value.id}
        dependency_names.update(
            node.id for node in walk_nodes(source.slice)
            if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load))
        return (all(
            cls._binding_reaches_writeback(
                func_node, source, name, stmt_pos, target,
                for_read_dependency=True)
            for name in dependency_names)
            and cls._composite_dependencies_reach_writeback(
                func_node, source, stmt_pos, target))

    @staticmethod
    def _dependency_form(node: ast.Attribute | ast.Subscript) -> str:
        if isinstance(node, ast.Attribute):
            node = ast.Attribute(
                value=node.value, attr=node.attr, ctx=ast.Load())
        else:
            node = ast.Subscript(
                value=node.value, slice=node.slice, ctx=ast.Load())
        return ast.dump(node, include_attributes=False)

    @classmethod
    def _composite_dependencies_reach_writeback(
            cls, func_node: ast.AST, source: ast.Subscript,
            stmt_pos: tuple[int, int], target: ast.Subscript) -> bool:
        dependency_forms = {
            cls._dependency_form(node) for node in walk_nodes(source.slice)
            if isinstance(node, (ast.Attribute, ast.Subscript))}
        if not dependency_forms:
            return True
        parents = shared_parent_map(func_node)
        source_path = _branch_path(source, parents, func_node)
        target_path = _branch_path(target, parents, func_node)
        target_pos = (target.lineno, target.col_offset)
        for node in iter_own_scope(func_node, skip_lambda=True):
            assigned = assign_targets_value(node)
            if assigned is not None:
                targets = assigned[0]
            elif isinstance(node, (ast.AugAssign, ast.For, ast.AsyncFor)):
                targets = [node.target]
            elif isinstance(node, ast.Delete):
                targets = node.targets
            elif (isinstance(node, ast.withitem)
                  and node.optional_vars is not None):
                targets = [node.optional_vars]
            else:
                continue
            for write_target in targets:
                for leaf in _iter_target_leaves(write_target):
                    if (not isinstance(leaf, (ast.Attribute, ast.Subscript))
                            or cls._dependency_form(leaf) not in dependency_forms):
                        continue
                    pos = (leaf.lineno, leaf.col_offset)
                    if not (stmt_pos <= pos < target_pos):
                        continue
                    event_path = _branch_path(leaf, parents, func_node)
                    if (_paths_compatible(source_path, event_path)
                            and _paths_compatible(event_path, target_path)):
                        return False
        return True
    @classmethod
    def _has_precise_writeback(
            cls, func_node: ast.AST,
            func_writes: list[tuple[ast.Subscript, ast.AST]],
            source: ast.Subscript, var_name: str,
            stmt_pos: tuple[int, int]) -> bool:
        container_name = source.value.id
        source_slice = ast.dump(source.slice, include_attributes=False)
        for target, value in func_writes:
            if (target.value.id != container_name
                    or (target.lineno, target.col_offset) <= stmt_pos
                    or ast.dump(target.slice, include_attributes=False) != source_slice):
                continue
            if (cls._value_uses_name(value, var_name)
                    and cls._binding_reaches_writeback(
                        func_node, source, var_name, stmt_pos, target)
                    and cls._read_dependencies_reach_writeback(
                        func_node, source, stmt_pos, target)):
                return True
        return False
    _WRITEBACK_HINTS = frozenset(
        {'new', 'modified', 'updated', 'result', 'fixed'})
    @staticmethod
    def _hints_new_value(var_name: str) -> bool:
        return bool(set(split_identifier(var_name))
                    & LocalVarNotWrittenBackDetector._WRITEBACK_HINTS)
    def detect_file(self, filepath: str) -> list[PatternFinding]:
        findings: list[PatternFinding] = []
        parsed = _parse_source(filepath, self.DETECTOR_ID)
        if parsed is None:
            return findings
        _source, tree = parsed
        for node in walk_nodes(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                findings.extend(self._scan_function_scope(node, filepath))
        return findings
    def _scan_function_scope(self, func_node: ast.AST,
                             filepath: str) -> list[PatternFinding]:
        func_writes, candidate_stmts = (
            self._collect_scope_writes_and_candidates(func_node))
        findings: list[PatternFinding] = []
        for targets, value, stmt_lineno, stmt_col in candidate_stmts:
            source = self._read_modify_subscript(value)
            if source is None:
                continue
            container_name = source.value.id
            for var_name in self._unwritten_targets(
                    func_node, targets, source, func_writes,
                    (stmt_lineno, stmt_col)):
                findings.append(self._make_finding(_UnwrittenWriteHit(
                    var_name, container_name, value.func.attr,
                    stmt_lineno), filepath))
        return findings
    def _unwritten_targets(self, func_node: ast.AST, targets,
                           source: ast.Subscript,
                           func_writes: list[tuple[ast.Subscript, ast.AST]],
                           stmt_pos: tuple[int, int]) -> list[str]:
        source_slice = ast.dump(source.slice, include_attributes=False)
        if any(
                isinstance(tgt, ast.Subscript)
                and isinstance(tgt.value, ast.Name)
                and tgt.value.id == source.value.id
                and ast.dump(tgt.slice, include_attributes=False) == source_slice
                for tgt in targets):
            return []
        return [
            tgt.id for tgt in targets
            if isinstance(tgt, ast.Name)
            and tgt.id != source.value.id
            and self._hints_new_value(tgt.id)
            and not self._has_precise_writeback(
                func_node, func_writes, source, tgt.id, stmt_pos)
        ]
    def _make_finding(self, hit: _UnwrittenWriteHit,
                      filepath: str) -> PatternFinding:
        return PatternFinding(
            detector_id=self.DETECTOR_ID,
            pattern_name=self.PATTERN_NAME,
            severity="WARN",
            filepath=filepath,
            line=hit.lineno,
            snippet=f"{hit.var} = {hit.container}[...].{hit.method}(...)",
            message=f"变量 {hit.var} 从 {hit.container} 读取并修改,但未写回 {hit.container}",
            suggestion=suggest('代码缺少必要的元素。该问题属于代码质量类别。',
                                f"添加写回语句: {hit.container}[idx] = {hit.var}")
        )
class NoOpExpressionDetector:
    DETECTOR_ID = "D45"
    PATTERN_NAME = "无效表达式语句(no-op)"
    _EXEMPT_VALUE_TYPES = (ast.Call, ast.Yield, ast.YieldFrom, ast.Await)
    _NOOP_FORMS = (
        (ast.BinOp, "WARN",
         "表达式语句无赋值目标,不产生效果: {snippet}",
         '添加赋值目标或使用增强赋值: var = ... 或 var += ...'),
        (ast.Compare, "INFO",
         "比较表达式作为独立语句,结果被丢弃: {snippet}",
         '如果需要断言,使用 assert;如果需要赋值,添加赋值目标'),
    )
    @staticmethod
    def _is_unwritten_container_string_call(value: ast.AST) -> bool:
        return (isinstance(value, ast.Call)
                and isinstance(value.func, ast.Attribute)
                and value.func.attr in LocalVarNotWrittenBackDetector.STRING_METHODS
                and isinstance(value.func.value, ast.Subscript))
    def _is_exempt(self, node: ast.Expr) -> bool:
        value = node.value
        if self._is_unwritten_container_string_call(value):
            return False
        if isinstance(value, ast.Constant) and isinstance(value.value, str):
            return True
        if _walrus_rebinds(value, None):
            return True
        return isinstance(value, self._EXEMPT_VALUE_TYPES)
    def detect_file(self, filepath: str) -> list[PatternFinding]:
        findings: list[PatternFinding] = []
        parsed = _parse_source(filepath, self.DETECTOR_ID)
        if parsed is None:
            return findings
        source, tree = parsed
        lines = aligned_source_lines(source)
        for node in walk_nodes(tree):
            if not isinstance(node, ast.Expr):
                continue
            if self._is_exempt(node):
                continue
            finding = self._make_finding(node, lines, filepath)
            if finding is not None:
                findings.append(finding)
        return findings
    def _make_finding(self, node: ast.Expr, lines: list[str],
                      filepath: str) -> PatternFinding | None:
        source_line = safe_source_line(lines, node.lineno)
        if self._is_unwritten_container_string_call(node.value):
            return PatternFinding(
                detector_id=self.DETECTOR_ID,
                pattern_name=self.PATTERN_NAME,
                severity="WARN",
                filepath=filepath,
                line=node.lineno,
                snippet=source_line[:120],
                message=f"字符串方法 {node.value.func.attr}() 的返回结果被丢弃,"
                        f"容器元素未写回: {source_line[:60]}",
                suggestion=suggest(
                    '代码缺少必要的元素。该问题属于代码质量类别。',
                    '接收字符串方法的返回值并写回原容器元素'),
            )
        for node_type, severity, template, hint in self._NOOP_FORMS:
            if isinstance(node.value, node_type):
                return PatternFinding(
                    detector_id=self.DETECTOR_ID,
                    pattern_name=self.PATTERN_NAME,
                    severity=severity,
                    filepath=filepath,
                    line=node.lineno,
                    snippet=source_line[:120],
                    message=template.format(snippet=source_line[:60]),
                    suggestion=suggest(
                        '代码缺少必要的元素。该问题属于代码质量类别。', hint),
                )
        return None
def _iterates_keys(iter_node: ast.expr,
                   iter_call: tuple[str, str] | None) -> bool:
    return (isinstance(iter_node, ast.Name)
            or (iter_call is not None and iter_call[1] == 'keys'))
def _items_unpack_key(target: ast.expr,
                      iter_call: tuple[str, str] | None) -> str | None:
    if not (iter_call is not None and iter_call[1] == 'items'):
        return None
    if not (isinstance(target, (ast.Tuple, ast.List)) and target.elts):
        return None
    first = target.elts[0]
    return first.id if isinstance(first, ast.Name) else None
def _nested_stmt_bodies(stmt: ast.stmt):
    if isinstance(stmt, TRY_TYPES):
        for handler in stmt.handlers:
            if handler.body:
                yield handler.body
    if isinstance(stmt, ast.Match):
        for case in stmt.cases:
            if case.body:
                yield case.body
def _iter_call_target(iter_node: ast.AST) -> tuple[str, str] | None:
    if (isinstance(iter_node, ast.Call)
            and isinstance(iter_node.func, ast.Attribute)
            and isinstance(iter_node.func.value, ast.Name)):
        return iter_node.func.value.id, iter_node.func.attr
    return None
def _record_named_bind(events: dict, key_vars: set[str], name: str | None,
                       lineno: int, col_offset: int, bound: bool) -> None:
    if name and name in key_vars:
        events.setdefault(name, []).append(((lineno, col_offset), bound))
def _record_target_binds(events: dict, key_vars: set[str], target: ast.AST,
                         bound: bool) -> None:
    for name, lineno, col_offset in iter_target_bindings(target):
        _record_named_bind(events, key_vars, name, lineno, col_offset, bound)
def _walrus_rebinds(node: ast.AST, key_name: str | None) -> bool:
    stack: list[ast.AST] = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, ast.Lambda):
            _push_lambda_defaults(stack, cur.args)
            continue
        if isinstance(cur, ast.GeneratorExp):
            # 仅首个迭代表达式在创建生成器时求值，主体与其余部分均延迟执行。
            stack.append(cur.generators[0].iter)
            continue
        if (isinstance(cur, ast.NamedExpr)
                and isinstance(cur.target, ast.Name)
                and (key_name is None or cur.target.id == key_name)):
            return True
        stack.extend(ast.iter_child_nodes(cur))
    return False
def _record_rebind_form(events: dict, key_vars: set[str],
                        cur: ast.AST) -> None:
    if isinstance(cur, (ast.Assign, ast.Delete)):
        for target in cur.targets:
            _record_target_binds(
                events, key_vars, target, not isinstance(cur, ast.Delete))
    elif (isinstance(cur, (ast.AugAssign, ast.For, ast.AsyncFor, ast.NamedExpr))
          or (isinstance(cur, ast.AnnAssign) and cur.value is not None)):
        _record_target_binds(events, key_vars, cur.target, True)
    elif isinstance(cur, ast.withitem) and cur.optional_vars is not None:
        _record_target_binds(events, key_vars, cur.optional_vars, True)
    if isinstance(cur, (ast.ExceptHandler, ast.MatchAs, ast.MatchStar)):
        _record_named_bind(events, key_vars, cur.name,
                           cur.lineno, cur.col_offset, True)
    elif isinstance(cur, ast.alias):
        _record_named_bind(events, key_vars,
                           cur.asname or cur.name.split('.')[0],
                           cur.lineno, cur.col_offset, True)
    elif isinstance(cur, ast.MatchMapping):
        _record_named_bind(events, key_vars, cur.rest,
                           cur.lineno, cur.col_offset, True)
def _push_lambda_defaults(stack: list, args: ast.arguments) -> None:
    stack.extend(args.defaults)
    stack.extend(d for d in args.kw_defaults if d is not None)
def _definition_outer_exprs(node: ast.AST) -> list[ast.AST]:
    return [
        *definition_time_exprs(node),
        *(kw.value for kw in (getattr(node, "keywords", ()) or ())
          if kw.value is not None),
        *(getattr(node, "bases", ()) or ()),
    ]
def _push_definition_outer_exprs(stack: list, node: ast.AST) -> None:
    stack.extend(_definition_outer_exprs(node))
def _collect_key_binding_events(node: ast.AST, key_vars: set[str]) -> dict:
    events: dict[str, list[tuple[tuple[int, int], bool]]] = {}
    if not key_vars:
        return events
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        for name in collect_param_names(node):
            _record_named_bind(events, key_vars, name,
                               node.lineno, node.col_offset, True)
    stack: list[ast.AST] = list(node.body)
    while stack:
        cur = stack.pop()
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            _record_named_bind(events, key_vars, cur.name,
                               cur.lineno, cur.col_offset, True)
            _push_definition_outer_exprs(stack, cur)
            continue
        if isinstance(cur, ast.Lambda):
            _push_lambda_defaults(stack, cur.args)
            continue
        stack.extend(ast.iter_child_nodes(cur))
        _record_rebind_form(events, key_vars, cur)
    for records in events.values():
        records.sort(key=lambda event: event[0])
    return events
def _collect_key_rebind_positions(
        node: ast.For | ast.AsyncFor | ast.FunctionDef
        | ast.AsyncFunctionDef | ast.ClassDef,
        key_vars: set[str]) -> dict[str, list[tuple[int, int]]]:
    return {
        name: [pos for pos, _bound in records]
        for name, records in _collect_key_binding_events(node, key_vars).items()
    }
def _key_rebound_before_assign(rebind_positions: dict[str, list[tuple[int, int]]],
                               key_name: str,
                               stmt_pos: tuple[int, int],
                               earlier_targets,
                               value_node,
                               event_reaches: Callable[[tuple[int, int]], bool] | None = None) -> bool:
    for pos in rebind_positions.get(key_name, ()):
        if pos < stmt_pos and (event_reaches is None or event_reaches(pos)):
            return True
    for tgt in earlier_targets:
        for name, _lineno, _col_offset in iter_target_bindings(tgt):
            if name == key_name:
                return True
        if _walrus_rebinds(tgt, key_name):
            return True
    return bool(value_node is not None and _walrus_rebinds(value_node, key_name))
def _collect_nested_scope_key_binds(
        node: ast.For | ast.AsyncFor,
        key_vars: set[str]) -> tuple[
            dict[int, dict[str, list[tuple[int, int]]]],
            dict[int, frozenset[int]]]:
    binds: dict[int, dict[str, list[tuple[int, int]]]] = {}
    outer_expr_ids: dict[int, frozenset[int]] = {}
    if not key_vars:
        return binds, outer_expr_ids
    for sub in walk_nodes(node):
        if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef)):
            scoped = _collect_key_rebind_positions(sub, key_vars)
            if scoped:
                binds[id(sub)] = scoped
            outer_expr_ids[id(sub)] = frozenset(
                node_id for expr in _definition_outer_exprs(sub)
                for node_id in subtree_node_ids([expr]))
    return binds, outer_expr_ids
@dataclass(frozen=True)
class _KeyExemption:
    for_node: ast.For | ast.AsyncFor
    key_vars: set[str] = field(default_factory=set)
    rebind_positions: dict[str, list[tuple[int, int]]] = field(default_factory=dict)
    scope_binds: dict[int, dict[str, list[tuple[int, int]]]] = field(
        default_factory=dict)
    outer_expr_ids: dict[int, frozenset[int]] = field(default_factory=dict)
    parent_map: dict[ast.AST, ast.AST] = field(default_factory=dict)
    shadowed_call_ids: frozenset[int] = frozenset()
    event_paths: dict[tuple[int, int], tuple[frozenset[tuple[int, int]], ...]] = field(
        default_factory=dict)
    try_ids: frozenset[int] = frozenset()
    @classmethod
    def build(cls, for_node: ast.For | ast.AsyncFor,
              key_vars: set[str]) -> _KeyExemption:
        if not key_vars:
            return cls(for_node=for_node)
        scope_binds, outer_expr_ids = _collect_nested_scope_key_binds(
            for_node, key_vars)
        shadowed_call_ids: set[int] = set()
        for key_name in key_vars:
            shadowed_call_ids.update(_shadowed_call_ids(
                for_node,
                lambda node, name=key_name: (
                    name if isinstance(node, ast.Call) else None),
            ))
        parent_map = shared_parent_map(for_node)
        mutable_event_paths: dict[
            tuple[int, int], list[frozenset[tuple[int, int]]]] = {}
        for event_node in _d42_body_nodes(for_node):
            lineno = getattr(event_node, 'lineno', None)
            col_offset = getattr(event_node, 'col_offset', None)
            if lineno is None or col_offset is None:
                continue
            mutable_event_paths.setdefault((lineno, col_offset), []).append(
                _branch_path(event_node, parent_map, for_node))
        return cls(
            for_node=for_node,
            key_vars=key_vars,
            rebind_positions=_collect_key_rebind_positions(for_node, key_vars),
            scope_binds=scope_binds,
            outer_expr_ids=outer_expr_ids,
            parent_map=parent_map,
            shadowed_call_ids=frozenset(shadowed_call_ids),
            event_paths={pos: tuple(paths)
                         for pos, paths in mutable_event_paths.items()},
            try_ids=frozenset(
                id(parent) for parent in parent_map.values()
                if isinstance(parent, TRY_TYPES)),
        )

    def _rebind_reaches(self, child: ast.AST,
                        position: tuple[int, int]) -> bool:
        paths = self.event_paths.get(position, ())
        if not paths:
            return True
        child_path = _branch_path(child, self.parent_map, self.for_node)
        child_decisions = dict(child_path)
        for event_path in paths:
            if _paths_compatible(event_path, child_path):
                return True
            conflicts = {
                decision for decision, value in event_path
                if decision in child_decisions
                and child_decisions[decision] != value}
            if conflicts & self.try_ids:
                return True
        return False

    def allows(self, child: ast.AST, key_name: str,
               earlier_targets, value_node) -> bool:
        if (key_name not in self.key_vars
                or id(child) in self.shadowed_call_ids):
            return False
        stmt_pos = (child.lineno, child.col_offset)
        if _key_rebound_before_assign(
                self.rebind_positions, key_name, stmt_pos,
                earlier_targets, value_node,
                event_reaches=lambda pos: self._rebind_reaches(child, pos)):
            return False
        return not _key_shadowed_by_nested_scope(
            child, key_name, self.scope_binds, self.outer_expr_ids,
            self.parent_map, self.for_node)
def _class_key_binding_active(
        child: ast.AST, class_node: ast.ClassDef,
        positions: list[tuple[int, int]],
        parent_map: dict[ast.AST, ast.AST]) -> bool:
    child_pos = (child.lineno, child.col_offset)
    if any(pos < child_pos for pos in positions):
        return True
    current = child
    while current is not class_node:
        current = parent_map[current]
        if not isinstance(current, (ast.For, ast.AsyncFor, ast.While)):
            continue
        for stmt in current.body:
            start = (stmt.lineno, stmt.col_offset)
            end = (stmt.end_lineno, stmt.end_col_offset)
            if any(start <= pos <= end for pos in positions):
                return True
    return False
def _key_shadowed_by_nested_scope(
        child: ast.AST, key_name: str,
        scope_binds: dict[int, dict[str, list[tuple[int, int]]]],
        outer_expr_ids: dict[int, frozenset[int]],
        parent_map: dict[ast.AST, ast.AST],
        for_node: ast.For | ast.AsyncFor) -> bool:
    if not scope_binds:
        return False
    cur: ast.AST = child
    crossed_func = False
    while cur is not for_node:
        cur = parent_map[cur]
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef)) and id(child) in outer_expr_ids.get(
                                id(cur), ()):
            continue
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef)):
            crossed_func = True
        elif not isinstance(cur, ast.ClassDef) or crossed_func:
            continue
        bindings = scope_binds.get(id(cur), {})
        if isinstance(cur, ast.ClassDef):
            if _class_key_binding_active(
                    child, cur, bindings.get(key_name, []), parent_map):
                return True
        elif key_name in bindings:
            return True
    return False
def _d42_body_nodes(node: ast.For | ast.AsyncFor) -> list[ast.AST]:
    out: list[ast.AST] = []
    stack: list[ast.AST] = list(node.body)
    while stack:
        cur = stack.pop()
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef)):
            stack.extend(definition_time_exprs(cur))
            continue
        if isinstance(cur, ast.Lambda):
            _push_lambda_defaults(stack, cur.args)
            continue
        out.append(cur)
        stack.extend(ast.iter_child_nodes(cur))
    return out
class DictInPlaceMutationDetector:
    DETECTOR_ID = "D42"
    PATTERN_NAME = "字典就地突变"
    MUTATING_METHODS = frozenset({
        'pop', 'popitem', 'update', 'clear', 'setdefault',
        '__ior__', '__setitem__', '__delitem__',
    })
    KEY_WRITE_METHODS = frozenset({
        'setdefault', 'update', '__ior__', '__setitem__',
    })
    def _get_key_var_names(self, node: ast.For | ast.AsyncFor) -> set[str]:
        t = node.target
        _iter_call = _iter_call_target(node.iter)
        if isinstance(t, ast.Name) and _iterates_keys(node.iter, _iter_call):
            return {t.id}
        key_name = _items_unpack_key(t, _iter_call)
        return {key_name} if key_name else set()
    def _get_iterated_names(self, node: ast.For | ast.AsyncFor) -> set[str]:
        iter_node = node.iter
        if isinstance(iter_node, ast.Name):
            return {iter_node.id}
        _iter_call = _iter_call_target(iter_node)
        if _iter_call is not None and _iter_call[1] in ('items', 'keys', 'values'):
            return {_iter_call[0]}
        return set()
    def _scan_adjacent_terminal(self, stmts: list[ast.stmt],
                                iterated_names: set[str],
                                binds_node: bool,
                                return_is_terminal: bool,
                                raise_is_terminal: bool,
                                safe_ids: set[int]) -> None:
        if len(stmts) < 2:
            return
        for i in range(len(stmts) - 1):
            cur, nxt = stmts[i], stmts[i + 1]
            if (self._terminates_iteration(
                    nxt, binds_node, return_is_terminal, raise_is_terminal)
                    and self._mutates_iterated(cur, iterated_names)):
                safe_ids.update(self._mutation_node_ids(cur))
    @staticmethod
    def _terminates_iteration(nxt: ast.stmt, binds_node: bool,
                              return_is_terminal: bool,
                              raise_is_terminal: bool) -> bool:
        if isinstance(nxt, ast.Return):
            return return_is_terminal
        if isinstance(nxt, ast.Break):
            return binds_node
        return isinstance(nxt, ast.Raise) and raise_is_terminal
    def _mutates_iterated(self, stmt: ast.stmt,
                          iterated_names: set[str]) -> bool:
        if isinstance(stmt, ast.Delete):
            return any(self._is_iterated_dict_subscript(t, iterated_names)
                       for target in stmt.targets
                       for t in _iter_target_leaves(target))
        if (isinstance(stmt, ast.AugAssign)
                and isinstance(stmt.op, ast.BitOr)
                and isinstance(stmt.target, ast.Name)
                and stmt.target.id in iterated_names):
            return True
        if isinstance(stmt, ast.Expr):
            return self._is_mutating_call_on(stmt.value, iterated_names)
        if isinstance(stmt, ast.AugAssign):
            return self._is_mutating_call_on(stmt.value, iterated_names)
        assigned = assign_targets_value(stmt)
        if assigned is None:
            return False
        targets, value = assigned
        return (self._is_mutating_call_on(value, iterated_names)
                or any(self._is_iterated_dict_subscript(t, iterated_names)
                       for target in targets
                       for t in _iter_target_leaves(target)))
    @staticmethod
    def _mutation_node_ids(stmt: ast.stmt) -> tuple[int, ...]:
        value = getattr(stmt, "value", None)
        if isinstance(stmt, ast.Expr) and isinstance(value, ast.Call):
            return (id(value),)
        ids = (id(stmt),)
        if (isinstance(stmt, (ast.Assign, ast.AnnAssign, ast.AugAssign))
                and isinstance(value, ast.Call)):
            ids += (id(value),)
        return ids
    @staticmethod
    def _iter_child_stmt_lists(s: ast.stmt):
        is_loop = isinstance(s, (ast.For, ast.AsyncFor, ast.While))
        for body_name in ("body", "orelse", "finalbody"):
            sub = getattr(s, body_name, None)
            if isinstance(sub, list) and sub:
                catches_raise = (
                    isinstance(s, TRY_TYPES) and body_name == "body"
                    and bool(s.handlers))
                yield sub, (is_loop and body_name == "body"), catches_raise
        for sub in _nested_stmt_bodies(s):
            yield sub, False, False
    @staticmethod
    def _finally_loop_transfers(node: ast.AST) -> frozenset[str]:
        transfers: set[str] = set()
        stack: list[ast.AST] = list(getattr(node, "finalbody", ()) or ())
        while stack:
            cur = stack.pop()
            if isinstance(cur, ast.Continue):
                transfers.add("continue")
            elif isinstance(cur, ast.Break):
                transfers.add("break")
            if isinstance(cur, (ast.For, ast.AsyncFor, ast.While)):
                stack.extend(cur.orelse)
                continue
            if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda, ast.ClassDef)):
                continue
            stack.extend(ast.iter_child_nodes(cur))
        return frozenset(transfers)
    def _collect_safe_terminal_ids(self, node: ast.For | ast.AsyncFor,
                                   iterated_names: set[str]) -> set[int]:
        safe_ids: set[int] = set()
        stack: list[tuple[list[ast.stmt], bool, bool, bool]] = [
            (node.body, True, True, True),
        ]
        while stack:
            stmts, binds_node, return_is_terminal, raise_is_terminal = stack.pop()
            self._scan_adjacent_terminal(
                stmts, iterated_names, binds_node, return_is_terminal,
                raise_is_terminal, safe_ids)
            for s in stmts:
                if isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef)):
                    continue
                finally_transfers = (
                    self._finally_loop_transfers(s)
                    if isinstance(s, TRY_TYPES) else frozenset())
                finalbody = getattr(s, "finalbody", None)
                for sub, binds_self, catches_raise in (
                        self._iter_child_stmt_lists(s)):
                    suppressed = (
                        sub is not finalbody
                        and ("continue" in finally_transfers
                             or (not binds_node and "break" in finally_transfers))
                    )
                    stack.append((
                        sub,
                        binds_node and not binds_self and not suppressed,
                        return_is_terminal and not suppressed,
                        raise_is_terminal and not catches_raise and not suppressed,
                    ))
        return safe_ids
    def _make_finding(self, severity: str, filepath: str, line: int,
                      *, snippet: str, message: str,
                      fix_hint: str) -> PatternFinding:
        return PatternFinding(
            detector_id=self.DETECTOR_ID,
            pattern_name=self.PATTERN_NAME,
            severity=severity,
            filepath=filepath,
            line=line,
            snippet=snippet,
            message=message,
            suggestion=suggest(_QUALITY_ROOT_CAUSE, fix_hint))
    def _is_mutating_call_on(self, node: ast.AST,
                             iterated_names: set[str]) -> bool:
        return (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr in self.MUTATING_METHODS
                and isinstance(node.func.value, ast.Name)
                and node.func.value.id in iterated_names)
    def _writes_only_current_keys(self, call: ast.Call,
                                 exemption: _KeyExemption) -> bool:
        written = _call_written_keys(call)
        if written is None:
            return False
        return all(exemption.allows(call, key, (), None) for key in written)
    def _check_mutating_call(self, child: ast.AST, iterated_names: set[str],
                             exemption: _KeyExemption, safe_ids: set[int],
                             filepath: str) -> list[PatternFinding]:
        if id(child) in safe_ids or not self._is_mutating_call_on(
                child, iterated_names):
            return []
        if (child.func.attr in self.KEY_WRITE_METHODS
                and self._writes_only_current_keys(child, exemption)):
            return []
        return [self._make_finding(
            "ERROR", filepath, child.lineno,
            snippet=f"{child.func.value.id}.{child.func.attr}(...)",
            message=f"迭代过程中对字典 {child.func.value.id} 调用 "
                    f".{child.func.attr}(),可能导致 RuntimeError",
            fix_hint='创建副本后修改: for k, v in dict(my_var).items(): '
                     '或 my_copy = dict(my_var)')]
    def _check_in_place_union(self, child: ast.AST,
                              iterated_names: set[str],
                              exemption: _KeyExemption, safe_ids: set[int],
                              filepath: str) -> list[PatternFinding]:
        if (id(child) in safe_ids
                or not isinstance(child, ast.AugAssign)
                or not isinstance(child.op, ast.BitOr)
                or not isinstance(child.target, ast.Name)
                or child.target.id not in iterated_names):
            return []
        written = _dict_literal_written_keys(child.value)
        if (written is not None
                and all(exemption.allows(child, key, (), child.value)
                        for key in written)):
            return []
        return [self._make_finding(
            "ERROR", filepath, child.lineno,
            snippet=f"{child.target.id} |= ...",
            message=f"迭代过程中对字典 {child.target.id} 执行 |=,"
                    "可能导致 RuntimeError",
            fix_hint='先合并副本再替换: my_copy = my_var | other')]
    def _check_delete(self, child: ast.AST, iterated_names: set[str],
                      safe_ids: set[int],
                      filepath: str) -> list[PatternFinding]:
        if not isinstance(child, ast.Delete) or id(child) in safe_ids:
            return []
        out: list[PatternFinding] = []
        for target in child.targets:
            for tgt in _iter_target_leaves(target):
                if not self._is_iterated_dict_subscript(tgt, iterated_names):
                    continue
                out.append(self._make_finding(
                    "ERROR", filepath, child.lineno,
                    snippet=f"del {tgt.value.id}[...]",
                    message=f"迭代过程中 del {tgt.value.id}[key],"
                            f"可能导致 RuntimeError",
                    fix_hint='创建副本后删除: for k in list(my_var.keys()): '
                             'del my_var[k]'))
        return out
    @staticmethod
    def _is_iterated_dict_subscript(tgt: ast.AST,
                                    iterated_names: set[str]) -> bool:
        return (isinstance(tgt, ast.Subscript)
                and isinstance(tgt.value, ast.Name)
                and tgt.value.id in iterated_names)
    def _check_subscript_assign(self, child: ast.AST, iterated_names: set[str],
                                exemption: _KeyExemption, safe_ids: set[int],
                                filepath: str) -> list[PatternFinding]:
        if id(child) in safe_ids:
            return []
        assigned = assign_targets_value(child)
        if assigned is None:
            return []
        _targets, _value = assigned
        out: list[PatternFinding] = []
        flat_targets = [
            leaf for target in _targets for leaf in _iter_target_leaves(target)
        ]
        for _ti, tgt in enumerate(flat_targets):
            if not self._is_iterated_dict_subscript(tgt, iterated_names):
                continue
            _slice = tgt.slice
            if (isinstance(_slice, ast.Name)
                    and exemption.allows(child, _slice.id,
                                         flat_targets[:_ti], _value)):
                continue
            out.append(self._make_finding(
                "WARN", filepath, child.lineno,
                snippet=f"{tgt.value.id}[...] = ...",
                message=f"迭代过程中对字典 {tgt.value.id} 赋值,"
                        f"可能导致 RuntimeError",
                fix_hint='创建副本后修改: my_copy = dict(my_var); '
                         'my_copy[k] = v'))
        return out
    def detect_file(self, filepath: str) -> list[PatternFinding]:
        findings: list[PatternFinding] = []
        parsed = _parse_source(filepath, self.DETECTOR_ID)
        if parsed is None:
            return findings
        _source, tree = parsed
        for node in walk_nodes(tree):
            if isinstance(node, (ast.For, ast.AsyncFor)):
                findings.extend(self._check_for_loop(node, filepath))
        return dedupe_findings(findings)
    def _check_for_loop(self, node: ast.For | ast.AsyncFor,
                        filepath: str) -> list[PatternFinding]:
        iterated_names = self._get_iterated_names(node)
        if not iterated_names:
            return []
        safe_ids = self._collect_safe_terminal_ids(node, iterated_names)
        exemption = _KeyExemption.build(node, self._get_key_var_names(node))
        findings: list[PatternFinding] = []
        for child in _d42_body_nodes(node):
            findings.extend(self._check_mutating_call(
                child, iterated_names, exemption, safe_ids, filepath))
            findings.extend(self._check_in_place_union(
                child, iterated_names, exemption, safe_ids, filepath))
            findings.extend(self._check_delete(
                child, iterated_names, safe_ids, filepath))
            findings.extend(self._check_subscript_assign(
                child, iterated_names, exemption, safe_ids, filepath))
        return findings
def wiring_declarations() -> dict:
    return {"catalogs": {
        "new_pattern_classes": {'D40': EmptyDictStubDetector},
        "audit_detector_classes": {
            'D42': DictInPlaceMutationDetector,
            'D44': LocalVarNotWrittenBackDetector,
            'D45': NoOpExpressionDetector,
            'D46': StringMaxMinComparisonDetector,
            'D47': ListDictMethodMisuseDetector,
        },
    }}

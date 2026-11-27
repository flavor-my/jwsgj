from __future__ import annotations

import ast
import logging
import math
import time
import weakref
from collections import Counter
from collections.abc import Iterator
from dataclasses import dataclass, fields

from jwsgj.diag_shared_ast_nodes import (
    BUILTIN_CALLABLES,
    cognitive_complexity,
    collect_param_names,
    cyclomatic_complexity,
    is_static_method,
    iter_class_scope_methods,
    own_scope_line_span,
)
from jwsgj.diag_shared_ast_views import (
    WalkIndex,
    shared_walk,
)
from jwsgj.diag_testing_source import (
    MATCH_T,
    TRY_STAR_T,
    FileCache,
    entry_calls,
    entry_class_method_ids,
    entry_nodes,
    entry_rel_path,
    iter_own_scope_nodes,
    node_first_line,
    nodes_where,
    qualified_name,
    resolve_file_cache,
)
from jwsgj.diag_types_defs import (
    TestMethodResult,
)
from jwsgj.diag_types_vocab import (
    HARD_MAX_FILE_LINES,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import (
    binding_evaluation_position,
    iter_binding_entries,
    walk_nodes,
)
from jwsgj.runtime_scope import (
    is_test_file_path,
)

_log = logging.getLogger(__name__)
_log.info("diag_testing_perf_metrics 已加载")
__all__ = [
    'calc_function_metrics',
    'run_complexity_analysis',
]
@dataclass(frozen=True)
class _AnalysisPolicy:
    max_file_lines: int = HARD_MAX_FILE_LINES
    hotspot_cc: int = 80
    dense_io: int = 40
    large_alloc: int = 1000
    global_mutations: int = 50
    cc_medium: int = 15
    cc_high: int = 20
    param_count: int = 7
    nesting_depth: int = 5
    lcom_high: float = 0.8
    rfc_high: int = 30
    include_test_files: bool = True
    analyze_package_init: bool = True
def _annotation_matches(annotation, expected: type) -> bool:
    return annotation is expected or annotation == expected.__name__
_POLICY_FIELD_NAMES = tuple(_field.name for _field in fields(_AnalysisPolicy))
_POLICY_NUMERIC_FIELDS = tuple(
    _field.name for _field in fields(_AnalysisPolicy)
    if _annotation_matches(_field.type, int)
    or _annotation_matches(_field.type, float))
_POLICY_BOOL_FIELDS = tuple(
    _field.name for _field in fields(_AnalysisPolicy)
    if _annotation_matches(_field.type, bool))
def _coerce_analysis_policy(value=None, kwargs=None) -> _AnalysisPolicy:
    kwargs = kwargs or {}
    value = kwargs.get('analysis_policy', value)
    if value is None:
        supplied = {}
    elif isinstance(value, _AnalysisPolicy):
        supplied = {name: getattr(value, name)
                    for name in _POLICY_FIELD_NAMES}
    elif isinstance(value, dict):
        supplied = dict(value)
    else:
        raise TypeError('analysis_policy 须为映射或 _AnalysisPolicy')
    supplied.update({name: kwargs[name]
                     for name in _POLICY_FIELD_NAMES
                     if name in kwargs})
    policy = _AnalysisPolicy(**supplied)
    for name in _POLICY_NUMERIC_FIELDS:
        item = getattr(policy, name)
        if (isinstance(item, bool) or not isinstance(item, (int, float))
                or item < 0
                or (isinstance(item, float) and not math.isfinite(item))):
            raise ValueError(f'{name} 须为有限非负数: {item!r}')
    if not 0 <= policy.lcom_high <= 1:
        raise ValueError('lcom_high 须位于 [0, 1]')
    if policy.cc_high < policy.cc_medium:
        raise ValueError('cc_high 不得小于 cc_medium')
    for name in _POLICY_BOOL_FIELDS:
        if not isinstance(getattr(policy, name), bool):
            raise TypeError(f'{name} 须为 bool')
    return policy
def _is_package_init_entry(entry) -> bool:
    rel_path = entry_rel_path(entry).replace("\\", "/")
    return rel_path.rsplit("/", 1)[-1].lower() == "__init__.py"
class _AnalysisCache:
    def __init__(self, base, policy: _AnalysisPolicy) -> None:
        self._base = base
        entries = list(base.valid_entries)
        self._added = []
        if policy.include_test_files:
            known = {entry_rel_path(entry) for entry in entries}
            self._added = [entry for entry in getattr(
                base, 'test_dir_entries', ()) or ()
                if entry_rel_path(entry) not in known
                and getattr(entry, 'tree', None) is not None]
            entries.extend(self._added)
        else:
            entries = [entry for entry in entries
                       if not is_test_file_path(entry_rel_path(entry))]
        if not policy.analyze_package_init:
            entries = [entry for entry in entries
                       if not _is_package_init_entry(entry)]
        self.valid_entries = entries
        self._recompute_names = (
            not policy.include_test_files or bool(self._added)
            or not policy.analyze_package_init)
    @staticmethod
    def _names_from_entry(entry) -> set[str]:
        names = {item.get('name') for item in getattr(entry, 'functions', ()) or ()
                 if isinstance(item, dict)}
        names.discard(None)
        return names
    def get_all_function_names(self) -> set[str]:
        if not self._recompute_names:
            return self._base.get_all_function_names()
        names: set[str] = set()
        for entry in self.valid_entries:
            names.update(self._names_from_entry(entry))
        return names
def _int_attr(node: ast.AST, name: str, default: int) -> int:
    _v = getattr(node, name, None)
    return _v if isinstance(_v, int) else default
def _name_id(node) -> str | None:
    _id = getattr(node, 'id', None)
    return _id if isinstance(_id, str) else None
def _node_line_span(node: ast.AST) -> tuple[int, int]:
    _s = _int_attr(node, 'lineno', 0)
    return _s, _int_attr(node, 'end_lineno', _s)
def _ensure_widx(_widx):
    return _widx if _widx is not None else WalkIndex()
def _expr_field(node: ast.AST, name: str) -> ast.expr | None:
    _v = getattr(node, name, None)
    return _v if isinstance(_v, ast.expr) else None
def _list_field(node: ast.AST, name: str) -> tuple:
    _v = getattr(node, name, None)
    return tuple(_v) if isinstance(_v, list) else ()
def _names_in_expr(node: ast.AST) -> set[str]:
    names: set[str] = set()
    for child in walk_nodes(node):
        if isinstance(child, ast.Name):
            _name = _name_id(child)
            if _name is not None:
                names.add(_name)
    return names
_SELF_CLS_RECEIVERS = frozenset(("self", "cls"))
def _perf_identify_hotspots(
        tree: ast.AST, rel_path: str, *, _nodes=None,
        policy: _AnalysisPolicy) -> list:
    if not policy.include_test_files and is_test_file_path(rel_path):
        return []
    hotspots = []
    _iter = _nodes if _nodes is not None else shared_walk(tree)
    for node in _iter:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_info, _ = calc_function_metrics(node, rel_path)
            _fname = func_info["function"]
            func_cc = func_info["cyclomatic_complexity"]
            cognitive = func_info["cognitive_complexity"]
            func_len = func_info["lines"]
            if func_cc >= policy.hotspot_cc:
                hotspots.append({
                    "file": rel_path, "function": _fname,
                    "line": func_info["line"],
                    "type": "hotspot",
                    "cc": func_cc,
                    "cognitive": cognitive,
                    "halstead_volume": func_info["halstead_volume"],
                    "halstead_difficulty": func_info["halstead_difficulty"],
                    "lines": func_len,
                    "severity": "high",
                    "message": (
                        f"热点函数 {_fname}: CC={func_cc}, "
                        f"Cognitive={cognitive}, "
                        f"Halstead_V={func_info['halstead_volume']}, "
                        f"{func_len} 行"
                    ),
                })
    return hotspots
def _call_is_self_call(_cf, _fname: str, *, allow_bare: bool,
                       shadowed: set | frozenset) -> bool:
    if isinstance(_cf, ast.Name):
        return (allow_bare
                and getattr(_cf, 'id', None) == _fname
                and _fname not in shadowed)
    if isinstance(_cf, ast.Attribute):
        _cval = _expr_field(_cf, 'value')
        return (not allow_bare
                and getattr(_cf, 'attr', None) == _fname
                and isinstance(_cval, ast.Name)
                and getattr(_cval, 'id', None) in _SELF_CLS_RECEIVERS)
    return False
def _node_binding_names(child) -> set:
    if isinstance(child, ast.Name):
        if not isinstance(getattr(child, 'ctx', None), (ast.Store, ast.Del)):
            return set()
        name = getattr(child, 'id', None)
        return {name} if isinstance(name, str) else set()
    if isinstance(child, (ast.ExceptHandler, ast.MatchAs, ast.MatchStar)):
        name = getattr(child, 'name', None)
        return {name} if isinstance(name, str) else set()
    if isinstance(child, ast.MatchMapping):
        name = getattr(child, 'rest', None)
        return {name} if isinstance(name, str) else set()
    if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        name = getattr(child, 'name', None)
        return {name} if isinstance(name, str) else set()
    if not isinstance(child, (ast.Import, ast.ImportFrom)):
        return set()
    names: set = set()
    for alias in _list_field(child, 'names'):
        alias_name = getattr(alias, 'name', '')
        if alias_name != '*':
            names.add(getattr(alias, 'asname', None)
                      or alias_name.split('.')[0])
    return names
def _local_binding_names(node) -> set:
    names = collect_param_names(node)
    explicitly_nonlocal: set[str] = set()
    stack = list(ast.iter_child_nodes(node))
    comprehension_target_ids: set[int] = set()
    while stack:
        child = stack.pop()
        if isinstance(child, (ast.Global, ast.Nonlocal)):
            explicitly_nonlocal.update(_list_field(child, 'names'))
        if isinstance(child, ast.comprehension):
            comprehension_target_ids.update(
                id(item) for item in walk_nodes(child.target))
        if id(child) not in comprehension_target_ids:
            names.update(_node_binding_names(child))
        if not isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.Lambda, ast.ClassDef)):
            stack.extend(ast.iter_child_nodes(child))
    return names - explicitly_nonlocal
def _positional_param_names(node) -> list[str]:
    arguments = getattr(node, 'args', None)
    return [arg.arg for arg in (
        *_list_field(arguments, 'posonlyargs'),
        *_list_field(arguments, 'args'))
        if isinstance(getattr(arg, 'arg', None), str)]
def _strip_receiver_params(call, params: list[str]) -> list[str]:
    func = _expr_field(call, 'func')
    receiver = (_expr_field(func, 'value')
                if isinstance(func, ast.Attribute) else None)
    receiver_name = (getattr(receiver, 'id', None)
                     if isinstance(receiver, ast.Name) else None)
    if (receiver_name in _SELF_CLS_RECEIVERS and params
            and params[0] == receiver_name):
        return params[1:]
    return params
def _starred_arg_identity(arg, index, call_args, params: tuple[str, ...],
                          vararg_name) -> bool:
    inner = _expr_field(arg, 'value')
    if not (isinstance(inner, ast.Name) and index == len(call_args) - 1):
        return False
    return (isinstance(vararg_name, str)
            and index == len(params) and inner.id == vararg_name)
def _param_alignments(call, node) -> tuple[tuple[str, ...], ...]:
    full = tuple(_positional_param_names(node))
    stripped = tuple(_strip_receiver_params(call, list(full)))
    if stripped != full and not is_static_method(node):
        return (stripped,)
    return (full,)
def _is_zero_numeric_expr(node: ast.AST) -> bool:
    if (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.USub, ast.UAdd))):
        node = node.operand
    if not isinstance(node, ast.Constant):
        return False
    value = node.value
    return (not isinstance(value, bool)
            and isinstance(value, int) and value == 0)
def _is_zero_shifted_name(node: ast.AST, name: str) -> bool:
    if not isinstance(node, ast.BinOp):
        return False
    if isinstance(node.op, ast.Add):
        pairs = ((node.left, node.right), (node.right, node.left))
    elif isinstance(node.op, ast.Sub):
        pairs = ((node.left, node.right),)
    else:
        return False
    return any(isinstance(candidate, ast.Name) and candidate.id == name
               and _is_zero_numeric_expr(delta) for candidate, delta in pairs)
def _positional_args_identity_for(node, call,
                                  params: tuple[str, ...]) -> bool:
    call_args = _list_field(call, 'args')
    vararg = getattr(getattr(node, 'args', None), 'vararg', None)
    vararg_name = getattr(vararg, 'arg', None)
    for index, arg in enumerate(call_args):
        if isinstance(arg, ast.Starred):
            if not _starred_arg_identity(
                    arg, index, call_args, params, vararg_name):
                return False
            continue
        if index >= len(params):
            return False
        if not ((isinstance(arg, ast.Name) and arg.id == params[index])
                or _is_zero_shifted_name(arg, params[index])):
            return False
    return True
def _positional_only_param_names(node) -> set[str]:
    arguments = getattr(node, 'args', None)
    return {arg.arg for arg in _list_field(arguments, 'posonlyargs')
            if isinstance(getattr(arg, 'arg', None), str)}
def _kwonly_param_names(node) -> set[str]:
    arguments = getattr(node, 'args', None)
    return {arg.arg for arg in _list_field(arguments, 'kwonlyargs')
            if isinstance(getattr(arg, 'arg', None), str)}
def _keyword_args_identity(node, call) -> bool:
    arguments = getattr(node, 'args', None)
    kwarg = getattr(arguments, 'kwarg', None)
    kwarg_name = getattr(kwarg, 'arg', None)
    posonly = _positional_only_param_names(node)
    bindable_params = set(_positional_param_names(node)) | _kwonly_param_names(node)
    expanded = False
    for keyword in _list_field(call, 'keywords'):
        value = _expr_field(keyword, 'value')
        if keyword.arg is None:
            if (expanded or not isinstance(value, ast.Name)
                    or not isinstance(kwarg_name, str)
                    or value.id != kwarg_name):
                return False
            expanded = True
        elif not (keyword.arg in bindable_params and keyword.arg not in posonly
                  and ((isinstance(value, ast.Name) and value.id == keyword.arg)
                       or _is_zero_shifted_name(value, keyword.arg))):
            return False
    return True
def _bound_receiver_name(node, call) -> str | None:
    full = _positional_param_names(node)
    alignments = _param_alignments(call, node)
    if len(alignments) != 1:
        return None
    bound_params = alignments[0]
    if len(bound_params) + 1 != len(full) or bound_params != tuple(full[1:]):
        return None
    func = _expr_field(call, 'func')
    if not isinstance(func, ast.Attribute):
        return None
    receiver = _expr_field(func, 'value')
    if not isinstance(receiver, ast.Name):
        return None
    receiver_name = _name_id(receiver)
    return receiver_name if receiver_name == full[0] else None
def _self_call_keyword_shape(keywords) -> tuple[set[str], bool]:
    named = {k.arg for k in keywords if k.arg is not None}
    return named, any(k.arg is None for k in keywords)
def _self_call_positional_shape(args) -> tuple[int, bool]:
    count = sum(not isinstance(a, ast.Starred) for a in args)
    return count, count != len(args)
def _self_call_kwonly_covered(arguments, named) -> bool:
    kwonly = _list_field(arguments, 'kwonlyargs')
    kwdefaults = _list_field(arguments, 'kw_defaults')
    return not any(
        a.arg not in named
        and (i >= len(kwdefaults) or kwdefaults[i] is None)
        for i, a in enumerate(kwonly))
def _self_call_has_valid_arity(node, call) -> bool:
    return any(_self_call_arity_ok(node, call, params)
               for params in _param_alignments(call, node))
def _required_positional_params(node, params: tuple[str, ...]) -> set[str]:
    arguments = getattr(node, 'args', None)
    full = _positional_param_names(node)
    defaults = _list_field(arguments, 'defaults')
    return set(full[:len(full) - len(defaults)]) & set(params)
def _self_call_arity_ok(node, call, params: tuple[str, ...]) -> bool:
    arguments = getattr(node, 'args', None)
    args = _list_field(call, 'args')
    keywords = _list_field(call, 'keywords')
    named, expanded = _self_call_keyword_shape(keywords)
    positional_count, starred = _self_call_positional_shape(args)
    posonly = _positional_only_param_names(node)
    receiver_name = _bound_receiver_name(node, call)
    if (receiver_name is not None and receiver_name not in posonly
            and receiver_name in named):
        return False
    if any(name in params[:positional_count] and name not in posonly
           for name in named):
        return False
    if (positional_count > len(params)
            and getattr(arguments, 'vararg', None) is None):
        return False
    if getattr(arguments, 'kwarg', None) is None:
        kwonly = _kwonly_param_names(node)
        for name in named:
            if name in posonly or (name not in params and name not in kwonly):
                return False
    required = _required_positional_params(node, params)
    covered = set(params[:positional_count]) | (named - posonly)
    if not starred and required - covered:
        return False
    return expanded or _self_call_kwonly_covered(arguments, named)
def _self_call_covers(node, call, params: tuple[str, ...]) -> bool:
    args = _list_field(call, 'args')
    keywords = _list_field(call, 'keywords')
    named, _ = _self_call_keyword_shape(keywords)
    positional_count, starred = _self_call_positional_shape(args)
    posonly = _positional_only_param_names(node)
    receiver_name = _bound_receiver_name(node, call)
    if (receiver_name is not None and receiver_name not in posonly
            and receiver_name in named):
        return False
    if any(name in params[:positional_count] for name in named):
        return False
    arguments = getattr(node, 'args', None)
    covered = (set(params[:positional_count])
               | (named - _positional_only_param_names(node)))
    required = _required_positional_params(node, params)
    if not starred and required - covered:
        return False
    return _self_call_kwonly_covered(arguments, named)
_SELF_CALL_SCOPE_BOUNDARIES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)
def _self_call_enclosing_scope(node, parents):
    current = parents.get(id(node))
    while current is not None:
        if isinstance(current, _SELF_CALL_SCOPE_BOUNDARIES):
            return current
        current = parents.get(id(current))
    return None
def _self_call_loop_ids(node, parents) -> set[int]:
    loops: set[int] = set()
    current = parents.get(id(node))
    while current is not None:
        if isinstance(current, (ast.For, ast.AsyncFor, ast.While)):
            loops.add(id(current))
        current = parents.get(id(current))
    return loops
_SELF_CALL_MUTATING_METHODS = frozenset((
    'add', 'append', 'clear', 'difference_update', 'discard', 'extend',
    'insert', 'intersection_update', 'pop', 'popitem', 'popleft', 'remove',
    'reverse',
    'setdefault', 'sort', 'symmetric_difference_update', 'update',
    '__anext__', '__delitem__', '__next__', '__setattr__', '__setitem__',
))
_SELF_CALL_CONSUMING_FUNCTIONS = frozenset(('anext', 'next'))
def _self_call_root_name(node) -> str | None:
    while isinstance(node, (ast.Attribute, ast.Subscript)):
        node = node.value
    return _name_id(node) if isinstance(node, ast.Name) else None
def _self_call_mutation_events(node):
    for current in iter_own_scope_nodes(node):
        targets = []
        if isinstance(current, ast.Assign):
            targets = list(current.targets)
        elif isinstance(current, (ast.AugAssign, ast.AnnAssign,
                                  ast.For, ast.AsyncFor)):
            targets = [current.target]
        elif isinstance(current, (ast.With, ast.AsyncWith)):
            targets = [item.optional_vars for item in current.items
                       if item.optional_vars is not None]
        elif isinstance(current, ast.Delete):
            targets = list(current.targets)
        for target in targets:
            for part in walk_nodes(target):
                if (isinstance(part, (ast.Attribute, ast.Subscript))
                        and isinstance(getattr(part, 'ctx', None),
                                       (ast.Store, ast.Del))):
                    name = _self_call_root_name(part)
                    if name is not None:
                        yield current, name
        if not isinstance(current, ast.Call):
            continue
        func = _expr_field(current, 'func')
        name = None
        if (isinstance(func, ast.Attribute)
                and func.attr in _SELF_CALL_MUTATING_METHODS):
            name = _self_call_root_name(func.value)
        elif (isinstance(func, ast.Name)
                and func.id in _SELF_CALL_CONSUMING_FUNCTIONS
                and current.args):
            name = _self_call_root_name(current.args[0])
        if name is not None:
            yield current, name
def _self_call_inputs_unchanged(node, call, param_names) -> bool:
    forwarded = _names_in_expr(call) & set(param_names)
    if not forwarded:
        return True
    parents = _ensure_widx(None).parent_index(node)
    body = getattr(node, 'body', ())
    events = [(bound, name)
              for bound, name, _value in iter_binding_entries(body)]
    events.extend(_self_call_mutation_events(node))
    for bound in walk_nodes(node):
        if (bound is not node
                and isinstance(bound, (ast.FunctionDef, ast.AsyncFunctionDef,
                                       ast.ClassDef))
                and _self_call_enclosing_scope(bound, parents) is node):
            events.append((bound, bound.name))
    cutoff = (getattr(call, 'lineno', 0) or 0,
              getattr(call, 'col_offset', 0) or 0)
    call_loops = _self_call_loop_ids(call, parents)
    for bound, name in events:
        if name not in forwarded:
            continue
        if binding_evaluation_position(bound) <= cutoff:
            return False
        if call_loops & _self_call_loop_ids(bound, parents):
            return False
    return True
def _self_call_is_identity(node, call, param_names) -> bool:
    return (_keyword_args_identity(node, call)
            and any(_positional_args_identity_for(node, call, params)
                    and _self_call_covers(node, call, params)
                    for params in _param_alignments(call, node))
            and _self_call_inputs_unchanged(node, call, param_names))
_RECURSION_NESTED_SCOPE_TYPES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
def _runtime_header_exprs(node, *,
                          postponed_annotations: bool) -> list[ast.AST]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        exprs = list(getattr(node, 'decorator_list', ()))
        exprs.extend(node.args.defaults)
        exprs.extend(item for item in node.args.kw_defaults if item is not None)
        if not postponed_annotations and not isinstance(node, ast.Lambda):
            arguments = node.args
            annotated_args = (
                *arguments.posonlyargs, *arguments.args, *arguments.kwonlyargs,
                arguments.vararg, arguments.kwarg)
            exprs.extend(arg.annotation for arg in annotated_args
                         if arg is not None and arg.annotation is not None)
            if node.returns is not None:
                exprs.append(node.returns)
        return exprs
    if isinstance(node, ast.ClassDef):
        return [*node.decorator_list, *node.bases,
                *(item.value for item in node.keywords)]
    return []
def _postpones_annotations(tree) -> bool:
    if not isinstance(tree, ast.Module):
        return False
    return any(isinstance(item, ast.ImportFrom) and item.module == '__future__'
               and any(alias.name == 'annotations' for alias in item.names)
               for item in tree.body)
_EAGER_ITERABLE_CALL_NAMES = frozenset((
    'all', 'any', 'dict', 'frozenset', 'list', 'max', 'min', 'next',
    'set', 'sorted', 'sum', 'tuple',
))
def _consumed_iter_expression(node, eager_names):
    if isinstance(node, (ast.For, ast.AsyncFor, ast.comprehension)):
        return _expr_field(node, 'iter')
    if isinstance(node, (ast.YieldFrom, ast.Starred)):
        return _expr_field(node, 'value')
    if isinstance(node, ast.Call):
        func = _expr_field(node, 'func')
        if isinstance(func, ast.Name) and getattr(func, 'id', None) in eager_names:
            args = _list_field(node, 'args')
            return args[0] if args else None
    return None
def _iter_execution_scope_nodes(node, *, postponed_annotations: bool,
                                func_name: str | None = None, eager_names=None):
    if eager_names is None:
        eager_names = _EAGER_ITERABLE_CALL_NAMES - _local_binding_names(node)
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        stack = [(stmt, False) for stmt in node.body]
    elif isinstance(node, ast.Lambda):
        stack = [(node.body, False)]
    else:
        stack = [(child, False) for child in ast.iter_child_nodes(node)]
    while stack:
        current, driven_generator = stack.pop()
        if isinstance(current, ast.GeneratorExp):
            yield current
            if driven_generator:
                stack.extend(
                    (child, False) for child in ast.iter_child_nodes(current))
            elif current.generators:
                stack.append((current.generators[0].iter, False))
            continue
        if isinstance(current, ast.ClassDef):
            yield current
            stack.extend((child, False) for child in _runtime_header_exprs(
                current, postponed_annotations=postponed_annotations))
            if (func_name is None
                    or func_name not in _local_binding_names(current)):
                stack.extend((stmt, False) for stmt in current.body)
            continue
        if isinstance(current, _RECURSION_NESTED_SCOPE_TYPES):
            stack.extend((child, False) for child in _runtime_header_exprs(
                current, postponed_annotations=postponed_annotations))
            continue
        yield current
        consumed = _consumed_iter_expression(current, eager_names)
        stack.extend(
            (child, child is consumed and isinstance(child, ast.GeneratorExp))
            for child in ast.iter_child_nodes(current))
_COMPREHENSION_SCOPE_TYPES = (
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
def _comprehension_shadowed_call_ids(node, func_name: str, *,
                                     postponed_annotations: bool,
                                     eager_names=None) -> set[int]:
    shadowed_calls: set[int] = set()
    for comp in _iter_execution_scope_nodes(
            node, postponed_annotations=postponed_annotations,
            eager_names=eager_names):
        if not isinstance(comp, _COMPREHENSION_SCOPE_TYPES) or not comp.generators:
            continue
        target_names = {
            target.id
            for generator in comp.generators
            for target in walk_nodes(generator.target)
            if isinstance(target, ast.Name)
            and isinstance(getattr(target, 'ctx', None), ast.Store)
        }
        if func_name not in target_names:
            continue
        first_iter = comp.generators[0].iter
        first_iter_ids = {id(item) for item in walk_nodes(first_iter)}
        shadowed_calls.update(
            id(item) for item in walk_nodes(comp)
            if isinstance(item, ast.Call)
            and isinstance(_expr_field(item, 'func'), ast.Name)
            and getattr(item.func, 'id', None) == func_name
            and id(item) not in first_iter_ids)
    return shadowed_calls
def _driven_iterable_call_ids(expression, eager_names, shadowed) -> set[int]:
    driven: set[int] = set()
    current = expression
    while isinstance(current, ast.Call):
        driven.add(id(current))
        func = _expr_field(current, 'func')
        name = _name_id(func) if isinstance(func, ast.Name) else None
        args = _list_field(current, 'args')
        if not args:
            break
        if name == 'iter':
            if name in shadowed or len(args) != 1:
                break
        elif name not in eager_names:
            break
        current = args[0]
    return driven


def _driven_deferred_call_ids(node, execution_nodes, *,
                              shadowed=None) -> set[int] | None:
    is_generator = any(isinstance(item, (ast.Yield, ast.YieldFrom))
                       for item in execution_nodes)
    if isinstance(node, ast.AsyncFunctionDef):
        mode = 'async_generator' if is_generator else 'coroutine'
    elif is_generator:
        mode = 'generator'
    else:
        return None
    if shadowed is None:
        shadowed = _local_binding_names(node)
    eager_names = _EAGER_ITERABLE_CALL_NAMES - shadowed
    driven: set[int] = set()
    for current in execution_nodes:
        expression = None
        if mode == 'coroutine' and isinstance(current, ast.Await):
            expression = current.value
        elif mode == 'generator':
            if isinstance(current, ast.YieldFrom):
                expression = current.value
            elif (isinstance(current, ast.For)
                  or (isinstance(current, ast.comprehension)
                      and not current.is_async)):
                expression = current.iter
        elif (mode == 'async_generator'
              and (isinstance(current, ast.AsyncFor)
                   or (isinstance(current, ast.comprehension)
                       and current.is_async))):
            expression = current.iter
        if isinstance(expression, ast.Call):
            if mode == 'generator':
                driven.update(_driven_iterable_call_ids(
                    expression, eager_names, shadowed))
            else:
                driven.add(id(expression))
    return driven
def _iter_self_calls(node, func_name: str, *,
                    allow_bare: bool = True, shadowed=None,
                    postponed_annotations: bool = False):
    if shadowed is None:
        shadowed = _local_binding_names(node)
    eager_names = _EAGER_ITERABLE_CALL_NAMES - shadowed
    comprehension_shadowed = _comprehension_shadowed_call_ids(
        node, func_name, postponed_annotations=postponed_annotations,
        eager_names=eager_names)
    execution_nodes = tuple(_iter_execution_scope_nodes(
        node, postponed_annotations=postponed_annotations,
        func_name=func_name, eager_names=eager_names))
    driven_deferred = _driven_deferred_call_ids(
        node, execution_nodes, shadowed=shadowed)
    for child in execution_nodes:
        if not isinstance(child, ast.Call) or id(child) in comprehension_shadowed:
            continue
        if driven_deferred is not None and id(child) not in driven_deferred:
            continue
        if (_call_is_self_call(_expr_field(child, 'func'), func_name,
                                allow_bare=allow_bare, shadowed=shadowed)
                and _self_call_has_valid_arity(node, child)):
            yield child
def _perf_has_identity_self_call(node, param_names, *,
                                 allow_bare: bool = True,
                                 shadowed=None,
                                 postponed_annotations: bool = False) -> bool:
    _fname = getattr(node, 'name', None)
    if not isinstance(_fname, str):
        return False
    return any(_self_call_is_identity(node, call, param_names)
               for call in _iter_self_calls(
                   node, _fname, allow_bare=allow_bare, shadowed=shadowed,
                   postponed_annotations=postponed_annotations))
def _recursion_issue_for(entry, node, _fname: str,
                         class_nested_func_ids, *,
                         postponed_annotations: bool) -> dict | None:
    param_names = collect_param_names(node)
    _is_method = id(node) in class_nested_func_ids
    if not _perf_has_identity_self_call(
            node, param_names, allow_bare=not _is_method,
            postponed_annotations=postponed_annotations):
        return None
    return {
        'file': entry_rel_path(entry), 'function': _fname,
        'line': node_first_line(node),
        'type': 'unbounded_recursion', 'severity': 'high',
        'message': f'递归函数 {_fname} 自调用实参与形参恒等，无结构下降',
    }
def _recursion_issues_for_entry(entry) -> list:
    _method_ids = entry_class_method_ids(entry)
    postponed_annotations = _postpones_annotations(getattr(entry, 'tree', None))
    issues = []
    for node in entry_nodes(entry):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        _fname = getattr(node, 'name', None)
        if not isinstance(_fname, str):
            continue
        issue = _recursion_issue_for(
            entry, node, _fname, _method_ids,
            postponed_annotations=postponed_annotations)
        if issue is not None:
            issues.append(issue)
    return issues
def _perf_detect_recursion(cache) -> list:
    recursion_issues = []
    for entry in cache.valid_entries:
        recursion_issues.extend(_recursion_issues_for_entry(entry))
    return recursion_issues
@dataclass
class _ComplexityContext:
    class_lcom: dict
    class_rfc: dict
    function_complexities: list
    avg_cc: float
    max_cc: int
    avg_cognitive: float
    avg_mi: float
    avg_depth: float
    avg_params: float
    high_complexity: list
    total_loc: int
    complexity_density: float
    tech_debt_hours: float
    tech_debt_ratio: float
    call_frequency: Counter
    external_calls: Counter
    avg_effort: float
def _mean_or_zero(values) -> float:
    _vals = list(values)
    return sum(_vals) / len(_vals) if _vals else 0.0
def _max_or_zero(values):
    _vals = list(values)
    return max(_vals) if _vals else 0
def _top_counter_key(counter):
    if not counter:
        return None
    return min(counter.items(), key=lambda item: (-item[1], str(item[0])))[0]
def _build_complexity_metrics(
        ctx: _ComplexityContext, policy: _AnalysisPolicy) -> dict:
    _lcom_values = list(ctx.class_lcom.values())
    avg_lcom = (round(_mean_or_zero(_lcom_values), 2)
                if _lcom_values else -1.0)
    avg_rfc = _mean_or_zero(ctx.class_rfc.values())
    return {
        "total_functions": len(ctx.function_complexities),
        "avg_cyclomatic_complexity": round(ctx.avg_cc, 2),
        "max_cyclomatic_complexity": ctx.max_cc,
        "avg_cognitive_complexity": round(ctx.avg_cognitive, 2),
        "avg_maintainability_index": round(ctx.avg_mi, 1),
        "avg_nesting_depth": round(ctx.avg_depth, 2),
        "avg_param_count": round(ctx.avg_params, 2),
        "high_complexity_functions": len(ctx.high_complexity),
        "total_loc": ctx.total_loc,
        "complexity_density": round(ctx.complexity_density, 3),
        "tech_debt_hours": round(ctx.tech_debt_hours, 1),
        "tech_debt_ratio": round(ctx.tech_debt_ratio, 2),
        "max_fan_in": _max_or_zero(ctx.call_frequency.values()),
        "top_called_function": _top_counter_key(ctx.call_frequency),
        "external_coupling": len(ctx.external_calls),
        "avg_lcom": avg_lcom,
        "avg_rfc": round(avg_rfc, 1),
        "max_rfc": _max_or_zero(ctx.class_rfc.values()),
        "avg_halstead_effort": round(ctx.avg_effort, 1),
        "low_cohesion_classes": sum(h.get("type") == "low_cohesion"
                                    for h in ctx.high_complexity),
        "high_rfc_classes": sum(v > policy.rfc_high
                                for v in ctx.class_rfc.values()),
    }
_VERDICT_PASS_ISSUE_LIMIT = 3
_VERDICT_WARN_CRITICAL_LIMIT = 3
_MAX_REPORTED_FINDINGS = 30
_SEVERITY_ORDER = {'high': 0, 'medium': 1, 'low': 2}
def _pass_verdict(ctx: _ComplexityContext, medium: int) -> tuple[str, int, str]:
    summary = (f"平均CC {ctx.avg_cc:.1f}, 最大 {ctx.max_cc}, "
               f"平均MI {ctx.avg_mi:.0f}, 平均嵌套 {ctx.avg_depth:.1f}"
               + (f", {medium} 个中等问题项" if medium else ""))
    return "pass", (100 if not ctx.high_complexity else 80), summary
def _medium_cc_band(policy: _AnalysisPolicy) -> str:
    if policy.cc_high > policy.cc_medium:
        return f"CC {policy.cc_medium}-{policy.cc_high - 1}"
    return f"CC≥{policy.cc_medium}"
def _warn_severity_parts(critical: int, medium: int,
                         policy: _AnalysisPolicy) -> list[str]:
    _parts = ([f"{critical} 个高复杂度函数 (CC≥{policy.cc_high})"]
              if critical else [])
    if medium:
        _parts.append(
            f"{medium} 个中等问题项 ({_medium_cc_band(policy)}/参数/嵌套/内聚/RFC)")
    return _parts
def _warn_verdict(ctx: _ComplexityContext, critical: int,
                  medium: int, policy: _AnalysisPolicy) -> tuple[str, int, str]:
    _severity = ", ".join(_warn_severity_parts(critical, medium, policy))
    if critical <= _VERDICT_WARN_CRITICAL_LIMIT:
        return ("warn", 60, f"{_severity}, 平均MI {ctx.avg_mi:.0f}")
    return ("warn", 40,
            (f"{critical} 个高复杂度函数需重构, "
             f"共 {len(ctx.high_complexity)} 个问题项, "
             f"平均MI {ctx.avg_mi:.0f}"))
def _resolve_complexity_verdict(ctx: _ComplexityContext, critical: int,
                                medium: int,
                                policy: _AnalysisPolicy) -> tuple[str, int, str]:
    if critical == 0 and len(ctx.high_complexity) <= _VERDICT_PASS_ISSUE_LIMIT:
        return _pass_verdict(ctx, medium)
    return _warn_verdict(ctx, critical, medium, policy)
def _finding_order_key(finding: dict) -> tuple:
    severity = str(finding.get('severity') or '').lower()
    cc = finding.get('cc')
    line = finding.get('line')
    return (_SEVERITY_ORDER.get(severity, len(_SEVERITY_ORDER)),
            -(cc if isinstance(cc, int) and not isinstance(cc, bool) else 0),
            str(finding.get('file') or ''),
            line if isinstance(line, int) and not isinstance(line, bool) else 0,
            str(finding.get('type') or ''),
            str(finding.get('function') or ''))
def _finalize_complexity_results(
        result, ctx: _ComplexityContext, start: float,
        policy: _AnalysisPolicy):
    result.metrics = _build_complexity_metrics(ctx, policy)
    ordered = sorted(ctx.high_complexity, key=_finding_order_key)
    result.findings = [dict(h) for h in ordered[:_MAX_REPORTED_FINDINGS]]
    critical = sum(h.get("severity") == "high"
                   for h in ctx.high_complexity)
    medium = len(ctx.high_complexity) - critical
    result.status, result.score, result.summary = (
        _resolve_complexity_verdict(ctx, critical, medium, policy))
    result.elapsed_ms = (time.perf_counter() - start) * 1000
    _log.info(
        "[Complexity] 复杂度度量完成: 状态=%s 评分=%s 函数=%d 类=%d "
        "问题项=%d(高严重=%d) 平均CC=%.1f 最大CC=%d 耗时=%.0fms",
        result.status, result.score, len(ctx.function_complexities),
        len(ctx.class_rfc), len(ctx.high_complexity), critical,
        ctx.avg_cc, ctx.max_cc, result.elapsed_ms)
    return result
_NEST_T = frozenset((ast.If, ast.IfExp, ast.For, ast.AsyncFor,
                     ast.While, ast.With, ast.AsyncWith,
                     ast.ExceptHandler, ast.Try, TRY_STAR_T))
_NESTED_METRIC_SCOPE_T = frozenset((
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef,
))
_HALSTEAD_FIXED_T = {
    ast.Assign: '=', ast.AugAssign: '=', ast.AnnAssign: '=',
    ast.Call: '()', ast.Return: 'return', ast.Yield: 'return',
    ast.YieldFrom: 'return',
    ast.If: 'if', ast.For: 'for', ast.AsyncFor: 'for', ast.While: 'while',
    ast.Try: 'try', TRY_STAR_T: 'try', ast.With: 'with',
    ast.AsyncWith: 'with',
}
if MATCH_T is not None:
    _NEST_T = _NEST_T | {MATCH_T}
    _HALSTEAD_FIXED_T[MATCH_T] = 'match'
_TECH_DEBT_CC_BASELINE = 10
_TECH_DEBT_HOURS_PER_CC = 0.5
_MI_CC_BUDGET = 30
_MI_VOLUME_BUDGET = 5000
def _aggregate_function_stats(function_complexities: list) -> dict:
    _n = len(function_complexities)
    if not _n:
        return {"avg_cc": 0, "max_cc": 0, "avg_cognitive": 0,
                "avg_mi": 0, "avg_depth": 0, "avg_params": 0,
                "total_loc": 0, "tech_debt_hours": 0,
                "tech_debt_ratio": 0, "complexity_density": 0,
                "avg_effort": 0}
    _sum_cc = _sum_cog = _sum_mi = _sum_depth = _sum_params = 0
    _max_cc = 0
    total_loc = 0
    tech_debt_hours = 0.0
    total_effort = 0.0
    for f in function_complexities:
        _cc = f['cyclomatic_complexity']
        _sum_cc += _cc
        _max_cc = max(_max_cc, _cc)
        _sum_cog += f['cognitive_complexity']
        _sum_mi += f['maintainability_index']
        _sum_depth += f['max_nesting_depth']
        _sum_params += f['param_count']
        total_loc += f['lines']
        tech_debt_hours += (max(0, _cc - _TECH_DEBT_CC_BASELINE)
                            * _TECH_DEBT_HOURS_PER_CC)
        total_effort += f.get('halstead_difficulty', 0) * f.get('halstead_volume', 0)
    return {
        "avg_cc": _sum_cc / _n,
        "max_cc": _max_cc,
        "avg_cognitive": _sum_cog / _n,
        "avg_mi": _sum_mi / _n,
        "avg_depth": _sum_depth / _n,
        "avg_params": _sum_params / _n,
        "total_loc": total_loc,
        "tech_debt_hours": tech_debt_hours,
        "tech_debt_ratio": (tech_debt_hours / max(total_loc, 1)) * 100,
        "complexity_density": _sum_cc / max(total_loc, 1),
        "avg_effort": total_effort / _n,
    }
def _call_name_of(call) -> str | None:
    if not isinstance(call, dict):
        return None
    name = call.get('name')
    return name if isinstance(name, str) and name else None
def _iter_entry_call_names(entries) -> Iterator[str]:
    for entry in entries:
        yield from _entry_call_names(entry)
def _entry_call_names(entry) -> Iterator[str]:
    _calls = entry_calls(entry)
    if not isinstance(_calls, list):
        return
    for call in _calls:
        name = _call_name_of(call)
        if name is not None:
            yield name
def _collect_call_counters(cache: FileCache) -> tuple[Counter, Counter]:
    call_frequency: Counter = Counter()
    external_calls: Counter = Counter()
    _project_func_names = cache.get_all_function_names()
    for name in _iter_entry_call_names(cache.valid_entries):
        if name in BUILTIN_CALLABLES:
            continue
        call_frequency[name] += 1
        if name not in _project_func_names:
            external_calls[name] += 1
    return call_frequency, external_calls
_FUNC_METRICS_MEMO = weakref.WeakKeyDictionary()
def _copy_function_metrics(value: tuple) -> tuple:
    func_info, high = value
    return dict(func_info), [dict(item) for item in high]
def _memo_get(node, is_method: bool, rel_path: str, policy):
    try:
        bucket = _FUNC_METRICS_MEMO.get(node)
    except TypeError as _e:
        log_swallowed(__name__, _e, context='_memo_get:TypeError')
        return None
    if not isinstance(bucket, dict):
        return None
    value = bucket.get((is_method, rel_path, policy))
    return _copy_function_metrics(value) if value is not None else None
def _memo_put(node, is_method: bool, rel_path: str, policy, value: tuple) -> None:
    try:
        bucket = _FUNC_METRICS_MEMO.get(node)
        if not isinstance(bucket, dict):
            bucket = {}
            _FUNC_METRICS_MEMO[node] = bucket
        bucket[(is_method, rel_path, policy)] = _copy_function_metrics(value)
    except TypeError:
        _log.debug("[Complexity] 函数节点不可弱引用，memo 降级不缓存: %s",
                   value[0].get('function') or type(node).__name__)
def _boolop_token(node, operators: list) -> None:
    _bop = getattr(node, 'op', None)
    if _bop is not None:
        token = 'and' if _bop.__class__ is ast.And else 'or'
        operators.extend(
            [token] * max(len(_list_field(node, 'values')) - 1, 0))
def _compare_tokens(node, operators: list) -> None:
    _cmp_ops = getattr(node, 'ops', None)
    if not isinstance(_cmp_ops, list):
        return
    for _op in _cmp_ops:
        operators.append(_HALSTEAD_OPERATOR_TYPES.get(_op.__class__, 'cmp'))
_HALSTEAD_OPERATOR_TYPES = {
    ast.Add: '+', ast.Sub: '-', ast.Mult: '*', ast.Div: '/',
    ast.FloorDiv: '//', ast.Mod: '%', ast.Pow: '**',
    ast.LShift: '<<', ast.RShift: '>>', ast.BitOr: '|',
    ast.BitXor: '^', ast.BitAnd: '&', ast.MatMult: '@',
    ast.And: 'and', ast.Or: 'or', ast.Not: 'not',
    ast.USub: 'u-', ast.UAdd: 'u+',
    ast.Invert: '~', ast.Eq: '==', ast.NotEq: '!=',
    ast.Lt: '<', ast.LtE: '<=', ast.Gt: '>', ast.GtE: '>=',
    ast.Is: 'is', ast.IsNot: 'isnot',
    ast.In: 'in', ast.NotIn: 'notin',
}
_HALSTEAD_DYNAMIC_OP = {
    ast.BinOp: ('op', 'binop'),
    ast.UnaryOp: ('op', 'unop'),
}
def _halstead_op_token(n, operators: list) -> None:
    _t = n.__class__
    _spec = _HALSTEAD_DYNAMIC_OP.get(_t)
    if _spec is not None:
        _field, _fallback = _spec
        operators.append(_HALSTEAD_OPERATOR_TYPES.get(
            getattr(n, _field, None).__class__, _fallback))
        return
    if _t is ast.BoolOp:
        _boolop_token(n, operators)
        return
    if _t is ast.Compare:
        _compare_tokens(n, operators)
_HALSTEAD_OPERAND_FIELD = {ast.Name: 'id', ast.arg: 'arg'}
def _halstead_operand_token(n) -> str | None:
    _t = n.__class__
    if _t is ast.Constant:
        return repr(n.value) if hasattr(n, 'value') else None
    _field = _HALSTEAD_OPERAND_FIELD.get(_t)
    if _field is None:
        return None
    _val = getattr(n, _field, None)
    return _val if isinstance(_val, str) else None
def _halstead_fixed_token(n, operators: list, operands: list) -> int:
    _t = n.__class__
    _fixed = _HALSTEAD_FIXED_T.get(_t)
    if _fixed is not None:
        operators.append(_fixed)
        return int(_t is ast.Call)
    _token = _halstead_operand_token(n)
    if _token is not None:
        operands.append(_token)
    return 0
def _accumulate_comment_density(n, m: dict) -> None:
    if n.__class__ is not ast.Expr:
        return
    _nv = getattr(n, 'value', None)
    if (_nv is not None and _nv.__class__ is ast.Constant
            and isinstance(getattr(_nv, 'value', None), str)):
        m['comment_count'] += 1
def _visit_metrics_node(n, nest_d: int, m: dict, in_body: bool) -> int:
    _halstead_op_token(n, m['operators'])
    fan_out = _halstead_fixed_token(n, m['operators'], m['operands'])
    if not in_body:
        return nest_d
    m['fan_out'] += fan_out
    _accumulate_comment_density(n, m)
    new_nest_d = nest_d + 1 if n.__class__ in _NEST_T else nest_d
    m['max_depth'] = max(m['max_depth'], new_nest_d)
    return new_nest_d
def _is_elif_continuation(parent, child) -> bool:
    return (parent.__class__ is ast.If and child.__class__ is ast.If
            and len(parent.orelse) == 1 and parent.orelse[0] is child)
def _push_metric_children(stack: list, n, nest_d: int,
                          branch_nest: int, in_body: bool) -> None:
    for ch in ast.iter_child_nodes(n):
        _nest = nest_d if _is_elif_continuation(n, ch) else branch_nest
        stack.append((ch, _nest, in_body))
def _compute_all_metrics(func_node) -> dict:
    m: dict = {
        "operators": [], "operands": [],
        "max_depth": 0, "fan_out": 0, "comment_count": 0,
    }
    body_ids = {id(stmt) for stmt in getattr(func_node, 'body', ()) or ()}
    stack = [(ch, 0, id(ch) in body_ids)
             for ch in ast.iter_child_nodes(func_node)]
    while stack:
        n, nest_d, in_body = stack.pop()
        if n.__class__ in _NESTED_METRIC_SCOPE_T:
            continue
        new_nest_d = _visit_metrics_node(n, nest_d, m, in_body)
        _push_metric_children(stack, n, nest_d, new_nest_d, in_body)
    return {
        "cc": cyclomatic_complexity(func_node),
        "cognitive": cognitive_complexity(func_node),
        "max_depth": m['max_depth'], "fan_out": m['fan_out'],
        "comment_count": m['comment_count'],
        "halstead": _halstead_rollup(m['operators'], m['operands']),
    }
def _halstead_rollup(operators: list, operands: list) -> dict:
    N1 = len(operators)
    N2 = len(operands)
    n1 = len(set(operators))
    n2 = len(set(operands))
    vocabulary = n1 + n2
    length = N1 + N2
    volume = length * math.log2(vocabulary) if vocabulary > 1 else 0
    difficulty = (n1 / 2) * (N2 / n2) if n2 > 0 else 0
    return {
        'N1': N1, 'N2': N2, 'n1': n1, 'n2': n2,
        'vocabulary': vocabulary, 'length': length,
        'volume': round(volume, 2), 'difficulty': round(difficulty, 2),
        'effort': round(difficulty * volume, 2),
    }
def _node_name_str(node) -> str:
    _name = getattr(node, 'name', None)
    return _name if isinstance(_name, str) else ''
def _implicit_bound_param_count(node, is_method: bool) -> int:
    if not is_method or is_static_method(node):
        return 0
    _pargs = getattr(node, 'args', None)
    if not isinstance(_pargs, ast.arguments):
        return 0
    return 1 if (_pargs.posonlyargs or _pargs.args) else 0
def _node_param_count(node, is_method: bool) -> int:
    _pargs = getattr(node, 'args', None)
    if not isinstance(_pargs, ast.arguments):
        return 0
    def _alen(v):
        return len(v) if isinstance(v, list) else 0
    total = (_alen(getattr(_pargs, 'posonlyargs', None))
             + _alen(getattr(_pargs, 'args', None))
             + _alen(getattr(_pargs, 'kwonlyargs', None))
             + int(getattr(_pargs, 'vararg', None) is not None)
             + int(getattr(_pargs, 'kwarg', None) is not None))
    return max(total - _implicit_bound_param_count(node, is_method), 0)
def calc_function_metrics(node, rel_path: str,
                          is_method: bool = False, policy=None) -> tuple:
    policy = _coerce_analysis_policy(policy)
    _memo_hit = _memo_get(node, is_method, rel_path, policy)
    if _memo_hit is not None:
        return _memo_hit
    _m = _compute_all_metrics(node)
    cc = _m['cc']
    cognitive = _m['cognitive']
    halstead = _m['halstead']
    _fname = _node_name_str(node)
    _start = node_first_line(node)
    func_len = own_scope_line_span(node)
    param_count = _node_param_count(node, is_method)
    mi = max(0, 100 * (1 - cc / _MI_CC_BUDGET
                       - halstead['volume'] / _MI_VOLUME_BUDGET))
    func_info = {
        "file": rel_path, "function": _fname, "line": _start,
        "cyclomatic_complexity": cc,
        "cognitive_complexity": cognitive,
        "halstead_length": halstead['length'],
        "halstead_vocabulary": halstead['vocabulary'],
        "halstead_volume": round(halstead['volume'], 2),
        "halstead_difficulty": round(halstead['difficulty'], 2),
        "param_count": param_count,
        "max_nesting_depth": _m['max_depth'],
        "fan_out": _m['fan_out'],
        "lines": func_len,
        "comment_rate": round(_m['comment_count'] / max(func_len, 1), 3),
        "maintainability_index": round(mi, 1),
    }
    high = _func_high_entries(func_info, mi, policy)
    _memo_put(node, is_method, rel_path, policy, (func_info, high))
    return func_info, high
def _func_high_entries(
        func_info: dict, mi: float, policy: _AnalysisPolicy) -> list:
    rel_path = func_info['file']
    fname = func_info['function']
    start = func_info['line']
    cc = func_info['cyclomatic_complexity']
    cognitive = func_info['cognitive_complexity']
    max_depth = func_info['max_nesting_depth']
    param_count = func_info['param_count']
    high = []
    if cc >= policy.cc_medium:
        high.append({
            "file": rel_path, "function": fname, "line": start,
            "type": "high_cc", "cc": cc, "cognitive": cognitive, "mi": round(mi, 1),
            "depth": max_depth, "params": param_count,
            "severity": "high" if cc >= policy.cc_high else "medium",
            "message": (f"函数 {fname} 圈复杂度 {cc}, 认知复杂度 {cognitive}, "
                        f"嵌套深度 {max_depth}, MI {mi:.0f}"),
        })
    if param_count > policy.param_count:
        high.append({
            "file": rel_path, "function": fname, "line": start,
            "type": "too_many_params", "severity": "medium",
            "params": param_count,
            "message": f"函数 {fname} 参数过多 ({param_count}, 阈值 {policy.param_count})",
        })
    if max_depth > policy.nesting_depth:
        high.append({
            "file": rel_path, "function": fname, "line": start,
            "type": "deep_nesting", "severity": "medium",
            "depth": max_depth,
            "message": (f"函数 {fname} 嵌套过深 "
                        f"({max_depth} 层, 阈值 {policy.nesting_depth})"),
        })
    return high
def _class_scope_row(item) -> tuple[tuple, tuple] | None:
    if not isinstance(item, dict):
        return None
    _cname, _cline = item.get('name'), item.get('line')
    if not isinstance(_cname, str) or not isinstance(_cline, int):
        return None
    _cscope = item.get('scope')
    if _cscope is None:
        _cscope = ()
    elif not isinstance(_cscope, (list, tuple)):
        return None
    if not all(isinstance(_seg, str) for _seg in _cscope):
        return None
    return (_cname, _cline), tuple(_cscope)
def _class_scope_table(entry) -> dict:
    _cls_scopes: dict[tuple, tuple] = {}
    _classes = getattr(entry, 'classes', None)
    if not isinstance(_classes, (list, tuple)):
        return _cls_scopes
    for _ci in _classes:
        _row = _class_scope_row(_ci)
        if _row is not None:
            _cls_scopes[_row[0]] = _row[1]
    return _cls_scopes
def _lcom_pairwise(methods_attrs: list) -> float | None:
    if len(methods_attrs) <= 1:
        return None
    intersections = 0
    unions = 0
    for i in range(len(methods_attrs)):
        for j in range(i + 1, len(methods_attrs)):
            intersections += len(methods_attrs[i] & methods_attrs[j])
            unions += len(methods_attrs[i] | methods_attrs[j])
    if unions == 0:
        return None
    return 1 - (intersections / unions)
def _self_state_attrs(nodes, call_attr_ids: set) -> set:
    attrs = set()
    for child in nodes:
        if (isinstance(child, ast.Attribute) and id(child) not in call_attr_ids
                and isinstance(getattr(child, 'value', None), ast.Name)
                and getattr(getattr(child, 'value', None), 'id', None) == 'self'):
            attrs.add(getattr(child, 'attr', None))
    attrs.discard(None)
    return attrs
def _call_response_names(nodes) -> set:
    responses = set()
    for child in nodes:
        if not isinstance(child, ast.Call):
            continue
        _func = child.func
        if isinstance(_func, ast.Attribute):
            responses.add(_func.attr)
        elif isinstance(_func, ast.Name):
            responses.add(_func.id)
    responses.discard(None)
    return responses
def _method_self_attrs_and_responses(method) -> tuple[set, set]:
    nodes = list(iter_own_scope_nodes(method))
    call_attr_ids = {
        id(child.func) for child in nodes
        if isinstance(child, ast.Call) and isinstance(child.func, ast.Attribute)
    }
    return (_self_state_attrs(nodes, call_attr_ids),
            _call_response_names(nodes))
def _high_rfc_entry(rel_path: str, cname: str, line: int, rfc: int,
                    policy: _AnalysisPolicy) -> dict:
    return {
        "file": rel_path, "function": cname, "line": line,
        "type": "high_rfc", "severity": "medium",
        "rfc": rfc,
        "message": f"类 {cname} RFC={rfc} (阈值 {policy.rfc_high})，响应集过大",
    }
def _test_double_name(cname: str) -> bool:
    """测试替身命名：Fake*/Stub*/Dummy*/Mock*/Spy*/_Fake* 等。

    替身类的职责就是「按需实现被测代码用到的全部接口」，方法之间天然不共享
    状态（LCOM 高是定义使然）。把它们判成低内聚，等于要求给测试替身做职责
    拆分——只会让替身更难用。
    """
    stem = str(cname or "").lstrip("_")
    return any(stem.startswith(prefix) for prefix in (
        "Fake", "Stub", "Dummy", "Mock", "Spy", "Recording", "Broken",
        "Exploding", "Rejecting", "Locked", "ColorLocked"))

def _low_cohesion_entry(rel_path: str, cname: str, line: int,
                        lcom: float) -> dict:
    return {
        "file": rel_path, "function": cname, "line": line,
        "type": "low_cohesion", "severity": "medium",
        "lcom": round(lcom, 2),
        "message": (f"类 {cname} 内聚度低 (LCOM={lcom:.2f})，"
                    "建议收敛职责或提取同模块私有实现"),
    }
def _class_rfc_and_attrs(node) -> tuple[int, list]:
    methods_attrs: list[set[str]] = []
    responses: set[str] = set()
    unnamed = 0
    for method in iter_class_scope_methods(node):
        attrs, method_responses = _method_self_attrs_and_responses(method)
        methods_attrs.append(attrs)
        responses |= method_responses
        _mname = _node_name_str(method)
        if _mname:
            responses.add(_mname)
        else:
            unnamed += 1
    return len(responses) + unnamed, methods_attrs
def _calc_class_metrics(entry, policy: _AnalysisPolicy) -> tuple:
    high_lcom: list = []
    class_lcom: dict[str, float] = {}
    high_rfc: list = []
    class_rfc: dict[str, int] = {}
    rel_path = entry_rel_path(entry)
    _cls_scopes = _class_scope_table(entry)
    for node in nodes_where(entry, (ast.ClassDef,)):
        _start = node_first_line(node)
        _cname = _node_name_str(node)
        rfc, methods_attrs = _class_rfc_and_attrs(node)
        _qualified_class_name = qualified_name(
            _cls_scopes.get((_cname, _start), ()), _cname)
        _ckey = f"{rel_path}::{_qualified_class_name}"
        class_rfc[_ckey] = rfc
        if rfc > policy.rfc_high:
            high_rfc.append(_high_rfc_entry(
                rel_path, _cname, _start, rfc, policy))
        lcom = _lcom_pairwise(methods_attrs)
        if lcom is not None:
            _lcom = round(lcom, 2)
            class_lcom[_ckey] = _lcom
            if _lcom > policy.lcom_high and not _test_double_name(_cname):
                high_lcom.append(_low_cohesion_entry(rel_path, _cname,
                                                     _start, _lcom))
    return high_lcom, class_lcom, high_rfc, class_rfc
_COMPLEXITY_METHOD_NAME = "代码复杂度度量"
_COMPLEXITY_METHOD_ID = "complexity"
def _collect_function_metrics(
        cache, policy: _AnalysisPolicy) -> tuple[list, list]:
    function_complexities = []
    high_complexity = []
    for entry in cache.valid_entries:
        rel_path = entry_rel_path(entry)
        class_func_ids = entry_class_method_ids(entry)
        for node in nodes_where(entry, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_info, func_high = calc_function_metrics(
                node, rel_path, is_method=id(node) in class_func_ids,
                policy=policy)
            function_complexities.append(func_info)
            high_complexity.extend(func_high)
    return function_complexities, high_complexity
def _merge_class_metrics(
        cache, policy: _AnalysisPolicy) -> tuple[dict, dict, list, list]:
    class_lcom: dict[str, float] = {}
    class_rfc: dict[str, int] = {}
    lcom_highs: list = []
    rfc_highs: list = []
    for entry in cache.valid_entries:
        _lh, _lm, _rh, _rm = _calc_class_metrics(entry, policy)
        class_lcom.update(_lm)
        class_rfc.update(_rm)
        lcom_highs.extend(_lh)
        rfc_highs.extend(_rh)
    return class_lcom, class_rfc, lcom_highs, rfc_highs
def run_complexity_analysis(skill_dir: str, **kwargs) -> TestMethodResult:
    start = time.perf_counter()
    policy = _coerce_analysis_policy(kwargs=kwargs)
    cache = resolve_file_cache(skill_dir, kwargs)
    if cache is None:
        _log.warning(
            "[Complexity] 复杂度度量中止: 度量目录无效 %r", skill_dir)
        return TestMethodResult.invalid_input(
            skill_dir, _COMPLEXITY_METHOD_NAME, _COMPLEXITY_METHOD_ID,
            "度量", start)
    cache = _AnalysisCache(cache, policy)
    result = TestMethodResult(
        method_name=_COMPLEXITY_METHOD_NAME,
        method_id=_COMPLEXITY_METHOD_ID,
    )
    function_complexities, high_complexity = _collect_function_metrics(
        cache, policy)
    stats = _aggregate_function_stats(function_complexities)
    call_frequency, external_calls = _collect_call_counters(cache)
    class_lcom, class_rfc, lcom_highs, rfc_highs = _merge_class_metrics(
        cache, policy)
    high_complexity.extend(lcom_highs)
    high_complexity.extend(rfc_highs)
    _ctx = _ComplexityContext(
        class_lcom=class_lcom, class_rfc=class_rfc,
        function_complexities=function_complexities,
        high_complexity=high_complexity,
        call_frequency=call_frequency, external_calls=external_calls,
        **stats,
    )
    return _finalize_complexity_results(result, _ctx, start, policy)

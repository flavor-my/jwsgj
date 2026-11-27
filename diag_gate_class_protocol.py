from __future__ import annotations

import ast
import builtins
import logging
import sys
from collections.abc import Iterator
from typing import Any, NamedTuple

from jwsgj.diag_gate_class import (
    _AUTO_FIELD_BASE_NAMES,
    _B53_STATELESS_BASE_NAMES,
    _DEFAULT_FILEPATH,
    _DEFAULT_SOURCE_LINES,
    _assign_value_pairs,
    _base_name,
    _class_binding_precedes,
    _class_owned_inits,
    _class_scope_index,
    _collect_scope_import_aliases,
    _container_assign_parts,
    _dataclass_has_instance_field,
    _definition_head_slots,
    _docstring_free_stmts,
    _enclosing_import_aliases,
    _file_class_graph,
    _finish,
    _implicit_receiver_name,
    _import_name_shadowed,
    _is_classmethod,
    _is_composition_type_name,
    _is_dataclass,
    _is_receiver_ref,
    _issue,
    _iter_class_methods,
    _iter_import_scopes,
    _method_defs,
    _mm01_annotation_is_classvar,
    _ref_sets_from_aliases,
    _resolvable_base_name,
    _resolve_base,
    _scope_shadow_state,
)
from jwsgj.diag_shared_ast_bindings import (
    import_stmt_binds,
    module_scope_binds,
)
from jwsgj.diag_shared_ast_nodes import (
    block_may_fall_through as _block_may_fall_through,
)
from jwsgj.diag_shared_ast_nodes import (
    empty_container_ctor_name,
    is_placeholder_stmt,
    is_static_method,
    iter_own_nodes,
    iter_own_scope,
    str_constant_value,
    walk_stmts,
)
from jwsgj.diag_shared_ast_views import (
    iter_skip_nested_class,
    parent_map,
    same_scope_bfs_nodes,
    tree_nodes,
)
from jwsgj.diag_shared_source_core import (
    extract_code_lines,
    parse_py_file,
    suggest,
)
from jwsgj.diag_types_defs import (
    DiagnoseIssue,
    PatternFinding,
    finding_scan_exempt,
)
from jwsgj.diag_types_vocab import DiagnoseSeverity
from jwsgj.prevention_scope_facts import walk_nodes

logger = logging.getLogger(__name__)
def _has_positional_slot(fn: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    a = fn.args
    return any((a.args, a.posonlyargs, a.vararg))
class _B41Hits(NamedTuple):
    as_str: bool
    as_repr: bool
    as_format: bool
    receiver_nodes: frozenset[int] = frozenset()
def _b41_conversion_hits(conversion: str | None, hits: _B41Hits) -> bool:
    if conversion in ('r', 'a'):
        return hits.as_repr
    return hits.as_format if conversion is None else hits.as_str
def _b41_constant_fstring_text(node: ast.JoinedStr) -> str | None:
    parts: list[str] = []
    for part in node.values:
        if isinstance(part, ast.Constant):
            if not isinstance(part.value, str):
                return None
            parts.append(part.value)
            continue
        if not isinstance(part, ast.FormattedValue):
            return None
        if not isinstance(part.value, ast.Constant):
            return None
        if not _b41_format_spec_is_bare(part.format_spec):
            return None
        value = part.value.value
        try:
            if part.conversion == -1:
                converted = format(value, '')
            elif part.conversion == 115:
                converted = str(value)
            elif part.conversion == 114:
                converted = repr(value)
            elif part.conversion == 97:
                converted = ascii(value)
            else:
                return None
        except (TypeError, ValueError, OverflowError):
            return None
        parts.append(converted)
    return ''.join(parts)
def _b41_format_spec_is_bare(spec: ast.AST | None) -> bool:
    if spec is None:
        return True
    return (isinstance(spec, ast.JoinedStr)
            and _b41_constant_fstring_text(spec) == '')
def _b41_fstring_hits_self(sub: ast.FormattedValue, hits: _B41Hits,
                           receiver: str) -> bool:
    if sub.conversion == -1:
        if not _b41_format_spec_is_bare(sub.format_spec):
            return False
        conversion = None
    elif sub.conversion in (114, 97, 115):
        conversion = chr(sub.conversion)
    else:
        return False
    return _b41_value_hits_self(sub.value, conversion, hits, receiver)
def _b41_format_spec_is_empty(rest: list[ast.expr]) -> bool:
    if not rest:
        return True
    return len(rest) == 1 and str_constant_value(rest[0]) == ''
def _builtin_name_shadowed(node: ast.AST, name: str, parents: dict,
                           module_bindings: set[str]) -> bool:
    if (name in module_bindings
            or _import_name_shadowed(node, name, parents, {})):
        return True
    memo: dict = {}
    current = parents.get(node)
    while current is not None and not isinstance(current, ast.Module):
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda)):
            _rebound, is_global = _scope_shadow_state(
                name, current, memo, include_imports=False)
            if is_global:
                return False
            for bound_name, source in _collect_scope_import_aliases(
                    current).items():
                if bound_name == '*':
                    if not (isinstance(source, tuple)
                            and source[0] == 'builtins'):
                        return True
                    continue
                if bound_name != name:
                    continue
                if isinstance(source, tuple) and source == ('builtins', name):
                    continue
                return True
        current = parents.get(current)
    return False

def _b41_strcall_hits_self(sub: ast.Call, hits: _B41Hits,
                            receiver: str, parents: dict,
                            module_bindings: set[str]) -> bool:
    f_ = sub.func
    if not (isinstance(f_, ast.Name) and not sub.keywords and sub.args):
        return False
    if f_.id not in ('str', 'format', 'repr', 'ascii'):
        return False
    if _builtin_name_shadowed(sub, f_.id, parents, module_bindings):
        return False
    argument = sub.args[0]
    rest = sub.args[1:]
    if f_.id == 'str':
        return (not rest and _b41_value_hits_self(
            argument, 's', hits, receiver))
    if f_.id == 'format':
        return (_b41_format_spec_is_empty(rest)
                and _b41_value_hits_self(argument, None, hits, receiver))
    return (f_.id in ('repr', 'ascii') and not rest
            and _b41_value_hits_self(
                argument, 'r' if f_.id == 'repr' else 'a', hits, receiver))
def _b41_split_arg_accessor(head: str) -> tuple[str, str]:
    for index, char in enumerate(head):
        if char in '.[':
            return head[:index], head[index:]
    return head, ''
def _b41_field_arg_key(
        field_text: str) -> tuple[int | str | None, str | None, bool]:
    head, _sep, format_spec = field_text.partition(':')
    conversion = None
    if '!' in head:
        head, _, conv_text = head.partition('!')
        conversion = (conv_text
                      if len(conv_text) == 1 and conv_text in 'sra' else '')
    arg_ref, accessor = _b41_split_arg_accessor(head)
    key: int | str | None
    if not arg_ref:
        key = None
    elif arg_ref.isdecimal():
        try:
            key = int(arg_ref)
        except ValueError:
            key = arg_ref
    else:
        key = arg_ref
    if accessor:
        return key, conversion, False
    bare = bool(conversion) or not format_spec
    if not arg_ref:
        return None, conversion, bare
    return key, conversion, bare
def _b41_format_field_end(fmt_text: str, start: int) -> tuple[int, bool]:
    depth = 1
    pos = start
    while pos < len(fmt_text) and depth:
        if fmt_text[pos] == '{':
            depth += 1
        elif fmt_text[pos] == '}':
            depth -= 1
        pos += 1
    return pos, depth == 0
def _b41_iter_format_fields(fmt_text: str) -> Iterator[str]:
    i = 0
    n = len(fmt_text)
    while i < n:
        ch = fmt_text[i]
        if ch == '{':
            if i + 1 < n and fmt_text[i + 1] == '{':
                i += 2
                continue
            field_start = i + 1
            i, closed = _b41_format_field_end(fmt_text, field_start)
            if closed:
                yield fmt_text[field_start:i - 1]
        elif ch == '}':
            if i + 1 < n and fmt_text[i + 1] == '}':
                i += 2
                continue
            return
        else:
            i += 1
def _b41_skip_mapping_key(fmt_text: str, i: int,
                          n: int) -> tuple[int, str | None]:
    start = i + 1
    depth = 0
    while i < n:
        if fmt_text[i] == '(':
            depth += 1
        elif fmt_text[i] == ')':
            depth -= 1
            if depth == 0:
                return i + 1, fmt_text[start:i]
        i += 1
    return i, None
def _b41_skip_flags(fmt_text: str, i: int, n: int) -> int:
    while i < n and fmt_text[i] in '#0- +':
        i += 1
    return i
def _b41_skip_width(fmt_text: str, i: int, n: int) -> tuple[int, int]:
    if i < n and fmt_text[i] == '*':
        return i + 1, 1
    while i < n and fmt_text[i].isdigit():
        i += 1
    return i, 0
def _b41_skip_precision(fmt_text: str, i: int, n: int) -> tuple[int, int]:
    if not (i < n and fmt_text[i] == '.'):
        return i, 0
    i += 1
    if i < n and fmt_text[i] == '*':
        return i + 1, 1
    while i < n and fmt_text[i].isdigit():
        i += 1
    return i, 0
def _b41_skip_length(fmt_text: str, i: int, n: int) -> int:
    if i < n and fmt_text[i] in 'hlL':
        i += 1
    return i
def _b41_iter_percent_specs(
        fmt_text: str) -> Iterator[tuple[str | None, str, int]]:
    i = 0
    n = len(fmt_text)
    while i < n:
        if fmt_text[i] != '%':
            i += 1
            continue
        i += 1
        if i >= n:
            return
        if fmt_text[i] == '%':
            i += 1
            continue
        mapping_key = None
        if fmt_text[i] == '(':
            i, mapping_key = _b41_skip_mapping_key(fmt_text, i, n)
            if mapping_key is None:
                return
        i = _b41_skip_flags(fmt_text, i, n)
        i, stars = _b41_skip_width(fmt_text, i, n)
        i, precision_stars = _b41_skip_precision(fmt_text, i, n)
        stars += precision_stars
        i = _b41_skip_length(fmt_text, i, n)
        if i >= n:
            return
        if fmt_text[i] not in 'diouxXeEfFgGcrsa':
            return
        yield mapping_key, fmt_text[i], stars
        i += 1
def _b41_format_call_parts(
        sub: ast.Call,
) -> tuple[str, dict[int, ast.expr], dict[str, ast.expr]] | None:
    func = sub.func
    if not (isinstance(func, ast.Attribute) and func.attr == 'format'):
        return None
    fmt_text = str_constant_value(func.value)
    if fmt_text is None or not (sub.args or sub.keywords):
        return None
    positions = dict(enumerate(sub.args))
    keywords = {kw.arg: kw.value for kw in sub.keywords if kw.arg}
    return fmt_text, positions, keywords
_B41_SPEC_UNKNOWN = object()
_B41_SPEC_ERROR = object()
def _b41_spec_output_is_bounded(text: str) -> bool:
    if len(text) > 256:
        return False
    digits = 0
    for char in text:
        if char.isdigit():
            digits += 1
            if digits > 3:
                return False
        else:
            digits = 0
    return True
def _b41_constant_format_spec(
        spec_text: str, positions: dict[int, ast.expr],
        keywords: dict[str, ast.expr], auto_start: int = 0):
    if not spec_text:
        return ''
    if not _b41_spec_output_is_bounded(spec_text):
        return _B41_SPEC_UNKNOWN
    initial_auto = auto_start
    uses_auto = False
    uses_manual = False
    for field_text in _b41_iter_format_fields(spec_text):
        key, _conversion, bare = _b41_field_arg_key(field_text)
        if key is None:
            key = auto_start
            auto_start += 1
            uses_auto = True
        elif isinstance(key, int):
            uses_manual = True
        if not bare:
            return _B41_SPEC_UNKNOWN
        if uses_auto and uses_manual:
            return _B41_SPEC_ERROR
        argument = positions.get(key) if isinstance(key, int) else keywords.get(key)
        if not isinstance(argument, ast.Constant):
            return _B41_SPEC_UNKNOWN
        if isinstance(argument.value, int) and abs(argument.value) > 999:
            return _B41_SPEC_UNKNOWN
    values = [node.value if isinstance(node, ast.Constant) else None
              for _key, node in sorted(positions.items())]
    if uses_auto:
        values = values[initial_auto:]
    named_values = {key: node.value if isinstance(node, ast.Constant) else None
                    for key, node in keywords.items()}
    try:
        resolved = spec_text.format(*values, **named_values)
    except (AttributeError, IndexError, KeyError, TypeError, ValueError):
        return _B41_SPEC_ERROR
    return resolved if _b41_spec_output_is_bounded(resolved) else _B41_SPEC_UNKNOWN
def _b41_constant_format_has_error(argument: ast.expr, conversion: str | None,
                                   format_spec: str) -> bool:
    if not isinstance(argument, ast.Constant):
        return False
    value = argument.value
    try:
        if conversion == 's':
            value = str(value)
        elif conversion == 'r':
            value = repr(value)
        elif conversion == 'a':
            value = ascii(value)
        format(value, format_spec)
    except (TypeError, ValueError, OverflowError):
        return True
    return False
def _b41_fstring_format_error(node: ast.FormattedValue, hits: _B41Hits,
                              receiver: str) -> bool:
    if node.conversion == -1:
        conversion = None
    elif node.conversion in (114, 97, 115):
        conversion = chr(node.conversion)
    else:
        return False
    if node.format_spec is None:
        spec_text = ''
    elif isinstance(node.format_spec, ast.JoinedStr):
        spec_text = _b41_constant_fstring_text(node.format_spec)
    else:
        return False
    if spec_text is None:
        return False
    if _b41_constant_format_has_error(node.value, conversion, spec_text):
        return True
    if conversion is not None or not spec_text:
        return False
    if isinstance(node.value, (ast.List, ast.Tuple, ast.Set, ast.Dict)):
        return True
    return hits.as_format and _is_receiver_ref(node.value, receiver)
def _b41_fstring_unreachable(node: ast.AST, parents: dict,
                             hits: _B41Hits, receiver: str) -> bool:
    current: ast.AST | None = node
    while current is not None:
        if isinstance(current, ast.FormattedValue):
            parent = parents.get(current)
            if isinstance(parent, ast.JoinedStr):
                for previous in parent.values:
                    if previous is current:
                        break
                    if (isinstance(previous, ast.FormattedValue)
                            and _b41_fstring_format_error(
                                previous, hits, receiver)):
                        return True
        current = parents.get(current)
    return False
def _b41_format_fields_hit_self(
        fmt_text: str, positions: dict[int, ast.expr],
        keywords: dict[str, ast.expr], hits: _B41Hits,
        receiver: str) -> bool:
    auto = 0
    numbering: str | None = None
    halted = False
    def visit(text: str) -> bool:
        nonlocal auto, numbering, halted
        for field_text in _b41_iter_format_fields(text):
            key, conversion, bare = _b41_field_arg_key(field_text)
            if conversion == '':
                halted = True
                return False
            if key is None:
                if numbering == 'manual':
                    halted = True
                    return False
                numbering = 'auto'
                key = auto
                auto += 1
            elif isinstance(key, int):
                if numbering == 'auto':
                    halted = True
                    return False
                numbering = 'manual'
            if key in positions:
                argument = positions[key]
            elif key in keywords:
                argument = keywords[key]
            else:
                halted = True
                return False
            _head, separator, nested_spec = field_text.partition(':')
            resolved_spec = (_b41_constant_format_spec(
                nested_spec, positions, keywords, auto) if separator
                else _B41_SPEC_UNKNOWN)
            effective_bare = (bool(conversion) or not resolved_spec
                              if isinstance(resolved_spec, str) else bare)
            if (conversion is not None and effective_bare
                    and _b41_value_hits_self(
                        argument, conversion, hits, receiver)):
                return True
            if separator and '{' in nested_spec and visit(nested_spec):
                return True
            if halted:
                return False
            if (resolved_spec is _B41_SPEC_ERROR
                    or (separator and resolved_spec is _B41_SPEC_UNKNOWN)):
                halted = True
                return False
            if (conversion is None and effective_bare
                    and _b41_value_hits_self(
                        argument, conversion, hits, receiver)):
                return True
            if isinstance(resolved_spec, str):
                if _b41_constant_format_has_error(
                        argument, conversion, resolved_spec):
                    halted = True
                    return False
                if (conversion is None and resolved_spec
                        and (_is_receiver_ref(argument, receiver)
                             or isinstance(argument, (ast.List, ast.Tuple,
                                                      ast.Set, ast.Dict)))):
                    halted = True
                    return False
        return False
    return visit(fmt_text)
def _b41_format_method_hits_self(sub: ast.Call, hits: _B41Hits,
                                 receiver: str) -> bool:
    parts = _b41_format_call_parts(sub)
    return bool(parts and _b41_format_fields_hit_self(
        *parts, hits, receiver))
def _b41_percent_star_is_valid_literal(node: ast.expr) -> bool:
    if isinstance(node, (ast.List, ast.Tuple, ast.Set, ast.Dict)):
        return False
    try:
        value = ast.literal_eval(node)
    except (SyntaxError, TypeError, ValueError):
        return False
    return isinstance(value, int)
def _b41_literal_percent_error(argument: ast.expr,
                                  conversion: str) -> bool | None:
    if isinstance(argument, ast.List):
        value = []
    elif isinstance(argument, ast.Tuple):
        value = ()
    elif isinstance(argument, ast.Set):
        value = set()
    elif isinstance(argument, ast.Dict):
        value = {}
    else:
        try:
            value = ast.literal_eval(argument)
        except (SyntaxError, TypeError, ValueError):
            return None
    try:
        ('%' + conversion) % (value,)
    except (TypeError, ValueError, OverflowError):
        return True
    return False
def _b41_tuple_percent_hits_self(
        specs: list[tuple[str | None, str, int]],
        elements: list[ast.expr], hits: _B41Hits,
        receiver: str) -> bool:
    index = 0
    for mapping_key, conversion, stars in specs:
        if index + stars > len(elements):
            return False
        if not all(_b41_percent_star_is_valid_literal(element)
                   for element in elements[index:index + stars]):
            return False
        index += stars
        if index >= len(elements):
            return False
        element = elements[index]
        index += 1
        if mapping_key is not None:
            return False
        error = _b41_literal_percent_error(element, conversion)
        if error:
            return False
        if _b41_percent_value_hits_self(element, conversion, hits, receiver):
            return True
        if error is None and conversion not in ('s', 'r', 'a'):
            return False
    return False
def _b41_container_elements(node: ast.expr) -> list[ast.expr]:
    if isinstance(node, ast.Dict):
        return [item for item in (*node.keys, *node.values)
                if item is not None]
    return list(node.elts)
def _b41_container_hits_self(node: ast.expr, hits: _B41Hits,
                             receiver: str) -> bool:
    if isinstance(node, (ast.List, ast.Set, ast.Dict, ast.Tuple)):
        return any(_b41_value_hits_self(element, 'r', hits, receiver)
                   for element in _b41_container_elements(node))
    # 列表/集合/字典推导式在格式化时会先构造容器，再对元素逐个 repr；
    # 生成器表达式只 repr 生成器对象、不评估元素，故不在此列。
    if isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp)):
        elements = ((node.key, node.value)
                    if isinstance(node, ast.DictComp) else (node.elt,))
        return any(_b41_value_hits_self(element, 'r', hits, receiver)
                   for element in elements)
    return False
_B41_COMPREHENSION_TYPES = (
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
)
def _b41_target_names(target: ast.AST) -> set[str]:
    return {sub.id for sub in ast.walk(target)
            if isinstance(sub, ast.Name)}
def _b41_lambda_binds_name(node: ast.Lambda, name: str) -> bool:
    args = node.args
    parameters = {arg.arg for arg in (
        *args.posonlyargs, *args.args, *args.kwonlyargs)}
    if args.vararg:
        parameters.add(args.vararg.arg)
    if args.kwarg:
        parameters.add(args.kwarg.arg)
    return name in parameters or any(
        isinstance(sub, ast.Name) and sub.id == name
        and isinstance(sub.ctx, (ast.Store, ast.Del))
        for sub in ast.walk(node.body))
def _b41_collect_receiver_aliases(
        root: ast.AST, name: str, aliases: set[int]) -> None:
    stack = [root]
    while stack:
        current = stack.pop()
        if current is not root:
            if (isinstance(current, ast.Lambda)
                    and _b41_lambda_binds_name(current, name)):
                continue
            if (isinstance(current, _B41_COMPREHENSION_TYPES)
                    and any(name in _b41_target_names(gen.target)
                            for gen in current.generators)):
                continue
        if (isinstance(current, ast.Name) and current.id == name
                and isinstance(current.ctx, ast.Load)):
            aliases.add(id(current))
        stack.extend(ast.iter_child_nodes(current))
def _b41_collect_active_receiver_aliases(
        root: ast.AST, active: set[str], aliases: set[int]) -> None:
    for name in active:
        _b41_collect_receiver_aliases(root, name, aliases)
def _b41_comprehension_receiver_nodes(
        node: ast.AST, receiver: str) -> frozenset[int]:
    aliases: set[int] = set()
    for sub in ast.walk(node):
        if not isinstance(sub, _B41_COMPREHENSION_TYPES):
            continue
        active: set[str] = set()
        for gen in sub.generators:
            _b41_collect_active_receiver_aliases(gen.iter, active, aliases)
            value_is_receiver = False
            if (isinstance(gen.iter, (ast.List, ast.Tuple, ast.Set))
                    and len(gen.iter.elts) == 1):
                value = gen.iter.elts[0]
                value_is_receiver = (
                    _is_receiver_ref(value, receiver)
                    or (isinstance(value, ast.Name) and value.id in active)
                    or id(value) in aliases)
            for name in _b41_target_names(gen.target):
                active.discard(name)
            if isinstance(gen.target, ast.Name) and value_is_receiver:
                active.add(gen.target.id)
            for condition in gen.ifs:
                _b41_collect_active_receiver_aliases(
                    condition, active, aliases)
        values = ([sub.key, sub.value] if isinstance(sub, ast.DictComp)
                  else [sub.elt])
        for value in values:
            _b41_collect_active_receiver_aliases(value, active, aliases)
    return frozenset(aliases)
def _b41_value_hits_self(node: ast.expr, conversion: str | None,
                         hits: _B41Hits, receiver: str) -> bool:
    if (_is_receiver_ref(node, receiver)
            or id(node) in hits.receiver_nodes):
        return _b41_conversion_hits(conversion, hits)
    return hits.as_repr and _b41_container_hits_self(node, hits, receiver)
def _b41_percent_value_hits_self(node: ast.expr, conversion: str,
                                 hits: _B41Hits, receiver: str) -> bool:
    if conversion not in ('s', 'r', 'a'):
        return False
    return _b41_value_hits_self(node, conversion, hits, receiver)
def _b41_mapping_value(node: ast.Dict,
                       mapping_key: str) -> tuple[ast.expr | None, bool]:
    for key_node, value in reversed(list(zip(node.keys, node.values,
                                             strict=True))):
        if key_node is None:
            return None, False
        key = str_constant_value(key_node)
        if key is None:
            return None, False
        if key == mapping_key:
            return value, True
    return None, False
def _b41_dict_percent_hits_self(
        specs: list[tuple[str | None, str, int]], rhs: ast.Dict,
        hits: _B41Hits, receiver: str) -> bool:
    for index, (mapping_key, conversion, stars) in enumerate(specs):
        if stars:
            return False
        if mapping_key is None:
            if index:
                return False
            argument = rhs
        else:
            argument, found = _b41_mapping_value(rhs, mapping_key)
            if not found or argument is None:
                return False
        error = _b41_literal_percent_error(argument, conversion)
        if error:
            return False
        if _b41_percent_value_hits_self(argument, conversion, hits, receiver):
            return True
        if error is None and conversion not in ('s', 'r', 'a'):
            return False
    return False
def _b41_percent_hits_self(sub: ast.BinOp, hits: _B41Hits,
                           receiver: str) -> bool:
    fmt_text = str_constant_value(sub.left)
    if fmt_text is None:
        return False
    specs = list(_b41_iter_percent_specs(fmt_text))
    if not specs:
        return False
    rhs = sub.right
    if isinstance(rhs, ast.Tuple):
        return _b41_tuple_percent_hits_self(specs, rhs.elts, hits, receiver)
    if isinstance(rhs, ast.Dict):
        return _b41_dict_percent_hits_self(specs, rhs, hits, receiver)
    if not (_is_receiver_ref(rhs, receiver)
            or isinstance(rhs, (ast.List, ast.Set,
                                ast.ListComp, ast.SetComp, ast.DictComp))):
        return False
    mapping_key, conversion, stars = specs[0]
    if mapping_key is not None or stars:
        return False
    return _b41_percent_value_hits_self(rhs, conversion, hits, receiver)
_EAGER_GENEXP_CALL_ARITIES = {
    'list': (1,), 'tuple': (1,), 'set': (1,), 'frozenset': (1,),
    'dict': (1,), 'sorted': (1,), 'any': (1,), 'all': (1,),
    'min': (1,), 'max': (1,), 'sum': (1, 2), 'next': (1, 2),
}
_EAGER_GENEXP_ANY_EXPLICIT_KEYWORDS = frozenset({'dict', 'sorted'})
_EAGER_GENEXP_ALLOWED_KEYWORDS = {
    'min': frozenset({'key', 'default'}),
    'max': frozenset({'key', 'default'}),
    'sum': frozenset({'start'}),
}
def _eager_genexp_keywords_consumed(name: str, keywords: list) -> bool:
    if any(keyword.arg is None for keyword in keywords):
        return False
    if name in _EAGER_GENEXP_ANY_EXPLICIT_KEYWORDS:
        return True
    allowed = _EAGER_GENEXP_ALLOWED_KEYWORDS.get(name, frozenset())
    return all(keyword.arg in allowed for keyword in keywords)
def _is_zero_arg_lambda_call(node: ast.Call) -> bool:
    if not isinstance(node.func, ast.Lambda) or node.args or node.keywords:
        return False
    if any(isinstance(sub, (ast.Yield, ast.YieldFrom))
           for sub in iter_own_nodes(node.func)):
        return False
    args = node.func.args
    positional = [*args.posonlyargs, *args.args]
    required_positional = max(len(positional) - len(args.defaults), 0)
    return (required_positional == 0
            and all(default is not None for default in args.kw_defaults))
def _is_async_generator_exp(node: ast.AST) -> bool:
    return (isinstance(node, ast.GeneratorExp)
            and any(gen.is_async for gen in node.generators))
def _consumed_genexp(node: ast.AST, *, is_async: bool) -> ast.GeneratorExp | None:
    if not isinstance(node, ast.GeneratorExp):
        return None
    return node if _is_async_generator_exp(node) == is_async else None
def _eager_exec_child_ids(node: ast.AST, consumed: bool, parents: dict,
                          module_bindings: set[str]) -> set[int]:
    eager: set[int] = set()
    if isinstance(node, ast.Call):
        if _is_zero_arg_lambda_call(node):
            eager.add(id(node.func))
        elif isinstance(node.func, ast.Name):
            name = node.func.id
            arities = _EAGER_GENEXP_CALL_ARITIES.get(name)
            genexp = (_consumed_genexp(node.args[0], is_async=False)
                      if node.args else None)
            if (arities and genexp is not None
                    and not _builtin_name_shadowed(
                        node, name, parents, module_bindings)
                    and _eager_genexp_keywords_consumed(name, node.keywords)
                    and len(node.args) in arities):
                eager.add(id(genexp))
        elif (isinstance(node.func, ast.Attribute)
              and node.func.attr == 'join'
              and isinstance(node.func.value, ast.Constant)
              and isinstance(node.func.value.value, str)
              and len(node.args) == 1 and not node.keywords):
            genexp = _consumed_genexp(node.args[0], is_async=False)
            if genexp is not None:
                eager.add(id(genexp))
    elif isinstance(node, (ast.For, ast.AsyncFor)):
        genexp = _consumed_genexp(
            node.iter, is_async=isinstance(node, ast.AsyncFor))
        if genexp is not None:
            eager.add(id(genexp))
    elif (isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp))
          or (isinstance(node, ast.GeneratorExp) and consumed)):
        for gen in node.generators:
            genexp = _consumed_genexp(gen.iter, is_async=bool(gen.is_async))
            if genexp is not None:
                eager.add(id(gen))
    elif isinstance(node, ast.comprehension) and consumed:
        genexp = _consumed_genexp(node.iter, is_async=bool(node.is_async))
        if genexp is not None:
            eager.add(id(genexp))
    elif isinstance(node, (ast.Starred, ast.YieldFrom)):
        genexp = _consumed_genexp(node.value, is_async=False)
        if genexp is not None:
            eager.add(id(genexp))
    return eager
def _iter_exec_nodes(node: ast.AST, *, include_root: bool, parents: dict,
                     module_bindings: set[str]) -> Iterator[ast.AST]:
    stack: list[tuple[ast.AST, bool]] = [(node, False)]
    while stack:
        current, consumed = stack.pop()
        if include_root or current is not node:
            yield current
        eager: set[int] = set()
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef)):
            children = _definition_head_slots(current)
        elif isinstance(current, ast.Lambda):
            children = _definition_head_slots(current)
            if consumed:
                children = [*children, current.body]
        elif isinstance(current, ast.GeneratorExp) and not consumed:
            children = ([current.generators[0].iter]
                        if current.generators else [])
        else:
            children = list(ast.iter_child_nodes(current))
            eager = _eager_exec_child_ids(
                current, consumed, parents, module_bindings)
        stack.extend(reversed([(child, id(child) in eager)
                               for child in children]))
def _b41_lambda_has_constant_receiver_default(
        node: ast.Lambda, receiver: str) -> bool:
    args = node.args
    positional = [*args.posonlyargs, *args.args]
    default_offset = len(positional) - len(args.defaults)
    for index, argument in enumerate(positional):
        if argument.arg == receiver:
            default_index = index - default_offset
            return (default_index >= 0
                    and isinstance(args.defaults[default_index], ast.Constant))
    for argument, default in zip(args.kwonlyargs, args.kw_defaults,
                                 strict=True):
        if argument.arg == receiver:
            return isinstance(default, ast.Constant)
    return False
def _b41_constant_lambda_shadows_receiver(
        node: ast.AST, root: ast.AST, receiver: str, parents: dict) -> bool:
    current = node
    while current is not root:
        parent = parents.get(current)
        if parent is None:
            return False
        if (isinstance(parent, ast.Lambda) and current is parent.body
                and _b41_lambda_has_constant_receiver_default(
                    parent, receiver)):
            return True
        current = parent
    return False
def _b41_fmt_refs_bare_self(node: ast.AST, hits: _B41Hits,
                            receiver: str, parents: dict,
                            module_bindings: set[str]) -> bool:
    for sub in _iter_exec_nodes(
            node, include_root=True, parents=parents,
            module_bindings=module_bindings):
        if _b41_constant_lambda_shadows_receiver(
                sub, node, receiver, parents):
            continue
        if _b41_node_hits_self(
                sub, hits, receiver, parents, module_bindings):
            return True
    return False
def _b41_node_hits_self(sub: ast.AST, hits: _B41Hits,
                        receiver: str, parents: dict,
                        module_bindings: set[str]) -> bool:
    if _b41_fstring_unreachable(sub, parents, hits, receiver):
        return False
    if isinstance(sub, ast.FormattedValue):
        return _b41_fstring_hits_self(sub, hits, receiver)
    if isinstance(sub, ast.Call):
        return (_b41_strcall_hits_self(
            sub, hits, receiver, parents, module_bindings)
                or _b41_format_method_hits_self(sub, hits, receiver))
    if isinstance(sub, ast.BinOp) and isinstance(sub.op, ast.Mod):
        return _b41_percent_hits_self(sub, hits, receiver)
    return False
def _b41_declares_dunder(cls: ast.ClassDef, bases_of: dict,
                          dunder_name: str) -> bool:
    pending = [cls]
    seen: set[ast.ClassDef] = set()
    while pending:
        cur = pending.pop()
        if cur in seen:
            continue
        seen.add(cur)
        if any(isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef))
               and fn.name == dunder_name
               for fn in same_scope_bfs_nodes(cur)):
            return True
        pending.extend(bases_of.get(cur, []))
    return False
_B41_OBJECT_FALLBACK_BASES = frozenset({
    'object', 'ABC', 'ABCMeta', 'Protocol', 'Generic',
})
def _b41_external_base_declares_dunder(base_name: str,
                                       dunder_name: str) -> bool | None:
    if base_name in _B41_OBJECT_FALLBACK_BASES:
        return False
    base_type = getattr(builtins, base_name, None)
    if not isinstance(base_type, type):
        return None
    for base in base_type.__mro__:
        if dunder_name in vars(base):
            return base is not object
    return False
def _b41_external_base_interrupts_fallback(
        cls: ast.ClassDef, bases_of: dict, parents: dict, scopes: dict,
        dunder_name: str) -> bool:
    pending = [cls]
    seen: set[ast.ClassDef] = set()
    while pending:
        cur = pending.pop()
        if cur in seen:
            continue
        seen.add(cur)
        for base in cur.bases:
            base_name = _resolvable_base_name(base)
            if base_name is None:
                return True
            local = _resolve_base(base_name, cur, parents, scopes)
            if local is not None:
                continue
            if _b41_external_base_declares_dunder(
                    base_name, dunder_name) is not False:
                return True
        pending.extend(bases_of.get(cur, []))
    return False
def _b41_object_fallback_interrupted(
        cls: ast.ClassDef, bases_of: dict, parents: dict, scopes: dict,
        dunder_name: str) -> bool:
    return (_b41_declares_dunder(cls, bases_of, dunder_name)
            or _b41_external_base_interrupts_fallback(
                cls, bases_of, parents, scopes, dunder_name))
def detect_b41_repr_str_self_recursion(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    parents = parent_map(tree)
    scopes = _class_scope_index(tree, parents)
    module_bindings = module_scope_binds(tree.body)
    _children, bases_of = _file_class_graph(tree)
    for cls, fn in _iter_class_methods(tree):
        if not (isinstance(fn, ast.FunctionDef)
                and fn.name in ('__repr__', '__str__')):
            continue
        if any(isinstance(sub, (ast.Yield, ast.YieldFrom))
               for sub in iter_own_nodes(fn)):
            continue
        if _is_classmethod(fn):
            continue
        receiver = _implicit_receiver_name(fn, is_method=True)
        if receiver is None:
            continue
        str_hits = (fn.name == '__str__'
                    or not _b41_object_fallback_interrupted(
                        cls, bases_of, parents, scopes, '__str__'))
        hits = _B41Hits(
            as_str=str_hits,
            as_repr=fn.name == '__repr__',
            as_format=(str_hits
                       and not _b41_object_fallback_interrupted(
                           cls, bases_of, parents, scopes, '__format__')),
            receiver_nodes=_b41_comprehension_receiver_nodes(fn, receiver),
        )
        if not any(_b41_fmt_refs_bare_self(
                stmt, hits, receiver, parents, module_bindings)
                   for stmt in fn.body):
            continue
        issues.append(_issue(
            'B41', DiagnoseSeverity.ERROR,
            f'{fn.name} 内格式化裸 self——重入自身即无限递归（RecursionError）',
            fn.lineno,
            '格式化 self 的属性（{self.x}），或拼接固定描述（f"<ClassName id=...>"）'))
    return _finish('B41', 'repr/str 自递归', issues, filepath)
def _b10_init_value_returns(node: ast.AST):
    for sub in same_scope_bfs_nodes(node):
        if not isinstance(sub, ast.Return):
            continue
        if sub.value is None:
            continue
        if isinstance(sub.value, ast.Constant) and sub.value.value is None:
            continue
        yield sub
def _b10_init_issues(init: ast.AST) -> list[DiagnoseIssue]:
    if isinstance(init, ast.AsyncFunctionDef):
        return [_issue(
            'B10', DiagnoseSeverity.ERROR,
            'async __init__ 是协程函数，实例化时返回 coroutine 对象而非 None，必触发 TypeError',
            init.lineno, '移除 async，改为普通同步 __init__')]
    return [_issue(
        'B10', DiagnoseSeverity.ERROR,
        '__init__ 返回非 None 值，会触发 TypeError',
        sub.lineno, '__init__ 应隐式返回 None，移除 return 值')
        for sub in _b10_init_value_returns(init)]
def detect_b10_return_value_in_init(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues: list[DiagnoseIssue] = []
    for cls in tree_nodes(tree):
        if not isinstance(cls, ast.ClassDef):
            continue
        for init in _class_owned_inits(cls):
            issues.extend(_b10_init_issues(init))
    return _finish('B10', '__init__ 返回值', issues, filepath)
def detect_b47_method_missing_self(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    for _cls, fn in _iter_class_methods(tree):
        if fn.name.startswith('__') and fn.name.endswith('__'):
            continue
        if _has_positional_slot(fn):
            continue
        if (fn.decorator_list
                and (not _is_classmethod(fn) or is_static_method(fn))):
            continue
        issues.append(_issue(
            'B47', DiagnoseSeverity.ERROR,
            f"方法 '{fn.name}' 零位置参数且无装饰器：实例调用必 "
            f"TypeError（self 被隐式传入无处接收）——漏写 self 或漏写 @staticmethod",
            fn.lineno, '补第一参数 self（实例方法）或加 @staticmethod 装饰器'))
    return _finish('B47', '方法漏 self', issues, filepath)
_B48_PROP_SIG: dict[str, tuple[int, str]] = {
    'property': (1, 'fget'), 'cached_property': (1, 'fget'),
    'getter': (1, 'fget'),
    'setter': (2, 'fset'), 'deleter': (1, 'fdel'),
}
def _b48_decorator_kind(dec: ast.expr) -> str | None:
    if isinstance(dec, ast.Name) and dec.id in ('property', 'cached_property'):
        return dec.id
    if isinstance(dec, ast.Attribute) and dec.attr in (
            'property', 'setter', 'getter', 'deleter', 'cached_property'):
        return dec.attr
    return None
def _b48_positional_count(fn: ast.FunctionDef | ast.AsyncFunctionDef) -> int:
    return len(fn.args.args) + len(fn.args.posonlyargs)
def _b48_required_positional_count(
        fn: ast.FunctionDef | ast.AsyncFunctionDef) -> int:
    return max(_b48_positional_count(fn) - len(fn.args.defaults), 0)
def _b48_required_kwonly_names(
        fn: ast.FunctionDef | ast.AsyncFunctionDef) -> list[str]:
    return [arg.arg for arg, default in zip(fn.args.kwonlyargs,
                                            fn.args.kw_defaults,
                                            strict=True)
            if default is None]
def _b48_absorbs_extra_positional(
        fn: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    return bool(fn.args.vararg)
def _b48_positional_error(fn: ast.FunctionDef | ast.AsyncFunctionDef,
                          expect: int) -> bool:
    if _b48_required_positional_count(fn) > expect:
        return True
    return (_b48_positional_count(fn) < expect
            and not _b48_absorbs_extra_positional(fn))
def _b48_signature_issues(fn: ast.FunctionDef | ast.AsyncFunctionDef) -> list[DiagnoseIssue]:
    required_kwonly = _b48_required_kwonly_names(fn)
    issues: list[DiagnoseIssue] = []
    for dec in fn.decorator_list:
        kind = _b48_decorator_kind(dec)
        if kind is None:
            continue
        expect, role = _B48_PROP_SIG[kind]
        if _b48_positional_error(fn, expect):
            issues.append(_issue(
                'B48', DiagnoseSeverity.ERROR,
                f"property {role} 签名应接受 {expect} 个位置参数"
                f"（{'self' if expect == 1 else 'self, value'}），"
                f"'{fn.name}' 实际 {_b48_positional_count(fn)} 个"
                f"（必填 {_b48_required_positional_count(fn)} 个）——存取时即 TypeError",
                fn.lineno, 'property 不接受业务参数：改为普通方法，或修正参数数'))
        if required_kwonly:
            names = ', '.join(repr(name) for name in required_kwonly)
            issues.append(_issue(
                'B48', DiagnoseSeverity.ERROR,
                f"property {role} 含必填仅关键字参数 {names}："
                f"属性存取不会传入该参数，'{fn.name}' 读取/赋值时即 TypeError",
                fn.lineno, 'property 不接受业务参数：移除必填仅关键字参数或给默认值'))
    return issues
def detect_b48_property_bad_signature(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    for _cls, fn in _iter_class_methods(tree):
        issues.extend(_b48_signature_issues(fn))
    return _finish('B48', 'property 签名错', issues, filepath)
def _b49_has_no_binding_arg(fn: ast.AST) -> bool:
    return not (fn.args.args or fn.args.posonlyargs)
def _b49_is_bare_super_call(node: ast.AST) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'super' and not node.args
            and not node.keywords)
def _b49_call_owner(node: ast.AST, parents: dict) -> ast.AST | None:
    cur = parents.get(node)
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            return cur
        if isinstance(cur, ast.ClassDef):
            return None
        cur = parents.get(cur)
    return None
def _b49_issues_for(fn: ast.FunctionDef | ast.AsyncFunctionDef,
                    parents: dict) -> list[DiagnoseIssue]:
    issues: list[DiagnoseIssue] = []
    for sub in iter_skip_nested_class(fn):
        if not _b49_is_bare_super_call(sub):
            continue
        owner = _b49_call_owner(sub, parents)
        if owner is None or not _b49_has_no_binding_arg(owner):
            continue
        issues.append(_issue(
            'B49', DiagnoseSeverity.ERROR,
            f"staticmethod '{fn.name}' 内零参 super()：无隐式第一参数可绑定，"
            f"一执行即 RuntimeError: super(): no arguments",
            sub.lineno,
            '改显式形态 super(类名, 实例)，或改实例方法/classmethod'))
    return issues
def detect_b49_super_in_staticmethod(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    parents = parent_map(tree)
    for _cls, fn in _iter_class_methods(tree):
        if not is_static_method(fn):
            continue
        issues.extend(_b49_issues_for(fn, parents))
    return _finish('B49', 'staticmethod 内 super', issues, filepath)
def _b53_init_is_inert(init_fn: ast.FunctionDef) -> bool:
    for stmt in _docstring_free_stmts(init_fn.body):
        if is_placeholder_stmt(stmt):
            continue
        if _b53_is_notimplemented_raise(stmt):
            continue
        if (isinstance(stmt, ast.Return)
                and (stmt.value is None
                     or (isinstance(stmt.value, ast.Constant)
                         and stmt.value.value is None))):
            continue
        return False
    return True
def _local_base_has_meaningful_init(base: ast.expr, owner: ast.ClassDef,
                                    parents: dict, scopes: dict,
                                    _seen: frozenset = frozenset()) -> bool:
    base_name = _resolvable_base_name(base)
    if base_name is None:
        return True
    local = _resolve_base(base_name, owner, parents, scopes)
    if local is None:
        return not _b53_base_is_exempt(base_name)
    if local in _seen:
        return False
    init_fn = _b53_find_init(local)
    if init_fn is not None:
        return not _b53_init_is_inert(init_fn)
    # dataclass 的 __init__ 由解释器生成，AST 中没有显式节点；
    # 带字段的 dataclass 基类同样会初始化实例状态，子类重写 __init__
    # 而不调用 super().__init__ 时字段静默缺失，必须视为“有实质初始化”。
    if _is_dataclass(local) and _dataclass_has_instance_field(local):
        return True
    return any(
        _local_base_has_meaningful_init(candidate, local, parents, scopes,
                                        _seen | {local})
        for candidate in local.bases
    )
def _b53_find_init(cls: ast.ClassDef) -> ast.FunctionDef | None:
    return next((fn for fn in _method_defs(cls)
                 if isinstance(fn, ast.FunctionDef) and fn.name == '__init__'),
                None)
def _b53_base_is_exempt(base_name: str) -> bool:
    return (base_name in _B53_STATELESS_BASE_NAMES
            or _is_composition_type_name(base_name))
def _b53_init_exempt(
        init_fn: ast.FunctionDef, base_names: set, parents: dict,
        module_bindings: set[str]) -> bool:
    if any(_b53_is_notimplemented_raise(stmt) for stmt in init_fn.body):
        return True
    for stmt in init_fn.body:
        if any(_b53_is_parent_init_call(sub, base_names)
               for sub in _iter_exec_nodes(
                   stmt, include_root=True, parents=parents,
                   module_bindings=module_bindings)):
            return True
    return False
def _b53_is_parent_init_call(node: ast.AST, base_names: set) -> bool:
    if not isinstance(node, ast.Call):
        return False
    f_ = node.func
    if not (isinstance(f_, ast.Attribute) and f_.attr == '__init__'):
        return False
    receiver = f_.value
    if (isinstance(receiver, ast.Call) and isinstance(receiver.func, ast.Name)
            and receiver.func.id == 'super'):
        return True
    return _base_name(receiver) in base_names
def _b53_is_notimplemented_raise(node: ast.AST) -> bool:
    if not isinstance(node, ast.Raise):
        return False
    exc = node.exc.func if isinstance(node.exc, ast.Call) else node.exc
    return ((isinstance(exc, ast.Name) and exc.id == 'NotImplementedError')
            or (isinstance(exc, ast.Attribute)
                and exc.attr == 'NotImplementedError'))
def _b53_effective_base_names(cls: ast.ClassDef, parents: dict,
                              scopes: dict) -> set[str]:
    base_names: set[str] = set()
    for base in cls.bases:
        base_name = _base_name(base)
        if base_name is None:
            continue
        if _local_base_has_meaningful_init(base, cls, parents, scopes):
            base_names.add(base_name)
    return base_names
def _b53_missing_super_issue(
        cls: ast.ClassDef, parents: dict, scopes: dict,
        module_bindings: set[str]) -> DiagnoseIssue | None:
    base_names = _b53_effective_base_names(cls, parents, scopes)
    if not base_names:
        return None
    init_fn = _b53_find_init(cls)
    if (init_fn is None or _b53_init_exempt(
            init_fn, base_names, parents, module_bindings)):
        return None
    return _issue(
        'B53', DiagnoseSeverity.WARN,
        f"子类 '{cls.name}' 重写 __init__ 未调用父类初始化"
        f"（{'/'.join(sorted(base_names))}）——父类属性/状态可能静默缺失，"
        f"后续访问即 AttributeError",
        init_fn.lineno,
        '首行补 super().__init__(...)（有意完全接管父类初始化时忽略本提示）')
def detect_b53_missing_super_init(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    parents = parent_map(tree)
    scopes = _class_scope_index(tree, parents)
    module_bindings = module_scope_binds(tree.body)
    for cls in tree_nodes(tree):
        if not isinstance(cls, ast.ClassDef):
            continue
        issue = _b53_missing_super_issue(
            cls, parents, scopes, module_bindings)
        if issue is not None:
            issues.append(issue)
    return _finish('B53', '漏调父类 __init__', issues, filepath)
class _ImportShadowContext(NamedTuple):
    parents: dict
    memo: dict
    module_rebound: frozenset[str]
    local_imports: frozenset[str]
def _local_import_names(scope: ast.AST, parents: dict) -> frozenset[str]:
    names: set[str] = set()
    cur = scope
    while cur is not None and not isinstance(cur, ast.Module):
        if (isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef))
                or (isinstance(cur, ast.ClassDef) and cur is scope)):
            names.update(_collect_scope_import_aliases(cur))
        cur = parents.get(cur)
    return frozenset(names)
def _module_rebound_import_names(
        tree: ast.Module, parents: dict, module_aliases: dict,
) -> frozenset[str]:
    own_nodes = list(iter_own_nodes(tree))
    rebound: set[str] = set()
    for name in module_aliases:
        imports = [
            node for node in own_nodes
            if isinstance(node, (ast.Import, ast.ImportFrom))
            and name in import_stmt_binds(node)
        ]
        if not imports:
            rebound.add(name)
            continue
        last_import = max(
            imports, key=lambda node: (node.lineno, node.col_offset))
        if _class_binding_precedes(
                tree, name, tree, parents, include_imports=False,
                after=last_import, before_reference=False):
            rebound.add(name)
    return frozenset(rebound)
def _call_import_name_shadowed(
        node: ast.AST, name: str,
        shadow_ctx: _ImportShadowContext | None) -> bool:
    if shadow_ctx is None:
        return False
    if _import_name_shadowed(
            node, name, shadow_ctx.parents, shadow_ctx.memo):
        return True
    return (name in shadow_ctx.module_rebound
            and name not in shadow_ctx.local_imports)
def _b54_is_time_sleep_call(node: ast.AST, time_mods: set[str],
                             sleep_names: set[str],
                             shadow_ctx: _ImportShadowContext | None
                             ) -> bool:
    if not isinstance(node, ast.Call):
        return False
    f_ = node.func
    if isinstance(f_, ast.Attribute) and f_.attr == 'sleep':
        if not (isinstance(f_.value, ast.Name)
                and f_.value.id in time_mods):
            return False
        _recv = f_.value.id
    elif isinstance(f_, ast.Name):
        if f_.id not in sleep_names:
            return False
        _recv = f_.id
    else:
        return False
    return not _call_import_name_shadowed(node, _recv, shadow_ctx)
def _b54_scan_blocking_sleep(node: ast.AST, time_mods: set[str],
                             sleep_names: set[str], seen_calls: set[int],
                             issues: list[DiagnoseIssue],
                             shadow_ctx: _ImportShadowContext | None,
                             module_bindings: set[str]) -> None:
    parents = shadow_ctx[0] if shadow_ctx is not None else {}
    for current in _iter_exec_nodes(
            node, include_root=False, parents=parents,
            module_bindings=module_bindings):
        if not (_b54_is_time_sleep_call(
                    current, time_mods, sleep_names, shadow_ctx)
                and id(current) not in seen_calls):
            continue
        seen_calls.add(id(current))
        issues.append(_issue(
            'B54', DiagnoseSeverity.WARN,
            'async 函数内 time.sleep 同步阻塞——冻结事件循环上全部协程，'
            '并发静默退化为串行',
            current.lineno,
            '改用 await asyncio.sleep(...)（同步库调用请 loop.run_in_executor）'))
def detect_b54_blocking_sleep_in_async(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    parents = parent_map(tree)
    module_aliases = _collect_scope_import_aliases(tree)
    module_bindings = module_scope_binds(tree.body)
    seen_calls: set[int] = set()
    memo: dict = {}
    module_rebound = _module_rebound_import_names(
        tree, parents, module_aliases)
    for node in tree_nodes(tree):
        if not isinstance(node, ast.AsyncFunctionDef):
            continue
        aliases = _enclosing_import_aliases(node, parents, module_aliases)
        time_mods, sleep_names = _ref_sets_from_aliases(aliases, 'time', 'sleep')
        if not time_mods and not sleep_names:
            continue
        shadow_ctx = _ImportShadowContext(
            parents, memo, module_rebound, _local_import_names(node, parents))
        for stmt in node.body:
            _b54_scan_blocking_sleep(stmt, time_mods, sleep_names,
                                     seen_calls, issues, shadow_ctx,
                                     module_bindings)
    return _finish('B54', 'async 内 time.sleep', issues, filepath)
def _b55_dropped_call(node: ast.AST, aio_mods: set[str],
                       ct_names: set[str],
                       shadow_ctx: _ImportShadowContext | None
                       ) -> ast.Call | None:
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)):
        return None
    call = node.value
    f_ = call.func
    if isinstance(f_, ast.Attribute):
        if not (f_.attr == 'create_task' and isinstance(f_.value, ast.Name)
                and f_.value.id in aio_mods):
            return None
        _recv = f_.value.id
    elif isinstance(f_, ast.Name) and f_.id in ct_names:
        _recv = f_.id
    else:
        return None
    if _call_import_name_shadowed(call, _recv, shadow_ctx):
        return None
    return call
def detect_b55_create_task_dropped(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    parents = parent_map(tree)
    module_aliases = _collect_scope_import_aliases(tree)
    memo: dict = {}
    module_rebound = _module_rebound_import_names(
        tree, parents, module_aliases)
    for scope in _iter_import_scopes(tree):
        aliases = _enclosing_import_aliases(scope, parents, module_aliases)
        aio_mods, ct_names = _ref_sets_from_aliases(
            aliases, 'asyncio', 'create_task')
        if not aio_mods and not ct_names:
            continue
        shadow_ctx = _ImportShadowContext(
            parents, memo, module_rebound,
            _local_import_names(scope, parents))
        for node in iter_own_nodes(scope):
            call = _b55_dropped_call(node, aio_mods, ct_names, shadow_ctx)
            if call is None:
                continue
            issues.append(_issue(
                'B55', DiagnoseSeverity.WARN,
                'asyncio.create_task() 结果丢弃：事件循环仅持弱引用，'
                '任务可能在完成前被 GC 静默取消',
                call.lineno,
                '保存句柄（task = create_task(...) 入集合，回调中 discard），或 await 之'))
    return _finish('B55', 'create_task 丢弃', issues, filepath)
def _b59_init_issue(fn: ast.FunctionDef | ast.AsyncFunctionDef) -> DiagnoseIssue | None:
    if isinstance(fn, ast.AsyncFunctionDef):
        return _issue(
            'B59', DiagnoseSeverity.ERROR,
            "async def __init__：类实例化时 __init__() 返回协程对象，"
            "必 TypeError: __init__() should return None",
            fn.lineno,
            '__init__ 只能是普通同步函数；异步初始化放工厂类方法（async def create()）')
    for node in iter_own_nodes(fn):
        if isinstance(node, (ast.Yield, ast.YieldFrom)):
            return _issue(
                'B59', DiagnoseSeverity.ERROR,
                "__init__ 含 yield/yield from：变为生成器函数，类实例化时"
                "返回生成器对象，必 TypeError: __init__() should return None",
                node.lineno,
                '__init__ 内移除 yield；惰性产出改由独立生成器方法承载')
    return None
def detect_b59_dunder_yield_in_init(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    for _cls, fn in _iter_class_methods(tree):
        if fn.name != '__init__':
            continue
        issue = _b59_init_issue(fn)
        if issue is not None:
            issues.append(issue)
    return _finish('B59', '__init__ 生成器化', issues, filepath)
_DUNDER_RETURN_CONTRACT: dict[str, tuple[str, tuple[type, ...]]] = {
    '__bool__': ('bool', (bool,)),
    '__len__': ('int', (int, bool)),
    '__int__': ('int', (int, bool)),
    '__index__': ('int', (int, bool)),
    '__hash__': ('int', (int, bool)),
    '__str__': ('str', (str,)),
    '__repr__': ('str', (str,)),
    '__bytes__': ('bytes', (bytes,)),
    '__float__': ('float', (float,)),
    '__complex__': ('complex', (complex,)),
}
_B60_NOT_LITERAL = object()
def _b60_literal_value(val: ast.expr):
    if (isinstance(val, ast.UnaryOp)
            and isinstance(val.op, (ast.USub, ast.UAdd))
            and isinstance(val.operand, ast.Constant)
            and isinstance(val.operand.value, (int, float, complex))):
        return -val.operand.value if isinstance(val.op, ast.USub) else val.operand.value
    if isinstance(val, ast.Constant):
        return val.value
    return _B60_NOT_LITERAL
def _b60_return_issue(fn_name: str, node: ast.Return, type_name: str,
                      accepted: tuple[type, ...]) -> DiagnoseIssue | None:
    val = node.value
    if val is None:
        return _issue(
            'B60', DiagnoseSeverity.ERROR,
            f"{fn_name} 裸 return（返回 None）：协议要求返回 {type_name}，"
            f"消费点必 TypeError",
            node.lineno, f'{fn_name} 必须返回 {type_name} 类型值')
    v = _b60_literal_value(val)
    if v is _B60_NOT_LITERAL:
        return None
    if fn_name == '__len__' and isinstance(v, int):
        if v < 0:
            return _issue(
                'B60', DiagnoseSeverity.ERROR,
                f"__len__ 返回负数字面量 {v}：消费点必 ValueError: "
                f"__len__() should return >= 0",
                node.lineno, '__len__ 必须返回非负 int')
        if v > sys.maxsize:
            return _issue(
                'B60', DiagnoseSeverity.ERROR,
                f"__len__ 返回字面值 {v} 超过 sys.maxsize：消费点必 "
                f"OverflowError: cannot fit 'int' into an index-sized integer",
                node.lineno, '__len__ 必须返回 0 <= value <= sys.maxsize 的 int')
    if isinstance(v, accepted):
        return None
    return _issue(
        'B60', DiagnoseSeverity.ERROR,
        f"{fn_name} 返回 {type(v).__name__} 字面量 {v!r}：协议要求 {type_name}，"
        f"消费点必 TypeError（__bool__ should return bool 同族）",
        node.lineno, f'{fn_name} 必须返回 {type_name} 类型值')
def _b60_method_issues(fn: ast.FunctionDef | ast.AsyncFunctionDef) -> list[DiagnoseIssue]:
    contract = _DUNDER_RETURN_CONTRACT.get(fn.name)
    if contract is None:
        return []
    type_name, accepted = contract
    if (any(_base_name(dec) == 'abstractmethod'
            for dec in fn.decorator_list)
            and _b53_init_is_inert(fn)):
        return []
    if isinstance(fn, ast.AsyncFunctionDef):
        return [_issue(
            'B60', DiagnoseSeverity.ERROR,
            f"async {fn.name} 的调用结果为 coroutine，而非协议要求的 "
            f"{type_name}：消费点必 TypeError",
            fn.lineno,
            f"移除 async，改为同步 {fn.name} 并返回 {type_name} 类型值")]
    issues = []
    for node in iter_own_nodes(fn):
        if not isinstance(node, ast.Return):
            continue
        issue = _b60_return_issue(fn.name, node, type_name, accepted)
        if issue is not None:
            issues.append(issue)
    has_yield = any(isinstance(node, (ast.Yield, ast.YieldFrom))
                    for node in iter_own_nodes(fn))
    if has_yield:
        issues.append(_issue(
            'B60', DiagnoseSeverity.ERROR,
            f'{fn.name} 含 yield：变为生成器函数，调用结果不是 {type_name}，'
            f'消费点必 TypeError',
            fn.lineno, f'{fn.name} 内移除 yield，改为直接返回 {type_name} 类型值'))
    elif _block_may_fall_through(_docstring_free_stmts(fn.body)):
        issues.append(_issue(
            'B60', DiagnoseSeverity.ERROR,
            f'{fn.name} 存在隐式返回 None 的执行路径：协议要求返回 '
            f'{type_name}，消费点必 TypeError',
            fn.lineno, f'{fn.name} 的所有执行路径都必须返回 {type_name} 类型值'))
    return issues
def detect_b60_dunder_return_type_violation(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    for _cls, fn in _iter_class_methods(tree):
        issues.extend(_b60_method_issues(fn))
    return _finish('B60', 'dunder 返回类型违反', issues, filepath)
class MissingDataclassDecoratorDetector:
    DETECTOR_ID = "D54"
    PATTERN_NAME = "@dataclass缺失"
    _AUTO_FIELD_BASES = _AUTO_FIELD_BASE_NAMES
    def _inherits_auto_field_base(self, class_node: ast.ClassDef) -> bool:
        for base in class_node.bases:
            if isinstance(base, ast.Subscript):
                base = base.value
            if isinstance(base, ast.Name) and base.id in self._AUTO_FIELD_BASES:
                return True
            if isinstance(base, ast.Attribute) and base.attr in self._AUTO_FIELD_BASES:
                return True
        return False
    def _has_init(self, class_node: ast.ClassDef) -> bool:
        return any(item.name == '__init__' for item in _method_defs(class_node))
    @staticmethod
    def _collect_dataclass_names(tree: ast.AST) -> set:
        names = {'dataclass'}
        for node in walk_nodes(tree):
            if isinstance(node, ast.ImportFrom) and node.module == 'dataclasses':
                for alias in node.names:
                    if alias.name == 'dataclass' and alias.asname:
                        names.add(alias.asname)
        return names
    def _is_dataclass_decorated(self, class_node: ast.ClassDef,
                                dataclass_names: set | None = None) -> bool:
        names = dataclass_names if dataclass_names is not None else {'dataclass'}
        for dec in class_node.decorator_list:
            target = dec.func if isinstance(dec, ast.Call) else dec
            if isinstance(target, ast.Name) and target.id in names:
                return True
            if isinstance(target, ast.Attribute) and target.attr == 'dataclass':
                return True
        return False
    def _annotated_fields(self, class_node: ast.ClassDef) -> list:
        fields = []
        for item in same_scope_bfs_nodes(class_node):
            if not (isinstance(item, ast.AnnAssign)
                    and isinstance(item.target, ast.Name)
                    and item.annotation is not None
                    and item.value is None):
                continue
            if _mm01_annotation_is_classvar(item.annotation):
                continue
            fields.append(item.target.id)
        return fields
    def detect_file(self, filepath: str) -> list[PatternFinding]:
        findings: list[PatternFinding] = []
        _source, tree = parse_py_file(filepath)
        if tree is None:
            logger.debug("[D54] 解析失败跳过: %s", filepath)
            return findings
        dataclass_names = self._collect_dataclass_names(tree)
        for node in walk_nodes(tree):
            if not isinstance(node, ast.ClassDef):
                continue
            if self._is_dataclass_decorated(node, dataclass_names):
                continue
            if self._has_init(node):
                continue
            if self._inherits_auto_field_base(node):
                continue
            fields = self._annotated_fields(node)
            if not fields:
                continue
            findings.append(PatternFinding(
                detector_id=self.DETECTOR_ID,
                pattern_name=self.PATTERN_NAME,
                severity="WARN",
                filepath=filepath,
                line=node.lineno,
                snippet=f"class {node.name}: ({len(fields)} 个注解字段)",
                message=f"类 {node.name} 有 {len(fields)} 个类型注解字段"
                        f"但未加 @dataclass,实例化后字段不可访问",
                suggestion=suggest('类缺少必要的初始化机制。该问题属于代码质量类别。',
                            f"为 {node.name} 添加 @dataclass 装饰器,"
                            f"或显式定义 __init__ 初始化字段",
                            reference='PEP 557 / pylint / SonarQube')
            ))
        logger.debug("[D54] %s: %d 项缺失 @dataclass 的注解字段类",
                      filepath, len(findings))
        return findings
def _is_result_return(node: ast.AST) -> bool:
    return (isinstance(node, ast.Return)
            and node.value is not None
            and not (isinstance(node.value, ast.Constant)
                     and node.value.value is None))
class FixMethodMissingReturnDetector:
    DETECTOR_ID = "D43"
    PATTERN_NAME = "修复器fix()缺失return"
    FIX_METHOD_NAMES = frozenset({
        'fix', 'apply_fix', 'execute_fix', 'do_fix',
        '_fix', '_apply_fix',
    })
    FIXER_CLASS_PATTERN = ('fix', 'repair')
    def __init__(self, method_names=None, class_name_patterns=None,
                 result_type: str = 'FixResult') -> None:
        if isinstance(method_names, str):
            method_names = (method_names,)
        if isinstance(class_name_patterns, str):
            class_name_patterns = (class_name_patterns,)
        self.method_names = frozenset(
            self.FIX_METHOD_NAMES if method_names is None else method_names)
        self.class_name_patterns = tuple(
            self.FIXER_CLASS_PATTERN if class_name_patterns is None
            else class_name_patterns)
        if (not all(isinstance(name, str) and name
                    for name in self.method_names)
                or not all(isinstance(name, str) and name
                           for name in self.class_name_patterns)
                or not isinstance(result_type, str) or not result_type):
            raise ValueError('修复器方法名、类名模式与结果类型须为非空字符串')
        self.result_type = result_type
    def _is_fixer_class(self, class_node: ast.ClassDef) -> bool:
        return (self._fixer_class_name_matches(class_node)
                or self._has_fix_method(class_node))
    def _fixer_class_name_matches(self, class_node: ast.ClassDef) -> bool:
        if self._matches_fixer_pattern(class_node.name):
            return True
        return any(self._matches_fixer_pattern(name)
                   for name in map(_base_name, class_node.bases) if name)
    def _matches_fixer_pattern(self, name: str) -> bool:
        lowered = name.lower()
        return any(p in lowered for p in self.class_name_patterns)
    def _has_fix_method(self, class_node: ast.ClassDef) -> bool:
        return any(item.name in self.method_names
                   for item in _method_defs(class_node))
    def _function_has_missing_return(
            self, func_node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
        returns = [
            sub for sub in iter_own_scope(func_node, skip_lambda=True)
            if isinstance(sub, ast.Return)
        ]
        if any(not _is_result_return(node) for node in returns):
            return True
        return _block_may_fall_through(func_node.body)
    def detect_file(self, filepath: str) -> list[PatternFinding]:
        findings: list[PatternFinding] = []
        _source, tree = parse_py_file(filepath)
        if tree is None:
            return findings
        for class_node, method_node in self._iter_fix_methods(tree):
            if self._function_has_missing_return(method_node):
                findings.append(
                    self._make_finding(class_node, method_node, filepath))
        return findings
    def _iter_fix_methods(self, tree: ast.AST):
        for node in walk_nodes(tree):
            if not isinstance(node, ast.ClassDef) or not self._is_fixer_class(node):
                continue
            for item in _method_defs(node):
                if item.name in self.method_names:
                    yield node, item
    def _make_finding(self, class_node: ast.ClassDef,
                      method_node: ast.FunctionDef | ast.AsyncFunctionDef,
                      filepath: str) -> PatternFinding:
        return PatternFinding(
            detector_id=self.DETECTOR_ID,
            pattern_name=self.PATTERN_NAME,
            severity="ERROR",
            filepath=filepath,
            line=method_node.lineno,
            snippet=f"def {method_node.name}(self, ...):",
            message=f"修复器 {class_node.name}.{method_node.name}() 存在缺失 return 的代码路径",
            suggestion=suggest(
                '代码实现中存在代码质量方面的问题, 需要规范化处理。',
                f'确保所有代码路径都返回 {self.result_type} 或修复结果对象')
        )
def _mm01_extract_assignment(item: Any) -> tuple[list, Any] | None:
    if (isinstance(item, ast.AnnAssign)
            and _mm01_annotation_is_classvar(item.annotation)):
        return None
    return _container_assign_parts(item)
def _mm01_empty_literal_shape(value: Any) -> str | None:
    if isinstance(value, ast.List) and not value.elts:
        return "[]"
    if isinstance(value, ast.Dict) and not value.keys:
        return "{}"
    return None
def _mm01_empty_constructor_shape(value: Any) -> str | None:
    ctor = empty_container_ctor_name(value)
    return f"{ctor}()" if ctor else None
def _mm01_empty_container_shape(value: Any) -> str | None:
    return (_mm01_empty_literal_shape(value)
            or _mm01_empty_constructor_shape(value))
def _mm01_finding(target: ast.Name, shape: str, item: ast.stmt,
                  source_lines: Any, filepath: Any) -> dict:
    return {
        "rule_id": "MM-01", "severity": "P1", "dimension": "memory_safety",
        "file": filepath, "line": item.lineno,
        "title": f"类属性 '{target.id} = {shape}' 被所有实例共享",
        "description": (
            "类体中直接赋值空列表/字典/集合,该对象将被类的所有实例共享."
            "对一个实例的修改会影响其他实例,且可能造成内存中数据无限累积."
        ),
        "code_snippet": extract_code_lines(source_lines, item.lineno),
        "suggestion": f'根因: 代码实现中存在可变默认参数方面的问题, 需要规范化处理。\n修复策略: 在 __init__ 中初始化: self.{target.id} = {shape}\n参考标准: PEP 8 / pylint W0102',
        "rule_ref": "class-attr-mutable-default",
    }
def _mm01_class_issues(node: ast.ClassDef, source_lines: Any,
                       filepath: Any) -> list[dict]:
    issues: list[dict] = []
    for item in walk_stmts(node.body):
        extracted = _mm01_extract_assignment(item)
        if extracted is None:
            continue
        targets, value = extracted
        for target, bound_value in _assign_value_pairs(targets, value):
            if not isinstance(target, ast.Name):
                continue
            shape = _mm01_empty_container_shape(bound_value)
            if shape is None:
                continue
            issues.append(_mm01_finding(
                target, shape, item, source_lines, filepath))
    return issues
def check_MM01(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues: list[dict] = []
    if tree is None:
        return issues
    for node in walk_nodes(tree):
        if isinstance(node, ast.ClassDef):
            issues.extend(_mm01_class_issues(node, source_lines, filepath))
    return issues
def check_MM03(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    for node in walk_nodes(tree):
        if isinstance(node, ast.ClassDef):
            for child in _method_defs(node):
                if child.name == '__del__':
                    issues.append({
                        "rule_id": "MM-03", "severity": "P2", "dimension": "memory_safety",
                        "file": filepath, "line": child.lineno,
                        "title": f"类 '{node.name}' 定义了 __del__ 方法,参与循环引用时回收时机不可控",
                        "description": (
                            "定义了 __del__ 的对象参与循环引用时,回收降级为等待 GC 代际扫描."
                            "__del__ 执行时机不可控,解释器关闭阶段模块全局可能已清理."
                        ),
                        "code_snippet": extract_code_lines(source_lines, child.lineno),
                        "suggestion": '根因: 代码使用了不规范或有风险的实现方式。该问题属于内存管理类别。\n修复策略: 1. 避免在参与循环引用的类中定义 __del__\n 2. 使用 weakref.ref 打破循环引用\n 3. 使用 context manager (__enter__/__exit__) 替代 __del__\n参考标准: PEP 442 / Python gc 模块文档',
                        "rule_ref": "circular-ref-del",
                    })
    return issues
GATE_DETECTORS: dict[str, Any] = {
    "B10": detect_b10_return_value_in_init,
    "B41": detect_b41_repr_str_self_recursion,
    "B47": detect_b47_method_missing_self,
    "B48": detect_b48_property_bad_signature,
    "B49": detect_b49_super_in_staticmethod,
    "B53": detect_b53_missing_super_init,
    "B54": detect_b54_blocking_sleep_in_async,
    "B55": detect_b55_create_task_dropped,
    "B59": detect_b59_dunder_yield_in_init,
    "B60": detect_b60_dunder_return_type_violation,
}
def wiring_declarations() -> dict:
    return {"catalogs": {
        "rule_bindings": {
            'MM01': check_MM01, 'MM03': check_MM03,
        },
        "diag4_direct": {'MM-03': check_MM03},
        "audit_detector_classes": {
            'D43': FixMethodMissingReturnDetector,
            'D54': MissingDataclassDecoratorDetector,
        },
    }}
__all__ = [
    "GATE_DETECTORS",
    "FixMethodMissingReturnDetector",
    "MissingDataclassDecoratorDetector",
    "check_MM01",
    "check_MM03",
    "detect_b10_return_value_in_init",
    "detect_b41_repr_str_self_recursion",
    "detect_b47_method_missing_self",
    "detect_b48_property_bad_signature",
    "detect_b49_super_in_staticmethod",
    "detect_b53_missing_super_init",
    "detect_b54_blocking_sleep_in_async",
    "detect_b55_create_task_dropped",
    "detect_b59_dunder_yield_in_init",
    "detect_b60_dunder_return_type_violation",
]
logger.info("diag_gate_class_protocol 已加载: %d 项导出", len(__all__))

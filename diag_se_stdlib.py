from __future__ import annotations

import ast
import logging
import re
import stat as _stat
from collections.abc import Iterator
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_nodes import (
    build_parent_map,
    collect_param_names,
    dotted_name,
    get_call_name,
    import_alias_bound_name,
    is_docstring_stmt,
    is_invariant_assert,
    iter_arg_nodes,
    iter_scope_nodes,
    iter_target_bindings,
    pattern_capture_name,
    resolve_module_member_call,
)
from jwsgj.diag_shared_ast_views import (
    collect_lexical_scope_table,
    collect_module_bindings,
    collect_module_bindings_detailed,
    iter_nodes,
    materialized_index,
    qualified_and_bare_call_targets,
    qualified_and_bare_call_targets_detailed,
)
from jwsgj.diag_shared_source_core import (
    build_ast_issue,
    iter_frame_nodes,
)
from jwsgj.diag_shared_source_scan import (
    get_code_snippet,
    has_nosec_marker,
)
from jwsgj.diag_types_defs import (
    DiagnoseFinding,
    finding_scan_exempt,
)
from jwsgj.diag_types_vocab import (
    YAML_SAFE_LOADERS,
)
from jwsgj.fix_guide_rule_identity import get_fix_guidance
from jwsgj.prevention_scope_facts import walk_nodes

_log = logging.getLogger(__name__)
__all__ = [
    "check_B108",
    "check_CV01b",
    "check_RG02",
    "check_RG04",
    "check_SE04",
    "check_SE07",
    "check_SE09",
    "check_SE11",
    "check_SE12",
    "check_SE13",
    "check_SE14",
    "check_SE15",
    "check_SE16",
    "check_SE17",
    "check_SE18",
    "check_SE19",
    "check_SE23",
    "check_SE24",
    "check_SE25",
    "check_SE26",
    "check_SE29",
    "check_SE30",
    "check_SE31",
    "check_SE33",
    "check_SE34",
    "wiring_declarations",
    "yaml_load_is_safe",
]
_log.info("diag_se_stdlib SE 标准库安全域检测器已加载: %d 项导出",
          len(__all__))
_SE_DIMENSION = "security"
def _se_finding(rule_id: str, severity: str, line: int, message: str,
                filepath: Any, title: str, rule_ref: str,
                source_lines: Any = None) -> dict:
    finding = _se_df(
        rule_id, severity, line, message, filepath, source_lines,
        title=title, rule_ref=rule_ref).to_dict()
    finding["rule_id"] = finding.pop("id")
    return finding
def _se_df(rule_id: str, severity: str, line: int, message: str,
           filepath: Any, source_lines: Any,
           suggestion: str | None = None,
           *, title: str, rule_ref: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id=rule_id,
        severity=severity,
        dimension=_SE_DIMENSION,
        file=filepath,
        line=line,
        title=title,
        message=message,
        suggestion=(suggestion if suggestion is not None
                    else get_fix_guidance(rule_id)),
        rule_ref=rule_ref,
        code_snippet=get_code_snippet(source_lines, line),
    )
def _call_arg_or_kw(node: ast.Call, kw_names: str | tuple[str, ...],
                    position: int = 0) -> ast.AST | None:
    if len(node.args) > position:
        return node.args[position]
    names = (kw_names,) if isinstance(kw_names, str) else tuple(kw_names)
    return next(
        (value for name, value in _iter_static_call_keywords(node)
         if name in names),
        None)
def _literal_truth_value(node: ast.AST | None) -> bool | None:
    if isinstance(node, ast.Constant):
        return bool(node.value)
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        if not node.elts:
            return False
        if any(not isinstance(item, ast.Starred) for item in node.elts):
            return True
        states = [_literal_truth_value(item.value) for item in node.elts]
        if any(state is True for state in states):
            return True
        return False if all(state is False for state in states) else None
    if isinstance(node, ast.Dict):
        if not node.keys:
            return False
        if any(key is not None for key in node.keys):
            return True
        states = [_literal_truth_value(value)
                  if isinstance(value, ast.Dict) else None
                  for value in node.values]
        if any(state is True for state in states):
            return True
        return False if all(state is False for state in states) else None
    return None
def _iter_static_call_keywords(node: ast.Call) -> Iterator[tuple[str, ast.AST]]:
    for kw in node.keywords:
        if kw.arg is not None:
            yield kw.arg, kw.value
        elif isinstance(kw.value, ast.Dict):
            for key, value in zip(
                    kw.value.keys, kw.value.values, strict=False):
                if (isinstance(key, ast.Constant)
                        and isinstance(key.value, str)):
                    yield key.value, value
def _call_member_name(node: ast.Call, func_name: str, origins: dict) -> str:
    if isinstance(node.func, ast.Name):
        return origins.get(func_name, func_name)
    return getattr(node.func, "attr", "")
def _named_attribute(func: ast.AST) -> tuple[str, str] | None:
    if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        return func.value.id, func.attr
    return None
def check_SE04(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    module_names: set[str] = set()
    member_origins: dict[str, str] = {}
    for module in ('pickle', 'cPickle'):
        aliases, origins = collect_module_bindings_detailed(
            tree, module, ('load', 'loads'))
        module_names.update(aliases)
        member_origins.update(origins)
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        if isinstance(node.func, ast.Name):
            attr = member_origins.get(node.func.id)
            if attr is None:
                continue
            display = node.func.id
        else:
            named_attr = _named_attribute(node.func)
            if named_attr is None:
                continue
            recv, attr = named_attr
            if recv not in module_names or attr not in ('load', 'loads'):
                continue
            display = f'{recv}.{attr}'
        issues.append(_se_finding(
            "SE-04", "P1", node.lineno,
            f"{display}() 反序列化不可信数据可能导致任意代码执行(RCE)",
            filepath,
            f"不安全反序列化: {display}()",
            "Bandit B301/B401", source_lines))
    return issues
def _se07_hit_bare_name(func: ast.expr, yaml_names: set,
                        from_yaml_origins: dict) -> str | None:
    if isinstance(func, ast.Name) and func.id in from_yaml_origins:
        return from_yaml_origins[func.id]
    named_attr = _named_attribute(func)
    if named_attr is None:
        return None
    recv, attr = named_attr
    if recv in yaml_names and attr in ('load', 'unsafe_load'):
        return attr
    return None
def _se07_message(bare: str, explicit_loader: bool = False) -> tuple[str, str]:
    if bare == 'unsafe_load':
        return ('yaml.unsafe_load() 为显式不安全反序列化API, 存在任意代码执行风险',
                'yaml.unsafe_load 显式不安全反序列化')
    if explicit_loader:
        return ('yaml.load()指定了不安全的Loader, 存在任意代码执行风险',
                'yaml.load 使用不安全 Loader')
    return ('yaml.load()未指定Loader参数, 存在任意代码执行风险',
            'yaml.load 未指定安全 Loader')
def check_SE07(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    yaml_names, from_yaml_origins = collect_module_bindings_detailed(
        tree, 'yaml', ('load', 'unsafe_load'))
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        bare = _se07_hit_bare_name(node.func, yaml_names, from_yaml_origins)
        if bare is None:
            continue
        _loader = _call_arg_or_kw(node, 'Loader', 1)
        if bare == 'load' and yaml_load_is_safe(node, tree):
            continue
        explicit_loader = (_loader is not None
                           and not (isinstance(_loader, ast.Constant)
                                    and _loader.value is None))
        _msg, _title = _se07_message(bare, explicit_loader)
        issues.append(_se_finding(
            "SE-07", "P0", node.lineno, _msg,
            filepath, _title, "Bandit B506 / CWE-502", source_lines))
    return issues
_SE14_XML_LIB_MEMBERS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ('xml.etree.ElementTree',
     ('parse', 'fromstring', 'iterparse', 'XMLParser')),
    ('xml.dom.minidom', ('parse', 'parseString')),
    ('xml.sax', ('parse', 'parseString')),
    ('lxml.etree', ('parse', 'fromstring')),
)
def _se14_collect_targets(tree: Any) -> set:
    targets: set[str] = set()
    for _lib, _members in _SE14_XML_LIB_MEMBERS:
        _lib_targets, _origins = qualified_and_bare_call_targets_detailed(
            tree, _lib, _members)
        targets |= _lib_targets
    return targets
def _is_defusedxml_module(name: str) -> bool:
    return name == 'defusedxml' or name.startswith('defusedxml.')
def _defused_bound_names(tree: Any, idx: list) -> set[str]:
    names: set[str] = set()
    for node in iter_nodes(tree, idx):
        if isinstance(node, ast.Import):
            for alias in node.names:
                if _is_defusedxml_module(alias.name):
                    name = import_alias_bound_name(alias, from_import=False)
                    if name is not None:
                        names.add(name)
        elif (isinstance(node, ast.ImportFrom) and node.level == 0
              and node.module and _is_defusedxml_module(node.module)):
            for alias in node.names:
                name = import_alias_bound_name(alias, from_import=True)
                if name is not None:
                    names.add(name)
    return names
def _xml_unsafe_bound_names(tree: Any) -> set[str]:
    bound: set[str] = set()
    for _lib, _members in (_SE14_XML_LIB_MEMBERS + _SE19_XML_LIB_MEMBERS):
        aliases, origins = collect_module_bindings_detailed(
            tree, _lib, _members)
        bound |= set(aliases) | set(origins)
    return bound
def _drop_defused_targets(tree: Any, idx: list, targets: set) -> set:
    defused = _defused_bound_names(tree, idx)
    if not defused:
        return targets
    unsafe = _xml_unsafe_bound_names(tree)
    return {t for t in targets
            if not (t.split('.', 1)[0] in defused
                    and t.split('.', 1)[0] not in unsafe)}
def check_SE14(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    _idx = materialized_index(index)
    targets = _drop_defused_targets(tree, _idx, _se14_collect_targets(tree))
    for node in iter_nodes(tree, _idx):
        if isinstance(node, ast.Call):
            func_name = get_call_name(node)
            if func_name in targets:
                issues.append(_se_finding(
                    "SE-14", "P1", node.lineno,
                    "XML解析未限制嵌套深度,存在C栈溢出风险(CVE-2026-4224)",
                    filepath, "XML 解析未限制嵌套深度",
                    "CVE-2026-4224 / CWE-776", source_lines))
    return issues
_SE15_VALIDATE_MEMBERS = frozenset({'b64decode'})
_SE15_IGNORE_SUGGESTION = (
    '根因: a85decode 没有 validate 参数，非目标字符被静默忽略，输入校验可被绕过。'
    '该问题属于输入校验类别。\n'
    '修复策略: 先按目标字符集白名单校验（或 ignorechars=b\'\' 显式禁用忽略），再调用解码\n'
    '参考标准: CWE-20 / base64 文档')
def _se15_flag_enabled(value: ast.AST | None) -> bool:
    return _literal_truth_value(value) is True
def _se15_has_validate_exemption(node: ast.Call, member: str) -> bool:
    if member in _SE15_VALIDATE_MEMBERS:
        if any(name == 'validate' and _se15_flag_enabled(value)
               for name, value in _iter_static_call_keywords(node)):
            return True
        return _se15_position_validate_true(node, member)
    if member == 'a85decode':
        return _se15_ignores_nothing(node)
    return False
def _se15_ignores_nothing(node: ast.Call) -> bool:
    return any(name == 'ignorechars'
               and isinstance(value, ast.Constant)
               and value.value == b''
               for name, value in _iter_static_call_keywords(node))
def _se15_position_validate_true(node: ast.Call, member: str) -> bool:
    if member != 'b64decode' or len(node.args) < 3:
        return False
    return _se15_flag_enabled(node.args[2])
def check_SE15(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    targets, b64_origins = qualified_and_bare_call_targets_detailed(
        tree, 'base64', ('b64decode', 'a85decode'))
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        func_name = get_call_name(node)
        if func_name not in targets:
            continue
        member = _call_member_name(node, func_name, b64_origins)
        if _se15_has_validate_exemption(node, member):
            continue
        issues.append(_se15_finding(
            node, func_name, member, filepath, source_lines))
    return issues
def _se15_finding(node: ast.Call, func_name: str, member: str,
                  filepath: Any, source_lines: Any) -> dict:
    if member in _SE15_VALIDATE_MEMBERS:
        return _se_finding(
            "SE-15", "P1", node.lineno,
            func_name + '() 未使用 validate=True, 非Base64字符可绕过输入校验',
            filepath, "base64 解码未启用 validate",
            "CVE-2026-3446 / CWE-20", source_lines)
    finding = _se_finding(
        "SE-15", "P1", node.lineno,
        func_name + '() 默认静默忽略非目标字符, 未显式收紧字符集',
        filepath, "base64 解码未收紧字符集",
        "CVE-2026-3446 / CWE-20", source_lines)
    finding["suggestion"] = _SE15_IGNORE_SUGGESTION
    return finding
_SE19_XML_LIB_MEMBERS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ('xml.etree.ElementTree', ('parse', 'fromstring', 'iterparse')),
    ('xml.dom.minidom', ('parse', 'parseString')),
    ('xml.sax', ('parse', 'parseString')),
    ('lxml.etree', ('parse', 'fromstring', 'iterparse')),
)
_SE19_POSITIONAL_PARSER_MODULES = frozenset({
    'xml.etree.ElementTree', 'xml.dom.minidom', 'lxml.etree',
})
_SE19_XXE_FEATURE_HINTS = (
    "external-general-entities", "external-parameter-entities",
    "external-ges", "external-pes",
)
_SE19_FORBID_ENTITIES_ARG_NAMES = ('value', 'flag', 'enabled', 'forbid')
_SE19_FEATURE_ARG_NAMES = ('name', 'feature')
_SE19_SWITCH_ARG_NAMES = ('state', 'value')
class _SE19ParserEvent(NamedTuple):
    line: int
    col: int
    seq: int
    scope: ast.AST | None
    name: str
    safe: bool
    node: ast.AST
def _se19_flag_value(node: ast.AST | None) -> bool | None:
    if isinstance(node, ast.Constant):  # noqa: SIM102
        if (node.value is None or not isinstance(
                node.value, (bool, int, float, str, bytes))):
            return None
    return _literal_truth_value(node)
def _se19_feature_name(feature: ast.AST | None) -> str:
    if isinstance(feature, ast.Constant) and isinstance(feature.value, str):
        raw = feature.value
    elif isinstance(feature, ast.Attribute):
        raw = feature.attr
    elif isinstance(feature, ast.Name):
        raw = feature.id
    else:
        return ''
    return raw.strip().lower().replace('_', '-')
def _se19_feature_kind(feature: ast.AST | None) -> str:
    name = _se19_feature_name(feature)
    for hint in _SE19_XXE_FEATURE_HINTS:
        if (name in (hint, f'feature-{hint}')
                or name.endswith(f'/{hint}')):
            return hint
    return ''
def _se19_feature_switch_state(call: ast.Call) -> bool | None:
    feature = _call_arg_or_kw(call, _SE19_FEATURE_ARG_NAMES, 0)
    if not _se19_feature_kind(feature):
        return None
    switch = _call_arg_or_kw(call, _SE19_SWITCH_ARG_NAMES, 1)
    return _se19_flag_value(switch) is False
def _se19_parser_kwargs_disabled(call: ast.Call) -> bool:
    for name, value in _iter_static_call_keywords(call):
        if name == 'resolve_entities':
            return _se19_flag_value(value) is False
    return False
def _se19_parser_constructor_state(
        call: ast.AST, parser_targets: set[str]) -> bool | None:
    if not isinstance(call, ast.Call):
        return None
    if dotted_name(call.func) not in parser_targets:
        return None
    return _se19_parser_kwargs_disabled(call)
def _se19_receiver_defense_state(call: ast.Call) -> tuple[str, bool] | None:
    if not isinstance(call.func, ast.Attribute) or not isinstance(
            call.func.value, ast.Name):
        return None
    name = call.func.value.id
    if call.func.attr == 'forbid_entities':
        flag = _call_arg_or_kw(call, _SE19_FORBID_ENTITIES_ARG_NAMES, 0)
        return name, _se19_flag_value(flag) is True
    if call.func.attr == 'setFeature':
        state = _se19_feature_switch_state(call)
        if state is not None:
            return name, state
    return None
def _iter_target_value_bindings(target: ast.AST, value: ast.AST | None):
    if isinstance(target, ast.Starred):
        yield from _iter_target_value_bindings(target.value, None)
        return
    if isinstance(target, (ast.Tuple, ast.List)):
        targets = list(target.elts)
        starred = [idx for idx, element in enumerate(targets)
                   if isinstance(element, ast.Starred)]
        values = (list(value.elts)
                  if isinstance(value, (ast.Tuple, ast.List)) else None)
        aligned = None
        if values is not None and not starred and len(targets) == len(values):
            aligned = values
        elif (values is not None and len(starred) == 1
              and len(values) >= len(targets) - 1):
            star = starred[0]
            tail_count = len(targets) - star - 1
            tail = values[len(values) - tail_count:] if tail_count else []
            aligned = [*values[:star], None, *tail]
        if aligned is not None:
            for element, bound_value in zip(targets, aligned, strict=False):
                yield from _iter_target_value_bindings(element, bound_value)
            return
        for name, _line, _col in iter_target_bindings(target):
            yield name, None
        return
    for name, _line, _col in iter_target_bindings(target):
        yield name, value
def _se19_parser_events(
        tree: ast.AST | None, parent_map: dict,
        parser_targets: set[str]) -> list[_SE19ParserEvent]:
    if tree is None:
        return []
    events: list[_SE19ParserEvent] = []
    lexical_table = collect_lexical_scope_table(tree)
    for seq, node in enumerate(walk_nodes(tree)):
        line = getattr(node, 'lineno', 0) or 0
        col = getattr(node, 'col_offset', 0) or 0
        scope = _enclosing_scope(node, parent_map)
        event_node = node
        bindings: list[tuple[str, bool]] = []
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            bindings = [(parameter.arg, False)
                        for parameter in iter_arg_nodes(node.args)]
            if not isinstance(node, ast.Lambda):
                definition_scope = _enclosing_scope(
                    parent_map.get(id(node)), parent_map)
                if definition_scope is not None:
                    events.append(_SE19ParserEvent(
                        line, col, seq,
                        _se_binding_scope(
                            definition_scope, node.name,
                            parent_map, lexical_table),
                        node.name, False, node))
        elif isinstance(node, ast.ClassDef):
            definition_scope = _enclosing_scope(
                parent_map.get(id(node)), parent_map)
            if definition_scope is not None:
                events.append(_SE19ParserEvent(
                    getattr(node, 'end_lineno', None) or line,
                    getattr(node, 'end_col_offset', None) or col,
                    seq,
                    _se_binding_scope(
                        definition_scope, node.name,
                        parent_map, lexical_table),
                    node.name, False, node))
        elif isinstance(node, (ast.With, ast.AsyncWith)):
            bindings = [(name, False) for item in node.items
                        if item.optional_vars is not None
                        for name, _line, _col in iter_target_bindings(
                            item.optional_vars)]
        elif isinstance(node, ast.Assign):
            bindings = [(name, _se19_parser_constructor_state(
                value, parser_targets) is True)
                        for target in node.targets
                        for name, value in _iter_target_value_bindings(
                            target, node.value)]
        elif isinstance(node, (ast.AnnAssign, ast.NamedExpr)):
            if node.value is not None:
                bindings = [(name, _se19_parser_constructor_state(
                    value, parser_targets) is True)
                            for name, value in _iter_target_value_bindings(
                                node.target, node.value)]
        elif isinstance(node, (ast.For, ast.AsyncFor, ast.comprehension)):
            bindings = [(name, False) for name, _line, _col
                        in iter_target_bindings(node.target)]
            if isinstance(node, ast.comprehension):
                event_node = node.target
                line = getattr(event_node, 'lineno', 0) or 0
                col = getattr(event_node, 'col_offset', 0) or 0
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            bindings = [
                (name, False) for alias in node.names
                if (name := import_alias_bound_name(
                    alias, from_import=isinstance(node, ast.ImportFrom)))
                is not None]
        else:
            capture = pattern_capture_name(node)
            if capture is not None:
                bindings = [(capture, False)]
        events.extend(_SE19ParserEvent(
            line, col, seq,
            _se_binding_scope(
                scope, name, parent_map, lexical_table,
                named_expr=isinstance(node, ast.NamedExpr)),
            name, safe, event_node)
                      for name, safe in bindings)
        if isinstance(node, ast.Call):
            defense = _se19_receiver_defense_state(node)
            if defense is not None:
                name, safe = defense
                events.append(_SE19ParserEvent(
                    line, col, seq,
                    _se_binding_scope(
                        scope, name, parent_map, lexical_table),
                    name, safe, node))
    return events
_TRY_FLOW_TYPES = (ast.Try, getattr(ast, 'TryStar', ast.Try))
_CONDITIONAL_FLOW_TYPES = (ast.If, *_TRY_FLOW_TYPES)
_CONDITIONAL_EXPR_TYPES = (ast.IfExp, ast.BoolOp)
def _in_conditional_operand(node: ast.AST, root: ast.AST,
                            parent_map: dict) -> bool:
    """node 是否位于 root（IfExp/BoolOp）中仅按条件求值的操作数内。

    IfExp 的 body/orelse 与 BoolOp 首操作数之后的操作数只在特定分支下求值；
    IfExp.test 与 BoolOp 首操作数恒求值，不构成条件流。
    """
    child: ast.AST = node
    current: ast.AST | None = parent_map.get(id(node))
    while current is not None and current is not root:
        child = current
        current = parent_map.get(id(current))
    if current is not root:
        return False
    if isinstance(root, ast.IfExp):
        return child is root.body or child is root.orelse
    return any(child is operand for operand in root.values[1:])
def _conditional_before_call(
        node: ast.AST, call: ast.AST, parent_map: dict) -> ast.AST | None:
    current: ast.AST | None = node
    while current is not None:
        if isinstance(current, _CONDITIONAL_EXPR_TYPES):
            if (_in_conditional_operand(node, current, parent_map)
                    and not any(child is call
                                for child in walk_nodes(current))):
                return current
            current = parent_map.get(id(current))
            continue
        if (isinstance(current, _CONDITIONAL_FLOW_TYPES)
                and not any(child is call for child in walk_nodes(current))):
            if (isinstance(current, ast.If)
                    and any(child is node for child in walk_nodes(current.test))):
                current = parent_map.get(id(current))
                continue
            if (isinstance(current, _TRY_FLOW_TYPES)
                    and _node_in_block(node, current.finalbody, parent_map)):
                current = parent_map.get(id(current))
                continue
            return current
        current = parent_map.get(id(current))
    return None
def _conditional_branch_blocks(node: ast.AST) -> tuple[list[ast.stmt], ...]:
    if isinstance(node, ast.If):
        return node.body, node.orelse
    if isinstance(node, ast.IfExp):
        return [node.body], [node.orelse]
    if isinstance(node, ast.BoolOp):
        return list(node.values[1:]), []
    normal_path = [*node.body, *node.orelse]
    return (normal_path, *(handler.body for handler in node.handlers))
def _node_in_block(node: ast.AST, block: list[ast.stmt],
                   parent_map: dict) -> bool:
    current: ast.AST | None = node
    while current is not None:
        if any(current is statement for statement in block):
            return True
        current = parent_map.get(id(current))
    return False
def _iter_enclosing_loops(node: ast.AST, parent_map: dict):
    current: ast.AST | None = node
    while current is not None:
        if (isinstance(current, (ast.For, ast.AsyncFor, ast.While))
                and _node_in_block(node, current.body, parent_map)):
            yield current
        current = parent_map.get(id(current))
def _loop_body_end_position(loop: ast.For | ast.AsyncFor | ast.While
                            ) -> tuple[int, int]:
    last = loop.body[-1]
    return (getattr(last, 'end_lineno', None) or getattr(last, 'lineno', 0) or 0,
            getattr(last, 'end_col_offset', None)
            or getattr(last, 'col_offset', 0) or 0)
def _nested_conditional_in_block(node: ast.AST, block: list[ast.stmt],
                                 parent_map: dict) -> bool:
    current: ast.AST | None = node
    while current is not None and not any(
            current is statement for statement in block):
        if isinstance(current, _CONDITIONAL_FLOW_TYPES):
            return True
        current = parent_map.get(id(current))
    return False
def _se19_event_key(event: _SE19ParserEvent) -> tuple[int, int, int]:
    return event.line, event.col, event.seq
def _latest_positioned(items: list, position_key: Any) -> Any:
    return max(
        enumerate(items),
        key=lambda item: (*position_key(item[1]), item[0]))[1]
def _se19_branch_safe(block: list[ast.stmt], prior: list[_SE19ParserEvent],
                      prior_safe: bool, parent_map: dict) -> bool:
    candidates = [event for event in prior
                  if _node_in_block(event.node, block, parent_map)]
    if not candidates:
        return prior_safe
    branch_latest = _latest_positioned(candidates, _se19_event_key)
    if _nested_conditional_in_block(branch_latest.node, block, parent_map):
        return all(event.safe for event in candidates)
    return branch_latest.safe
def _se19_parser_name_is_safe_at(
        name: ast.Name, reference: ast.AST, position: tuple[int, int],
        events: list[_SE19ParserEvent], parent_map: dict) -> bool:
    for scope in _binding_scope_chain(name, parent_map):
        scoped = [event for event in events
                  if event.scope is scope and event.name == name.id]
        if not scoped:
            continue
        prior = [event for event in scoped
                 if (event.line, event.col) <= position]
        if not prior:
            return False
        latest = _latest_positioned(prior, _se19_event_key)
        branch_node = _conditional_before_call(
            latest.node, reference, parent_map)
        if branch_node is None:
            return latest.safe
        branch_pos = (getattr(branch_node, 'lineno', 0) or 0,
                      getattr(branch_node, 'col_offset', 0) or 0)
        before_branch = [event for event in prior
                         if (event.line, event.col) < branch_pos]
        prior_safe = False
        if before_branch:
            previous = _latest_positioned(before_branch, _se19_event_key)
            prior_safe = (previous.safe
                          and _conditional_before_call(
                              previous.node, branch_node, parent_map) is None)
        return all(_se19_branch_safe(
                       block, prior, prior_safe, parent_map)
                   for block in _conditional_branch_blocks(branch_node))
    return False
def _se19_parser_name_is_safe(name: ast.Name, call: ast.Call,
                              events: list[_SE19ParserEvent],
                              parent_map: dict) -> bool:
    call_pos = (getattr(call, 'lineno', 0) or 0,
                getattr(call, 'col_offset', 0) or 0)
    if not _se19_parser_name_is_safe_at(
            name, call, call_pos, events, parent_map):
        return False
    return all(
        _se19_parser_name_is_safe_at(
            name, call, _loop_body_end_position(loop), events, parent_map)
        for loop in _iter_enclosing_loops(call, parent_map))
def _se19_parser_expression_safe(
        parser: ast.AST, call: ast.Call, events: list[_SE19ParserEvent],
        parent_map: dict, parser_targets: set[str]) -> bool:
    if _se19_parser_constructor_state(parser, parser_targets) is True:
        return True
    return (isinstance(parser, ast.Name)
            and _se19_parser_name_is_safe(
                parser, call, events, parent_map))
def _se19_collect_targets(tree: ast.AST) -> tuple[set, dict, dict]:
    targets: set[str] = set()
    origins_all: dict[str, str] = {}
    target_modules: dict[str, set[str]] = {}
    for _lib, _members in _SE19_XML_LIB_MEMBERS:
        _lib_targets, _origins = qualified_and_bare_call_targets_detailed(
            tree, _lib, _members)
        targets |= _lib_targets
        origins_all.update(_origins)
        for target in _lib_targets:
            target_modules.setdefault(target, set()).add(_lib)
    return targets, origins_all, target_modules
def _se19_parser_argument(call: ast.Call, member: str,
                          modules: set[str]) -> ast.AST | None:
    for name, value in _iter_static_call_keywords(call):
        if name == 'parser':
            return value
    if (len(call.args) >= 2
            and member in ('parse', 'fromstring', 'parseString')
            and modules and modules <= _SE19_POSITIONAL_PARSER_MODULES):
        return call.args[1]
    return None
def _se19_iterparse_entities_disabled(call: ast.Call, member: str,
                                      modules: set[str]) -> bool:
    return (member == 'iterparse' and modules == {'lxml.etree'}
            and _se19_parser_kwargs_disabled(call))
def _se19_plain_xml_literal(value: Any) -> bool:
    if not isinstance(value, (str, bytes)):
        return False
    if isinstance(value, bytes):
        try:
            if value.startswith((b'\xff\xfe\x00\x00', b'\x00\x00\xfe\xff')):
                text = value.decode('utf-32')
            elif value.startswith((b'\xff\xfe', b'\xfe\xff')):
                text = value.decode('utf-16')
            else:
                text = value.decode('utf-8-sig')
        except UnicodeError:
            return False
    else:
        text = value
    normalized = text.upper()
    return '<!DOCTYPE' not in normalized and '<!ENTITY' not in normalized
def _se19_content_literal_exempt(node: ast.Call, member: str) -> bool:
    if member not in ('fromstring', 'parseString'):
        return False
    if node.args:
        return (isinstance(node.args[0], ast.Constant)
                and _se19_plain_xml_literal(node.args[0].value))
    return any(name in ('text', 'string')
               and isinstance(value, ast.Constant)
               and _se19_plain_xml_literal(value.value)
               for name, value in _iter_static_call_keywords(node))
def check_SE19(tree: ast.AST, source_lines: list, filepath: str, index: list | None=None) -> list:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    _idx = materialized_index(index)
    parent_map = build_parent_map(tree) if tree is not None else {}
    parser_targets = qualified_and_bare_call_targets(
        tree, 'lxml.etree', ('XMLParser',))
    parser_events = _se19_parser_events(
        tree, parent_map, parser_targets)
    targets, origins_all, target_modules = _se19_collect_targets(tree)
    targets = _drop_defused_targets(tree, _idx, targets)
    for node in iter_nodes(tree, _idx):
        if not isinstance(node, ast.Call):
            continue
        func_name = dotted_name(node.func)
        if not func_name or func_name not in targets:
            continue
        member = _call_member_name(node, func_name, origins_all)
        if _se19_content_literal_exempt(node, member):
            continue
        modules = target_modules.get(func_name, set())
        if _se19_iterparse_entities_disabled(node, member, modules):
            continue
        parser = _se19_parser_argument(node, member, modules)
        if (parser is not None and _se19_parser_expression_safe(
                parser, node, parser_events, parent_map, parser_targets)):
            continue
        issues.append(_se_finding(
            "SE-19", "P0", node.lineno,
            "XML 解析未禁用外部实体(XXE), 可能导致信息泄露/SSRF",
            filepath, "XML 外部实体注入（XXE）",
            "CWE-611 / Bandit B317/B320", source_lines))
    return issues
def _se25_call_message(func: ast.expr, pickle_alias: set,
                       from_pickle_names: set) -> str | None:
    if isinstance(func, ast.Name) and func.id in from_pickle_names:
        return f'{func.id}() 是 pickle.Unpickler 别名调用,可执行任意代码(RCE风险)'
    named_attr = _named_attribute(func)
    if named_attr is None:
        return None
    recv, attr = named_attr
    if recv in pickle_alias and attr == 'Unpickler':
        return f'{recv}.Unpickler() 直接实例化等价于不安全反序列化(RCE风险)'
    return None
def check_SE25(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    pickle_alias, from_pickle_names = collect_module_bindings(
        tree, 'pickle', ('Unpickler',))
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        _msg = _se25_call_message(
            node.func, pickle_alias, from_pickle_names)
        if _msg is None:
            continue
        issues.append(_se_df(
            'SE-25', 'P0', node.lineno, _msg, filepath, source_lines,
            title='pickle 反序列化可执行任意代码',
            rule_ref='CWE-502 / Bandit B301'))
    return issues
def _cv01b_message(func: ast.expr, marshal_alias: set,
                   from_marshal_names: set) -> str | None:
    if isinstance(func, ast.Name) and func.id in from_marshal_names:
        return (f'{func.id}() 是 marshal 反序列化别名调用,'
                '处理不可信数据可执行任意代码')
    named_attr = _named_attribute(func)
    if named_attr is None:
        return None
    recv, attr = named_attr
    if recv in marshal_alias and attr in ('load', 'loads'):
        return (f'{recv}.{attr}() 是 marshal 反序列化调用,'
                '对不可信数据不安全')
    return None
def check_CV01b(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    marshal_alias, from_marshal_names = collect_module_bindings(
        tree, 'marshal', ('load', 'loads'))
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        message = _cv01b_message(node.func, marshal_alias, from_marshal_names)
        if message is not None:
            issues.append(_se_df(
                'CV-01b', 'P1', node.lineno, message,
                filepath, source_lines,
                title='marshal 反序列化不可信数据',
                rule_ref='CWE-502 / Bandit B302'))
    return issues
def _iter_target_calls(tree: Any, index: list | None,
                       targets: set) -> Iterator[ast.Call]:
    for node in iter_nodes(tree, index):
        if isinstance(node, ast.Call) and get_call_name(node) in targets:
            yield node
class _RuleCopy(NamedTuple):
    rule_id: str
    severity: str
    message: str
    title: str
    rule_ref: str
def _single_target_findings(tree: Any, filepath: Any, index: list | None,
                            targets: set, copy: _RuleCopy,
                            source_lines: Any = None) -> list:
    return [
        _se_finding(copy.rule_id, copy.severity, node.lineno, copy.message,
                    filepath, copy.title, copy.rule_ref, source_lines)
        for node in _iter_target_calls(tree, index, targets)
    ]
def check_SE09(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    targets = qualified_and_bare_call_targets(tree, 'tempfile', ('mktemp',))
    return _single_target_findings(
        tree, filepath, index, targets,
        _RuleCopy("SE-09", "P0", '使用 tempfile.mktemp() 存在竞态条件漏洞',
                  "tempfile.mktemp() 竞态条件", "Bandit B306 / CWE-377"),
        source_lines)
_SE11_RAND_FUNCS = (
    'randint', 'choice', 'choices', 'random', 'randrange', 'randbytes',
    'getrandbits',
)
def _se11_rand_member(node: ast.Call, random_names: set,
                      rand_from: dict) -> str | None:
    member = resolve_module_member_call(node, random_names, _SE11_RAND_FUNCS,
                                       rand_from)
    return member if member in _SE11_RAND_FUNCS else None
def _se11_nosec_suppressed(source_lines: Any, lineno: Any) -> bool:
    try:
        if not source_lines or not lineno or lineno < 1:
            return False
        line_no = int(lineno)
    except (IndexError, TypeError, KeyError, ValueError):  # jwsgj:silent-ok
        return False
    return has_nosec_marker(source_lines, line_no, None)
def check_SE11(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    _idx = materialized_index(index)
    _random_names, _rand_from = collect_module_bindings_detailed(
        tree, 'random', _SE11_RAND_FUNCS)
    for node in iter_nodes(tree, _idx):
        if not isinstance(node, ast.Call):
            continue
        _attr = _se11_rand_member(node, _random_names, _rand_from)
        if _attr is not None:
            if _se11_nosec_suppressed(source_lines,
                                     getattr(node, 'lineno', None)):
                continue
            issues.append(_se_df(
                'SE-11', 'P1', node.lineno,
                'random.' + _attr + '() 生成安全令牌, 可预测存在风险',
                filepath, source_lines,
                title='random 生成安全令牌',
                rule_ref='CWE-330 / Bandit B311'))
    return issues
_SAFE_EXTRACTION_FILTERS = frozenset({'data'})
def _tarfile_data_filter_bindings(
        tree: ast.AST | None) -> tuple[set[str], set[str]]:
    aliases, origins = collect_module_bindings_detailed(
        tree, 'tarfile', ('data_filter',))
    function_names = {name for name, origin in origins.items()
                      if origin == 'data_filter'}
    return set(aliases), function_names
def _has_safe_extraction_filter(
        call: ast.Call,
        data_filter_bindings: tuple[set[str], set[str]]) -> bool:
    module_names, function_names = data_filter_bindings
    for name, value in _iter_static_call_keywords(call):
        if name != 'filter':
            continue
        if isinstance(value, ast.Constant):
            return (isinstance(value.value, str)
                    and value.value in _SAFE_EXTRACTION_FILTERS)
        if isinstance(value, ast.Name):
            return value.id in function_names
        named = _named_attribute(value)
        return bool(named is not None
                    and named[0] in module_names
                    and named[1] == 'data_filter')
    return False
def check_SE12(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    targets = qualified_and_bare_call_targets(
        tree, 'shutil', ('unpack_archive',))
    data_filter_bindings = _tarfile_data_filter_bindings(tree)
    issues = []
    for node in _iter_target_calls(tree, index, targets):
        if _has_safe_extraction_filter(node, data_filter_bindings):
            continue
        issues.append(_se_finding(
            "SE-12", "P0", node.lineno,
            "shutil.unpack_archive() 未校验ZIP成员绝对路径, 存在Zip Slip风险",
            filepath, "unpack_archive 未校验 ZIP 成员路径",
            "CVE-2026-3087 / CWE-22", source_lines))
    return issues
def _is_url_sanitize_chars_constant(node: ast.AST) -> bool:
    return (isinstance(node, ast.Constant) and isinstance(node.value, str)
            and '-' in node.value
            and any(char.isspace() for char in node.value))
def _se13_url_is_sanitized(url_arg: ast.AST) -> bool:
    if not isinstance(url_arg, ast.Call):
        return False
    func = url_arg.func
    if not (isinstance(func, ast.Attribute)
            and func.attr in ('strip', 'lstrip')):
        return False
    candidates = [*url_arg.args,
                  *(kw.value for kw in url_arg.keywords if kw.arg == 'chars')]
    return any(_is_url_sanitize_chars_constant(a) for a in candidates)
def _se13_name_matches(node: ast.AST, name: str) -> bool:
    return isinstance(node, ast.Name) and node.id == name
def _se13_strip_call_matches(node: ast.AST, name: str) -> bool:
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in ('strip', 'lstrip')
            and _se13_name_matches(node.func.value, name)):
        return False
    if not node.args and not node.keywords:
        return True
    candidates = [*node.args,
                  *(kw.value for kw in node.keywords if kw.arg == 'chars')]
    return any(
        isinstance(arg, ast.Constant)
        and (arg.value is None or (
            isinstance(arg.value, str)
            and any(char.isspace() for char in arg.value)))
        for arg in candidates)
def _se13_rejects_surrounding_space(node: ast.AST, name: str) -> bool:
    if (not isinstance(node, ast.Compare) or len(node.ops) != 1
            or len(node.comparators) != 1
            or not isinstance(node.ops[0], ast.NotEq)):
        return False
    left, right = node.left, node.comparators[0]
    return ((_se13_name_matches(left, name)
             and _se13_strip_call_matches(right, name))
            or (_se13_strip_call_matches(left, name)
                and _se13_name_matches(right, name)))
def _se13_rejects_dash_prefix(node: ast.AST, name: str) -> bool:
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == 'startswith'
            and _se13_name_matches(node.func.value, name)):
        return False
    if not node.args:
        return False
    arg = node.args[0]
    if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
        return arg.value == '-'
    if isinstance(arg, (ast.Tuple, ast.List)):
        return any(
            isinstance(elt, ast.Constant) and isinstance(elt.value, str)
            and elt.value == '-'
            for elt in arg.elts)
    return False
_SE13_REJECT_SPACE = 1
_SE13_REJECT_DASH = 2
_SE13_REJECT_ALL = _SE13_REJECT_SPACE | _SE13_REJECT_DASH
def _se13_guard_rejection_mask(node: ast.AST, name: str) -> int:
    if isinstance(node, ast.BoolOp):
        masks = [_se13_guard_rejection_mask(value, name)
                 for value in node.values]
        if isinstance(node.op, ast.Or):
            result = 0
            for mask in masks:
                result |= mask
            return result
        result = _SE13_REJECT_ALL
        for mask in masks:
            result &= mask
        return result
    if _se13_rejects_surrounding_space(node, name):
        return _SE13_REJECT_SPACE
    if _se13_rejects_dash_prefix(node, name):
        return _SE13_REJECT_DASH
    return 0
def _se13_guard_rejects_url(node: ast.AST, name: str, call_lineno: int,
                            scope: ast.AST, parent_map: dict) -> bool:
    if (not isinstance(node, ast.If)
            or getattr(node, 'lineno', 0) >= call_lineno):
        return False
    if _enclosing_scope(node, parent_map) is not scope:
        return False
    if not any(node is stmt for stmt in scope.body):
        return False
    if not any(isinstance(stmt, ast.Raise) for stmt in node.body):
        return False
    return (_se13_guard_rejection_mask(node.test, name)
            == _SE13_REJECT_ALL)
def _se13_node_binding_names(node: ast.AST) -> tuple[str, ...]:
    if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)):
        return (node.id,)
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return (node.name,)
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return tuple(
            name for alias in node.names
            if (name := import_alias_bound_name(
                alias, from_import=isinstance(node, ast.ImportFrom)))
            is not None)
    capture = pattern_capture_name(node)
    return (capture,) if capture is not None else ()
def _se13_name_rebound_between(scope: ast.AST, name: str,
                               guard: ast.AST, call: ast.Call,
                               parent_map: dict) -> bool:
    start = (getattr(guard, 'lineno', 0) or 0,
             getattr(guard, 'col_offset', 0) or 0)
    ends = [(getattr(call, 'lineno', 0) or 0,
             getattr(call, 'col_offset', 0) or 0)]
    ends.extend(_loop_body_end_position(loop)
                for loop in _iter_enclosing_loops(call, parent_map))
    for node in iter_scope_nodes(scope):
        position = (getattr(node, 'lineno', 0) or 0,
                    getattr(node, 'col_offset', 0) or 0)
        if not start < position <= max(ends):
            continue
        parent = parent_map.get(id(node))
        if (isinstance(parent, ast.AnnAssign) and parent.value is None
                and node is parent.target):
            continue
        if name in _se13_node_binding_names(node):
            return True
    return False
def _se13_guarded_url_is_sanitized(url_arg: ast.AST, call: ast.Call,
                                  parent_map: dict) -> bool:
    if not isinstance(url_arg, ast.Name):
        return False
    scope = _enclosing_scope(call, parent_map)
    if scope is None:
        return False
    return any(
        _se13_guard_rejects_url(
            node, url_arg.id, getattr(call, 'lineno', 0), scope, parent_map)
        and not _se13_name_rebound_between(
            scope, url_arg.id, node, call, parent_map)
        for node in walk_nodes(scope))
_PY_COMP_SCOPE_NODES = (
    ast.ListComp, ast.SetComp, ast.GeneratorExp, ast.DictComp)
_PY_SCOPE_NODES = (
    ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda,
    ast.ClassDef, *_PY_COMP_SCOPE_NODES)
def _enclosing_scope(node: ast.AST, parent_map: dict) -> ast.AST | None:
    cur: ast.AST | None = node
    while cur is not None:
        if isinstance(cur, _PY_SCOPE_NODES):
            return cur
        cur = parent_map.get(id(cur))
    return None
def _lexical_scope_chain(node: ast.AST, parent_map: dict):
    scope = _enclosing_scope(node, parent_map)
    first = True
    while scope is not None:
        if first or not isinstance(scope, ast.ClassDef):
            yield scope
        first = False
        scope = _enclosing_scope(parent_map.get(id(scope)), parent_map)
def _binding_scope_chain(node: ast.AST, parent_map: dict):
    for scope in _lexical_scope_chain(node, parent_map):
        if isinstance(scope, _PY_COMP_SCOPE_NODES) and scope.generators:
            outer_iter = scope.generators[0].iter
            current: ast.AST | None = node
            in_outer_iter = False
            while current is not None and current is not scope:
                if current is outer_iter:
                    in_outer_iter = True
                    break
                current = parent_map.get(id(current))
            if in_outer_iter:
                continue
        yield scope
def _se_binding_scope(scope: ast.AST | None, name: str,
                      parent_map: dict, lexical_table: Any,
                      named_expr: bool = False) -> ast.AST | None:
    if scope is None:
        return None
    if named_expr:
        while isinstance(scope, _PY_COMP_SCOPE_NODES):
            scope = _enclosing_scope(parent_map.get(id(scope)), parent_map)
    for candidate in _lexical_scope_chain(scope, parent_map):
        if name in lexical_table.bound.get(candidate, ()):
            return candidate
    return scope
def _se13_scope_binds_bare_open(scope: ast.AST) -> bool:
    return any(
        isinstance(child, ast.ImportFrom) and child.level == 0
        and child.module == 'webbrowser'
        and any(alias.name == 'open' and alias.asname in (None, 'open')
                for alias in child.names)
        for child in iter_scope_nodes(scope))
def _se13_bare_open_bound(node: ast.Call, parent_map: dict,
                          memo: dict) -> bool:
    for scope in _lexical_scope_chain(node, parent_map):
        if (isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))
                and 'open' in collect_param_names(scope)):
            return False
        key = id(scope)
        cached = memo.get(key)
        if cached is None:
            cached = _se13_scope_binds_bare_open(scope)
            memo[key] = cached
        if cached:
            return True
    return False
def check_SE13(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    targets = qualified_and_bare_call_targets(
        tree, 'webbrowser', ('open', 'open_new', 'open_new_tab'))
    parent_map = build_parent_map(tree) if tree is not None else {}
    bare_open_memo: dict[int, bool] = {}
    for node in _iter_target_calls(tree, index, targets):
        if (isinstance(node.func, ast.Name) and node.func.id == 'open'
                and not _se13_bare_open_bound(
                    node, parent_map, bare_open_memo)):
            continue
        _url_arg = _call_arg_or_kw(node, 'url')
        if _se13_url_is_sanitized(_url_arg):
            continue
        if _se13_guarded_url_is_sanitized(_url_arg, node, parent_map):
            continue
        issues.append(_se_finding(
            "SE-13", "P2", node.lineno,
            "webbrowser.open() 未净化URL, 前导横杠可被解析为浏览器命令行选项",
            filepath, "webbrowser.open 未净化 URL",
            "CVE-2026-4519 / CWE-601", source_lines))
    return issues
def check_SE16(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    _, js_output_bare = collect_module_bindings(
        tree, 'http.cookies', ('js_output',))
    for node in iter_nodes(tree, index):
        if isinstance(node, ast.Call):
            func = node.func
            if ((isinstance(func, ast.Attribute) and func.attr == 'js_output')
                    or (isinstance(func, ast.Name)
                        and func.id in js_output_bare)):
                issues.append(_se_finding(
                    "SE-16", "P1", node.lineno,
                    'BaseCookie.js_output()存在XSS风险(CVE-2026-6019), 未转义</script>序列',
                    filepath, "BaseCookie.js_output() XSS",
                    "CVE-2026-6019 / CWE-79", source_lines))
    return issues
def check_SE17(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    targets = qualified_and_bare_call_targets(
        tree, 'pkgutil', ('get_data',))
    return _single_target_findings(
        tree, filepath, index, targets,
        _RuleCopy("SE-17", "P1",
                  'pkgutil.get_data() 资源参数未校验, 存在路径遍历风险',
                  "pkgutil.get_data 路径遍历", "CVE-2026-3479 / CWE-22"),
        source_lines)
def check_SE18(tree: ast.AST, source_lines: list, filepath: str, index: list | None=None) -> list:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Assert):
            continue
        if is_invariant_assert(node):
            continue
        issues.append(_se_finding(
            "SE-18", "P1", node.lineno,
            "使用 assert 进行输入验证, -O 模式下会被移除导致验证失效",
            filepath, "assert 输入验证（-O 模式失效）",
            "CWE-617 / Bandit B101", source_lines))
    return issues
_SE24_WRITABLE_MASK = 0o022
def _se24_is_chmod_call(node: ast.Call, os_names: set,
                        chmod_bare: set) -> bool:
    func = node.func
    if isinstance(func, ast.Name):
        return func.id in chmod_bare
    if not isinstance(func, ast.Attribute):
        return False
    if func.attr == 'chmod':
        return True
    return (func.attr == 'fchmod' and isinstance(func.value, ast.Name)
            and func.value.id in os_names)
_SE24_PATH_CLASSES = ('Path', 'PosixPath', 'WindowsPath')
def _se24_path_class_receivers(tree: ast.AST) -> set[str]:
    path_modules, path_origins = collect_module_bindings_detailed(
        tree, 'pathlib', _SE24_PATH_CLASSES)
    return ({f'{name}.{member}' for name in path_modules
             for member in _SE24_PATH_CLASSES}
            | set(path_origins))
def _se24_mode_position(node: ast.Call, os_names: set,
                        path_class_receivers: set[str]) -> int:
    func = node.func
    if isinstance(func, ast.Attribute) and func.attr == 'chmod':
        if dotted_name(func.value) in path_class_receivers:
            return 1
        if not (isinstance(func.value, ast.Name)
                and func.value.id in os_names):
            return 0
    return 1
def _se24_symbolic_mode_value(node: ast.AST) -> int | None:
    name = (node.id if isinstance(node, ast.Name)
            else node.attr if isinstance(node, ast.Attribute) else '')
    value = getattr(_stat, name, None) if name.startswith('S_') else None
    return value if isinstance(value, int) else None
def _se24_mode_static_value(node: ast.AST) -> int | None:
    if isinstance(node, ast.Constant):
        return node.value if isinstance(node.value, int) else None
    symbolic = _se24_symbolic_mode_value(node)
    if symbolic is not None:
        return symbolic
    if (not isinstance(node, ast.BinOp)
            or not isinstance(node.op, (ast.BitOr, ast.BitAnd, ast.BitXor))):
        return None
    left = _se24_mode_static_value(node.left)
    right = _se24_mode_static_value(node.right)
    if left is None or right is None:
        return None
    if isinstance(node.op, ast.BitOr):
        return left | right
    if isinstance(node.op, ast.BitAnd):
        return left & right
    return left ^ right

def _se24_mode_is_writable(mode_arg: ast.AST) -> bool:
    value = _se24_mode_static_value(mode_arg)
    if value is not None:
        return bool(value & _SE24_WRITABLE_MASK)
    if isinstance(mode_arg, ast.BinOp) and isinstance(mode_arg.op, ast.BitOr):
        return any(_se24_mode_is_writable(side)
                   for side in (mode_arg.left, mode_arg.right))
    return False
def check_SE24(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    os_names, chmod_bare = collect_module_bindings(
        tree, 'os', ('chmod', 'fchmod'))
    path_class_receivers = _se24_path_class_receivers(tree)
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        if not _se24_is_chmod_call(node, os_names, chmod_bare):
            continue
        mode_arg = _call_arg_or_kw(
            node, 'mode', _se24_mode_position(
                node, os_names, path_class_receivers))
        if mode_arg is None:
            continue
        if _se24_mode_is_writable(mode_arg):
            issues.append(_se_df(
                'SE-24', 'P1', node.lineno,
                'chmod()设置过于宽松的权限,存在安全风险',
                filepath, source_lines,
                title='chmod 权限过宽',
                rule_ref='CWE-732 / Bandit B103'))
    return issues
_SE26_TARFILE_FACTORIES = frozenset({
    'open', 'taropen', 'gzopen', 'bz2open', 'xzopen', 'TarFile',
})
def _se26_factory_receiver_bound(receiver: ast.AST, tarfile_names: set,
                                 factory_bare: set) -> bool:
    name = dotted_name(receiver)
    if not name:
        return False
    head = name.split('.', 1)[0]
    return head in tarfile_names or head in factory_bare
def _se26_is_tarfile_factory(call: ast.AST, tarfile_names: set,
                            factory_bare: set) -> bool:
    if not isinstance(call, ast.Call):
        return False
    func = call.func
    if (isinstance(func, ast.Attribute)
            and func.attr in _SE26_TARFILE_FACTORIES
            and _se26_factory_receiver_bound(
                func.value, tarfile_names, factory_bare)):
        return True
    return isinstance(func, ast.Name) and func.id in factory_bare
def _se26_binding_kind(value: ast.AST | None, tarfile_names: set,
                       factory_bare: set) -> str | tuple[str, str]:
    if _se26_is_tarfile_factory(value, tarfile_names, factory_bare):
        return 'tar'
    if isinstance(value, ast.Name):
        return ('alias', value.id)
    return 'other'
def _se26_binding_pairs(node: ast.AST, tarfile_names: set,
                        factory_bare: set) -> list[tuple[str, str]]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        return [(parameter.arg, 'unknown')
                for parameter in iter_arg_nodes(node.args)]
    if isinstance(node, (ast.With, ast.AsyncWith)):
        pairs: list[tuple[str, str]] = []
        for item in node.items:
            if item.optional_vars is None:
                continue
            kind = _se26_binding_kind(
                item.context_expr, tarfile_names, factory_bare)
            pairs.extend((name, kind) for name, _line, _col
                         in iter_target_bindings(item.optional_vars))
        return pairs
    if isinstance(node, ast.Assign):
        return [(name, _se26_binding_kind(
            value, tarfile_names, factory_bare))
                for target in node.targets
                for name, value in _iter_target_value_bindings(
                    target, node.value)]
    if isinstance(node, (ast.AnnAssign, ast.NamedExpr)):
        value = node.value
        if value is None:
            return []
        return [(name, _se26_binding_kind(
            bound_value, tarfile_names, factory_bare))
                for name, bound_value in _iter_target_value_bindings(
                    node.target, value)]
    if isinstance(node, (ast.For, ast.AsyncFor, ast.comprehension)):
        return [(name, 'other') for name, _line, _col
                in iter_target_bindings(node.target)]
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return [
            (name, 'other') for alias in node.names
            if (name := import_alias_bound_name(
                alias, from_import=isinstance(node, ast.ImportFrom)))
            is not None]
    capture = pattern_capture_name(node)
    return [(capture, 'other')] if capture is not None else []
def _se26_collect_bindings(tree: ast.AST, tarfile_names: set,
                           factory_bare: set) -> tuple[dict, dict]:
    parent_map = build_parent_map(tree)
    lexical_table = collect_lexical_scope_table(tree)
    bindings: dict[tuple[int, str], list[tuple[int, int, str]]] = {}
    for seq, node in enumerate(walk_nodes(tree)):
        pairs = _se26_binding_pairs(node, tarfile_names, factory_bare)
        if not pairs and not isinstance(
                node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        scope = _enclosing_scope(node, parent_map)
        position_node = (node.target if isinstance(node, ast.comprehension)
                         else node)
        line = getattr(position_node, 'lineno', 0) or 0
        col = getattr(position_node, 'col_offset', 0) or 0
        groups = [(scope, line, col, pairs)]
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            definition_scope = _enclosing_scope(
                parent_map.get(id(node)), parent_map)
            if definition_scope is not None:
                definition_line = (getattr(node, 'end_lineno', None) or line
                                   if isinstance(node, ast.ClassDef) else line)
                definition_col = (getattr(node, 'end_col_offset', None) or col
                                  if isinstance(node, ast.ClassDef) else col)
                groups.append((definition_scope, definition_line,
                               definition_col, [(node.name, 'other')]))
        for group_scope, group_line, group_col, group_pairs in groups:
            for name, kind in group_pairs:
                binding_scope = _se_binding_scope(
                    group_scope, name, parent_map, lexical_table,
                    named_expr=isinstance(node, ast.NamedExpr))
                scope_id = (id(binding_scope) if binding_scope is not None
                            else id(tree))
                bindings.setdefault((scope_id, name), []).append(
                    (group_line, group_col, seq, kind, node))
    _se26_resolve_alias_kinds(bindings, parent_map)
    return bindings, parent_map
def _se26_resolve_alias_kinds(bindings: dict, parent_map: dict) -> None:
    pending = [(key, idx) for key, entries in bindings.items()
               for idx, entry in enumerate(entries)
               if isinstance(entry[3], tuple)]
    for _ in range(len(pending) + 1):
        progressed = False
        for key, idx in pending:
            entries = bindings[key]
            line, col, seq, kind, node = entries[idx]
            if not isinstance(kind, tuple):
                continue
            _tag, rhs = kind
            resolved = _se26_binding_kind_at(
                bindings, rhs, node, parent_map, line, col, before_seq=seq)
            if isinstance(resolved, str):
                entries[idx] = (line, col, seq, resolved, node)
                progressed = True
        if not progressed:
            break
    for entries in bindings.values():
        for idx, entry in enumerate(entries):
            if isinstance(entry[3], tuple):
                entries[idx] = (entry[0], entry[1], entry[2], 'other',
                                entry[4])
def _se26_entry_key(entry: tuple) -> tuple[int, int, int]:
    return entry[0], entry[1], entry[2]
def _se26_branch_kind(block: list[ast.stmt], prior: list[tuple],
                      prior_kind: str | None, parent_map: dict) -> str | None:
    candidates = [entry for entry in prior
                  if _node_in_block(entry[4], block, parent_map)]
    if not candidates:
        return prior_kind
    branch_latest = _latest_positioned(candidates, _se26_entry_key)
    if (_nested_conditional_in_block(branch_latest[4], block, parent_map)
            and any(entry[3] == 'tar' for entry in candidates)):
        return 'tar'
    return branch_latest[3]
def _se26_binding_kind_at(bindings: dict, name: str, node: ast.AST,
                          parent_map: dict, lineno: int,
                          col_offset: int,
                          before_seq: int | None = None) -> str | None:
    for scope in _binding_scope_chain(node, parent_map):
        entries = bindings.get((id(scope), name))
        if not entries:
            continue
        if before_seq is None:
            prior = [entry for entry in entries
                     if (entry[0], entry[1]) <= (lineno, col_offset)]
        else:
            prior = [entry for entry in entries
                     if (entry[0], entry[1], entry[2]) < (
                         lineno, col_offset, before_seq)]
        if not prior:
            return 'unknown'
        latest = _latest_positioned(prior, _se26_entry_key)
        branch_node = _conditional_before_call(
            latest[4], node, parent_map)
        if branch_node is None:
            return latest[3]
        prior_kind = _se26_binding_kind_at(
            bindings, name, branch_node, parent_map,
            getattr(branch_node, 'lineno', 0) or 0,
            getattr(branch_node, 'col_offset', 0) or 0)
        kinds = [_se26_branch_kind(
                     block, prior, prior_kind, parent_map)
                 for block in _conditional_branch_blocks(branch_node)]
        if 'tar' in kinds:
            return 'tar'
        known = [kind for kind in kinds if kind is not None]
        if not known:
            return None
        if all(kind == 'unknown' for kind in known):
            return 'unknown'
        first = known[0]
        return first if all(kind == first for kind in known[1:]) else 'other'
    return None
def _se26_obj_is_risky(obj: ast.AST, call: ast.Call, tarfile_names: set,
                       bindings: dict, parent_map: dict,
                       factory_bare: set) -> bool:
    if isinstance(obj, ast.Name):
        kind = _se26_binding_kind_at(
            bindings, obj.id, call, parent_map,
            getattr(call, 'lineno', 0) or 0,
            getattr(call, 'col_offset', 0) or 0)
        if kind == 'tar':
            return True
        for loop in _iter_enclosing_loops(call, parent_map):
            end_line, end_col = _loop_body_end_position(loop)
            if _se26_binding_kind_at(
                    bindings, obj.id, call, parent_map,
                    end_line, end_col) == 'tar':
                return True
        if kind is not None:
            return False
        return obj.id in tarfile_names
    if isinstance(obj, ast.Call):
        return _se26_is_tarfile_factory(obj, tarfile_names, factory_bare)
    return False
def _se26_call_is_extractall_risk(
        node: ast.AST, tarfile_names: set, bindings: dict, parent_map: dict,
        factory_bare: set,
        data_filter_bindings: tuple[set[str], set[str]]) -> bool:
    if not isinstance(node, ast.Call):
        return False
    func = node.func
    if not (isinstance(func, ast.Attribute) and func.attr == 'extractall'):
        return False
    risky = _se26_obj_is_risky(func.value, node, tarfile_names,
                               bindings, parent_map, factory_bare)
    return risky and not _has_safe_extraction_filter(
        node, data_filter_bindings)
def _se26_bindings(tree: Any) -> tuple[set, set]:
    tarfile_names, tar_from = collect_module_bindings_detailed(
        tree, 'tarfile', tuple(_SE26_TARFILE_FACTORIES))
    factory_bare = {name for name, origin in tar_from.items()
                    if origin in _SE26_TARFILE_FACTORIES}
    module_names = set(tarfile_names)
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
            continue
        value = node.value
        if value is None:
            continue
        targets = node.targets if isinstance(node, ast.Assign) else [node.target]
        for target in targets:
            for name, bound_value in _iter_target_value_bindings(target, value):
                if (isinstance(bound_value, ast.Name)
                        and bound_value.id in module_names):
                    module_names.add(name)
    return module_names, factory_bare
def check_SE26(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if tree is None:
        return issues
    names, factory_bare = _se26_bindings(tree)
    bindings, parent_map = _se26_collect_bindings(
        tree, names, factory_bare)
    data_filter_bindings = _tarfile_data_filter_bindings(tree)
    for node in iter_nodes(tree, index):
        if _se26_call_is_extractall_risk(
                node, names, bindings, parent_map,
                factory_bare, data_filter_bindings):
            issues.append(_se_df(
                'SE-26', 'P1', node.lineno,
                'tarfile.extractall()未校验成员路径,存在路径穿越风险',
                filepath, source_lines,
                title='tarfile.extractall 路径穿越',
                rule_ref='CWE-22 / PEP 706'))
    return issues
def _se30_parser_module():
    try:
        from re import (
            _parser as _p,  # lazy-by-design
        )
        return _p
    except ImportError:
        try:
            import sre_parse as _p  # pragma: no cover  # lazy-by-design
            return _p
        except ImportError as _e:
            _log.debug("SE-30 解析模块回退失败，跳过该模式: %s", _e)
            return None
def _se30_repeat_ops(pmod) -> tuple:
    return tuple(op for name in (
        'MAX_REPEAT', 'MIN_REPEAT', 'POSSESSIVE_REPEAT')
        if (op := getattr(pmod, name, None)) is not None)
def _se30_hard_consume(pmod, item) -> bool:
    op, av = item
    if op in (pmod.LITERAL, pmod.NOT_LITERAL, pmod.ANY, pmod.IN,
              pmod.RANGE, pmod.CATEGORY):
        return True
    if op in _se30_repeat_ops(pmod):
        lo = av[0]
        return lo >= 1 and _se30_seq_hard_consume(pmod, av[2])
    if op == pmod.SUBPATTERN:
        return _se30_seq_hard_consume(pmod, av[-1])
    if op == pmod.BRANCH:
        return all(_se30_seq_hard_consume(pmod, br) for br in av[1])
    if hasattr(pmod, 'ATOMIC_GROUP') and op == pmod.ATOMIC_GROUP:
        return _se30_seq_hard_consume(pmod, av)
    return False
def _se30_seq_hard_consume(pmod, seq) -> bool:
    return any(_se30_hard_consume(pmod, it) for it in seq)
def _se30_may_consume(pmod, item) -> bool:
    op, av = item
    if op in (pmod.AT, pmod.ASSERT, pmod.ASSERT_NOT):
        return False
    if op in _se30_repeat_ops(pmod):
        return _se30_seq_may_consume(pmod, av[2])
    if op == pmod.SUBPATTERN:
        return _se30_seq_may_consume(pmod, av[-1])
    if op == pmod.BRANCH:
        return any(_se30_seq_may_consume(pmod, br) for br in av[1])
    if hasattr(pmod, 'ATOMIC_GROUP') and op == pmod.ATOMIC_GROUP:
        return _se30_seq_may_consume(pmod, av)
    return True
def _se30_seq_may_consume(pmod, seq) -> bool:
    return any(_se30_may_consume(pmod, item) for item in seq)
def _se30_first_chars(pmod, item):
    op, av = item
    if op == pmod.LITERAL:
        return {chr(av)} if isinstance(av, int) else None
    if op == pmod.IN:
        chars = set()
        for sub_op, sub_av in av:
            if sub_op == pmod.LITERAL:
                chars.add(chr(sub_av))
                continue
            return None
        return chars or None
    if op in _se30_repeat_ops(pmod):
        return _se30_first_chars_seq(pmod, av[2])
    if op == pmod.SUBPATTERN:
        return _se30_first_chars_seq(pmod, av[-1])
    if op == pmod.BRANCH:
        chars = set()
        for branch in av[1]:
            branch_chars = _se30_first_chars_seq(pmod, branch)
            if (branch_chars is None
                    and _se30_seq_may_consume(pmod, branch)):
                return None
            chars.update(branch_chars or ())
        return chars or None
    if hasattr(pmod, 'ATOMIC_GROUP') and op == pmod.ATOMIC_GROUP:
        return _se30_first_chars_seq(pmod, av)
    return None
def _se30_first_chars_seq(pmod, seq):
    chars = set()
    unknown = False
    for item in seq:
        item_chars = _se30_first_chars(pmod, item)
        if item_chars:
            chars.update(item_chars)
        elif _se30_may_consume(pmod, item):
            unknown = True
        if _se30_hard_consume(pmod, item):
            break
    return None if unknown else chars or None
def _se30_branch_ambiguous(pmod, branches) -> bool:
    seen = []
    for br in branches:
        seen.append(_se30_first_chars_seq(pmod, br))
    for idx in range(len(seen)):
        for jdx in range(idx + 1, len(seen)):
            left, right = seen[idx], seen[jdx]
            if left and right and (left & right):
                return True
    return False
def _se30_unwrap_group(pmod, seq) -> list:
    current = list(seq)
    while len(current) == 1 and current[0][0] == pmod.SUBPATTERN:
        current = list(current[0][1][-1])
    return current
def _se30_adjacent_first_chars(pmod, items):
    for item in items:
        if _se30_may_consume(pmod, item):
            return _se30_first_chars(pmod, item)
    return None
def _se30_repeat_has_ambiguous_neighbor(pmod, sub, jdx: int) -> bool:
    chars = _se30_first_chars(pmod, sub[jdx])
    if not chars:
        return False
    before = _se30_adjacent_first_chars(
        pmod, reversed(sub[:jdx]))
    after = _se30_adjacent_first_chars(pmod, sub[jdx + 1:])
    return bool((before and chars & before)
                or (after and chars & after))
def _se30_repeat_payload_dangerous(pmod, sub) -> bool:
    if _se30_seq_repeat_dangerous(pmod, sub):
        return True
    for item in sub:
        if item[0] != pmod.BRANCH:
            continue
        if any(not br for br in item[1][1]):
            return True
        if _se30_branch_ambiguous(pmod, item[1][1]):
            return True
        if any(_se30_seq_repeat_dangerous(pmod, br)
               for br in item[1][1]):
            return True
    return False
def _se30_seq_repeat_dangerous(pmod, seq) -> bool:
    for jdx, inner in enumerate(seq):
        if inner[0] not in (pmod.MAX_REPEAT, pmod.MIN_REPEAT):
            continue
        lo, hi = inner[1][0], inner[1][1]
        if hi == lo:
            continue
        if ((_se30_seq_hard_consume(pmod, seq[:jdx])
                or _se30_seq_hard_consume(pmod, seq[jdx + 1:]))
                and not _se30_repeat_has_ambiguous_neighbor(pmod, seq, jdx)):
            continue
        return True
    return False
def _se30_seq_dangerous(pmod, seq) -> bool:
    for op, av in seq:
        if op in (pmod.MAX_REPEAT, pmod.MIN_REPEAT):
            sub = _se30_unwrap_group(pmod, av[2])
            if (av[1] == pmod.MAXREPEAT
                    and _se30_repeat_payload_dangerous(pmod, sub)):
                return True
            if _se30_seq_dangerous(pmod, sub):
                return True
        elif op == pmod.SUBPATTERN:
            if _se30_seq_dangerous(pmod, av[-1]):
                return True
        elif op == pmod.BRANCH:
            for br in av[1]:
                if _se30_seq_dangerous(pmod, br):
                    return True
        elif ((op in (pmod.ASSERT, pmod.ASSERT_NOT)
               and _se30_seq_dangerous(pmod, av[1]))
              or (hasattr(pmod, 'ATOMIC_GROUP')
                  and op == pmod.ATOMIC_GROUP
                  and _se30_seq_dangerous(pmod, av))
              or (op == pmod.GROUPREF_EXISTS
                  and any(_se30_seq_dangerous(pmod, branch)
                          for branch in av[1:] if branch))):
            return True
    return False
def _se30_has_nested_repeat(pattern_str: str) -> bool:
    pmod = _se30_parser_module()
    if pmod is None:
        return False
    try:
        parsed = pmod.parse(pattern_str, 0)
    except Exception as _parse_err:  # noqa: BLE001
        _log.debug("SE-30 模式解析失败(跳过): %s: %s", pattern_str[:40], _parse_err)
        return False
    return _se30_seq_dangerous(pmod, list(parsed))
_SE30_PATTERN_APIS = frozenset({
    'compile', 'match', 'search', 'findall', 'finditer', 'fullmatch',
    'split', 'sub', 'subn',
})
def _se30_constant_text(value: Any) -> str | None:
    if isinstance(value, str):
        return value
    if isinstance(value, bytes):
        return value.decode('latin-1')
    return None
def _se30_static_text(node: ast.AST) -> str | None:
    if isinstance(node, ast.Constant):
        return _se30_constant_text(node.value)
    if isinstance(node, ast.JoinedStr):
        parts: list[str] = []
        for part in node.values:
            if not (isinstance(part, ast.Constant)
                    and isinstance(part.value, str)):
                return None
            parts.append(part.value)
        return ''.join(parts)
    return None
def _se30_pattern_from_arg(arg: ast.AST) -> str | None:
    if not (isinstance(arg, ast.BinOp) and isinstance(arg.op, ast.Add)):
        return _se30_static_text(arg)
    parts: list[str] = []
    stack: list[ast.AST] = [arg]
    while stack:
        cur = stack.pop()
        if isinstance(cur, ast.BinOp) and isinstance(cur.op, ast.Add):
            stack.append(cur.right)
            stack.append(cur.left)
            continue
        text = _se30_static_text(cur)
        if text is None:
            return None
        parts.append(text)
    return ''.join(parts)
def _se30_pattern_text(node: ast.Call) -> str:
    pattern_node = _call_arg_or_kw(node, 'pattern')
    if pattern_node is None:
        return ''
    return _se30_pattern_from_arg(pattern_node) or ''
def _se30_is_re_call(node: ast.Call, re_names: set, re_bare: set) -> bool:
    func = node.func
    if isinstance(func, ast.Name):
        return func.id in re_bare
    return (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)
            and func.value.id in re_names
            and func.attr in _SE30_PATTERN_APIS)
def check_SE30(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    re_names, re_bare = collect_module_bindings(
        tree, 're', tuple(_SE30_PATTERN_APIS))
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        if not _se30_is_re_call(node, re_names, re_bare):
            continue
        pattern_str = _se30_pattern_text(node)
        if not pattern_str:
            continue
        if _se30_has_nested_repeat(pattern_str):
            issues.append(_se_df(
                'SE-30', 'P1', node.lineno,
                f'正则表达式可能存在ReDoS(灾难性回溯)风险: {pattern_str[:60]}',
                filepath, source_lines,
                title='正则表达式 ReDoS 风险',
                rule_ref='CWE-1333'))
    return issues
_TMP_PREFIXES = (
    '/tmp/', '/var/tmp/', '/dev/shm/',
    'c:/windows/temp/', 'c:/temp/',
)
_TMP_BARE_DIRS = frozenset((
    '/tmp', '/var/tmp', '/dev/shm',
    'c:/windows/temp', 'c:/temp',
))
def _b108_arg_is_tmp_path(arg: ast.AST) -> bool:
    if not (isinstance(arg, ast.Constant) and isinstance(arg.value, str)):
        return False
    val = arg.value.strip().lower().replace('\\', '/')
    return val in _TMP_BARE_DIRS or val.startswith(_TMP_PREFIXES)
def check_B108(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        arguments = [value for _name, value in _iter_static_call_keywords(node)]
        if not any(_b108_arg_is_tmp_path(a)
                   for a in [*node.args, *arguments]):
            continue
        issues.append(_se_df(
            'B108', 'P3', node.lineno,
            '硬编码系统临时目录路径，可预测路径存在符号链接风险且不可移植',
            filepath, source_lines,
            title='硬编码临时目录',
            rule_ref='CWE-377 / Bandit B108'))
    return issues
def _yaml_loader_origin_is_safe(loader: ast.AST, yaml_names: set[str],
                                loader_origins: dict[str, str]) -> bool:
    if isinstance(loader, ast.Name):
        return loader_origins.get(loader.id) in YAML_SAFE_LOADERS
    named_attr = _named_attribute(loader)
    return bool(named_attr is not None
                and named_attr[0] in yaml_names
                and named_attr[1] in YAML_SAFE_LOADERS)
def yaml_load_is_safe(node: ast.Call, tree: ast.AST | None = None) -> bool:
    loader = _call_arg_or_kw(node, 'Loader', 1)
    if loader is None:
        return False
    if tree is None:
        return (isinstance(loader, ast.Attribute)
                and isinstance(loader.value, ast.Name)
                and loader.value.id == 'yaml'
                and loader.attr in YAML_SAFE_LOADERS)
    members = tuple(sorted({*YAML_SAFE_LOADERS,
                            'Loader', 'FullLoader', 'UnsafeLoader'}))
    yaml_names, loader_origins = collect_module_bindings_detailed(
        tree, 'yaml', members)
    return _yaml_loader_origin_is_safe(loader, yaml_names, loader_origins)
def _iter_loop_nodes(tree: Any, index: list | None = None) -> Any:
    return (node for node in iter_nodes(tree, index)
            if isinstance(node, (ast.For, ast.AsyncFor, ast.While)))
def _rg02_scan_roots(node: Any) -> list:
    if isinstance(node, ast.While):
        return [node.test] + list(node.body)
    return list(node.body)
_RG02_RULE = {
    "rule_id": "RG-02", "severity": "P2", "dimension": "regex_safety",
    "rule_ref": "re-compile-in-loop"}
def _rg02_report(issues: list, node: ast.Call, source: Any,
                 filepath: Any) -> None:
    title = "re.compile() 在循环体内重复调用"
    issues.append(build_ast_issue(
        _RG02_RULE, source, filepath, node, title,
        "re.compile() 在循环体内被重复调用，每次迭代都重新编译正则。"
        "应将其提升到循环外部。",
        get_fix_guidance("RG-02")))
def check_RG02(tree: Any, source: Any, filepath: Any,
               index: list | None = None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    _log.debug("规则入口 check_RG02 执行")
    issues: list[dict[str, Any]] = []
    if tree is None:
        return issues
    reported: set[int] = set()
    targets = qualified_and_bare_call_targets(tree, 're', ('compile',))
    for loop in _iter_loop_nodes(tree, index):
        for child in iter_frame_nodes(_rg02_scan_roots(loop)):
            if not (isinstance(child, ast.Call)
                    and get_call_name(child) in targets):
                continue
            child_id = id(child)
            if child_id in reported:
                continue
            reported.add(child_id)
            _rg02_report(issues, child, source, filepath)
    return issues
def _dotstar_span(pattern: str, i: int, n: int) -> int:
    if not (pattern[i] == '.' and i + 1 < n and pattern[i + 1] == '*'):
        return 0
    if i + 2 < n and pattern[i + 2] == '?':
        return 3
    return 2
def _regex_scan_step(pattern: str, i: int, in_class: bool) -> tuple[int, bool] | None:
    ch = pattern[i]
    if ch == '\\':
        return i + 2, in_class
    if in_class:
        return i + 1, ch != ']'
    if ch == '[':
        return i + 1, True
    return None
def _regex_has_greedy_dotstar(pattern: str) -> bool:
    in_class = False
    i = 0
    n = len(pattern)
    while i < n:
        step = _regex_scan_step(pattern, i, in_class)
        if step is not None:
            i, in_class = step
            continue
        span = _dotstar_span(pattern, i, n)
        if span == 2:
            return True
        i += span or 1
    return False
def _rg04_has_inline_dotall(pattern: str) -> bool:
    in_class = False
    i = 0
    n = len(pattern)
    while i < n:
        step = _regex_scan_step(pattern, i, in_class)
        if step is not None:
            i, in_class = step
            continue
        if pattern[i] == '(' and i + 1 < n and pattern[i + 1] == '?':
            dotall_on, j = _rg04_scan_inline_flag_group(pattern, i, n)
            if dotall_on:
                return True
            i = j
            continue
        i += 1
    return False
_RG04_ADD_FLAGS: frozenset[str] = frozenset("aiLmsux")
_RG04_REMOVE_FLAGS: frozenset[str] = frozenset("imsx")
_RG_FLAGS_POSITION: dict[str, int] = {
    "compile": 1, "search": 2, "match": 2, "fullmatch": 2,
    "findall": 2, "finditer": 2, "split": 3, "sub": 4, "subn": 4,
}
_RG04_FLAG_VALUES: dict[str, int] = {
    'A': int(re.ASCII), 'ASCII': int(re.ASCII),
    'I': int(re.IGNORECASE), 'IGNORECASE': int(re.IGNORECASE),
    'L': int(re.LOCALE), 'LOCALE': int(re.LOCALE),
    'M': int(re.MULTILINE), 'MULTILINE': int(re.MULTILINE),
    'S': int(re.DOTALL), 'DOTALL': int(re.DOTALL),
    'U': int(re.UNICODE), 'UNICODE': int(re.UNICODE),
    'X': int(re.VERBOSE), 'VERBOSE': int(re.VERBOSE),
    'T': int(getattr(re, 'TEMPLATE', 0)),
    'TEMPLATE': int(getattr(re, 'TEMPLATE', 0)),
    'DEBUG': int(getattr(re, 'DEBUG', 0)),
    'NOFLAG': int(getattr(re, 'NOFLAG', 0)),
}
def _rg04_scan_inline_flag_group(pattern: str, i: int, n: int) -> tuple[bool, int]:
    j, added = _rg04_scan_flag_set(pattern, i + 2, n, _RG04_ADD_FLAGS)
    if "s" in added and _rg04_group_terminates(pattern, j, n):
        return True, j
    if j < n and pattern[j] == "-":
        k, removed = _rg04_scan_flag_set(
            pattern, j + 1, n, _RG04_REMOVE_FLAGS)
        scoped = k < n and pattern[k] == ":"
        return ("s" in added and "s" not in removed and scoped), k
    return False, j
def _rg04_scan_flag_set(pattern: str, j: int, n: int,
                        allowed: frozenset[str]) -> tuple[int, set[str]]:
    seen: set[str] = set()
    while j < n and pattern[j] in allowed:
        seen.add(pattern[j])
        j += 1
    return j, seen
def _rg04_group_terminates(pattern: str, j: int, n: int) -> bool:
    return j < n and pattern[j] in (':', ')')
def _rg04_flags_expr_value(node: ast.AST, re_names: set,
                           bare_origins: dict) -> tuple[int, bool]:
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        left, left_complete = _rg04_flags_expr_value(
            node.left, re_names, bare_origins)
        right, right_complete = _rg04_flags_expr_value(
            node.right, re_names, bare_origins)
        return left | right, left_complete and right_complete
    if isinstance(node, ast.Constant):
        value = node.value
        return ((value, True)
                if isinstance(value, int) and not isinstance(value, bool)
                else (0, False))
    if isinstance(node, ast.Name):
        value = _RG04_FLAG_VALUES.get(bare_origins.get(node.id, ''))
        return (0, False) if value is None else (value, True)
    name = dotted_name(node)
    if not name or "." not in name:
        return 0, False
    head, _sep, leaf = name.partition(".")
    value = (_RG04_FLAG_VALUES.get(leaf.rsplit(".", 1)[-1])
             if (head in re_names
                 or bare_origins.get(head) == 'RegexFlag') else None)
    return (0, False) if value is None else (value, True)
def _rg04_external_flags(node: ast.Call, member: str | None,
                         re_names: set, bare_origins: dict) -> tuple[int, bool]:
    fn_name = member or getattr(getattr(node, "func", None), "attr", "")
    flags_pos = _RG_FLAGS_POSITION.get(fn_name)
    flag_nodes: list[ast.expr] = []
    if flags_pos is not None and len(node.args) > flags_pos:
        flag_nodes.append(node.args[flags_pos])
    flag_nodes.extend(value for name, value in _iter_static_call_keywords(node)
                      if name == "flags")
    flags = 0
    complete = True
    for flag_node in flag_nodes:
        value, value_complete = _rg04_flags_expr_value(
            flag_node, re_names, bare_origins)
        flags |= value
        complete = complete and value_complete
    return flags, complete
def _rg04_call_member(node: ast.Call, re_names: set,
                      bare_origins: dict[str, str]) -> str | None:
    func = node.func
    if isinstance(func, ast.Name):
        return bare_origins.get(func.id)
    if (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)
            and func.value.id in re_names):
        return func.attr
    return None
def check_RG04(tree: Any, source: Any, filepath: Any,
               index: list | None = None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    _log.debug("规则入口 check_RG04 执行")
    issues: list[dict[str, Any]] = []
    if tree is None:
        return issues
    re_names, bare_origins = collect_module_bindings_detailed(
        tree, 're', tuple(dict.fromkeys(
            (*_RG_FLAGS_POSITION, *_RG04_FLAG_VALUES, 'RegexFlag'))))
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        member = _rg04_call_member(node, re_names, bare_origins)
        if member is None or member not in _RG_FLAGS_POSITION:
            continue
        pattern_arg = _call_arg_or_kw(node, "pattern")
        pattern = (_se30_pattern_from_arg(pattern_arg)
                   if pattern_arg is not None else None)
        if pattern is None or not _rg04_is_violation(
                pattern, node, member, re_names, bare_origins):
            continue
        issues.append(_rg04_build_ast_issue(node, source, filepath))
    return issues
def _rg04_zero_width_end_anchor(pmod, item, multiline: bool = False) -> bool:
    op, av = item
    if op == pmod.ASSERT and av[0] == 1:
        return any(_rg04_zero_width_end_anchor(
            pmod, child, multiline) for child in av[1])
    if op == pmod.AT:
        absolute_end_ops = set()
        if not multiline:
            absolute_end_ops.add(pmod.AT_END)
        end_string = getattr(pmod, 'AT_END_STRING', None)
        if end_string is not None:
            absolute_end_ops.add(end_string)
        return av in absolute_end_ops
    if op == pmod.SUBPATTERN:
        return any(_rg04_zero_width_end_anchor(pmod, child, multiline)
                   for child in av[-1])
    if op == pmod.BRANCH:
        return any(_rg04_zero_width_end_anchor(pmod, child, multiline)
                   for branch in av[1] for child in branch)
    return False
def _rg04_suffix_end_anchored(pmod, suffix, outer_anchored: bool,
                              multiline: bool = False) -> bool:
    anchored = outer_anchored
    for item in suffix:
        if _se30_may_consume(pmod, item):
            return False
        if _rg04_zero_width_end_anchor(pmod, item, multiline):
            anchored = True
    return anchored
def _rg04_parsed_greedy_dotall(pattern: str,
                                external_flags: int) -> bool | None:
    pmod = _se30_parser_module()
    if pmod is None:
        return None
    try:
        parsed = pmod.parse(pattern, external_flags)
    except Exception as _parse_err:  # noqa: BLE001
        _log.debug("RG-04 模式解析失败，回退词法扫描: %s", _parse_err)
        return None
    def visit(seq, dotall: bool, multiline: bool,
              end_anchored: bool = False) -> bool:
        for idx, (op, av) in enumerate(seq):
            suffix_anchored = _rg04_suffix_end_anchored(
                pmod, seq[idx + 1:], end_anchored, multiline)
            if op == pmod.SUBPATTERN:
                added = av[1] or 0
                removed = av[2] or 0
                flags = ((re.DOTALL if dotall else 0)
                         | (re.MULTILINE if multiline else 0) | added)
                active_flags = flags & ~removed
                if visit(av[-1], bool(active_flags & re.DOTALL),
                         bool(active_flags & re.MULTILINE), suffix_anchored):
                    return True
            elif op in (pmod.MAX_REPEAT, pmod.MIN_REPEAT):
                payload = list(av[2])
                if (op == pmod.MAX_REPEAT and dotall
                        and not suffix_anchored
                        and av[1] == pmod.MAXREPEAT and len(payload) == 1
                        and payload[0][0] == pmod.ANY):
                    return True
                if visit(payload, dotall, multiline):
                    return True
            elif op == pmod.BRANCH:
                if any(visit(branch, dotall, multiline, suffix_anchored)
                       for branch in av[1]):
                    return True
            elif op == pmod.GROUPREF_EXISTS:
                if any(visit(branch, dotall, multiline, suffix_anchored)
                       for branch in av[1:] if branch is not None):
                    return True
            elif (hasattr(pmod, 'ATOMIC_GROUP')
                  and op == pmod.ATOMIC_GROUP
                  and visit(av, dotall, multiline, suffix_anchored)):
                return True
        return False
    return visit(list(parsed), bool(parsed.state.flags & re.DOTALL),
                 bool(parsed.state.flags & re.MULTILINE))
def _rg04_is_violation(pattern: str, node: ast.Call, member: str | None,
                       re_names: set, bare_origins: dict) -> bool:
    external_flags, flags_complete = _rg04_external_flags(
        node, member, re_names, bare_origins)
    if not (external_flags & re.DOTALL or _rg04_has_inline_dotall(pattern)):
        return False
    if not flags_complete:
        candidates = [_rg04_parsed_greedy_dotall(pattern, external_flags | extra)
                      for extra in (0, re.MULTILINE, re.VERBOSE,
                                    re.MULTILINE | re.VERBOSE)]
        if any(result is None for result in candidates):
            return _regex_has_greedy_dotstar(pattern)
        return all(candidates)
    parsed_result = _rg04_parsed_greedy_dotall(pattern, external_flags)
    if parsed_result is not None:
        return parsed_result
    return _regex_has_greedy_dotstar(pattern)
_RG04_RULE = {
    "rule_id": "RG-04", "severity": "P3", "dimension": "regex_safety",
    "rule_ref": "regex-greedy-trap"}
def _rg04_build_ast_issue(node: ast.Call, source: Any, filepath: Any) -> dict:
    return build_ast_issue(
        _RG04_RULE, source, filepath, node,
        "正则使用贪婪 .* 可能过度匹配",
        "正则中使用贪婪 .* 可能跨越多行匹配过多内容。"
        "如果意图是匹配最短内容，应使用 .*?。",
        get_fix_guidance("RG-04"))
def _se29_dict_has_dynamic_unpack(value: ast.Dict) -> bool:
    return any(
        key is None and (
            not isinstance(item, ast.Dict)
            or _se29_dict_has_dynamic_unpack(item))
        for key, item in zip(value.keys, value.values, strict=False))
def _has_dynamic_kw_unpack(node: ast.Call) -> bool:
    return any(
        kw.arg is None and (
            not isinstance(kw.value, ast.Dict)
            or _se29_dict_has_dynamic_unpack(kw.value))
        for kw in node.keywords)
_HTTP_METHOD_NAMES = frozenset({
    'get', 'post', 'put', 'delete', 'patch', 'head', 'options',
    'request', 'stream', 'ws_connect',
})
def _se23_method_name(node: ast.Call) -> str:
    if isinstance(node.func, ast.Attribute):
        return node.func.attr
    if isinstance(node.func, ast.Name):
        return node.func.id
    return ""
_SE23_MESSAGES: dict[str, str] = {
    "verify": 'SSL verification disabled',
    "ssl": 'SSL verification disabled (aiohttp ssl=False)',
}
def _se23_ssl_disabled(value: ast.AST) -> bool:
    if isinstance(value, ast.Constant) and value.value is None:
        return False
    return _literal_truth_value(value) is False
def _se23_scan_ssl_keywords(node: ast.Call, source_lines: Any,
                            filepath: Any, issues: list) -> None:
    for name, value in _iter_static_call_keywords(node):
        _message = _SE23_MESSAGES.get(name)
        if _message is None:
            continue
        if not _se23_ssl_disabled(value):
            continue
        issues.append(_se_df(
            'SE-23', 'P1', node.lineno, _message,
            filepath, source_lines, title=_message,
            rule_ref='OWASP Top 10 / CWE-295 / Bandit B501'))
def check_SE23(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        if _se23_method_name(node) not in _HTTP_METHOD_NAMES:
            continue
        _se23_scan_ssl_keywords(node, source_lines, filepath, issues)
    return issues
def _se29_ua_in_dict(value: ast.Dict) -> bool:
    for key, item in zip(value.keys, value.values, strict=False):
        if key is None:
            if (not isinstance(item, ast.Dict)
                    or _se29_ua_in_dict(item)):
                return True
        elif (isinstance(key, ast.Constant) and isinstance(key.value, str)
              and key.value.lower() == 'user-agent'):
            return True
    return False
def _se29_ua_in_pairs(value: ast.AST) -> bool:
    for elt in value.elts:
        if not (isinstance(elt, (ast.Tuple, ast.List)) and len(elt.elts) == 2):
            return True
        key = elt.elts[0]
        if not (isinstance(key, ast.Constant)
                and isinstance(key.value, str)):
            return True
        if key.value.lower() == 'user-agent':
            return True
    return False
def _headers_value_has_ua(value: Any) -> bool:
    if isinstance(value, ast.Dict):
        return _se29_ua_in_dict(value)
    if isinstance(value, (ast.List, ast.Tuple)):
        return _se29_ua_in_pairs(value)
    return not isinstance(value, ast.Constant)
def _se29_call_has_user_agent(call_node: ast.Call) -> bool:
    return any(
        name == 'headers' and _headers_value_has_ua(value)
        for name, value in _iter_static_call_keywords(call_node))
def _se29_finding(node: ast.Call, source_lines: Any,
                  filepath: Any) -> DiagnoseFinding:
    _title = 'requests请求未设置User-Agent header'
    return _se_df(
        'SE-29', 'P3', node.lineno, _title,
        filepath, source_lines, title=_title,
        rule_ref='CWE-693 / requests 文档')
def check_SE29(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    targets = qualified_and_bare_call_targets(
        tree, 'requests', _HTTP_METHOD_NAMES)
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        if dotted_name(node.func) not in targets:
            continue
        if _se29_call_has_user_agent(node):
            continue
        if (_has_dynamic_kw_unpack(node)
                and not any(kw.arg == 'headers' for kw in node.keywords)):
            continue
        issues.append(_se29_finding(node, source_lines, filepath))
    return issues
_LOCAL_HOST_ALIASES = ("localhost", "127.0.0.1", "0.0.0.0", "[::1]")
def _se33_url_host(url: str) -> str:
    url = url.replace("\\", "/")
    netloc = url[len("http://"):].split("#", 1)[0]
    netloc = netloc.split("?", 1)[0].split("/", 1)[0]
    host = netloc.rsplit("@", 1)[-1]
    if host.startswith("["):
        _close = host.find("]")
        if _close != -1 and host[_close + 1:_close + 2] == ":":
            host = host[:_close + 1]
    elif ":" in host:
        host = host.rsplit(":", 1)[0]
    return host
_DOCSTRING_OWNERS = (ast.Module, ast.ClassDef, ast.FunctionDef,
                     ast.AsyncFunctionDef)
def _se33_docstring_nodes(tree: Any) -> set[int]:
    if tree is None:
        return set()
    ids: set[int] = set()
    for node in iter_nodes(tree, None):
        if not isinstance(node, _DOCSTRING_OWNERS):
            continue
        _doc_id = _docstring_constant_id(node)
        if _doc_id is not None:
            ids.add(_doc_id)
    return ids
def _docstring_constant_id(owner: ast.AST) -> int | None:
    body = getattr(owner, "body", None)
    if not isinstance(body, list) or not body:
        return None
    first = body[0]
    return id(first.value) if is_docstring_stmt(first) else None
_INSECURE_SCHEME_PREFIX = "http://"
def _se33_normalize_scheme(url: str) -> str:
    head, sep, rest = url.strip().partition("://")
    if not sep:
        return url
    return head.lower() + sep + rest
def _se33_is_insecure_url(node: ast.AST, doc_ids: set[int]) -> bool:
    if not (isinstance(node, ast.Constant) and isinstance(node.value, str)):
        return False
    if id(node) in doc_ids:
        return False
    url = _se33_normalize_scheme(node.value)
    if not url.startswith(_INSECURE_SCHEME_PREFIX):
        return False
    host = _se33_url_host(url).lower()
    return bool(host) and host not in _LOCAL_HOST_ALIASES
def _se33_finding(node: ast.AST, source_lines: Any,
                  filepath: Any) -> DiagnoseFinding:
    _title = 'Uses insecure HTTP URL'
    return _se_df(
        'SE-33', 'P1', node.lineno, _title,
        filepath, source_lines, title=_title,
        rule_ref='OWASP A02:2021 / CWE-319')
def check_SE33(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    _doc_ids = _se33_docstring_nodes(tree)
    for node in iter_nodes(tree, index):
        if _se33_is_insecure_url(node, _doc_ids):
            issues.append(_se33_finding(node, source_lines, filepath))
    return issues
def _se34_finding(node: ast.AST, source_lines: Any,
                  filepath: Any) -> DiagnoseFinding:
    _title = 'telnetlib使用明文传输,存在凭据泄露风险'
    return _se_df(
        'SE-34', 'P0', node.lineno, _title,
        filepath, source_lines, title=_title,
        rule_ref='OWASP A02:2021 / CWE-319 / PEP 594')
def _se34_is_telnet_import(node: ast.AST) -> bool:
    if isinstance(node, ast.Import):
        return any(alias.name == 'telnetlib' for alias in node.names)
    if isinstance(node, ast.ImportFrom):
        return node.module == 'telnetlib' and not node.level
    return False
def check_SE34(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    for node in iter_nodes(tree, index):
        if _se34_is_telnet_import(node):
            issues.append(_se34_finding(node, source_lines, filepath))
    return issues
_SE31_DEPRECATED_FUNCS = (
    'ARC4', 'Blowfish', 'CAST5', 'DES', 'IDEA', 'RC4', 'SEED', 'TripleDES',
)
_SE31_CIPHER_MODULE = 'cryptography.hazmat.primitives.ciphers'
_SE31_ALGORITHM_MODULES = (
    f'{_SE31_CIPHER_MODULE}.algorithms',
    'cryptography.hazmat.decrepit.ciphers.algorithms',
)
_SE31_MODE_MODULE = f'{_SE31_CIPHER_MODULE}.modes'
def _se31_call_targets(tree: ast.AST) -> dict[str, str]:
    if tree is None:
        return {}
    targets: dict[str, str] = {}
    for module in (*_SE31_ALGORITHM_MODULES, _SE31_MODE_MODULE):
        members = (_SE31_DEPRECATED_FUNCS if module in _SE31_ALGORITHM_MODULES
                   else ('ECB',))
        module_targets, origins = qualified_and_bare_call_targets_detailed(
            tree, module, members)
        for target in module_targets:
            targets[target] = origins.get(
                target, target.rsplit('.', 1)[-1])
    for node in iter_nodes(tree, None):
        if not (isinstance(node, ast.ImportFrom) and node.level == 0
                and node.module == _SE31_CIPHER_MODULE):
            continue
        for alias in node.names:
            bound = alias.asname or alias.name
            if alias.name == 'algorithms':
                targets.update({f'{bound}.{name}': name
                                for name in _SE31_DEPRECATED_FUNCS})
            elif alias.name == 'modes':
                targets[f'{bound}.ECB'] = 'ECB'
    return targets
def _se31_deprecated_issue(node: ast.Call, alg_name: str, filepath: Any,
                           source_lines: Any) -> DiagnoseFinding:
    return _se_df(
        'SE-31', 'P2', node.lineno,
        f"使用cryptography弃用API: {alg_name}", filepath, source_lines,
        title='使用已弃用的密码算法',
        rule_ref='CWE-477 / cryptography deprecation guide',
        suggestion='根因: 弃用API可能存在已知漏洞或不安全默认值。该问题属于安全类别。\n修复策略: 使用AES-256-GCM或ChaCha20-Poly1305替代弱加密算法\n参考标准: CWE-477 / cryptography deprecation guide')
def _se31_ecb_issue(node: ast.Call, filepath: Any,
                    source_lines: Any) -> DiagnoseFinding:
    return _se_df(
        'SE-31', 'P2', node.lineno,
        '使用ECB模式,不安全(相同明文产生相同密文)',
        filepath, source_lines,
        title='ECB 模式不安全',
        rule_ref='CWE-327 / cryptography 文档',
        suggestion='根因: ECB模式不提供语义安全性,相同明文块产生相同密文块。该问题属于安全类别。\n修复策略: 使用GCM或CBC模式替代ECB\n参考标准: CWE-327 / cryptography文档')
def _se31_issue_for(node: ast.Call, filepath: Any,
                    source_lines: Any, member: str) -> DiagnoseFinding | None:
    if member in _SE31_DEPRECATED_FUNCS:
        return _se31_deprecated_issue(
            node, member, filepath, source_lines)
    if member == 'ECB':
        return _se31_ecb_issue(node, filepath, source_lines)
    return None
def check_SE31(tree: Any, source_lines: Any, filepath: Any, index: list | None=None) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    targets = _se31_call_targets(tree)
    for node in iter_nodes(tree, index):
        if not isinstance(node, ast.Call):
            continue
        member = targets.get(get_call_name(node))
        if member is None:
            continue
        issue = _se31_issue_for(node, filepath, source_lines, member)
        if issue is not None:
            issues.append(issue)
    return issues
def wiring_declarations() -> dict:
    return {
        "catalogs": {
            "sec_registry_fns": {
                'CV01B': check_CV01b, 'B108': check_B108,
                'SE04': check_SE04, 'SE07': check_SE07,
                'SE09': check_SE09, 'SE11': check_SE11,
                'SE12': check_SE12, 'SE13': check_SE13,
                'SE14': check_SE14, 'SE15': check_SE15,
                'SE16': check_SE16, 'SE17': check_SE17,
                'SE19': check_SE19, 'SE23': check_SE23,
                'SE25': check_SE25, 'SE26': check_SE26,
                'SE29': check_SE29, 'SE30': check_SE30,
                'SE31': check_SE31, 'SE33': check_SE33, 'SE34': check_SE34,
            },
            "se_checks": {
                'SE04': check_SE04, 'SE07': check_SE07,
                'SE09': check_SE09, 'SE11': check_SE11,
                'SE12': check_SE12, 'SE13': check_SE13,
                'SE14': check_SE14, 'SE15': check_SE15,
                'SE16': check_SE16, 'SE17': check_SE17,
                'SE18': check_SE18, 'SE19': check_SE19,
                'SE23': check_SE23, 'SE24': check_SE24,
                'SE25': check_SE25, 'SE26': check_SE26,
                'SE29': check_SE29, 'SE30': check_SE30,
                'SE31': check_SE31, 'SE33': check_SE33, 'SE34': check_SE34,
            },
            "rule_bindings": {'RG-02': check_RG02, 'RG-04': check_RG04},
        },
    }

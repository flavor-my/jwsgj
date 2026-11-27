from __future__ import annotations

import ast
import re
from collections.abc import Iterable
from dataclasses import dataclass, field
from typing import ClassVar

from jwsgj.build_preintervention import (
    _dimension_entry,
    _DimensionSpec,
    _walk_loop_scope,
)
from jwsgj.diag_shared_ast_nodes import (
    TRY_NODE_TYPES,
    _type_checking_guard_node_polarities,
    calc_nesting,
    is_dataclass_decorator,
    is_mutable_default,
    is_shell_true_keyword,
    iter_arg_nodes,
    iter_own_scope,
    module_postpones_annotations,
)
from jwsgj.diag_shared_ast_views import (
    LexicalScopeTable,
    call_head_is_shadowed,
    call_scope_map,
    collect_lexical_scope_table,
    scope_import_tables,
    scope_node_bound_names,
    shadowed_open_call_ids,
    tree_nodes,
    unparse_or_type_name,
)
from jwsgj.diag_shared_source_core import (
    FRAME_BOUNDARY_NODES,
    source_line_count,
)
from jwsgj.diag_shared_source_scan import (
    comment_only_spans,
)
from jwsgj.diag_types_defs import (
    ArchitectureSuggestion,
    PreCheckItem,
    make_detail,
    normalize_text_param,
    type_error_precheck,
)
from jwsgj.diag_types_normalize import normalize_input
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
    RULE_HARDCODED_SECRET,
    SEVERITY_BLOCKING,
    SEVERITY_INFO,
    SEVERITY_WARNING,
    register_check_provider,
    register_review_provider,
)
from jwsgj.log_config import get_module_logger, log_swallowed

__all__ = [
    "PRECHECK_LONG_FUNCTION_LINES",
    "ArchitectureAdvisor",
    "CodeQualityPrecheck",
    "check_concurrency_safety",
    "check_guard_injection",
    "check_performance_baseline",
    "check_security_design",
]
logger = get_module_logger(__name__, __file__)
logger.info("preintervention_engines 已加载（绑定感知维度 + 质量预检 + 架构建议）")
_OS_DANGEROUS_ATTRS = frozenset({
    "system", "popen",
    "spawnl", "spawnle", "spawnlp", "spawnlpe",
    "spawnv", "spawnve", "spawnvp", "spawnvpe",
    "posix_spawn", "posix_spawnp",
})
_SUBPROCESS_CALL_ATTRS = frozenset({
    "run", "call", "check_call", "check_output",
    "Popen", "getoutput", "getstatusoutput",
})
_OPEN_FUNCS = frozenset({"open"})
_OS_FILE_OPS = frozenset({
    "open", "remove", "unlink", "rmdir", "rename", "replace", "mkdir",
    "makedirs",
})
_SHUTIL_FILE_OPS = frozenset({
    "copyfile", "copymode", "copystat", "copy", "copy2", "copytree",
    "move", "rmtree", "chown", "make_archive", "unpack_archive",
})
_DANGEROUS_DYNAMIC_CALLS = frozenset({"eval", "exec", "compile", "__import__"})
_PICKLE_FUNCS = frozenset({"load", "loads"})
_LOCK_NAMES = frozenset({"Lock", "RLock"})
_PATHLIB_CONSTRUCTORS = frozenset({
    "Path", "PurePath", "PosixPath", "WindowsPath"})
_THREAD_CREATION_APIS = frozenset({"Thread", "Timer"})
_PATHLIB_WRITE_OPS = frozenset({
    "write_text", "write_bytes", "unlink", "mkdir", "rmdir", "touch",
    "rename", "replace", "symlink_to", "hardlink_to", "link_to",
    "chmod", "lchmod",
})
@dataclass(frozen=True)
class _Rule:
    issue: str
    rule_id: str
    confidence: float
_RULE_DYNAMIC_EXEC = _Rule("dangerous_function", "SE-01", 0.95)
_RULE_DANGEROUS_SYSTEM = _Rule("dangerous_call", "SE-02", 0.90)
_RULE_SHELL_INJECTION = _Rule("shell_injection", "SE-08", 0.90)
_RULE_PICKLE = _Rule("pickle_usage", "SE-04", 0.92)
_RULE_HARDCODED_SECRET = _Rule(RULE_HARDCODED_SECRET, "SE-03", 0.80)
_RULE_AWS_KEY = _Rule("aws_key", "SE-03", 0.80)
_RULE_IO_IN_LOOP = _Rule("io_in_loop", "PERF-01", 0.75)
_RULE_MUTABLE_GLOBAL = _Rule("mutable_global", "PERF-05", 0.70)
_RULE_GLOBAL_DECL = _Rule("global_in_function", "CONC-01", 0.70)
_RULE_THREADING_NO_LOCK = _Rule("threading_without_lock", "CONC-02", 0.65)
_RULE_UNGUARDED_OPEN = _Rule("unguarded_open", "GUARD-01", 0.75)
_RULE_UNGUARDED_SYSTEM = _Rule("unguarded_system_call", "GUARD-02", 0.85)
_RULE_MISSING_PATH_GUARD = _Rule("missing_path_guard", "GUARD-03", 0.70)
# 边界用 ASCII 显式环视而非 `\b`：str 模式下 `\b` 按 Unicode 判定，
# `db_password`/`配置secret` 中关键字前是 `_`/中文（均属 \w），`\b` 不成立而漏报；
# 与 skill_scan_kernels.SENSITIVE_PATTERNS 的 `(?<![A-Za-z0-9])` 口径对齐。
_SECRET_PATTERNS = (
    (re.compile(r'(?i)(?<![A-Za-z0-9])(api_key|secret|password|token|access_key)\s*'
                r'(?::\s*[^=\n]+)?=\s*["\'][^"\']{8,}'),
     _RULE_HARDCODED_SECRET),
    (re.compile(r'(?i)["\'](?:api_key|secret|password|token|access_key)'
                r'["\']\s*:\s*["\'][^"\']{8,}'),
     _RULE_HARDCODED_SECRET),
    (re.compile(r'(?i)\b(AKIA|AGPA|AIDA|AROA|AIPA|ANPA|ANVA)\w{16}\b'),
     _RULE_AWS_KEY),
)
class _FindingSink:
    __slots__ = ("details", "suggestions")
    def __init__(self, details: list | None = None,
                 suggestions: list | None = None) -> None:
        self.details: list[dict] = [] if details is None else details
        self.suggestions: list[str] = [] if suggestions is None else suggestions
    def emit(self, rule: _Rule, line: int | None, message: str,
             **extra) -> None:
        locator = "module" if line is None else f"line:{line}"
        self.details.append(make_detail(
            rule.issue, rule.rule_id, locator,
            confidence=rule.confidence, **extra))
        self.suggestions.append(
            message if line is None else f"L{line}: {message}")
@dataclass(frozen=True)
class _ImportBindings:
    builtins_modules: frozenset[str]
    open_family_modules: frozenset[str]
    pathlib_modules: frozenset[str]
    pathlib_funcs: frozenset[str]
    dynamic_funcs: frozenset[str]
    pickle_modules: frozenset[str]
    pickle_funcs: frozenset[str]
    system_funcs: frozenset[str]
    threading_modules: frozenset[str]
    threading_funcs: frozenset[str]
    os_recv_names: frozenset[str]
    shutil_recv_names: frozenset[str]
    subprocess_modules: frozenset[str]
    subprocess_funcs: frozenset[str]
    open_aliases: frozenset[str]
    fileop_funcs: frozenset[str]
    lock_funcs: frozenset[str]
@dataclass
class _BindingLedger:
    builtins_modules: set[str] = field(default_factory=lambda: {"builtins"})
    open_family_modules: set[str] = field(
        default_factory=lambda: {"io", "codecs"})
    pathlib_modules: set[str] = field(default_factory=lambda: {"pathlib"})
    pathlib_funcs: set[str] = field(
        default_factory=lambda: set(_PATHLIB_CONSTRUCTORS))
    dynamic_funcs: set[str] = field(
        default_factory=lambda: set(_DANGEROUS_DYNAMIC_CALLS))
    pickle_modules: set[str] = field(default_factory=lambda: {"pickle"})
    pickle_funcs: set[str] = field(default_factory=set)
    system_funcs: set[str] = field(default_factory=set)
    threading_modules: set[str] = field(default_factory=lambda: {"threading"})
    threading_funcs: set[str] = field(default_factory=set)
    os_recv_names: set[str] = field(default_factory=lambda: {"os"})
    shutil_recv_names: set[str] = field(default_factory=lambda: {"shutil"})
    subprocess_modules: set[str] = field(default_factory=lambda: {"subprocess"})
    subprocess_funcs: set[str] = field(default_factory=set)
    open_aliases: set[str] = field(default_factory=lambda: {"open"})
    fileop_funcs: set[str] = field(default_factory=set)
    lock_funcs: set[str] = field(default_factory=set)
    def freeze(self) -> _ImportBindings:
        return _ImportBindings(
            builtins_modules=frozenset(self.builtins_modules),
            open_family_modules=frozenset(self.open_family_modules),
            pathlib_modules=frozenset(self.pathlib_modules),
            pathlib_funcs=frozenset(self.pathlib_funcs),
            dynamic_funcs=frozenset(self.dynamic_funcs),
            pickle_modules=frozenset(self.pickle_modules),
            pickle_funcs=frozenset(self.pickle_funcs),
            system_funcs=frozenset(self.system_funcs),
            threading_modules=frozenset(self.threading_modules),
            threading_funcs=frozenset(self.threading_funcs),
            os_recv_names=frozenset(self.os_recv_names),
            shutil_recv_names=frozenset(self.shutil_recv_names),
            subprocess_modules=frozenset(self.subprocess_modules),
            subprocess_funcs=frozenset(self.subprocess_funcs),
            open_aliases=frozenset(self.open_aliases),
            fileop_funcs=frozenset(self.fileop_funcs),
            lock_funcs=frozenset(self.lock_funcs),
        )
def _aliased_names(
        names: Iterable[ast.alias],
        wanted: frozenset[str] | tuple[str, ...] | None = None,
        excluded: frozenset[str] = frozenset()) -> set[str]:
    bound: set[str] = set()
    for alias in names:
        if alias.name == "*" or alias.name in excluded:
            continue
        if wanted is None or alias.name in wanted:
            bound.add(alias.asname or alias.name)
    return bound
_IMPORT_RECEIVER_FIELDS = {
    "builtins": "builtins_modules",
    "io": "open_family_modules",
    "codecs": "open_family_modules",
    "os": "os_recv_names",
    "pickle": "pickle_modules",
    "pathlib": "pathlib_modules",
    "shutil": "shutil_recv_names",
    "subprocess": "subprocess_modules",
}
_DEFAULT_MODULE_RECEIVERS = frozenset(_IMPORT_RECEIVER_FIELDS) | {"threading"}
def _bind_import_alias(alias: ast.alias, ledger: _BindingLedger) -> None:
    root = alias.name.split(".")[0]
    bound = alias.asname or root
    root_binding = alias.asname is None or alias.name == root
    if _is_threading_module(alias.name):
        if root_binding:
            ledger.threading_modules.add(bound)
        return
    if not root_binding:
        return
    receiver_field = _IMPORT_RECEIVER_FIELDS.get(root)
    if receiver_field is not None:
        getattr(ledger, receiver_field).add(bound)
def _bind_os_family(alias: ast.alias, module: str,
                    ledger: _BindingLedger) -> None:
    if module == "os":
        ledger.system_funcs.update(
            _aliased_names([alias], _OS_DANGEROUS_ATTRS))
        ledger.fileop_funcs.update(_aliased_names([alias], _OS_FILE_OPS))
        return
    ledger.subprocess_funcs.update(
        _aliased_names([alias], _SUBPROCESS_CALL_ATTRS))
_FROM_IMPORT_FIELD_SPECS: dict[str, tuple[tuple[str, frozenset[str]], ...]] = {
    "pickle": (("pickle_funcs", _PICKLE_FUNCS),),
    "builtins": (
        ("dynamic_funcs", _DANGEROUS_DYNAMIC_CALLS),
        ("open_aliases", _OPEN_FUNCS),
    ),
    "io": (("open_aliases", _OPEN_FUNCS),),
    "codecs": (("open_aliases", _OPEN_FUNCS),),
    "pathlib": (("pathlib_funcs", _PATHLIB_CONSTRUCTORS),),
}
def _bind_from_import_alias(node: ast.ImportFrom, alias: ast.alias,
                            ledger: _BindingLedger) -> None:
    module = node.module or ""
    if node.level or not module:
        return
    if module in ("os", "subprocess"):
        _bind_os_family(alias, module, ledger)
        return
    if _is_threading_module(module):
        bound = alias.asname or alias.name
        if alias.name in _THREAD_CREATION_APIS:
            ledger.threading_funcs.add(bound)
        if alias.name in _LOCK_NAMES:
            ledger.lock_funcs.add(bound)
        return
    if module == "shutil":
        ledger.fileop_funcs.update(
            _aliased_names([alias], _SHUTIL_FILE_OPS))
        return
    for field_name, wanted in _FROM_IMPORT_FIELD_SPECS.get(module, ()):
        getattr(ledger, field_name).update(
            _aliased_names([alias], wanted))
def _visible_scope_chain(scope: ast.AST, parent: dict):
    direct = scope
    while scope is not None:
        if not (isinstance(scope, ast.ClassDef) and scope is not direct):
            yield scope
        scope = parent.get(scope)
_BranchAlternative = tuple[ast.AST, int]
_ImportAlternative = tuple[_BranchAlternative, ...] | None
def _import_branch_map(node: ast.AST) -> dict[int, _BranchAlternative]:
    branches: dict[int, _BranchAlternative] = {}
    if isinstance(node, ast.If):
        branches.update({id(child): (node, 0) for child in node.body})
        branches.update({id(child): (node, 1) for child in node.orelse})
    elif isinstance(node, TRY_NODE_TYPES):
        branches.update({
            id(child): (node, 0) for child in [*node.body, *node.orelse]})
        for index, handler in enumerate(node.handlers, 1):
            branches[id(handler)] = (node, index)
    elif isinstance(node, ast.Match):
        branches.update({
            id(case): (node, index)
            for index, case in enumerate(node.cases)})
    elif isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
        branches.update({id(child): (node, 0) for child in node.body})
        branches.update({id(child): (node, 1) for child in node.orelse})
    return branches
def _collect_scoped_import_statements(tree: ast.Module) -> dict:
    scoped: dict[ast.AST, list[tuple[
        ast.Import | ast.ImportFrom, _ImportAlternative]]] = {}
    stack: list[tuple[ast.AST, ast.AST, _ImportAlternative]] = [
        (child, tree, None)
        for child in reversed(list(ast.iter_child_nodes(tree)))]
    while stack:
        node, scope, alternative = stack.pop()
        if isinstance(node, FRAME_BOUNDARY_NODES):
            scope = node
            alternative = None
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            scoped.setdefault(scope, []).append((node, alternative))
            continue
        branches = _import_branch_map(node)
        for child in reversed(list(ast.iter_child_nodes(node))):
            branch = branches.get(id(child))
            child_alternative = alternative
            if branch is not None:
                child_alternative = ((branch,) if alternative is None
                                     else (*alternative, branch))
            stack.append((child, scope, child_alternative))
    return scoped
def _match_has_irrefutable_case(node: ast.Match) -> bool:
    return any(
        case.guard is None
        and isinstance(case.pattern, ast.MatchAs)
        and case.pattern.pattern is None
        for case in node.cases)
def _conditional_branch_count(condition: ast.AST) -> int:
    if isinstance(condition, ast.If):
        return 2
    if isinstance(condition, ast.Match):
        return (len(condition.cases) if _match_has_irrefutable_case(condition)
                else len(condition.cases) + 1)
    if isinstance(condition, (ast.For, ast.AsyncFor, ast.While)):
        return 3
    return 1 + len(condition.handlers)
def _merge_branch_variant(variants: dict, alternative: _ImportAlternative,
                          value) -> _ImportAlternative:
    if alternative is None:
        variants.clear()
        variants[None] = value
        return None
    variants[alternative] = value
    parent = alternative[:-1]
    condition = alternative[-1][0]
    depth = len(parent)
    covered_branches = {
        key[depth][1] for key in variants
        if key is not None and len(key) == depth + 1
        and key[:depth] == parent and key[depth][0] is condition}
    if len(covered_branches) < _conditional_branch_count(condition):
        return alternative
    covered_values = [
        variants[key] for key in tuple(variants)
        if key is not None and len(key) == depth + 1
        and key[:depth] == parent and key[depth][0] is condition]
    merged_value = (any(covered_values)
                    if all(isinstance(item, bool) for item in covered_values)
                    else [binding for group in covered_values for binding in group])
    for key in tuple(variants):
        if key is not None and key[:depth] == parent:
            del variants[key]
    if not parent:
        variants.clear()
        variants[None] = merged_value
        return None
    variants[parent] = merged_value
    return parent
def _position_in_node(position: tuple[int, int], node: ast.AST) -> bool:
    end = (getattr(node, "end_lineno", None),
           getattr(node, "end_col_offset", None))
    if end[0] is None or end[1] is None:
        return False
    return ((node.lineno, node.col_offset) <= position <= end)
def _conditional_branch_nodes(condition: ast.AST, index: int) -> list[ast.AST]:
    if isinstance(condition, ast.If):
        return condition.body if index == 0 else condition.orelse
    if isinstance(condition, ast.Match):
        if index >= len(condition.cases):
            return []
        case = condition.cases[index]
        return [case.pattern, *([case.guard] if case.guard is not None else []),
                *case.body]
    if isinstance(condition, TRY_NODE_TYPES):
        if index == 0:
            return [*condition.body, *condition.orelse]
        return ([condition.handlers[index - 1]]
                if index <= len(condition.handlers) else [])
    if isinstance(condition, (ast.For, ast.AsyncFor, ast.While)):
        return condition.body if index == 0 else condition.orelse
    return []
def _branch_at_position(condition: ast.AST,
                        position: tuple[int, int]) -> int | None:
    for index in range(_conditional_branch_count(condition)):
        if any(_position_in_node(position, node)
               for node in _conditional_branch_nodes(condition, index)):
            return index
    return None
def _alternative_relation(alternative: _ImportAlternative,
                          position: tuple[int, int]) -> str:
    if alternative is None:
        return "guaranteed"
    for condition, branch in alternative:
        if not _position_in_node(position, condition):
            return "possible"
        current = _branch_at_position(condition, position)
        if current is None:
            return "possible"
        if current == branch:
            continue
        if ((isinstance(condition, TRY_NODE_TYPES)
             and branch == 0 < current)
                or (isinstance(condition, (ast.For, ast.AsyncFor, ast.While))
                    and branch == 0 and current == 1)):
            return "possible"
        return "impossible"
    return "guaranteed"
def _merge_variant_at_position(variants: dict,
                               alternative: _ImportAlternative, value,
                               position: tuple[int, int] | None) -> bool:
    """按位置合并分支变体，返回该事件是否对当前位置生效。"""
    if position is None:
        _merge_branch_variant(variants, alternative, value)
        return True
    relation = _alternative_relation(alternative, position)
    if relation == "impossible":
        return False
    if relation == "guaranteed":
        variants.clear()
        variants[None] = value
        return True
    merged = _merge_branch_variant(variants, alternative, value)
    if (merged is not None
            and _alternative_relation(merged, position) == "guaranteed"):
        merged_value = variants[merged]
        variants.clear()
        variants[None] = merged_value
    return True
_DELAYED_IMPORT_SCOPE_NODES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
_EAGER_IMPORT_CUTOFF_NODES = (
    ast.ClassDef, ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
def _outer_import_cutoff(scope: ast.AST, current: ast.AST,
                         parent: dict) -> tuple[int, int] | None:
    cutoff = None
    node = scope
    while node is not current:
        if isinstance(node, _DELAYED_IMPORT_SCOPE_NODES):
            return None
        if isinstance(node, _EAGER_IMPORT_CUTOFF_NODES):
            cutoff = node
        node = parent.get(node)
        if node is None:
            return None
    if cutoff is None:
        return None
    return cutoff.lineno, cutoff.col_offset
class _ScopedImportResolver:
    __slots__ = ("_cache", "_imports", "_parent", "_tree")
    def __init__(self, tree: ast.Module, shadow: LexicalScopeTable) -> None:
        self._tree = tree
        self._parent = shadow.parent
        self._imports = _collect_scoped_import_statements(tree)
        self._cache: dict[
            tuple[ast.AST, tuple[int, int] | None], _ImportBindings] = {}
    def for_scope(self, scope: ast.AST | None,
                  position: tuple[int, int] | None = None) -> _ImportBindings:
        if scope is None:
            scope = self._tree
        cache_key = (scope, position)
        cached = self._cache.get(cache_key)
        if cached is not None:
            return cached
        ledger = _BindingLedger()
        visible = list(_visible_scope_chain(scope, self._parent))
        effective: dict[str, dict[_ImportAlternative, list[tuple[
            ast.Import | ast.ImportFrom, ast.alias]] | None]] = {}
        for current in reversed(visible):
            cutoff = (position if current is scope else
                      _outer_import_cutoff(scope, current, self._parent))
            for node, alternative in self._imports.get(current, ()):
                if (cutoff is not None
                        and (node.lineno, node.col_offset) >= cutoff):
                    continue
                for alias in node.names:
                    if isinstance(node, ast.ImportFrom) and alias.name == "*":
                        continue
                    bound = (alias.asname or alias.name.split(".", 1)[0]
                             if isinstance(node, ast.Import)
                             else alias.asname or alias.name)
                    variants = effective.setdefault(bound, {None: None})
                    _merge_variant_at_position(
                        variants, alternative, [(node, alias)], position)
        for bound, variants in effective.items():
            if not (None in variants and variants[None] is None):
                for binding_names in vars(ledger).values():
                    binding_names.discard(bound)
        for variants in effective.values():
            for binding_group in variants.values():
                if binding_group is None:
                    continue
                for node, alias in binding_group:
                    if isinstance(node, ast.Import):
                        _bind_import_alias(alias, ledger)
                    else:
                        _bind_from_import_alias(node, alias, ledger)
        bindings = ledger.freeze()
        self._cache[cache_key] = bindings
        return bindings
    def for_call(self, node: ast.Call, scopes: dict[int, ast.AST]) -> _ImportBindings:
        return self.for_scope(
            scopes.get(id(node)), (node.lineno, node.col_offset))
def _is_threading_module(name: str) -> bool:
    return name == "threading" or name.startswith("threading.")
def _receiver_binds_module(func: ast.Attribute,
                           module_names: frozenset[str]) -> bool:
    return isinstance(func.value, ast.Name) and func.value.id in module_names
def _scan_dangerous_calls(tree: ast.AST, resolver: _ScopedImportResolver,
                          sink: _FindingSink,
                          shadow: LexicalScopeTable) -> bool:
    violated = False
    scopes = call_scope_map(shadow)
    imports = scope_import_tables(tree) if shadow.tree is not None else {}
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        if _call_head_shadowed(node, shadow, scopes, imports):
            continue
        bindings = resolver.for_call(node, scopes)
        if _check_dynamic_exec_call(node, bindings, sink):
            violated = True
        if _check_dangerous_system_call(node, bindings, sink):
            violated = True
        if _check_shell_true_injection(node, bindings, sink):
            violated = True
        if _is_pickle_call(node, bindings.pickle_modules,
                           bindings.pickle_funcs):
            sink.emit(_RULE_PICKLE, node.lineno,
                      "避免使用pickle反序列化不可信数据")
            violated = True
    return violated
def _check_dynamic_exec_call(node: ast.Call, bindings: _ImportBindings,
                             sink: _FindingSink) -> bool:
    func = node.func
    if (isinstance(func, ast.Name)
            and func.id in bindings.dynamic_funcs):
        label = func.id
    elif (isinstance(func, ast.Attribute)
          and isinstance(func.value, ast.Name)
          and func.value.id in bindings.builtins_modules
          and func.attr in _DANGEROUS_DYNAMIC_CALLS):
        label = f"{func.value.id}.{func.attr}"
    else:
        return False
    sink.emit(_RULE_DYNAMIC_EXEC, node.lineno,
              f"避免使用 {label}()", function=label)
    return True
def _check_dangerous_system_call(node: ast.Call, bindings: _ImportBindings,
                                 sink: _FindingSink) -> bool:
    func = node.func
    if (isinstance(func, ast.Attribute)
            and func.attr in _OS_DANGEROUS_ATTRS
            and _receiver_binds_module(func, bindings.os_recv_names)):
        label = f".{func.attr}"
    elif (isinstance(func, ast.Name)
            and func.id in bindings.system_funcs):
        label = func.id
    else:
        return False
    sink.emit(_RULE_DANGEROUS_SYSTEM, node.lineno,
              f"避免使用 {label}()", method=label.lstrip("."))
    return True
def _check_shell_true_injection(node: ast.Call, bindings: _ImportBindings,
                                sink: _FindingSink) -> bool:
    if not any(is_shell_true_keyword(kw) for kw in node.keywords):
        return False
    func = node.func
    if isinstance(func, ast.Attribute):
        label = func.attr
        flagged = (label in _SUBPROCESS_CALL_ATTRS
                   and _receiver_binds_module(func,
                                              bindings.subprocess_modules))
    elif isinstance(func, ast.Name):
        label = func.id
        flagged = label in bindings.subprocess_funcs
    else:
        return False
    if not flagged:
        return False
    sink.emit(_RULE_SHELL_INJECTION, node.lineno,
              f"避免使用 {label}(shell=True)", method=label)
    return True
def _is_pickle_call(node: ast.Call, pickle_mod_names: frozenset,
                    pickle_func_names: frozenset) -> bool:
    func = node.func
    return ((isinstance(func, ast.Attribute)
             and func.attr in _PICKLE_FUNCS
             and isinstance(func.value, ast.Name)
             and func.value.id in pickle_mod_names)
            or (isinstance(func, ast.Name)
                and func.id in pickle_func_names))
def _char_column(line: str, byte_col: int) -> int:
    return len(line.encode("utf-8")[:byte_col].decode("utf-8"))
_SOURCE_NEWLINE_RE = re.compile(r"\r\n|[\r\n]")
def _source_line_col(content: str, offset: int) -> tuple[int, int]:
    line_num = 1
    line_start = 0
    for matched in _SOURCE_NEWLINE_RE.finditer(content, 0, offset):
        line_num += 1
        line_start = matched.end()
    return line_num, offset - line_start
def _docstring_spans(content: str,
                     tree: ast.AST | None) -> dict[int, list[tuple[int, int]]]:
    spans: dict[int, list[tuple[int, int]]] = {}
    if tree is None:
        return spans
    lines = _SOURCE_NEWLINE_RE.split(content)
    for node in tree_nodes(tree):
        if not isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef,
                                 ast.AsyncFunctionDef)):
            continue
        if ast.get_docstring(node, clean=False) is None:
            continue
        first = node.body[0]
        end_line = first.end_lineno or first.lineno
        for line_num in range(first.lineno, end_line + 1):
            line = lines[line_num - 1] if line_num <= len(lines) else ""
            start_byte = first.col_offset if line_num == first.lineno else 0
            end_byte = (first.end_col_offset
                        if line_num == end_line
                        and first.end_col_offset is not None
                        else len(line.encode("utf-8")) + 1)
            spans.setdefault(line_num, []).append((
                _char_column(line, start_byte),
                _char_column(line, end_byte),
            ))
    return spans
def _position_in_spans(line: int, col: int,
                       spans: dict[int, list[tuple[int, int]]]) -> bool:
    return any(start <= col < end for start, end in spans.get(line, ()))
def _scan_hardcoded_secrets(content: str, sink: _FindingSink,
                           tree: ast.AST | None = None) -> bool:
    violated = False
    comment_spans = comment_only_spans(content) or {}
    doc_spans = _docstring_spans(content, tree)
    for pattern, rule in _SECRET_PATTERNS:
        for match in pattern.finditer(content):
            line_num, col = _source_line_col(content, match.start())
            if (_position_in_spans(line_num, col, doc_spans)
                    or _position_in_spans(line_num, col, comment_spans)):
                continue
            violated = True
            sink.emit(rule, line_num, "检测到疑似硬编码密钥")
    return violated
def _scan_security_design(tree: ast.AST, content: str, details: list, suggestions: list) -> bool:
    sink = _FindingSink(details, suggestions)
    shadow = collect_lexical_scope_table(tree)
    resolver = _ScopedImportResolver(tree, shadow)
    violated_calls = _scan_dangerous_calls(tree, resolver, sink, shadow)
    violated_secrets = _scan_hardcoded_secrets(content, sink, tree)
    return not (violated_calls or violated_secrets)
_SECURITY_DESIGN = _DimensionSpec("security_design_check", "安全设计检查", SEVERITY_BLOCKING, _scan_security_design)
check_security_design = _dimension_entry(_SECURITY_DESIGN)
def _iter_named_assign_pairs(node: ast.AST):
    if isinstance(node, ast.Assign):
        for target in node.targets:
            yield from _iter_target_value_pairs(target, node.value)
    elif (isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name) and node.value is not None):
        yield node.target, node.value
def _iter_target_value_pairs(target: ast.AST, value: ast.AST):
    if isinstance(target, ast.Name):
        yield target, value
        return
    if not isinstance(target, (ast.Tuple, ast.List)):
        return
    if (not isinstance(value, (ast.Tuple, ast.List))
            or len(value.elts) != len(target.elts)):
        return
    for sub_target, sub_value in zip(target.elts, value.elts, strict=True):
        yield from _iter_target_value_pairs(sub_target, sub_value)
_IO_BARE_FUNCS = frozenset({"open", "urlopen"})
_PATHLIB_IO_ATTRS = frozenset({
    "read_text", "read_bytes", "write_text", "write_bytes"})
_HTTP_VERB_RECEIVERS = frozenset({"requests", "session", "client", "httpx"})
_HTTP_VERBS = frozenset({
    "get", "post", "put", "patch", "delete", "head", "options"})
_HTTP_REQUEST_RECEIVERS = frozenset({"session", "client"})
def _is_io_call(call: ast.Call,
                open_aliases: frozenset[str] = frozenset()) -> bool:
    func = call.func
    if isinstance(func, ast.Name):
        return func.id in _IO_BARE_FUNCS or func.id in open_aliases
    if not isinstance(func, ast.Attribute):
        return False
    if func.attr == "open" or func.attr in _PATHLIB_IO_ATTRS:
        return True
    recv = func.value.id if isinstance(func.value, ast.Name) else ""
    if func.attr in _HTTP_VERBS:
        return recv in _HTTP_VERB_RECEIVERS
    return func.attr == "request" and recv in _HTTP_REQUEST_RECEIVERS
_LOOP_NODE_TYPES = (ast.For, ast.AsyncFor, ast.While,
                    ast.ListComp, ast.SetComp, ast.DictComp,
                    ast.GeneratorExp)
def _scan_performance_baseline(tree: ast.AST, _content: str, details: list, suggestions: list) -> bool:
    sink = _FindingSink(details, suggestions)
    passed = True
    shadow = collect_lexical_scope_table(tree)
    if _scan_io_in_loops(tree, sink, shadow):
        passed = False
    if _scan_mutable_globals(tree, sink):
        passed = False
    return passed
_PERFORMANCE_BASELINE = _DimensionSpec("performance_baseline_check", "性能基线检查", SEVERITY_WARNING, _scan_performance_baseline)
check_performance_baseline = _dimension_entry(_PERFORMANCE_BASELINE)
def _once_evaluated_nodes(loop_node: ast.AST) -> set[int]:
    if isinstance(loop_node, (ast.For, ast.AsyncFor)):
        roots = [loop_node.iter]
    elif getattr(loop_node, "generators", None):
        roots = [loop_node.generators[0].iter]
    else:
        return set()
    once: set[int] = set()
    for root in roots:
        once.update(id(node) for node in tree_nodes(root))
    return once
def _scan_io_in_loops(tree: ast.Module, sink: _FindingSink,
                      shadow: LexicalScopeTable) -> bool:
    violated = False
    reported_calls: set[int] = set()
    scopes = call_scope_map(shadow)
    imports = (scope_import_tables(tree)
               if shadow.tree is not None else {})
    resolver = _ScopedImportResolver(tree, shadow)
    annotations_evaluated = not module_postpones_annotations(tree)
    for node in tree_nodes(tree):
        if not isinstance(node, _LOOP_NODE_TYPES):
            continue
        once_nodes = _once_evaluated_nodes(node)
        for child in _walk_loop_scope(
                node, skip_orelse=True,
                annotations_evaluated=annotations_evaluated):
            if id(child) in once_nodes:
                continue
            if not isinstance(child, ast.Call):
                continue
            if not _is_io_call(child):
                if not isinstance(child.func, ast.Name):
                    continue
                bindings = resolver.for_call(child, scopes)
                if not _is_io_call(child, bindings.open_aliases):
                    continue
            if _call_head_shadowed(child, shadow, scopes, imports):
                continue
            if id(child) in reported_calls:
                continue
            reported_calls.add(id(child))
            violated = True
            sink.emit(_RULE_IO_IN_LOOP, child.lineno,
                      "避免在循环内做I/O操作", loop_line=node.lineno)
    return violated
def _iter_module_level_mutable_globals(tree: ast.AST):
    for stmt in iter_own_scope(tree, skip_lambda=True,
                               skip_type_checking_body=True,
                               tc_polarities=_type_checking_guard_node_polarities(tree)):
        for target, value in _iter_named_assign_pairs(stmt):
            if is_mutable_default(value):
                yield target, stmt
def _scan_mutable_globals(tree: ast.Module, sink: _FindingSink) -> bool:
    violated = False
    for target, stmt in _iter_module_level_mutable_globals(tree):
        violated = True
        sink.emit(_RULE_MUTABLE_GLOBAL, stmt.lineno,
                  f"全局可变变量 {target.id} 可能导致并发问题",
                  variable=target.id)
    return violated
def _scan_global_declarations(tree: ast.AST, sink: _FindingSink) -> bool:
    violated = False
    for node in tree_nodes(tree):
        if isinstance(node, ast.Global):
            violated = True
            sink.emit(_RULE_GLOBAL_DECL, node.lineno,
                      "多线程环境中避免使用global声明", variables=list(node.names))
    return violated
def _attr_is_lock_creation(node: ast.Attribute,
                           threading_bindings: frozenset[str]) -> bool:
    return (isinstance(node.value, ast.Name)
            and node.value.id in threading_bindings
            and node.attr in _LOCK_NAMES)
def _is_thread_creation_call(node: ast.Call,
                             bindings: _ImportBindings) -> bool:
    func = node.func
    if isinstance(func, ast.Name):
        return func.id in bindings.threading_funcs
    return (isinstance(func, ast.Attribute)
            and func.attr in _THREAD_CREATION_APIS
            and _receiver_binds_module(func, bindings.threading_modules))
def _is_lock_creation_call(node: ast.Call,
                           bindings: _ImportBindings) -> bool:
    func = node.func
    if isinstance(func, ast.Name):
        return func.id in bindings.lock_funcs
    return (isinstance(func, ast.Attribute)
            and _attr_is_lock_creation(func, bindings.threading_modules))
def _scan_threading_usage(shadow: LexicalScopeTable,
                          resolver: _ScopedImportResolver) -> tuple[bool, bool]:
    scopes = call_scope_map(shadow)
    imports = (scope_import_tables(shadow.tree)
               if shadow.tree is not None else {})
    call_bindings = {
        id(call): resolver.for_call(call, scopes)
        for call, _scope in shadow.calls}
    lock_events: dict[ast.AST, list[tuple[int, int]]] = {}
    for call, scope in shadow.calls:
        if _call_head_shadowed(call, shadow, scopes, imports):
            continue
        if _is_lock_creation_call(call, call_bindings[id(call)]):
            lock_events.setdefault(scope, []).append(
                (call.lineno, call.col_offset))
    violated = False
    has_thread = False
    for call, scope in shadow.calls:
        if _call_head_shadowed(call, shadow, scopes, imports):
            continue
        if not _is_thread_creation_call(call, call_bindings[id(call)]):
            continue
        has_thread = True
        position = (call.lineno, call.col_offset)
        protected = False
        for current in _visible_scope_chain(scope, shadow.parent):
            events = lock_events.get(current, ())
            if any(current is not scope or event < position for event in events):
                protected = True
                break
        if not protected:
            violated = True
            break
    return violated, has_thread
def _scan_concurrency_safety(tree: ast.AST, _content: str, details: list, suggestions: list) -> bool:
    sink = _FindingSink(details, suggestions)
    shadow = collect_lexical_scope_table(tree)
    resolver = _ScopedImportResolver(tree, shadow)
    violated_lock, has_thread = _scan_threading_usage(shadow, resolver)
    violated_global = (_scan_global_declarations(tree, sink)
                       if has_thread else False)
    if violated_lock:
        sink.emit(_RULE_THREADING_NO_LOCK, None,
                  "使用了threading但未检测到Lock，可能存在竞态条件")
    return not (violated_global or violated_lock)
_CONCURRENCY_SAFETY = _DimensionSpec("concurrency_safety_check", "并发安全检查", SEVERITY_WARNING, _scan_concurrency_safety)
check_concurrency_safety = _dimension_entry(_CONCURRENCY_SAFETY)
def _default_open_mode(node: ast.Call) -> str | None:
    unpacked = (any(isinstance(arg, ast.Starred) for arg in node.args)
                or any(kw.arg is None for kw in node.keywords))
    return None if unpacked else "r"
_OPEN_MODE_INDEX = 1
_PATH_OPEN_MODE_INDEX = 0
def _open_mode_literal(node: ast.Call,
                       mode_index: int = _OPEN_MODE_INDEX) -> str | None:
    if len(node.args) > mode_index:
        mode_arg = node.args[mode_index]
    else:
        mode_arg = next(
            (kw.value for kw in node.keywords if kw.arg == "mode"), None)
    if mode_arg is None:
        return _default_open_mode(node)
    if isinstance(mode_arg, ast.Constant) and isinstance(mode_arg.value, str):
        return mode_arg.value
    return None
def _is_read_mode(mode: str) -> bool:
    return not (set(mode) & {"w", "a", "x", "+"})
@dataclass(frozen=True)
class _GuardFlags:
    file_op: bool = False
    sandbox: bool = False
    violation: bool = False
    def merge(self, other: _GuardFlags) -> _GuardFlags:
        return _GuardFlags(
            file_op=self.file_op or other.file_op,
            sandbox=self.sandbox or other.sandbox,
            violation=self.violation or other.violation,
        )
@dataclass(frozen=True)
class _GuardBindings:
    import_resolver: _ScopedImportResolver
    shadowed_open_call_ids: frozenset[int]
    shadow: LexicalScopeTable
    scopes: dict[int, ast.AST]
    pathlib_names: dict[int, dict[str, list[_PathBindingEvent]]]
    import_tables: dict
def _guard_bare_open_flags(node: ast.Call, bindings: _GuardBindings,
                           sink: _FindingSink,
                           mode_index: int = _OPEN_MODE_INDEX) -> _GuardFlags:
    if id(node) in bindings.shadowed_open_call_ids:
        return _GuardFlags()
    mode = _open_mode_literal(node, mode_index)
    if mode is not None and _is_read_mode(mode):
        return _GuardFlags()
    sink.emit(_RULE_UNGUARDED_OPEN, node.lineno,
              "建议使用 guarded_open() 替代裸 open()", function="open")
    return _GuardFlags(file_op=True, violation=True)
_PATH_GUARD_MARKERS = frozenset({
    "guard", "guarded", "safe", "safely", "sandbox", "sandboxed",
    "secure", "secured", "atomic", "validated", "ensure"})
_PATH_GUARD_ACTIONS = frozenset({
    "open", "path", "file", "write", "read", "remove", "unlink",
    "delete", "mkdir", "rmdir", "copy", "move", "within"})
_PATH_GUARD_TOKEN_RE = re.compile(r"[^a-z0-9]+")
def _is_path_guard_name(name: str) -> bool:
    tokens = set(_PATH_GUARD_TOKEN_RE.split(str(name).lower()))
    return bool(tokens & _PATH_GUARD_MARKERS) and bool(tokens & _PATH_GUARD_ACTIONS)
def _guard_name_flags(node: ast.Call, bindings: _GuardBindings,
                      imports: _ImportBindings,
                      sink: _FindingSink) -> _GuardFlags:
    func = node.func
    if func.id in imports.open_aliases:
        return _guard_bare_open_flags(node, bindings, sink)
    if (func.id in imports.system_funcs
            or func.id in imports.subprocess_funcs):
        sink.emit(_RULE_UNGUARDED_SYSTEM, node.lineno,
                  f"建议使用安全包装函数替代 {func.id}()", method=func.id)
        return _GuardFlags(violation=True)
    if func.id in imports.fileop_funcs:
        return _GuardFlags(file_op=True)
    if _is_path_guard_name(func.id):
        return _GuardFlags(sandbox=True)
    return _GuardFlags()
def _guard_attr_flags(node: ast.Call, bindings: _GuardBindings,
                      imports: _ImportBindings,
                      sink: _FindingSink,
                      scope: ast.AST | None = None) -> _GuardFlags:
    func = node.func
    flags = _GuardFlags()
    if ((func.attr in _OS_DANGEROUS_ATTRS
         and _receiver_binds_module(func, imports.os_recv_names))
            or (func.attr in _SUBPROCESS_CALL_ATTRS
                and _receiver_binds_module(func,
                                          imports.subprocess_modules))):
        sink.emit(_RULE_UNGUARDED_SYSTEM, node.lineno,
                  f"建议使用安全包装函数替代 .{func.attr}()", method=func.attr)
        flags = _GuardFlags(violation=True)
    if (func.attr == "open"
            and _receiver_is_pathlib(
                func.value, bindings, scope, (node.lineno, node.col_offset))):
        flags = flags.merge(_guard_bare_open_flags(
            node, bindings, sink, mode_index=_PATH_OPEN_MODE_INDEX))
    elif (func.attr in _PATHLIB_WRITE_OPS
            and _receiver_is_pathlib(
                func.value, bindings, scope, (node.lineno, node.col_offset))):
        flags = flags.merge(_GuardFlags(file_op=True))
    if _is_path_guard_name(func.attr):
        flags = flags.merge(_GuardFlags(sandbox=True))
    if _attr_receiver_is_fileop(func, imports):
        flags = flags.merge(_GuardFlags(file_op=True))
    return flags
_PATHLIB_BINDING_SCOPE_TYPES = (
    ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)
def _pathlib_chain_root(value: ast.AST) -> ast.AST:
    while True:
        if isinstance(value, (ast.NamedExpr, ast.Attribute)):
            value = value.value
        elif isinstance(value, ast.BinOp) and isinstance(value.op, ast.Div):
            value = value.left
        elif (isinstance(value, ast.Call)
                and isinstance(value.func, ast.Attribute)):
            if value.func.attr in _PATHLIB_CONSTRUCTORS:
                return value
            value = value.func.value
        else:
            return value
def _is_pathlib_receiver(value: ast.AST,
                         resolver: _ScopedImportResolver,
                         shadow: LexicalScopeTable,
                         scopes: dict[int, ast.AST]) -> bool:
    if isinstance(value, ast.IfExp):
        return any(
            _is_pathlib_receiver(branch, resolver, shadow, scopes)
            for branch in (value.body, value.orelse))
    root = _pathlib_chain_root(value)
    if not isinstance(root, ast.Call):
        return False
    if call_head_is_shadowed(root, shadow, scopes):
        return False
    imports = resolver.for_call(root, scopes)
    func = root.func
    if isinstance(func, ast.Name):
        return func.id in imports.pathlib_funcs
    return (isinstance(func, ast.Attribute)
            and func.attr in _PATHLIB_CONSTRUCTORS
            and _receiver_binds_module(func, imports.pathlib_modules))
_PathBindingEvent = tuple[int, int, bool, _ImportAlternative]
def _collect_pathlib_bindings(
        tree: ast.AST,
        resolver: _ScopedImportResolver,
        shadow: LexicalScopeTable,
        scopes: dict[int, ast.AST],
) -> dict[int, dict[str, list[_PathBindingEvent]]]:
    bindings: dict[int, dict[str, list[_PathBindingEvent]]] = {}
    pending_scopes: list[ast.AST] = [tree]
    def _scan_scope(scope: ast.AST) -> None:
        names: dict[str, list[_PathBindingEvent]] = {}
        def _append_binding_at(name: str, position: tuple[int, int],
                               is_path: bool,
                               alternative: _ImportAlternative) -> None:
            names.setdefault(name, []).append(
                (*position, is_path, alternative))
        def _append_binding(target: ast.Name, child: ast.AST, is_path: bool,
                            alternative: _ImportAlternative) -> None:
            _append_binding_at(target.id, (child.lineno, child.col_offset),
                               is_path, alternative)
        if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda)):
            # 形参在函数体执行前绑定：未注解/非 pathlib 注解的形参遮蔽外层
            # 同名 pathlib 变量，不得回退到外层绑定误判为路径对象。
            for param in iter_arg_nodes(scope.args):
                _append_binding_at(
                    param.arg, (scope.lineno, scope.col_offset),
                    _annotation_is_pathlib(param.annotation), None)
        def _record_value(target: ast.Name, value: ast.AST, child: ast.AST,
                          alternative: _ImportAlternative) -> None:
            _append_binding(
                target, child,
                _is_pathlib_receiver(value, resolver, shadow, scopes),
                alternative)
        def _record_bindings(child: ast.Assign | ast.AnnAssign,
                             alternative: _ImportAlternative) -> None:
            for target, value in _iter_named_assign_pairs(child):
                _record_value(target, value, child, alternative)
        def _record_for_bindings(child: ast.For | ast.AsyncFor,
                                 alternative: _ImportAlternative) -> None:
            if not isinstance(child.target, ast.Name):
                return
            values = (list(child.iter.elts)
                      if isinstance(child.iter, (ast.List, ast.Tuple, ast.Set))
                      else [child.iter])
            is_path = bool(values) and any(
                _is_pathlib_receiver(value, resolver, shadow, scopes)
                for value in values)
            loop_alternative = ((child, 0),) if alternative is None else (
                *alternative, (child, 0))
            _append_binding(child.target, child, is_path, loop_alternative)
        def _walk(node: ast.AST, alternative: _ImportAlternative) -> None:
            branches = _import_branch_map(node)
            for child in ast.iter_child_nodes(node):
                branch = branches.get(id(child))
                child_alternative = alternative
                if branch is not None:
                    child_alternative = ((branch,) if alternative is None
                                         else (*alternative, branch))
                if isinstance(child, _PATHLIB_BINDING_SCOPE_TYPES):
                    if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                          ast.ClassDef)):
                        names.setdefault(child.name, []).append((
                            child.end_lineno or child.lineno,
                            (child.end_col_offset
                             if child.end_col_offset is not None
                             else child.col_offset),
                            False, child_alternative))
                    pending_scopes.append(child)
                    continue
                if isinstance(child, (ast.Assign, ast.AnnAssign)):
                    _record_bindings(child, child_alternative)
                elif (isinstance(child, (ast.For, ast.AsyncFor))
                      and isinstance(child.target, ast.Name)):
                    _record_for_bindings(child, alternative)
                elif (isinstance(child, ast.NamedExpr)
                      and isinstance(child.target, ast.Name)):
                    _record_value(
                        child.target, child.value, child, child_alternative)
                else:
                    for name, bound_at, bound_alternative in \
                            _non_path_binding_events(child, child_alternative):
                        _append_binding_at(
                            name, bound_at, False, bound_alternative)
                _walk(child, child_alternative)
        _walk(scope, None)
        bindings[id(scope)] = names
    while pending_scopes:
        _scan_scope(pending_scopes.pop())
    return bindings
def _binding_node_end(node: ast.AST) -> tuple[int, int]:
    return (getattr(node, "end_lineno", None) or node.lineno,
            getattr(node, "end_col_offset", None)
            if getattr(node, "end_col_offset", None) is not None
            else node.col_offset)
def _annotation_is_pathlib(annotation: ast.expr | None) -> bool:
    if isinstance(annotation, ast.Name):
        return annotation.id in _PATHLIB_CONSTRUCTORS
    if isinstance(annotation, ast.Attribute):
        return (annotation.attr in _PATHLIB_CONSTRUCTORS
                and isinstance(annotation.value, ast.Name)
                and annotation.value.id == "pathlib")
    if isinstance(annotation, ast.Constant) and isinstance(annotation.value, str):
        text = annotation.value.strip()
        return (text in _PATHLIB_CONSTRUCTORS
                or (text.startswith("pathlib.")
                    and text.removeprefix("pathlib.") in _PATHLIB_CONSTRUCTORS))
    return False
_NON_PATH_BINDING_POSITIONS = (
    (ast.withitem, lambda node: _binding_node_end(node.context_expr)),
    (ast.comprehension, lambda node: _binding_node_end(node.iter)),
    ((ast.For, ast.AsyncFor), lambda node: _binding_node_end(node.iter)),
    (ast.ExceptHandler, lambda node: (node.lineno, node.col_offset)),
    (ast.MatchAs, lambda node: (node.lineno, node.col_offset)),
    (ast.MatchStar, lambda node: (node.lineno, node.col_offset)),
    (ast.MatchMapping, lambda node: (node.lineno, node.col_offset)),
)
def _non_path_binding_events(
        node: ast.AST, alternative: _ImportAlternative,
) -> list[tuple[str, tuple[int, int], _ImportAlternative]]:
    """with-as/except-as/推导式目标/match 捕获等非路径绑定事件。

    绑定位置取在该绑定真正生效之后（with 取上下文表达式末尾、推导式
    取迭代源末尾），保证表达式内对同名外层变量的引用仍按外层绑定判定。
    """
    for node_type, position_of in _NON_PATH_BINDING_POSITIONS:
        if not isinstance(node, node_type):
            continue
        position = position_of(node)
        return [(name, position, alternative)
                for name in scope_node_bound_names(node)]
    return []
def _path_binding_possible(events: list[_PathBindingEvent],
                           position: tuple[int, int] | None) -> bool | None:
    """位置之前生效的绑定是否可能为路径对象；无生效事件返回 None。"""
    variants: dict[_ImportAlternative, bool] = {None: False}
    applied = False
    for line, col, is_path, alternative in sorted(
            events, key=lambda event: event[:2]):
        if position is not None and (line, col) >= position:
            continue
        applied = _merge_variant_at_position(
            variants, alternative, is_path, position) or applied
    return any(variants.values()) if applied else None
def _receiver_is_pathlib(value: ast.AST, bindings: _GuardBindings,
                         scope: ast.AST | None,
                         position: tuple[int, int]) -> bool:
    if _is_pathlib_receiver(
            value, bindings.import_resolver, bindings.shadow, bindings.scopes):
        return True
    root = _pathlib_chain_root(value)
    if not isinstance(root, ast.Name) or scope is None:
        return False
    for current in _visible_scope_chain(scope, bindings.shadow.parent):
        bound = bindings.pathlib_names.get(id(current))
        events = bound.get(root.id) if bound is not None else None
        if not events:
            continue
        possible = _path_binding_possible(
            events, position if current is scope else None)
        if possible is None:
            continue
        return possible
    return False
def _attr_receiver_is_fileop(func: ast.Attribute,
                             imports: _ImportBindings) -> bool:
    if not isinstance(func.value, ast.Name):
        return False
    recv = func.value.id
    return ((recv in imports.shutil_recv_names
             and func.attr in _SHUTIL_FILE_OPS)
            or (recv in imports.os_recv_names and func.attr in _OS_FILE_OPS))
_ASSIGNMENT_BINDING_NODE_TYPES = (
    ast.Assign, ast.AnnAssign, ast.AugAssign, ast.NamedExpr,
    ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef,
)
def _only_conditional_or_later_execution_binding(
        scope: ast.AST, name: str, call: ast.Call) -> bool:
    variants: dict[_ImportAlternative, bool] = {None: False}
    found = False
    call_position = (call.lineno, call.col_offset)
    stack: list[tuple[ast.AST, _ImportAlternative]] = [(scope, None)]
    while stack:
        node, alternative = stack.pop()
        if node is not scope:
            if (not isinstance(node, (ast.Import, ast.ImportFrom,
                                      ast.comprehension))
                    and name in scope_node_bound_names(node)):
                found = True
                if isinstance(node, _ASSIGNMENT_BINDING_NODE_TYPES):
                    line = getattr(node, "end_lineno", None)
                    col = getattr(node, "end_col_offset", None)
                else:
                    line = getattr(node, "lineno", None)
                    col = getattr(node, "col_offset", None)
                if line is None or col is None:
                    return False
                if (line, col) < call_position:
                    event_alternative = alternative
                    if isinstance(node, (ast.For, ast.AsyncFor)):
                        event_alternative = (
                            ((node, 0),) if alternative is None
                            else (*alternative, (node, 0)))
                    _merge_variant_at_position(
                        variants, event_alternative, True, call_position)
            if isinstance(node, FRAME_BOUNDARY_NODES):
                continue
        branches = _import_branch_map(node)
        for child in reversed(list(ast.iter_child_nodes(node))):
            branch = branches.get(id(child))
            child_alternative = alternative
            if branch is not None:
                child_alternative = ((branch,) if alternative is None
                                     else (*alternative, branch))
            stack.append((child, child_alternative))
    return found and variants.get(None) is not True
def _call_head_shadowed(node: ast.Call, table: LexicalScopeTable,
                        scopes: dict[int, ast.AST],
                        imports: dict) -> bool:
    func = node.func
    if isinstance(func, ast.Name):
        name = func.id
    elif isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        name = func.value.id
    else:
        return False
    scope = scopes.get(id(node))
    if scope is None:
        return False
    if isinstance(func, ast.Attribute):
        current: ast.AST | None = scope
        imported = False
        while current is not None:
            if name in imports.get(current, {}):
                imported = True
                break
            current = table.parent.get(current)
        if not imported and name not in _DEFAULT_MODULE_RECEIVERS:
            return False
    if not call_head_is_shadowed(node, table, scopes):
        return False
    for current in _visible_scope_chain(scope, table.parent):
        if name not in table.shadow_bound.get(current, ()):
            continue
        if not isinstance(current, (ast.Module, ast.ClassDef)):
            return True
        if not _only_conditional_or_later_execution_binding(
                current, name, node):
            return True
    return False
def _guard_call_flags(node: ast.Call, bindings: _GuardBindings,
                      sink: _FindingSink) -> _GuardFlags:
    func = node.func
    if (not (isinstance(func, ast.Name) and func.id == "open")
            and _call_head_shadowed(node, bindings.shadow, bindings.scopes,
                                    bindings.import_tables)):
        return _GuardFlags()
    imports = bindings.import_resolver.for_call(node, bindings.scopes)
    if isinstance(func, ast.Name):
        return _guard_name_flags(node, bindings, imports, sink)
    if isinstance(func, ast.Attribute):
        if (func.attr == "open"
                and (_receiver_binds_module(
                    func, imports.builtins_modules)
                    or _receiver_binds_module(
                        func, imports.open_family_modules))):
            return _guard_bare_open_flags(node, bindings, sink)
        return _guard_attr_flags(
            node, bindings, imports, sink, bindings.scopes.get(id(node)))
    return _GuardFlags()
def _scan_guard_calls(tree: ast.Module, bindings: _GuardBindings,
                      sink: _FindingSink) -> bool:
    violated = False
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        flags = _guard_call_flags(node, bindings, sink)
        if any(
                kwarg.arg == "sandbox_path"
                and (not isinstance(kwarg.value, ast.Constant)
                     or bool(kwarg.value.value))
                for kwarg in node.keywords):
            flags = flags.merge(_GuardFlags(sandbox=True))
        if flags.file_op and not flags.sandbox and not flags.violation:
            sink.emit(_RULE_MISSING_PATH_GUARD, node.lineno,
                      "文件操作未使用路径守卫"
                      "（guarded_open/sandbox_path 或同类安全包装）")
            flags = flags.merge(_GuardFlags(violation=True))
        violated = violated or flags.violation
    return violated
def _scan_guard_injection(tree: ast.AST, _content: str, details: list, suggestions: list) -> bool:
    sink = _FindingSink(details, suggestions)
    shadow = collect_lexical_scope_table(tree)
    resolver = _ScopedImportResolver(tree, shadow)
    scopes = call_scope_map(shadow)
    bindings = _GuardBindings(
        import_resolver=resolver,
        shadowed_open_call_ids=shadowed_open_call_ids(shadow),
        shadow=shadow,
        scopes=scopes,
        pathlib_names=_collect_pathlib_bindings(tree, resolver, shadow, scopes),
        import_tables=scope_import_tables(tree),
    )
    return not _scan_guard_calls(tree, bindings, sink)
_GUARD_INJECTION = _DimensionSpec("guard_injection_check", "守卫注入检查", SEVERITY_BLOCKING, _scan_guard_injection)
check_guard_injection = _dimension_entry(_GUARD_INJECTION)
PRECHECK_LONG_FUNCTION_LINES = 80
_PRECHECK_FILE_LINES_HINT = 2000
_GATE_SERIES_RE = re.compile(r'^([A-Za-z]+)\d')
_GATE_SEVERITY_MAP: dict[str, str] = {
    'BLOCK': SEVERITY_BLOCKING,
    'ERROR': SEVERITY_BLOCKING,
    'WARN': SEVERITY_WARNING,
    'INFO': SEVERITY_INFO,
}
class CodeQualityPrecheck:
    def __init__(self, gate=None):
        self._gate = gate
    ANTIPATTERNS: ClassVar[dict] = {
        "broad_import": {"severity": SEVERITY_INFO,
                         "desc": "宽泛导入 (import *)",
                         "fix": "显式导入需要的名称"},
        "deep_nesting": {"severity": SEVERITY_WARNING,
                         "desc": "嵌套层级过深 (>4层)",
                         "fix": "提取子函数或使用 early return"},
        "long_function": {"severity": SEVERITY_INFO,
                          "desc": f"函数过长 (>{PRECHECK_LONG_FUNCTION_LINES}行)",
                          "fix": "提取同模块私有函数或使用 early return 降低长度"},
        "global_mutable": {"severity": SEVERITY_WARNING,
                           "desc": "模块级可变状态",
                           "fix": "封装为类或使用配置对象"},
    }
    def check(self, code_content: str, filename: str = "") -> list[PreCheckItem]:
        items = []
        filename, filename_error = normalize_text_param(
            filename, "filename 期望 str",
            suggestion="传入 str 文件名后再继续",
            applicable_to="CodeQualityPrecheck.check() 参数",
            allow_pathlike=True)
        if filename_error is not None:
            items.append(filename_error)
        if not isinstance(code_content, str):
            items.append(type_error_precheck(
                code_content, "期望 str 源码", "ast_parser", filename))
            return items
        code_content = normalize_input(code_content, "code_content")
        try:
            tree = ast.parse(code_content)
        except PARSE_DEGRADE_EXC as e:
            log_swallowed(__name__, e,
                          context=f'CodeQualityPrecheck.check:{type(e).__name__}')
            items.append(PreCheckItem(
                category="code_quality",
                severity=SEVERITY_BLOCKING,
                description=f"语法错误或不可解析: {e}",
                suggestion="修复语法错误后再继续",
                source="ast_parser",
                applicable_to=filename,
            ))
            return items
        self._check_antipatterns(tree, items, filename)
        self._check_gate_series(code_content, items, filename, tree)
        line_count = source_line_count(code_content)
        if line_count > _PRECHECK_FILE_LINES_HINT:
            items.append(PreCheckItem(
                category="code_quality",
                severity=SEVERITY_INFO,
                description=(f"文件过长: {line_count} 行 "
                             f"(建议≤{_PRECHECK_FILE_LINES_HINT}行)"),
                suggestion=("优先简化逻辑/迁移无关块到既有职责模块"
                             "（GOV-01 禁止直接拆分）"),
                source="pattern",
                applicable_to=filename,
            ))
        return items
    @staticmethod
    def _gate_degradation_precheck(rule_id: str, description: str,
                                   filename: str) -> PreCheckItem:
        return PreCheckItem(
            category="code_quality",
            severity=SEVERITY_BLOCKING,
            description=description,
            suggestion="恢复严格门禁并确认返回契约后重跑预创建审查",
            source="diagnose_gate_series",
            applicable_to=filename,
            rule_id=rule_id,
            locator=filename,
            confidence=1.0,
            evidence_type="runtime",
        )
    def _check_gate_series(self, code_content: str, items: list[PreCheckItem],
                            filename: str, tree: ast.AST | None) -> None:
        if self._gate is None:
            return
        try:
            result = self._gate.check(code_content, filename, tree=tree)
        except Exception as exc:
            logger.warning("[PreCreationReview] 门禁系列检查异常，已转为阻断项: %s",
                           exc, exc_info=True)
            items.append(self._gate_degradation_precheck(
                "PRE-GATE-001",
                f"严格门禁执行异常: {type(exc).__name__}: {exc}", filename))
            return
        issues = getattr(result, "issues", None)
        if not isinstance(issues, (list, tuple)):
            logger.warning(
                "[PreCreationReview] 门禁系列检查返回形态非法(%s)，已转为阻断项",
                type(issues).__name__)
            items.append(self._gate_degradation_precheck(
                "PRE-GATE-002",
                "严格门禁返回值缺少合法 issues 列表: "
                f"{type(issues).__name__}", filename))
            return
        for issue in issues:
            item = self._gate_issue_to_precheck(issue, filename)
            if item is not None:
                items.append(item)
                continue
            logger.warning("[PreCreationReview] 门禁条目缺少 check_id，已转为阻断项")
            items.append(self._gate_degradation_precheck(
                "PRE-GATE-003", "严格门禁条目缺少 check_id/rule_id", filename))
    @staticmethod
    def _gate_issue_to_precheck(issue, filename: str) -> PreCheckItem | None:
        check_id = str(getattr(issue, "check_id", "")
                       or getattr(issue, "rule_id", "") or "")
        if not check_id:
            return None
        series = _GATE_SERIES_RE.match(check_id)
        source = (f"diagnose_gate_{series.group(1).lower()}_series"
                  if series else "diagnose_gate_series")
        raw_sev = getattr(issue, "severity", None)
        sev_value = getattr(raw_sev, "value", raw_sev)
        severity_name = str(sev_value or "").strip().upper()
        severity = _GATE_SEVERITY_MAP.get(severity_name)
        if severity is None:
            logger.warning(
                "[PreCreationReview] 门禁条目 %s severity=%r 非法，已按 blocking 计入",
                check_id, sev_value)
            severity = SEVERITY_BLOCKING
        line = getattr(issue, "line", 0) or 0
        return PreCheckItem(
            category="code_quality",
            severity=severity,
            description=f"[{check_id}] {getattr(issue, 'message', '') or ''}",
            suggestion=str(getattr(issue, "suggestion", "") or ""),
            source=source,
            applicable_to=f"{filename}:{line}",
            rule_id=check_id,
            locator=f"{filename}:{line}",
            confidence=1.0,
            evidence_type="ast",
        )
    def _check_antipatterns(self, tree: ast.AST,
                            items: list[PreCheckItem], filename: str) -> None:
        for node in tree_nodes(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                items.extend(self._function_structure_issues(node, filename))
            elif isinstance(node, ast.ImportFrom):
                items.extend(self._star_import_issues(node, filename))
        self._check_module_mutable_state(tree, items, filename)
    @classmethod
    def _rule_issue(cls, rule: dict, description: str, applicable_to: str,
                    *, source: str = "ast_pattern") -> PreCheckItem:
        return PreCheckItem(
            category="code_quality",
            severity=rule["severity"],
            description=description,
            suggestion=rule["fix"],
            source=source,
            applicable_to=applicable_to,
        )
    def _function_structure_issues(self, node: ast.FunctionDef | ast.AsyncFunctionDef,
                                   filename: str) -> list[PreCheckItem]:
        issues: list[PreCheckItem] = []
        end_lineno = getattr(node, 'end_lineno', None)
        if end_lineno:
            func_len = end_lineno - node.lineno + 1
            if func_len > PRECHECK_LONG_FUNCTION_LINES:
                rule = self.ANTIPATTERNS["long_function"]
                issues.append(self._rule_issue(
                    rule, f"{rule['desc']}: {node.name}() {func_len}行",
                    f"{filename}:{node.lineno}", source="pattern"))
        max_depth = calc_nesting(node)
        if max_depth > 4:
            rule = self.ANTIPATTERNS["deep_nesting"]
            issues.append(self._rule_issue(
                rule,
                f"{rule['desc']}: {node.name}() 嵌套 {max_depth} 层 "
                f"(行 {node.lineno})",
                f"{filename}:{node.lineno}"))
        return issues
    def _star_import_issues(self, node: ast.ImportFrom,
                            filename: str) -> list[PreCheckItem]:
        rule = self.ANTIPATTERNS["broad_import"]
        return [
            self._rule_issue(
                rule, rule["desc"] + f" in {filename} (行 {node.lineno})",
                f"{filename}:{node.lineno}")
            for alias in node.names if alias.name == "*"
        ]
    @staticmethod
    def _check_module_mutable_state(tree: ast.AST,
                                    items: list[PreCheckItem],
                                    filename: str) -> None:
        rule = CodeQualityPrecheck.ANTIPATTERNS["global_mutable"]
        for target, stmt in _iter_module_level_mutable_globals(tree):
            items.append(CodeQualityPrecheck._rule_issue(
                rule, f"{rule['desc']}: {target.id} (行 {stmt.lineno})",
                f"{filename}:{stmt.lineno}"))
_PRE_CREATE_LINE_SOFT_LIMIT = 2500
@dataclass
class _CodeStats:
    func_count: int = 0
    class_count: int = 0
    total_lines: int = 0
    has_type_annotations: bool = False
    has_dataclass: bool = False
    has_error_handling: bool = False
class ArchitectureAdvisor:
    ARCHITECTURE_PATTERNS: ClassVar[dict] = {
        "diagnostic": {
            "pattern": "Pipeline",
            "description": "诊断类模块应使用 Pipeline 模式：输入→检测→评分→输出",
            "layers": ["输入解析", "检测引擎", "评分器", "报告生成"],
        },
        "validator": {
            "pattern": "RuleEngine",
            "description": "验证类模块应使用规则引擎模式：规则注册→匹配→判定",
            "layers": ["规则定义", "规则匹配", "规则执行", "结果聚合"],
        },
        "fixer": {
            "pattern": "Strategy",
            "description": "修复类模块应使用策略模式：问题分类→策略选择→执行→验证",
            "layers": ["问题分析", "策略选择", "修复执行", "安全验证"],
        },
        "builder": {
            "pattern": "Builder",
            "description": "构建类模块应使用 Builder 模式：配置→组装→验证→产出",
            "layers": ["配置读取", "模板组装", "质量验证", "文件产出"],
        },
    }
    def _analyze_code_context(self, code_content: str,
                               module_name: str) -> list[dict]:
        try:
            tree = ast.parse(code_content, filename=module_name)
        except PARSE_DEGRADE_EXC as e:
            logger.warning("[PreCreate] 分析代码上下文失败,返回空: %s", e)
            return []
        stats = self._collect_code_stats(tree, source_line_count(code_content))
        return self._stats_to_issues(stats)
    @staticmethod
    def _collect_code_stats(tree: ast.AST, total_lines: int) -> _CodeStats:
        func_count = 0
        class_count = 0
        has_type_annotations = False
        has_dataclass = False
        has_error_handling = False
        for node in tree_nodes(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                func_count += 1
                if ArchitectureAdvisor._function_has_annotations(node):
                    has_type_annotations = True
            elif isinstance(node, ast.ClassDef):
                class_count += 1
                if ArchitectureAdvisor._class_uses_dataclass(node):
                    has_dataclass = True
            elif isinstance(node, TRY_NODE_TYPES) and node.handlers:
                has_error_handling = True
        return _CodeStats(
            func_count=func_count,
            class_count=class_count,
            total_lines=total_lines,
            has_type_annotations=has_type_annotations,
            has_dataclass=has_dataclass,
            has_error_handling=has_error_handling,
        )
    @staticmethod
    def _function_has_annotations(node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
        if node.returns:
            return True
        all_args = [*node.args.posonlyargs, *node.args.args,
                    *node.args.kwonlyargs]
        all_args.extend(a for a in (node.args.vararg, node.args.kwarg)
                        if a is not None)
        return any(a.annotation for a in all_args)
    @staticmethod
    def _class_uses_dataclass(node: ast.ClassDef) -> bool:
        return any(is_dataclass_decorator(unparse_or_type_name(dec))
                   for dec in node.decorator_list)
    @staticmethod
    def _stats_to_issues(stats: _CodeStats) -> list[dict]:
        issues: list[dict] = []
        if stats.total_lines > _PRE_CREATE_LINE_SOFT_LIMIT:
            issues.append({
                "aspect": "module_structure",
                "description": (f"当前文件 {stats.total_lines} 行超过 "
                                f"{_PRE_CREATE_LINE_SOFT_LIMIT} 行上限："
                                "治理候选（GOV-01 禁止直接拆分）"),
                "reasoning": (f"{stats.total_lines} 行远超推荐的 "
                              f"{_PRE_CREATE_LINE_SOFT_LIMIT} 行上限"),
                "pattern": "File Governance",
                "example": ("在既有模块内简化分支/去重/提取私有实现，"
                            "把无关职责迁到既有职责模块，不新增文件"),
            })
        interface_findings: list[str] = []
        if stats.func_count > 0 and not stats.has_type_annotations:
            interface_findings.append(
                f"{stats.func_count} 个函数中未检测到类型注解，建议添加")
        if stats.class_count > 1 and not stats.has_dataclass:
            interface_findings.append(
                f"{stats.class_count} 个类均未使用 @dataclass，数据类建议使用 dataclass")
        if interface_findings:
            issues.append({
                "aspect": "interface",
                "description": "；".join(interface_findings),
                "reasoning": "类型注解与 dataclass 共同决定接口的可读性与 IDE 支持",
                "pattern": "Type Annotations / Dataclass adoption",
                "example": ("def process(data: list[dict]) -> MethodResult:\n"
                            "@dataclass\nclass MyResult:\n    status: str"),
            })
        if stats.func_count > 5 and not stats.has_error_handling:
            issues.append({
                "aspect": "error_handling",
                "description": f"{stats.func_count} 个函数中未检测到 try/except，可能存在未处理异常风险",
                "reasoning": "外部调用未加异常保护会导致管道崩溃",
                "pattern": "Defensive Programming",
                "example": "使用 try/except 包裹所有外部调用（IO、子进程、网络）",
            })
        return issues
    _DEFAULT_SUGGESTION_SPECS: ClassVar[tuple[dict, ...]] = (
        {"aspect": "module_structure",
         "description": "模块应保持单一职责；超大文件优先在既有模块内治理",
         "reasoning": "大型文件难以维护和测试，但拆分不是治理手段（GOV-01）",
         "pattern": "Single Responsibility",
         "example": "简化分支/消除重复/收敛依赖，或迁移到既有职责模块，不新增文件"},
        {"aspect": "interface",
         "description": "公开 API 应使用 dataclass 或 TypedDict 作为输入输出类型",
         "reasoning": "类型化接口减少运行时错误，提高可读性",
         "pattern": "TypeScript-like typing",
         "example": "@dataclass\nclass MethodResult:\n    status: str\n    data: dict"},
        {"aspect": "error_handling",
         "description": "所有外部调用(文件IO、子进程、网络)必须使用 try/except",
         "reasoning": "未处理的异常会导致整条管道崩溃",
         "pattern": "Defensive Programming",
         "example": "try:\n    result = subprocess.run(...)\nexcept ... as e:\n    return error_result"},
    )
    def _append_default_suggestions(
            self, suggestions: list[ArchitectureSuggestion],
            context_issues: list[dict]) -> None:
        present = {ci.get("aspect") for ci in context_issues}
        for spec in self._DEFAULT_SUGGESTION_SPECS:
            if spec["aspect"] not in present:
                suggestions.append(ArchitectureSuggestion(
                    aspect=spec["aspect"],
                    description=spec["description"],
                    reasoning=spec["reasoning"],
                    pattern=spec["pattern"],
                    example=spec["example"]))
    def advise(self, module_type: str = "", module_name: str = "",
               code_content: str = "") -> list[ArchitectureSuggestion]:
        module_type, module_name = self._normalize_advise_inputs(
            module_type, module_name)
        context_issues = self._analyze_context_if_present(code_content, module_name)
        suggestions: list[ArchitectureSuggestion] = []
        self._append_default_suggestions(suggestions, context_issues)
        suggestions.extend(self._context_suggestions(context_issues))
        pattern_suggestion = self._pattern_suggestion(module_type)
        if pattern_suggestion is not None:
            suggestions.append(pattern_suggestion)
        suggestions.append(self._naming_suggestion())
        return suggestions
    @staticmethod
    def _normalize_advise_inputs(module_type: object,
                                 module_name: object) -> tuple[str, str]:
        normalized: list[str] = []
        for field_desc, value in (("module_type", module_type),
                                  ("module_name", module_name)):
            text, error = normalize_text_param(
                value, f"advise 参数 {field_desc} 期望 str",
                suggestion="传入 str 后再继续",
                applicable_to="ArchitectureAdvisor.advise() 参数")
            if error is not None:
                logger.warning(
                    "[PreCreationReview] advise 参数 %s 类型非法 %r，已归一空串",
                    field_desc, value)
            normalized.append(text)
        return normalized[0], normalized[1]
    def _analyze_context_if_present(self, code_content: object,
                                   module_name: str) -> list[dict]:
        if isinstance(code_content, str) and code_content.strip():
            return self._analyze_code_context(code_content, module_name or "unknown")
        return []
    @staticmethod
    def _context_suggestions(context_issues: list[dict]) -> list[ArchitectureSuggestion]:
        return [ArchitectureSuggestion(
            aspect=ci["aspect"],
            description=ci["description"],
            reasoning=ci.get("reasoning", "基于 AST 上下文分析"),
            pattern=ci.get("pattern", "Context-Aware"),
            example=ci.get("example", ""),
        ) for ci in context_issues]
    def _pattern_suggestion(self, module_type: str) -> ArchitectureSuggestion | None:
        pattern_info = self.ARCHITECTURE_PATTERNS.get(module_type.strip().lower())
        if pattern_info is None:
            return None
        return ArchitectureSuggestion(
            aspect="layering",
            description=f"推荐使用 {pattern_info['pattern']} 模式",
            reasoning=pattern_info["description"],
            pattern=pattern_info["pattern"],
            example=f"层级: {' → '.join(pattern_info['layers'])}",
        )
    @staticmethod
    def _naming_suggestion() -> ArchitectureSuggestion:
        return ArchitectureSuggestion(
            aspect="naming",
            description="函数名使用 snake_case，类名使用 PascalCase，常量使用 UPPER_SNAKE_CASE",
            reasoning="统一的命名约定提高代码可读性和 Agent 识别率",
            pattern="PEP 8 Naming",
            example="def run_audit():\nclass FixRouter:\nMAX_RETRIES = 3",
        )
register_review_provider("precreation_arch_advisor", ArchitectureAdvisor)
register_review_provider("precreation_code_precheck", CodeQualityPrecheck)
def _engine_check_provider() -> dict:
    return {
        "concurrency_safety_check": check_concurrency_safety,
        "guard_injection_check": check_guard_injection,
        "performance_baseline_check": check_performance_baseline,
        "security_design_check": check_security_design,
    }
register_check_provider(_engine_check_provider)

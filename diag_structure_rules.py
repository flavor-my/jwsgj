from __future__ import annotations

__all__ = [
    'FRAGMENT_FILE_MIN_LINES',
    'FRAGMENT_MERGE_TOLERANCE',
    'FRAGMENT_SAME_MODULE_MAX',
    'FRAGMENT_SUB_DIR_BLOCK_RATIO',
    'FRAGMENT_SUB_DIR_WARN_RATIO',
    'GATE_DETECTORS',
    'REBOUND_RISK_ZONE',
    'DirectoryFragmentReport',
    'FragmentFile',
    'FragmentGroup',
    'FragmentReport',
    'MiniFileDetector',
    'check_AF01',
    'check_AF02',
    'check_AF03',
    'check_AF04',
    'check_PI01',
    'check_af',
    'detect_d09_micro_file',
    'detect_d12_fragmentation',
    'detect_d14_facade_exceed',
    'detect_d21_duplicate_metadata',
    'detect_d33_duplicate_file',
    'detect_fragments',
    'format_report',
]
import ast
import hashlib
import logging
import os
import re
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass, field
from functools import cache
from pathlib import Path
from typing import Any, ClassVar

from jwsgj.diag_antipattern import FacadeOptimizer, count_facade_entries
from jwsgj.diag_shared_ast_nodes import (
    MATCH_NODE_TYPES,
    TRY_NODE_TYPES,
    ast_name,
    is_constant_expr_stmt,
    is_docstring_stmt,
    is_placeholder_stmt,
    typing_type_checking_names,
)
from jwsgj.diag_shared_ast_views import (
    subtree_nodes,
)
from jwsgj.diag_shared_source_core import (
    aligned_source_lines,
    load_source_tree,
    read_source_auto,
    source_lines_or,
)
from jwsgj.diag_types_defs import (
    DiagnoseFinding,
    DiagnoseIssue,
    PatternFinding,
)
from jwsgj.diag_types_vocab import (
    D_ARCH_RULE_SUGGESTIONS,
    MSG_EXCEPTION_BROAD_HANDLER,
    PARSE_DEGRADE_EXC,
    DiagnoseSeverity,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    AUDIT_SCAN_SKIP_DIRS,
    SCAN_COLLECT_PRUNE_DIRS_LOWER,
    TEST_DIR_CANDIDATES_LOWER,
    is_pruned_scan_dir,
    is_runtime_temp_path,
    is_test_file_path,
    rglob_paths_tolerant,
    safe_relpath,
)

logger = logging.getLogger(__name__)
_MICRO_FILE_EXEMPT_BASENAMES = frozenset({
    '__init__.py', '_version.py', '_version_meta.py', 'version.py',
    '__main__.py', 'setup.py',
})
_SPECIAL_FILES = _MICRO_FILE_EXEMPT_BASENAMES | frozenset({"conftest.py"})
FRAGMENT_FILE_MIN_LINES = 80
_MICRO_FILE_MAX_LINES = FRAGMENT_FILE_MIN_LINES
_THIN_FRAGMENT_MAX_LINES = 50
_THIN_FRAGMENT_MAX_DEFS = 2
_MAX_FACADE_COUNT = FacadeOptimizer.MAX_FACADE
_DEFAULT_SOURCE_LINES: list[str] | None = None
_DEFAULT_FILEPATH = ""
_DEFAULT_TYPE_CHECKING_ALIASES: frozenset[str] = frozenset()
_DEFAULT_TYPE_ALIAS_NAMES: frozenset[str] = frozenset({'TypeAlias'})
def _module_level_def_counts(tree: ast.Module) -> tuple[int, int]:
    func_count = sum(1 for n in tree.body
                     if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)))
    class_count = sum(1 for n in tree.body if isinstance(n, ast.ClassDef))
    return func_count, class_count
def _is_exempt_basename(filepath: str) -> bool:
    return (bool(filepath)
            and filepath.replace('\\', '/').split('/')[-1].lower()
            in _SPECIAL_FILES)
def detect_d09_micro_file(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    if _is_exempt_basename(filepath):
        return issues
    source_lines = source_lines_or(code, source_lines)
    if len(source_lines) < _MICRO_FILE_MAX_LINES:
        if _is_types_only_file(tree):
            return issues
        issues.append(DiagnoseIssue(
            check_id='D09', severity=DiagnoseSeverity.WARN,
            message=f'微型文件: {len(source_lines)} 行 (<{_MICRO_FILE_MAX_LINES}行阈值)',
            line=1,
            suggestion=D_ARCH_RULE_SUGGESTIONS['D09'],
            auto_fixable=False,
        ))
    return issues
_TYPE_ALIAS_NODES = ((ast.TypeAlias,) if hasattr(ast, "TypeAlias") else ())
def _effective_stmts(stmts: list[ast.stmt]) -> list[ast.stmt]:
    return [s for s in stmts
            if not is_constant_expr_stmt(s) and not isinstance(s, ast.Pass)]
def _assignment_has_substantive_logic(
        node: ast.Assign | ast.AnnAssign) -> bool:
    value = node.value
    if value is None:
        return False
    executable_nodes = (
        ast.Call, ast.comprehension, ast.Lambda, ast.Await,
        ast.Yield, ast.YieldFrom,
    )
    return any(isinstance(item, executable_nodes) for item in walk_nodes(value))
def _function_has_substantive_logic(
        node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    return bool(_effective_stmts(node.body))
def _class_has_substantive_logic(class_node: ast.ClassDef) -> bool:
    for stmt in _effective_stmts(class_node.body):
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if _function_has_substantive_logic(stmt):
                return True
            continue
        return True
    return False
def _is_type_checking_guard(
        node: ast.If,
        type_checking_aliases: frozenset[str] = _DEFAULT_TYPE_CHECKING_ALIASES,
        type_alias_names: frozenset[str] = _DEFAULT_TYPE_ALIAS_NAMES) -> bool:
    test_name = ast_name(node.test)
    if test_name != 'TYPE_CHECKING' and test_name not in type_checking_aliases:
        return False
    return (all(_is_type_only_guard_stmt(
                    stmt, type_checking_aliases, type_alias_names)
                for stmt in node.body)
            and all(_is_types_only_declaration(
                        stmt, type_checking_aliases, type_alias_names)
                    or is_placeholder_stmt(stmt)
                    for stmt in node.orelse))
_TYPE_ONLY_BASES = frozenset({
    'Protocol', 'ABC', 'Enum', 'IntEnum', 'StrEnum', 'Flag', 'IntFlag',
    'Generic', 'TypedDict', 'NamedTuple',
    'Exception', 'BaseException', 'Warning',
})
def _type_only_base_name(base: ast.expr) -> str:
    while isinstance(base, ast.Subscript):
        base = base.value
    return ast_name(base)
def _is_type_only_class(
        node: ast.ClassDef,
        type_checking_aliases: frozenset[str] = _DEFAULT_TYPE_CHECKING_ALIASES,
        type_alias_names: frozenset[str] = _DEFAULT_TYPE_ALIAS_NAMES,
) -> bool:
    for item in _effective_stmts(node.body):
        if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if _function_has_substantive_logic(item):
                return False
            continue
        if isinstance(item, (ast.Assign, ast.AnnAssign)):
            if _assignment_has_substantive_logic(item):
                return False
            continue
        if isinstance(item, _TYPE_ALIAS_NODES):
            continue
        if (isinstance(item, ast.If)
                and _is_type_checking_guard(
                    item, type_checking_aliases, type_alias_names)):
            continue
        return False
    bases = [_type_only_base_name(b) for b in node.bases]
    if any(b in _TYPE_ONLY_BASES for b in bases):
        return True
    return any(
        ast_name(d) == 'abstractmethod'
        for item in subtree_nodes(node)
        if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
        for d in item.decorator_list)
def _is_type_only_guard_stmt(
        stmt: ast.stmt,
        type_checking_aliases: frozenset[str] = _DEFAULT_TYPE_CHECKING_ALIASES,
        type_alias_names: frozenset[str] = _DEFAULT_TYPE_ALIAS_NAMES,
) -> bool:
    if isinstance(stmt, (ast.Import, ast.ImportFrom)):
        return True
    if isinstance(stmt, (ast.Assign, ast.AnnAssign) + _TYPE_ALIAS_NODES):
        return True
    if isinstance(stmt, ast.ClassDef):
        # 位于 TYPE_CHECKING 守卫内，运行期永不执行，必然只服务类型检查；
        # 不能再用「类型基类/abstractmethod」反推，否则普通纯声明类会把
        # 合法的 type-only 文件误判成业务代码（D09/D12 误报）。
        return True
    return is_placeholder_stmt(stmt)
def _assignment_targets_all(node: ast.Assign | ast.AnnAssign) -> bool:
    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
    return any(isinstance(target, ast.Name) and target.id == '__all__'
               for target in targets)
def _is_type_expression(node: ast.expr | None) -> bool:
    if isinstance(node, (ast.Name, ast.Attribute, ast.Subscript)):
        executable_nodes = (
            ast.Call, ast.comprehension, ast.Lambda, ast.Await,
            ast.Yield, ast.YieldFrom,
        )
        return not any(
            isinstance(item, executable_nodes) for item in walk_nodes(node))
    if isinstance(node, ast.Constant):
        return node.value is None or isinstance(node.value, str)
    if isinstance(node, ast.BinOp):
        return (isinstance(node.op, ast.BitOr)
                and _is_type_expression(node.left)
                and _is_type_expression(node.right))
    if isinstance(node, (ast.Tuple, ast.List)):
        return bool(node.elts) and all(
            _is_type_expression(item) for item in node.elts)
    return False
def _is_type_declaration_assignment(
        node: ast.Assign | ast.AnnAssign,
        type_alias_names: frozenset[str] = _DEFAULT_TYPE_ALIAS_NAMES) -> bool:
    if _assignment_targets_all(node):
        return not _assignment_has_substantive_logic(node)
    if isinstance(node, ast.AnnAssign):
        if node.value is None:
            return True
        return (ast_name(node.annotation) in type_alias_names
                and _is_type_expression(node.value))
    if isinstance(node.value, (ast.Constant, ast.Tuple, ast.List)):
        return False
    return _is_type_expression(node.value)
def _is_types_only_declaration(
        node: ast.AST,
        type_checking_aliases: frozenset[str] = _DEFAULT_TYPE_CHECKING_ALIASES,
        type_alias_names: frozenset[str] = _DEFAULT_TYPE_ALIAS_NAMES) -> bool:
    if isinstance(node, ast.ClassDef):
        return _is_type_only_class(
            node, type_checking_aliases, type_alias_names)
    if isinstance(node, ast.If):
        return _is_type_checking_guard(
            node, type_checking_aliases, type_alias_names)
    if isinstance(node, (ast.Assign, ast.AnnAssign)):
        return _is_type_declaration_assignment(node, type_alias_names)
    return isinstance(node, (ast.Import, ast.ImportFrom) + _TYPE_ALIAS_NODES)
def _typing_type_alias_names(tree: ast.Module) -> frozenset[str]:
    names = set(_DEFAULT_TYPE_ALIAS_NAMES)
    for stmt in tree.body:
        if not (isinstance(stmt, ast.ImportFrom) and stmt.level == 0
                and stmt.module in {'typing', 'typing_extensions'}):
            continue
        names.update(alias.asname or alias.name for alias in stmt.names
                     if alias.name == 'TypeAlias')
    return frozenset(names)
def _is_types_only_file(tree: ast.Module) -> bool:
    aliases = frozenset(typing_type_checking_names(tree))
    type_alias_names = _typing_type_alias_names(tree)
    for node in ast.iter_child_nodes(tree):
        if is_docstring_stmt(node) or _is_types_only_declaration(
                node, aliases, type_alias_names):
            continue
        return False
    return True
def detect_d12_fragmentation(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    if _is_exempt_basename(filepath):
        return issues
    source_lines = source_lines_or(code, source_lines)
    line_count = len(source_lines)
    func_count, class_count = _module_level_def_counts(tree)
    if (line_count < _THIN_FRAGMENT_MAX_LINES
            and func_count + class_count <= _THIN_FRAGMENT_MAX_DEFS):
        if _is_types_only_file(tree):
            return issues
        issues.append(DiagnoseIssue(
            check_id='D12', severity=DiagnoseSeverity.WARN,
            message=f'疑似碎片文件: {line_count}行, {func_count}函数, {class_count}类',
            line=1,
            suggestion=D_ARCH_RULE_SUGGESTIONS['D12'],
            auto_fixable=False,
        ))
    return issues
def detect_d14_facade_exceed(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    if filepath and os.path.basename(filepath).lower() == '__init__.py':
        total = count_facade_entries(tree)
        if total > _MAX_FACADE_COUNT:
            issues.append(DiagnoseIssue(
                check_id='D14', severity=DiagnoseSeverity.ERROR,
                message=f'门面数量超标: {total} 个 (阈值 {_MAX_FACADE_COUNT})',
                line=1,
                suggestion=D_ARCH_RULE_SUGGESTIONS['D14'],
                auto_fixable=False,
            ))
    return issues
def _d21_is_version_target(target: ast.expr) -> bool:
    if isinstance(target, ast.Name):
        return target.id == '__version__'
    if isinstance(target, (ast.Tuple, ast.List)):
        return any(_d21_is_version_target(item) for item in target.elts)
    if isinstance(target, ast.Starred):
        return _d21_is_version_target(target.value)
    return False
def _d21_collect_bind(
        node: ast.stmt,
        tags: tuple[tuple[int, int], ...],
        binds: list[tuple[int, tuple[tuple[int, int], ...]]]) -> bool:
    if isinstance(node, ast.Assign):
        if any(_d21_is_version_target(target) for target in node.targets):
            binds.append((node.lineno, tags))
        return True
    if isinstance(node, ast.AnnAssign):
        if node.value is not None and _d21_is_version_target(node.target):
            binds.append((node.lineno, tags))
        return True
    return False
def _d21_push_block(
        stack: list[tuple[ast.stmt, tuple[tuple[int, int], ...]]],
        stmts: list[ast.stmt],
        tags: tuple[tuple[int, int], ...]) -> None:
    stack.extend((s, tags) for s in reversed(stmts))
def _d21_expand_block(
        node: ast.stmt,
        tags: tuple[tuple[int, int], ...],
        stack: list[tuple[ast.stmt, tuple[tuple[int, int], ...]]]) -> None:
    if isinstance(node, ast.If):
        _d21_push_block(stack, node.orelse, tags + ((id(node), 1),))
        _d21_push_block(stack, node.body, tags + ((id(node), 0),))
        return
    if isinstance(node, (ast.While, ast.For, ast.AsyncFor)):
        _d21_push_block(stack, node.orelse, tags)
        _d21_push_block(stack, node.body, tags)
        return
    if isinstance(node, (ast.With, ast.AsyncWith)):
        _d21_push_block(stack, node.body, tags)
        return
    if isinstance(node, TRY_NODE_TYPES):
        _d21_push_block(stack, node.finalbody, tags)
        _d21_push_block(stack, node.orelse, tags + ((id(node), 0),))
        for _hidx, _handler in enumerate(reversed(node.handlers)):
            _d21_push_block(stack, _handler.body, tags + ((id(node), _hidx + 1),))
        _d21_push_block(stack, node.body, tags)
        return
    if isinstance(node, MATCH_NODE_TYPES):
        for _cidx, _case in enumerate(reversed(node.cases)):
            _d21_push_block(stack, _case.body, tags + ((id(node), _cidx),))
def _d21_module_scope_version_binds(
        tree: ast.Module) -> list[tuple[int, tuple[tuple[int, int], ...]]]:
    binds: list[tuple[int, tuple[tuple[int, int], ...]]] = []
    stack: list[tuple[ast.stmt, tuple[tuple[int, int], ...]]] = [
        (stmt, ()) for stmt in reversed(tree.body)]
    while stack:
        node, tags = stack.pop()
        if _d21_collect_bind(node, tags, binds):
            continue
        _d21_expand_block(node, tags, stack)
    return binds
def _d21_binds_compatible(a_tags: tuple[tuple[int, int], ...],
                          b_tags: tuple[tuple[int, int], ...]) -> bool:
    b_map = dict(b_tags)
    return all(b_map.get(cid, branch) == branch for cid, branch in a_tags)
def _d21_compat_masks(
        binds: list[tuple[int, tuple[tuple[int, int], ...]]]) -> list[int]:
    n = len(binds)
    compat = [0] * n
    for i in range(n):
        for j in range(i + 1, n):
            if _d21_binds_compatible(binds[i][1], binds[j][1]):
                compat[i] |= 1 << j
                compat[j] |= 1 << i
    return compat
def _d21_greedy_mask(compat: list[int]) -> int:
    chosen: list[int] = []
    for i in sorted(range(len(compat)), key=lambda idx: -compat[idx].bit_count()):
        if all(compat[i] >> j & 1 for j in chosen):
            chosen.append(i)
    return sum(1 << i for i in chosen)
def _d21_exact_mask(compat: list[int]) -> int:
    n = len(compat)
    best = [0, 0]
    def _expand(idx: int, mask: int, size: int, cand: int) -> None:
        if size > best[0]:
            best[0], best[1] = size, mask
        if idx >= n or not cand or size + cand.bit_count() <= best[0]:
            return
        for k in range(idx, n):
            bit = 1 << k
            if not cand & bit:
                continue
            _expand(k + 1, mask | bit, size + 1, cand & compat[k])
    _expand(0, 0, 0, (1 << n) - 1)
    return best[1]
def _d21_effective_bind_lines(
        binds: list[tuple[int, tuple[tuple[int, int], ...]]]) -> list[int]:
    n = len(binds)
    if n <= 1:
        return [ln for ln, _ in binds]
    compat = _d21_compat_masks(binds)
    best_mask = _d21_greedy_mask(compat) if n > 16 else _d21_exact_mask(compat)
    return [binds[i][0] for i in range(n) if best_mask >> i & 1]
def detect_d21_duplicate_metadata(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    effective_lines = _d21_effective_bind_lines(_d21_module_scope_version_binds(tree))
    if len(effective_lines) > 1:
        issues.append(DiagnoseIssue(
            check_id='D21', severity=DiagnoseSeverity.WARN,
            message=f'重复元数据: __version__ 定义了 {len(effective_lines)} 次',
            line=effective_lines[1],
            suggestion='保留一处 __version__ 定义,使用 _version.py 作为 SSOT',
            auto_fixable=False,
        ))
    return issues
_D33_BOOTSTRAP_NAMES = frozenset({
    '_TESTS_DIR', '_SKILL_DIR', '_PARENT_DIR', '_p', '_os', '_sys',
})
def _d33_is_bootstrap_node(node: ast.AST) -> bool:
    if isinstance(node, ast.Assign):
        targets = node.targets
    elif isinstance(node, ast.AnnAssign):
        targets = [node.target]
    else:
        targets = []
    if targets:
        return all(isinstance(t, ast.Name) and t.id in _D33_BOOTSTRAP_NAMES
                   for t in targets)
    if isinstance(node, ast.For):
        return (isinstance(node.target, ast.Name)
                and node.target.id in _D33_BOOTSTRAP_NAMES)
    return False
def detect_d33_duplicate_file(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues = []
    seen: dict[str, list[int]] = {}
    for node in ast.iter_child_nodes(tree):
        if _d33_is_bootstrap_node(node):
            continue
        try:
            key = ast.dump(node)
        except Exception as _e:  # noqa: BLE001
            logger.debug("[D33] ast.dump 畸形节点跳过（保守）: %s", _e)
            continue
        seen.setdefault(key, []).append(node.lineno)
    for _lines in seen.values():
        if len(_lines) >= 3:
            _lines_desc = ', '.join(str(_ln) for _ln in _lines)
            issues.append(DiagnoseIssue(
                check_id='D33', severity=DiagnoseSeverity.WARN,
                message=f'疑似重复代码块(出现{len(_lines)}次): 行 {_lines_desc}',
                line=_lines[0],
                suggestion='考虑提取为公共函数或常量，或删除多余副本',
                auto_fixable=False,
            ))
    return issues
class MiniFileDetector:
    DETECTOR_ID = "D36"
    PATTERN_NAME = "MINI 文件"
    MIN_LINES = 20
    EXEMPT_PATTERNS: ClassVar[tuple[str, ...]] = (
        r'^from\s+typing\s+import',
        r'^class\s+\w*Error\(',
        r'^class\s+\w+\((?:abc\.)?ABC\b',
        r'^@dataclass',
        r'^__all__\s*=',
    )
    def _matches_exempt_pattern(self, source: str) -> bool:
        return any(re.search(pattern, source, re.MULTILINE)
                   for pattern in self.EXEMPT_PATTERNS)
    @staticmethod
    def _top_level_has_substantive_logic(
        node: ast.stmt, type_checking_aliases: frozenset[str],
        type_alias_names: frozenset[str],
    ) -> bool:
        if isinstance(node, (ast.Import, ast.ImportFrom, ast.Pass) + _TYPE_ALIAS_NODES):
            return False
        if is_constant_expr_stmt(node):
            return False
        if isinstance(node, (ast.Assign, ast.AnnAssign)):
            return _assignment_has_substantive_logic(node)
        return not (isinstance(node, ast.If) and _is_type_checking_guard(
            node, type_checking_aliases, type_alias_names))
    def _has_substantive_logic(self, tree: ast.Module) -> tuple[int, int, bool]:
        func_count = 0
        class_count = 0
        has_logic = False
        type_checking_aliases = frozenset(typing_type_checking_names(tree))
        type_alias_names = _typing_type_alias_names(tree)
        for node in ast.iter_child_nodes(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                func_count += 1
                if _effective_stmts(node.body):
                    has_logic = True
            elif isinstance(node, ast.ClassDef):
                class_count += 1
                if _class_has_substantive_logic(node):
                    has_logic = True
            elif self._top_level_has_substantive_logic(
                    node, type_checking_aliases, type_alias_names):
                has_logic = True
        return func_count, class_count, has_logic
    def _is_exempt_file(self, filepath: str) -> bool:
        if _is_exempt_basename(filepath):
            return True
        if is_runtime_temp_path(filepath):
            return True
        parents = filepath.replace('\\', '/').split('/')[:-1]
        return any(is_pruned_scan_dir(part, _SCAN_PRUNE_DIRS)
                   for part in parents if part)
    def detect_file(self, filepath: str) -> list[PatternFinding]:
        findings = []
        if self._is_exempt_file(filepath):
            return findings
        parsed = load_source_tree(filepath)
        if parsed is None:
            return findings
        source, tree = parsed
        lines = len(aligned_source_lines(source))
        if lines >= self.MIN_LINES:
            return findings
        if self._matches_exempt_pattern(source):
            return findings
        func_count, class_count, has_logic = self._has_substantive_logic(tree)
        if has_logic:
            return findings
        findings.append(PatternFinding(
            detector_id=self.DETECTOR_ID,
            pattern_name=self.PATTERN_NAME,
            severity="WARN",
            filepath=filepath,
            line=1,
            snippet=f"{lines} 行, {func_count} 函数, {class_count} 类",
            message=f"MINI 文件: {lines} 行,无实质逻辑（{func_count} 函数, {class_count} 类）",
            suggestion="合并到相关模块或删除（如为兼容性重定向,标记为 REDIRECT_STUB）",
        ))
        return findings
FRAGMENT_SAME_MODULE_MAX = 3
FRAGMENT_SUB_DIR_WARN_RATIO = 0.3
FRAGMENT_SUB_DIR_BLOCK_RATIO = 0.5
FRAGMENT_MERGE_TOLERANCE = 1.2
_FRAGMENT_MERGE_LINE_BUDGET = 500
_MIN_COMMON_PREFIX_LEN = 8
_SCAN_PRUNE_DIRS = frozenset(
    SCAN_COLLECT_PRUNE_DIRS_LOWER
    | TEST_DIR_CANDIDATES_LOWER
    | {name.lower() for name in AUDIT_SCAN_SKIP_DIRS})
_LEGITIMATE_MICRO_DIRS = TEST_DIR_CANDIDATES_LOWER | frozenset({"scripts"})
_LEGITIMATE_MICRO_PATTERNS = (
    r'.*_facade\.py$',
    r'^facade\.py$',
    r'.*_types\.py$',
    r'^config\.py$',
    r'^_helpers\.py$',
    r'.*_cli.*\.py$',
    r'^conftest\.py$',
)
_LEGITIMATE_COMPILED = tuple(re.compile(p) for p in _LEGITIMATE_MICRO_PATTERNS)
_STUB_MAX_LINES = 5
_TINY_FILE_MAX_LINES = MiniFileDetector.MIN_LINES
_FragmentTreeSignature = tuple[
    int,
    tuple[tuple[str, str | None], ...],
    tuple[str, ...],
]
_FRAGMENT_CACHE: dict[str, tuple[_FragmentTreeSignature, FragmentReport]] = {}
REBOUND_RISK_ZONE = (FRAGMENT_FILE_MIN_LINES, FRAGMENT_FILE_MIN_LINES + 2)
def _is_scanned_rel(rel: str) -> bool:
    return not any(is_pruned_scan_dir(seg, _SCAN_PRUNE_DIRS)
                   for seg in rel.replace("\\", "/").split("/")[:-1])
def _iter_scanned_py_files(root: Path):
    found, _partial = rglob_paths_tolerant(root, "*.[pP][yY]")
    for f in sorted(found):
        if f.name.startswith("."):
            continue
        rel = safe_relpath(f, root)
        if not _is_scanned_rel(rel):
            continue
        if is_test_file_path(rel):
            continue
        yield f, rel
def _is_legitimate_micro_file(rel_path: str, content: str) -> bool:
    posix = rel_path.replace("\\", "/")
    parts = posix.split("/")
    if any(part.lower() in _LEGITIMATE_MICRO_DIRS for part in parts[:-1]):
        return True
    fname = parts[-1].lower()
    if any(p.match(fname) for p in _LEGITIMATE_COMPILED):
        return True
    tree = _parse_micro_tree(content, "<micro-file>")
    if tree is not None and _d21_module_scope_version_binds(tree):
        return True
    return _is_pure_decorated_class_module(content)
def _is_pure_decorated_class_module(content: str) -> bool:
    tree = _parse_micro_tree(content, "<micro-file>")
    if tree is None:
        return False
    children = [n for n in ast.iter_child_nodes(tree)
                if not _is_import_or_docstring(n)]
    return _all_decorated_classes(children)
def _all_decorated_classes(nodes: list) -> bool:
    return bool(nodes) and all(
        isinstance(n, ast.ClassDef) and n.decorator_list for n in nodes)
def _is_static_all_declaration(node: ast.AST) -> bool:
    if isinstance(node, ast.Assign):
        targets = node.targets
    elif isinstance(node, ast.AnnAssign):
        targets = [node.target]
    else:
        return False
    if not any(isinstance(target, ast.Name) and target.id == "__all__"
               for target in targets):
        return False
    if node.value is None:
        return False
    try:
        value = ast.literal_eval(node.value)
    except (ValueError, SyntaxError):
        return False
    return (isinstance(value, (list, tuple))
            and all(isinstance(name, str) for name in value))
def _is_pure_import_stub(content: str, line_count: int) -> bool:
    if not (0 < line_count <= _STUB_MAX_LINES):
        return False
    tree = _parse_micro_tree(content, "<import-stub>")
    if tree is None:
        return False
    children = list(ast.iter_child_nodes(tree))
    has_import = any(isinstance(n, (ast.Import, ast.ImportFrom))
                     for n in children)
    return has_import and all(
        isinstance(n, (ast.Import, ast.ImportFrom))
        or _is_static_all_declaration(n)
        or (index == 0 and _is_import_or_docstring(n))
        for index, n in enumerate(children))
def _parse_micro_tree(content: str, filename: str) -> ast.AST | None:
    try:
        return compile(content, filename, "exec", ast.PyCF_ONLY_AST)
    except PARSE_DEGRADE_EXC as _e:
        log_swallowed(__name__, _e, context='_parse_micro_tree:parse')
        return None
def _is_import_or_docstring(node: ast.AST) -> bool:
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return True
    return (isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant)
            and isinstance(node.value.value, str))
def _rebound_zone(min_lines: int) -> tuple[int, int]:
    lo_offset = FRAGMENT_FILE_MIN_LINES - REBOUND_RISK_ZONE[0]
    hi_offset = REBOUND_RISK_ZONE[1] - FRAGMENT_FILE_MIN_LINES
    return min_lines - lo_offset, min_lines + hi_offset
def _check_rebound_risk(line_count: int, min_lines: int) -> str:
    lo, hi = _rebound_zone(min_lines)
    if lo <= line_count <= hi:
        if line_count <= min_lines:
            return f"反弹边界({line_count}行≤{min_lines})"
        return f"反弹风险区({line_count}行)"
    return ""
def _longest_common_prefix(items: list[str]) -> str:
    if not items:
        return ""
    if len(items) == 1:
        return ""
    prefix = items[0]
    for s in items[1:]:
        while not s.startswith(prefix):
            prefix = prefix[:-1]
            if not prefix:
                return ""
    return prefix
_SUFFIX_FRAGMENT_RE = re.compile(r"^([a-zA-Z_][a-zA-Z0-9_]{2,})_([a-z])$")
@dataclass
class FragmentFile:
    path: str
    lines: int
    prefix: str
    is_fragment: bool
    is_stub: bool = False
    rebound_risk: str = ""
@dataclass
class FragmentGroup:
    prefix: str
    files: list[FragmentFile] = field(default_factory=list)
    total_lines: int = 0
    ref_counts: dict[str, int] = field(default_factory=dict)
    total_refs: int = 0
    @property
    def file_count(self) -> int:
        return len(self.files)
    @property
    def avg_lines(self) -> float:
        return self.total_lines / self.file_count if self.file_count > 0 else 0.0
    @property
    def is_worth_merging(self) -> bool:
        return self.total_lines <= (_FRAGMENT_MERGE_LINE_BUDGET
                                    * FRAGMENT_MERGE_TOLERANCE)
    @property
    def risk_level(self) -> str:
        if self.total_refs > 5:
            return "high"
        if self.total_refs > 2:
            return "medium"
        return "low"
    def to_dict(self) -> dict[str, Any]:
        data = asdict(self)
        data.update({
            "file_count": self.file_count,
            "avg_lines": self.avg_lines,
            "is_worth_merging": self.is_worth_merging,
            "risk_level": self.risk_level,
        })
        return data
@dataclass
class _FragmentAggregate:
    min_lines: int
    exempt_paths: frozenset[str] = frozenset()
    fragments: list[FragmentFile] = field(default_factory=list)
    assigned_prefixes: dict[str, str] = field(default_factory=dict)
    groups: list[FragmentGroup] = field(default_factory=list)
    def admit_group(self, prefix: str, items: list[tuple[str, int]]) -> None:
        total_lines = sum(ln for _, ln in items)
        group = FragmentGroup(prefix=prefix, total_lines=total_lines)
        for rel_path, lines in items:
            fragment = FragmentFile(
                path=rel_path, lines=lines, prefix=prefix,
                is_fragment=self.is_fragment(rel_path, lines))
            group.files.append(fragment)
            self.assigned_prefixes[rel_path] = prefix
            if fragment.is_fragment:
                self.fragments.append(fragment)
        self.groups.append(group)
    def is_fragment(self, rel_path: str, lines: int) -> bool:
        return lines < self.min_lines and rel_path not in self.exempt_paths
def _collect_common_prefix_groups(
    unassigned: list[tuple[str, int]],
    aggregate: _FragmentAggregate,
) -> None:
    prefix_candidates = _lcp_prefix_candidates(unassigned)
    for prefix, items in sorted(prefix_candidates.items(), key=lambda x: -len(x[0])):
        _admit_prefix_candidates(prefix, items, aggregate)
def _admit_prefix_candidates(prefix: str, items: list[tuple[str, int]],
                             aggregate: _FragmentAggregate) -> None:
    deduped = sorted({(r, ln) for r, ln in items})
    if len(deduped) < 2:
        return
    fresh = [(r, ln) for r, ln in deduped
             if r not in aggregate.assigned_prefixes]
    if len(fresh) >= 2:
        aggregate.admit_group(prefix, fresh)
def _prefix_candidate(stem_a: str, stem_b: str) -> str | None:
    lcp = _longest_common_prefix([stem_a, stem_b])
    if len(lcp) < _MIN_COMMON_PREFIX_LEN or lcp in (stem_a, stem_b):
        return None
    truncated = lcp.rstrip("_")
    return truncated if len(truncated) >= _MIN_COMMON_PREFIX_LEN else None
def _lcp_prefix_candidates(unassigned: list[tuple[str, int]]
                         ) -> dict[str, list[tuple[str, int]]]:
    stems = [(Path(r).stem, r, ln) for r, ln in sorted(unassigned)]
    prefix_candidates: dict[str, list[tuple[str, int]]] = defaultdict(list)
    for i, (stem_i, ri, li) in enumerate(stems):
        for stem_j, rj, lj in stems[i + 1:]:
            prefix = _prefix_candidate(stem_i, stem_j)
            if prefix is not None:
                prefix_candidates[prefix].extend([(ri, li), (rj, lj)])
    return prefix_candidates
def _split_suffix_fragment_groups(
    files: list[tuple[str, int]],
) -> tuple[dict[str, list[tuple[str, int]]], list[tuple[str, int]]]:
    suffix_groups: dict[str, list[tuple[str, int]]] = defaultdict(list)
    unassigned: list[tuple[str, int]] = []
    for rel_path, lines in files:
        stem = Path(rel_path).stem
        m = _SUFFIX_FRAGMENT_RE.match(stem)
        if m:
            suffix_groups[m.group(1)].append((rel_path, lines))
        else:
            unassigned.append((rel_path, lines))
    return suffix_groups, unassigned
def _detect_fragment_groups(
    all_files: list[tuple[str, int]],
    min_lines: int,
    exempt_paths: frozenset[str],
) -> tuple[list[FragmentFile], list[FragmentGroup]]:
    aggregate = _FragmentAggregate(
        min_lines=min_lines, exempt_paths=exempt_paths)
    dir_files: dict[str, list[tuple[str, int]]] = defaultdict(list)
    for rel_path, lines in all_files:
        d = str(Path(rel_path).parent)
        dir_files[d].append((rel_path, lines))
    for _dir_path, files in sorted(dir_files.items()):
        _detect_dir_fragment_groups(files, aggregate)
    aggregate.groups.sort(key=lambda g: g.file_count, reverse=True)
    return aggregate.fragments, aggregate.groups
def _detect_dir_fragment_groups(files: list[tuple[str, int]],
                                aggregate: _FragmentAggregate) -> None:
    suffix_groups, unassigned = _split_suffix_fragment_groups(files)
    for prefix, items in suffix_groups.items():
        if len(items) >= 2:
            aggregate.admit_group(prefix, items)
        else:
            unassigned.extend(items)
    if len(unassigned) >= 2:
        _collect_common_prefix_groups(unassigned, aggregate)
    _mark_ungrouped_fragments(unassigned, aggregate)
def _mark_ungrouped_fragments(unassigned: list[tuple[str, int]],
                              aggregate: _FragmentAggregate) -> None:
    for rel_path, lines in unassigned:
        if rel_path in aggregate.assigned_prefixes:
            continue
        candidate = FragmentFile(
            path=rel_path, lines=lines, prefix="",
            is_fragment=aggregate.is_fragment(rel_path, lines))
        if candidate.is_fragment:
            aggregate.fragments.append(candidate)
@cache
def _stem_boundary_pattern(stem: str):
    return re.compile(r"\b" + re.escape(stem) + r"\b")
_IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
def _identifier_hits(stems: frozenset[str],
                     contents: dict[str, str]) -> dict[str, set[str]]:
    hits: dict[str, set[str]] = defaultdict(set)
    plain = frozenset(stem for stem in stems if stem.isidentifier())
    if not plain:
        return hits
    for rel, content in contents.items():
        for name in set(_IDENTIFIER_RE.findall(content)) & plain:
            hits[name].add(rel)
    return hits
def _annotate_group_references(groups: list[FragmentGroup],
                               contents: dict[str, str]) -> None:
    stems = frozenset(Path(ff.path).stem
                      for group in groups for ff in group.files)
    hits = _identifier_hits(stems, contents)
    exotic = {stem for stem in stems if not stem.isidentifier()}
    for group in groups:
        for ff in group.files:
            stem = Path(ff.path).stem
            if stem in exotic:
                pattern = _stem_boundary_pattern(stem)
                referenced = {rel for rel, content in contents.items()
                              if rel != ff.path and pattern.search(content)}
            else:
                referenced = hits.get(stem, set()) - {ff.path}
            group.ref_counts[ff.path] = len(referenced)
        group.total_refs = sum(group.ref_counts.values())
@dataclass
class DirectoryFragmentReport:
    path: str
    total_py_files: int
    fragment_files: list[FragmentFile]
    fragment_ratio: float
    level: str = "ok"
@dataclass
class FragmentReport:
    root: str
    total_files: int
    fragment_files: list[FragmentFile]
    fragment_groups: list[FragmentGroup]
    dir_reports: list[DirectoryFragmentReport]
    blocked: bool = False
    rebound_files: list[FragmentFile] = field(default_factory=list)
    min_lines: int = FRAGMENT_FILE_MIN_LINES
    warn_ratio: float = FRAGMENT_SUB_DIR_WARN_RATIO
    block_ratio: float = FRAGMENT_SUB_DIR_BLOCK_RATIO
    @property
    def rebound_zone(self) -> tuple[int, int]:
        return _rebound_zone(self.min_lines)
    @property
    def fragment_count(self) -> int:
        return len(self.fragment_files)
    @property
    def fragment_ratio(self) -> float:
        return self.fragment_count / self.total_files if self.total_files > 0 else 0.0
    @property
    def stub_files(self) -> list[FragmentFile]:
        return [f for f in self.fragment_files if f.is_stub]
    def to_dict(self) -> dict[str, Any]:
        data = asdict(self)
        data.update({
            "fragment_groups": [group.to_dict()
                                for group in self.fragment_groups],
            "fragment_count": self.fragment_count,
            "fragment_ratio": self.fragment_ratio,
            "stub_files": [item.path for item in self.stub_files],
            "rebound_zone": list(self.rebound_zone),
        })
        return data
def _collect_fragment_files(
    root_path: Path, min_lines: int,
) -> tuple[list[tuple[str, int]], set[str], list[FragmentFile],
           dict[str, str], frozenset[str]]:
    all_files: list[tuple[str, int]] = []
    exempt_paths: set[str] = set()
    stub_paths: set[str] = set()
    rebound_files: list[FragmentFile] = []
    contents: dict[str, str] = {}
    for f, rel in _iter_scanned_py_files(root_path):
        entry = _read_fragment_entry(f, rel, contents)
        if entry is None:
            continue
        content, lines = entry
        if Path(rel).name.lower() in _SPECIAL_FILES:
            continue
        all_files.append((rel, lines))
        if _is_fragment_exempt(rel, content, lines, min_lines):
            exempt_paths.add(rel)
            continue
        if _is_pure_import_stub(content, lines):
            stub_paths.add(rel)
        risk_desc = _check_rebound_risk(lines, min_lines)
        if risk_desc:
            rebound_files.append(FragmentFile(
                path=rel, lines=lines, prefix="",
                is_fragment=lines < min_lines, rebound_risk=risk_desc,
            ))
    return (all_files, stub_paths, rebound_files, contents,
            frozenset(exempt_paths))
def _is_fragment_exempt(
    rel: str, content: str, line_count: int, min_lines: int,
) -> bool:
    return (line_count < min_lines
            and _is_legitimate_micro_file(rel, content))
def _read_fragment_entry(f: Path, rel: str,
                         contents: dict[str, str]) -> tuple[str, int] | None:
    try:
        content = read_source_auto(f)
    except (OSError, AttributeError, KeyError, TypeError, ValueError, RuntimeError):
        logger.warning(MSG_EXCEPTION_BROAD_HANDLER, exc_info=True)
        return None
    lines = len(aligned_source_lines(content)) if content else 0
    contents[rel] = content
    return content, lines
def _build_dir_reports(fragments: list[FragmentFile],
                       all_files: list[tuple[str, int]],
                       warn_ratio: float, block_ratio: float
                       ) -> tuple[list[DirectoryFragmentReport], bool]:
    dir_fragments: dict[str, list[FragmentFile]] = defaultdict(list)
    for ff in fragments:
        d = Path(ff.path).parent.as_posix()
        dir_fragments[d].append(ff)
    dir_total: Counter[str] = Counter(
        Path(rel_path).parent.as_posix() for rel_path, _lines in all_files)
    dir_reports = []
    blocked = False
    for d in sorted(dir_total):
        total = dir_total[d]
        frags = dir_fragments.get(d, [])
        ratio = len(frags) / total
        level = _ratio_level(ratio, warn_ratio, block_ratio)
        blocked = blocked or level == "block"
        dir_reports.append(DirectoryFragmentReport(
            path=d, total_py_files=total, fragment_files=frags,
            fragment_ratio=ratio, level=level,
        ))
    return dir_reports, blocked
def _ratio_level(ratio: float, warn_ratio: float, block_ratio: float) -> str:
    if ratio > block_ratio:
        return "block"
    return "warn" if ratio > warn_ratio else "ok"
def detect_fragments(
    root: str,
    min_lines: int = FRAGMENT_FILE_MIN_LINES,
    max_same_module: int = FRAGMENT_SAME_MODULE_MAX,
    warn_ratio: float = FRAGMENT_SUB_DIR_WARN_RATIO,
    block_ratio: float = FRAGMENT_SUB_DIR_BLOCK_RATIO,
) -> FragmentReport:
    raw_root = os.fsdecode(os.fspath(root))
    if not raw_root.strip():
        raise ValueError("碎片分析目标目录不能为空")
    root_path = Path(raw_root).resolve()
    if not root_path.exists():
        raise FileNotFoundError(f"碎片分析目标目录不存在: {str(root_path)!r}")
    if not root_path.is_dir():
        raise NotADirectoryError(f"碎片分析目标路径非目录: {str(root_path)!r}")
    (all_files, stub_paths, rebound_files, contents,
     exempt_paths) = _collect_fragment_files(root_path, min_lines)
    fragments, groups = _detect_fragment_groups(
        all_files, min_lines, exempt_paths)
    for ff in fragments:
        ff.is_stub = ff.path in stub_paths
    _annotate_group_references(groups, contents)
    dir_reports, blocked = _build_dir_reports(
        fragments, all_files, warn_ratio, block_ratio)
    if any(_group_blocks(g, max_same_module) for g in groups):
        blocked = True
    return FragmentReport(
        root=str(root_path),
        total_files=len(all_files),
        fragment_files=fragments,
        fragment_groups=groups,
        dir_reports=dir_reports,
        blocked=blocked,
        rebound_files=rebound_files,
        min_lines=min_lines,
        warn_ratio=warn_ratio,
        block_ratio=block_ratio,
    )
def _mergeable_groups(groups: list[FragmentGroup]) -> list[FragmentGroup]:
    return [g for g in groups if g.is_worth_merging]
def _group_blocks(group: FragmentGroup, max_same_module: int) -> bool:
    return (any(f.is_fragment for f in group.files)
            and group.file_count > max_same_module
            and group.is_worth_merging)
def _fragment_tree_signature(root: str) -> _FragmentTreeSignature:
    count = 0
    states: list[tuple[str, str | None]] = []
    names: list[str] = []
    _root = Path(root)
    for f, rel in _iter_scanned_py_files(_root):
        count += 1
        names.append(rel)
        try:
            digest = hashlib.sha256(f.read_bytes()).hexdigest()
        except OSError as e:
            logger.debug("文件内容指纹读取失败（显式降级）: %s", e)
            states.append((rel, None))
            continue
        states.append((rel, digest))
    return (count, tuple(sorted(states)), tuple(sorted(names)))
def _detect_fragments_shared(root: str) -> FragmentReport:
    key = os.path.abspath(root)
    sig = _fragment_tree_signature(root)
    hit = _FRAGMENT_CACHE.get(key)
    if hit is not None and hit[0] == sig:
        return hit[1]
    report = detect_fragments(root)
    if len(_FRAGMENT_CACHE) >= 16:
        _FRAGMENT_CACHE.clear()
    _FRAGMENT_CACHE[key] = (sig, report)
    return report
def _is_dir_path(path_or_code) -> bool:
    return isinstance(path_or_code, str) and os.path.isdir(path_or_code)
def check_AF01(path_or_code: str, context: Any = None) -> Any:
    if not _is_dir_path(path_or_code):
        return None
    report = _detect_fragments_shared(path_or_code)
    tiny_files = [f for f in report.fragment_files
                  if f.lines < _TINY_FILE_MAX_LINES]
    stubs = report.stub_files
    if not tiny_files:
        return None
    return _af01_result(tiny_files, stubs)
def _af01_result(tiny_files: list[FragmentFile],
                 stubs: list[FragmentFile]) -> dict:
    desc = f"检测到 {len(tiny_files)} 个微型文件(<{_TINY_FILE_MAX_LINES}行)"
    if stubs:
        desc += f"，其中 {len(stubs)} 个纯导入 stub(优先合并/删除)"
    return {
        "rule_id": "AF01",
        "severity": "ERROR" if stubs else "WARN",
        "count": len(tiny_files),
        "files": [f.path for f in tiny_files[:20]],
        "stub_count": len(stubs),
        "stub_files": [f.path for f in stubs[:10]],
        "description": desc,
    }
def check_AF02(path_or_code: str, context: Any = None) -> Any:
    if not _is_dir_path(path_or_code):
        return None
    groups = _groups_with_fragments(_detect_fragments_shared(path_or_code))
    if not groups:
        return None
    names = ", ".join(g.prefix for g in groups)
    return {
        "rule_id": "AF02",
        "severity": "WARN",
        "count": len(groups),
        "prefixes": [g.prefix for g in groups],
        "description": f"同主题碎片聚集: {names}",
    }
def _groups_with_fragments(report: FragmentReport) -> list[FragmentGroup]:
    return [g for g in report.fragment_groups
            if any(f.is_fragment for f in g.files)]
def _check_dir_fragment_ratio(path_or_code: str, level: str,
                              rule_id: str, severity: str) -> Any:
    if not _is_dir_path(path_or_code):
        return None
    report = _detect_fragments_shared(path_or_code)
    hit_dirs = [d for d in report.dir_reports if d.level == level]
    if not hit_dirs:
        return None
    threshold = report.block_ratio if level == "block" else report.warn_ratio
    names = ", ".join(f"{d.path}({d.fragment_ratio:.0%})" for d in hit_dirs[:5])
    return {
        "rule_id": rule_id,
        "severity": severity,
        "count": len(hit_dirs),
        "dirs": [{"path": d.path, "ratio": d.fragment_ratio} for d in hit_dirs[:10]],
        "description": f"目录碎片率超{threshold:.0%}: {names}",
    }
def check_AF03(path_or_code: str, context: Any = None) -> Any:
    return _check_dir_fragment_ratio(path_or_code, "warn", "AF03", "WARN")
def check_AF04(path_or_code: str, context: Any = None) -> Any:
    return _check_dir_fragment_ratio(path_or_code, "block", "AF04", "BLOCK")
def _append_group_sections(lines: list[str],
                           groups: list[FragmentGroup]) -> None:
    if groups:
        lines.append("  -- 同前缀碎片组 --")
        for group in groups:
            _append_group_detail(lines, group)
        lines.append("")
    mergeable_groups = _mergeable_groups(groups)
    if mergeable_groups:
        lines.append("  -- 合并建议 --")
        for group in mergeable_groups:
            lines.append(
                f"  合并 [{group.prefix}] {group.file_count} 碎片 -> 1 文件"
                f"（~{group.total_lines} 行，风险 {group.risk_level}）"
            )
        lines.append("")
def _append_group_detail(lines: list[str], group: FragmentGroup) -> None:
    risk_tag = (f" · 引用{group.total_refs} · 风险{group.risk_level}"
                if group.total_refs > 0 else "")
    lines.append(
        f"  [{group.prefix}] {group.file_count} 文件 · {group.total_lines} 行 · "
        f"均{group.avg_lines:.0f}行/文件{risk_tag}"
    )
    for item in group.files:
        flag = " < 碎片" if item.is_fragment else ""
        lines.append(f"    - {item.path} ({item.lines}行){flag}")
def _append_dir_section(lines: list[str],
                        dir_reports: list[DirectoryFragmentReport]) -> None:
    warn_dirs = [d for d in dir_reports if d.level in ("warn", "block")]
    if warn_dirs:
        lines.append("  -- 高碎片率目录 --")
        for d in warn_dirs:
            tag = d.level.upper()
            lines.append(
                f"  [{tag}] {d.path}: {d.total_py_files} 文件 · "
                f"{len(d.fragment_files)} 碎片 ({d.fragment_ratio:.1%})"
            )
        lines.append("")
def _append_candidate_sections(lines: list[str],
                               report: FragmentReport) -> None:
    stubs = report.stub_files
    if stubs:
        lines.append(f"  -- 纯导入 stub（合并/删除优先候选，共 {len(stubs)} 个） --")
        for f in stubs[:20]:
            lines.append(f"    - {f.path} ({f.lines}行)")
        lines.append("")
    rebounds = report.rebound_files
    if rebounds:
        zone_lo, zone_hi = report.rebound_zone
        lines.append(
            f"  -- 反弹风险区 {zone_lo}-{zone_hi} 行（A10-OVERSIZED 修复删行后"
            f"回落 <{report.min_lines} 行将触发 D09，共 {len(rebounds)} 个） --"
        )
        for rb in rebounds[:20]:
            lines.append(f"    - {rb.path} ({rb.lines}行) {rb.rebound_risk}")
        lines.append("")
def format_report(report: FragmentReport) -> str:
    lines = [
        f"{'=' * 60}",
        f"  反碎片检测报告 — {report.root}",
        f"{'=' * 60}",
        "",
        f"  总文件数: {report.total_files}",
        f"  碎片文件: {report.fragment_count} ({report.fragment_ratio:.1%})",
        f"  检测结果: {'阻断' if report.blocked else '通过'}",
        "",
    ]
    _append_group_sections(lines, _groups_with_fragments(report))
    _append_dir_section(lines, report.dir_reports)
    _append_candidate_sections(lines, report)
    if not report.blocked:
        lines.append("  未发现阻断级碎片问题.")
    return "\n".join(lines)
def check_af(root: str) -> dict:
    report = _detect_fragments_shared(root)
    return report.to_dict()
def check_PI01(tree: ast.AST | None, source_lines: list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if tree is None or not filepath:
        return issues
    dir_path = os.path.dirname(os.path.abspath(filepath))
    if not os.path.isdir(dir_path):
        return issues
    if os.path.isfile(os.path.join(dir_path, "__init__.py")):
        return issues
    try:
        py_files = sorted(f for f in os.listdir(dir_path)
                          if f.lower().endswith(".py")
                          and not f.startswith(".")
                          and not is_test_file_path(f)
                          and os.path.isfile(os.path.join(dir_path, f)))
    except OSError as _e:
        log_swallowed(__name__, _e, context='check_PI01:listdir')
        return issues
    if len(py_files) < 2:
        return issues
    anchor = _pi01_anchor(py_files)
    if not anchor:
        return issues
    if os.path.normcase(os.path.basename(filepath)) \
            != os.path.normcase(anchor):
        return issues
    issues.append(_pi01_finding(py_files, dir_path, filepath))
    return issues
def _pi01_anchor(py_files: list[str]) -> str:
    for name in py_files:
        if not is_test_file_path(name):
            return name
    return ""
def _pi01_finding(
    py_files: list[str], dir_path: str, filepath: str
) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="PI-01", severity="P2", dimension="package",
        file=filepath, line=0,
        description=f"目录含 {len(py_files)} 个 .py 文件但缺少 __init__.py（包导入可能断裂）",
        suggestion=("根因: 无 __init__.py 的多文件目录在包内导入时依赖隐式命名空间包，行为易碎。该问题属于包结构类别。\n"
                    f"修复策略: 为 {os.path.basename(dir_path)}/ 创建 __init__.py（可空）；确为命名空间包则忽略\n"
                    "参考标准: Python 打包文档 / PEP 420"),
    )
GATE_DETECTORS: dict[str, Any] = {
    "D09": detect_d09_micro_file,
    "D12": detect_d12_fragmentation,
    "D14": detect_d14_facade_exceed,
    "D21": detect_d21_duplicate_metadata,
    "D33": detect_d33_duplicate_file,
}
def wiring_declarations() -> dict[str, dict[str, dict[str, Any]]]:
    return {
        "catalogs": {
            "rule_bindings": {
                'AF01': check_AF01, 'AF02': check_AF02,
                'AF03': check_AF03, 'AF04': check_AF04,
            },
            "recovered_bindings": {
                'PI01': check_PI01,
            },
            "new_pattern_classes": {
                'D36': MiniFileDetector,
            },
        },
    }

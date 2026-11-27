from __future__ import annotations

import ast
import logging
import threading
from dataclasses import dataclass, field
from typing import Any

from jwsgj.diag_se_knowledge import search_vuln_patterns
from jwsgj.diag_shared_ast_bindings import (
    collect_shadow_bindings,
    owner_scope,
)
from jwsgj.diag_shared_ast_nodes import (
    import_alias_bound_name,
    iter_arg_nodes,
    iter_unpack_target_names,
    resolve_call_name,
)
from jwsgj.diag_types_normalize import severity_key
from jwsgj.diag_types_vocab import TAINT_SOURCE_CATEGORY_BY_NAME

__all__ = [
    'ASSIGN_NODES',
    'BUILTIN_SANITIZERS',
    'BUILTIN_SINKS',
    'BUILTIN_SOURCES',
    'CONTAINER_STMTS',
    'SINK_NAMES',
    'SOURCE_NAMES',
    'CFGBlock',
    'CFGBuilder',
    'DUChainAnalyzer',
    'DefUse',
    'TaintNameResolution',
    'TaintSanitizer',
    'TaintSink',
    'TaintSource',
    'assignment_form',
    'assignment_targets',
    'container_header_exprs',
    'container_sub_bodies',
    'first_taint_source',
    'iter_calls_pruned',
    'taint_root_name',
    'taint_source_of',
]
logger = logging.getLogger(__name__)
logger.info("diag_taint_model 已加载: %d 项导出", len(__all__))
_TRY_NODE_TYPES: tuple[type, ...] = (
    (ast.Try, ast.TryStar) if hasattr(ast, "TryStar") else (ast.Try,))
def _attr_chain_parts(node: ast.AST) -> tuple[list[str], ast.AST]:
    parts: list[str] = []
    cur: ast.AST = node
    while isinstance(cur, ast.Attribute):
        parts.append(cur.attr)
        cur = cur.value
    return parts, cur
ASSIGN_NODES = (ast.Assign, ast.AnnAssign, ast.AugAssign, ast.NamedExpr)
def assignment_targets(node: ast.AST) -> list:
    if isinstance(node, ast.Assign):
        return list(node.targets)
    target = getattr(node, "target", None)
    return [target] if target is not None else []
def assignment_form(node: ast.AST) -> tuple[list, ast.AST] | None:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return [node.target], node.iter
    if not isinstance(node, ASSIGN_NODES):
        return None
    value = node.value
    if value is None:
        return None
    return assignment_targets(node), value
def _value_ref_node(node: ast.AST) -> ast.AST:
    while isinstance(node, (ast.Subscript, ast.Starred)):
        node = node.value
    return node
def taint_source_of(node: ast.AST | None, source_names: frozenset,
                     call_name_candidates=None) -> str | None:
    if not isinstance(node, ast.AST):
        return None
    target: ast.AST = node
    if isinstance(node, ast.Call):
        if call_name_candidates is None:
            name = resolve_call_name(node)
            if name in source_names:
                return name
        else:
            name = next((candidate
                         for candidate in call_name_candidates(node) or ()
                         if candidate in source_names), None)
            if name is not None:
                return name
        target = node.func
    target = _value_ref_node(target)
    if isinstance(target, ast.Attribute):
        if call_name_candidates is not None:
            return next((candidate
                         for candidate in call_name_candidates(target) or ()
                         if candidate in source_names), None)
        full_name = _taint_attr_chain(target)
        if full_name in source_names:
            return full_name
    if isinstance(target, ast.Name) and call_name_candidates is not None:
        return next((candidate
                     for candidate in call_name_candidates(target) or ()
                     if candidate in source_names), None)
    return None
def first_taint_source(value, source_names, prune=None,
                       call_name_candidates=None) -> str | None:
    source = taint_source_of(
        value, source_names, call_name_candidates=call_name_candidates)
    if source is not None:
        return source
    for sub in _iter_value_channel_nodes(value, prune=prune):
        source = taint_source_of(
            sub, source_names, call_name_candidates=call_name_candidates)
        if source:
            return source
    return None
@dataclass
class CFGBlock:
    id: int
    statements: list[ast.AST] = field(default_factory=list)
    successors: list[int] = field(default_factory=list)
    predecessors: list[int] = field(default_factory=list)
    is_entry: bool = False
    is_exit: bool = False
@dataclass
class DefUse:
    variable: str
    def_line: int
    use_lines: list[int]
    scope: str = ""
class CFGBuilder:
    _COMPOUND_TYPES = (ast.If, ast.For, ast.While, ast.AsyncFor,
                       *_TRY_NODE_TYPES, ast.Match,
                       ast.With, ast.AsyncWith)
    def __init__(self) -> None:
        self.blocks: list[CFGBlock] = []
        self._block_id = 0
        self._finalizers: list[list[ast.AST]] = []
        self._loop_stack: list[tuple[CFGBlock, CFGBlock]] = []
        self._exit_block: CFGBlock | None = None
        self._abrupt_finalizer_stack: list[int] = []
        self._abrupt_finalizer_blocks: dict[int, frozenset[int]] = {}
    def build(self, func_node: ast.FunctionDef | ast.AsyncFunctionDef
              ) -> list[CFGBlock]:
        self.blocks = []
        self._block_id = 0
        self._finalizers = []
        self._loop_stack = []
        self._abrupt_finalizer_stack = []
        self._abrupt_finalizer_blocks = {}
        entry = self._new_block(is_entry=True)
        self._exit_block = self._new_block(is_exit=True)
        self._process_body(func_node.body, entry)
        for block in self.blocks:
            if not block.successors and not block.is_exit:
                self._link(block, self._exit_block)
        return self._prune_unreachable_empty_blocks()
    def _new_block(self, **flags: Any) -> CFGBlock:
        block = CFGBlock(id=self._next_id(), **flags)
        self.blocks.append(block)
        if self._abrupt_finalizer_stack:
            self._abrupt_finalizer_blocks[block.id] = frozenset(
                self._abrupt_finalizer_stack)
        return block
    def _link(self, src: CFGBlock, dst: CFGBlock) -> None:
        if dst.id not in src.successors:
            src.successors.append(dst.id)
        if src.id not in dst.predecessors:
            dst.predecessors.append(src.id)
    def _join(self, *sources: CFGBlock | None) -> CFGBlock | None:
        live = [src for src in sources if src is not None]
        if not live:
            return None
        block = self._new_block()
        for src in live:
            self._link(src, block)
        return block
    def _reachable_block_ids(self) -> set[int]:
        by_id = {block.id: block for block in self.blocks}
        seen: set[int] = set()
        stack = [block.id for block in self.blocks if block.is_entry]
        while stack:
            bid = stack.pop()
            if bid in seen:
                continue
            seen.add(bid)
            stack.extend(by_id[bid].successors)
        return seen
    def _prune_unreachable_empty_blocks(self) -> list[CFGBlock]:
        reachable = self._reachable_block_ids()
        keep = [block for block in self.blocks
                if block.id in reachable or block.statements
                or block.is_entry or block.is_exit]
        remap = {block.id: index for index, block in enumerate(keep, start=1)}
        for block in keep:
            block.successors = [remap[s] for s in block.successors
                                if s in remap]
            block.predecessors = [remap[p] for p in block.predecessors
                                  if p in remap]
            block.id = remap[block.id]
        self.blocks = keep
        return keep
    def _process_body(self, body: list[ast.AST],
                      current: CFGBlock | None) -> CFGBlock | None:
        dead: CFGBlock | None = None
        for stmt in body:
            if current is not None:
                block = current
            else:
                if dead is None:
                    dead = self._new_block()
                block = dead
            if isinstance(stmt, (ast.Return, ast.Raise)):
                self._process_terminal(stmt, block)
                current = None
                dead = None
                continue
            if isinstance(stmt, (ast.Break, ast.Continue)):
                resumed = self._process_jump(stmt, block)
                if current is not None:
                    current = resumed
                dead = None
                continue
            if isinstance(stmt, self._COMPOUND_TYPES):
                result = self._process_compound(stmt, block)
                if current is not None:
                    current = result
                else:
                    dead = result
            else:
                block.statements.append(stmt)
        return current
    def _enter_region(self, stmt: ast.AST,
                      current: CFGBlock) -> CFGBlock:
        current.statements.append(stmt)
        region = self._new_block()
        self._link(current, region)
        return region
    def _process_compound(self, stmt: ast.AST,
                          current: CFGBlock) -> CFGBlock | None:
        if isinstance(stmt, ast.If):
            return self._process_if(stmt, current)
        if isinstance(stmt, (ast.For, ast.While, ast.AsyncFor)):
            return self._process_loop(stmt, current)
        if isinstance(stmt, (ast.With, ast.AsyncWith)):
            return self._process_with(stmt, current)
        if isinstance(stmt, ast.Match):
            return self._process_match(stmt, current)
        return self._process_try(stmt, current)
    @staticmethod
    def _match_pattern_irrefutable(pattern: ast.pattern) -> bool:
        if isinstance(pattern, ast.MatchAs):
            return (pattern.pattern is None
                    or CFGBuilder._match_pattern_irrefutable(pattern.pattern))
        if isinstance(pattern, ast.MatchOr):
            return any(CFGBuilder._match_pattern_irrefutable(sub)
                       for sub in pattern.patterns)
        return False
    @staticmethod
    def _match_has_irrefutable_case(node: ast.Match) -> bool:
        return any(
            case.guard is None
            and CFGBuilder._match_pattern_irrefutable(case.pattern)
            for case in node.cases)
    def _process_match(self, node: ast.Match,
                       current: CFGBlock) -> CFGBlock | None:
        current.statements.append(node)
        fall_throughs: list[CFGBlock | None] = []
        cases_reachable = True
        for case in node.cases:
            case_block = self._new_block()
            if cases_reachable:
                self._link(current, case_block)
                fall_throughs.append(
                    self._process_body(case.body, case_block))
            else:
                self._process_body(case.body, case_block)
            if (cases_reachable and case.guard is None
                    and self._match_pattern_irrefutable(case.pattern)):
                cases_reachable = False
        if not self._match_has_irrefutable_case(node):
            fall_throughs.append(current)
        return self._join(*fall_throughs)
    def _process_terminal(self, stmt: ast.Return | ast.Raise,
                          current: CFGBlock) -> None:
        current.statements.append(stmt)
        self._complete_abrupt(current, list(self._finalizers), None)
    def _process_jump(self, stmt: ast.Break | ast.Continue,
                      current: CFGBlock) -> CFGBlock | None:
        current.statements.append(stmt)
        if not self._loop_stack:
            return current
        break_target, continue_target = self._loop_stack[-1]
        target = (break_target if isinstance(stmt, ast.Break)
                  else continue_target)
        self._complete_abrupt(current, list(self._finalizers), target)
        return None
    def _complete_abrupt(self, current: CFGBlock,
                         finalizers: list[list[ast.AST]],
                         target: CFGBlock | None) -> None:
        if not finalizers:
            self._link(current, target or self._exit_block)
            return
        finalbody = finalizers[-1]
        self._abrupt_finalizer_stack.append(id(finalbody))
        try:
            finally_block = self._new_block()
            self._link(current, finally_block)
            previous = self._finalizers
            self._finalizers = finalizers[:-1]
            try:
                fall_through = self._process_body(finalbody, finally_block)
            finally:
                self._finalizers = previous
        finally:
            self._abrupt_finalizer_stack.pop()
        if fall_through is not None:
            self._complete_abrupt(fall_through, finalizers[:-1], target)
    def _process_with(self, node: ast.With | ast.AsyncWith,
                      current: CFGBlock) -> CFGBlock | None:
        body_block = self._enter_region(node, current)
        return self._process_body(node.body, body_block)
    def _process_if(self, node: ast.If, current: CFGBlock) -> CFGBlock | None:
        then_block = self._enter_region(node, current)
        fall_through = self._process_body(node.body, then_block)
        if node.orelse:
            else_block = self._new_block()
            self._link(current, else_block)
            fall_through_else = self._process_body(node.orelse, else_block)
        else:
            fall_through_else = current
        return self._join(fall_through, fall_through_else)
    def _process_loop(self, node: ast.For | ast.While | ast.AsyncFor,
                      current: CFGBlock) -> CFGBlock | None:
        header = self._new_block()
        self._link(current, header)
        header.statements.append(node)
        loop_body = self._new_block()
        self._link(header, loop_body)
        after_loop = self._new_block()
        self._loop_stack.append((after_loop, header))
        try:
            fall_through = self._process_body(node.body, loop_body)
        finally:
            self._loop_stack.pop()
        if fall_through is not None:
            self._link(fall_through, header)
        infinite_while = (
            isinstance(node, ast.While)
            and isinstance(node.test, ast.Constant)
            and bool(node.test.value))
        if infinite_while:
            return after_loop if after_loop.predecessors else None
        if node.orelse:
            else_block = self._new_block()
            self._link(header, else_block)
            fall_through_else = self._process_body(node.orelse, else_block)
            if fall_through_else is not None:
                self._link(fall_through_else, after_loop)
        else:
            self._link(header, after_loop)
        return after_loop if after_loop.predecessors else None
    @staticmethod
    def _block_may_raise(block: CFGBlock) -> bool:
        if len(block.statements) != 1:
            return True
        stmt = block.statements[0]
        if isinstance(stmt, ast.Return):
            return stmt.value is not None
        return not isinstance(stmt, (ast.Break, ast.Continue))

    def _process_try(self, node: ast.Try | ast.TryStar,
                     current: CFGBlock) -> CFGBlock | None:
        excluded_finalizers = {id(body) for body in self._finalizers}
        if node.finalbody:
            excluded_finalizers.add(id(node.finalbody))
            self._finalizers.append(node.finalbody)
        try:
            try_block = self._enter_region(node, current)
            body_blocks_start = len(self.blocks)
            fall_through = self._process_body(node.body, try_block)
            exception_sources = [
                block for block in (try_block,
                                    *self.blocks[body_blocks_start:])
                if self._abrupt_finalizer_blocks.get(
                    block.id, frozenset()).isdisjoint(excluded_finalizers)
                and self._block_may_raise(block)
            ]
            fall_throughs = [self._process_handlers(
                node, exception_sources)]
            if node.orelse:
                else_block = self._new_block()
                if fall_through is not None:
                    self._link(fall_through, else_block)
                fall_throughs.append(
                    self._process_body(node.orelse, else_block))
            else:
                fall_throughs.append(fall_through)
            merge_block = self._join(*fall_throughs)
        finally:
            if node.finalbody:
                self._finalizers.pop()
        if merge_block is None:
            return None
        return self._process_finally(node, merge_block)
    def _process_handlers(self, node: ast.Try | ast.TryStar,
                          exception_sources: list[CFGBlock]
                          ) -> CFGBlock | None:
        fall_throughs: list[CFGBlock | None] = []
        for handler in node.handlers:
            handler_block = self._new_block()
            for source in exception_sources:
                self._link(source, handler_block)
            fall_throughs.append(
                self._process_body(handler.body, handler_block))
        return self._join(*fall_throughs)
    def _process_finally(self, node: ast.Try | ast.TryStar,
                         merge_block: CFGBlock) -> CFGBlock | None:
        if not node.finalbody:
            return merge_block
        finally_block = self._new_block()
        self._link(merge_block, finally_block)
        return self._process_body(node.finalbody, finally_block)
    def _next_id(self) -> int:
        self._block_id += 1
        return self._block_id
class _DUState:
    def __init__(self, bindings=None) -> None:
        self.du_chains: dict[tuple[str, str], list[DefUse]] = {}
        self.scope_stack: list[str] = [""]
        if bindings is None:
            bindings = ({}, {}, frozenset())
        self.local_bindings, self.global_names, class_scopes = bindings
        self.class_segments: set[str] = set(class_scopes)
        self.owner_redirects: dict[tuple[str, str], str] = {}
        self.definition_origins: dict[int, str] = {}
        self.unbound_names: set[tuple[str, str]] = set()
        self.deferred_uses: list[tuple[str, str, str, int]] = []
    def cur_scope(self) -> str:
        return self.scope_stack[-1]
    def child_segment(self, name: str) -> str:
        return f"{self.cur_scope()}.{name}" if self.cur_scope() else name
    def declare_global(self, name: str) -> None:
        self.owner_redirects[(self.cur_scope(), name)] = ""
    def declare_nonlocal(self, name: str) -> None:
        for segment in reversed(self.scope_stack[:-1]):
            if not segment or segment in self.class_segments:
                continue
            if (name in self.local_bindings.get(segment, ())
                    or self.du_chains.get((segment, name))):
                self.owner_redirects[(self.cur_scope(), name)] = segment
                return
    def register(self, name: str, line: int) -> None:
        scope = self.owner_redirects.get(
            (self.cur_scope(), name), self.cur_scope())
        self.register_in_scope(scope, name, line)
    def register_in_scope(self, scope: str, name: str, line: int) -> None:
        key = (scope, name)
        self.unbound_names.discard(key)
        chain = DefUse(
            variable=name, def_line=line, use_lines=[], scope=key[0])
        self.du_chains.setdefault(key, []).append(chain)
        self.definition_origins[id(chain)] = scope
    def unbind(self, name: str) -> None:
        scope = self.owner_redirects.get(
            (self.cur_scope(), name), self.cur_scope())
        self.unbound_names.add((scope, name))
    def register_params(self, fd: Any) -> None:
        for p in iter_arg_nodes(fd.args):
            self.register(p.arg, fd.lineno)
    def visible(self, name: str) -> DefUse | None:
        for segment in reversed(self.scope_stack):
            redirect_key = (segment, name)
            if redirect_key in self.owner_redirects:
                owner = self.owner_redirects[redirect_key]
                if (owner, name) in self.unbound_names:
                    return None
                hits = self.du_chains.get((owner, name))
                return hits[-1] if hits else None
            if segment in self.class_segments and segment != self.scope_stack[-1]:
                continue
            if (segment, name) in self.unbound_names:
                return None
            hits = self.du_chains.get((segment, name))
            if hits:
                return hits[-1]
            if name in self.local_bindings.get(segment, ()):
                return None
        return None
    def defer_use(self, name: str, line: int) -> None:
        use_scope = self.cur_scope()
        owner = owner_scope(
            use_scope, name, self.local_bindings, self.global_names,
            frozenset(self.class_segments))
        if owner != use_scope:
            self.deferred_uses.append((owner, use_scope, name, line))
    def resolve_deferred_uses(self) -> None:
        for owner, use_scope, name, line in self.deferred_uses:
            if (owner, name) in self.unbound_names:
                continue
            target = None
            for chain in self.du_chains.get((owner, name), ()):
                if self.definition_origins.get(id(chain)) != use_scope:
                    target = chain
            if target is None:
                continue
            target.use_lines.append(line)
            target.use_lines.sort()
    def register_targets(self, node: Any, targets: Any,
                         scope: str | None = None,
                         line: int | None = None) -> None:
        lineno = getattr(node, "lineno", 0) if line is None else line
        for name in iter_unpack_target_names(targets):
            if scope is None:
                self.register(name, lineno)
            else:
                self.register_in_scope(scope, name, lineno)
class _DUVisitor(ast.NodeVisitor):
    def __init__(self, state: _DUState) -> None:
        self._st = state
        self._walrus_scope: str | None = None
        self._late_binding_scopes: set[str] = set()
        self._definition_site_scopes: set[str] = set()
    def visit_Assign(self, node: Any) -> None:
        self.visit(node.value)
        self._st.register_targets(node, node.targets)
        for target in node.targets:
            self.visit(target)
    def _bind_target(self, node: Any) -> None:
        self._st.register_targets(node, [node.target])
        self.visit(node.target)
    def _record_name_use(self, name: str, line: int) -> None:
        hit = self._st.visible(name)
        current = self._st.cur_scope()
        if (hit is not None
                and not (current in self._late_binding_scopes
                         and hit.scope != current)):
            hit.use_lines.append(line)
            return
        if current not in self._definition_site_scopes:
            self._st.defer_use(name, line)
    def visit_AnnAssign(self, node: Any) -> None:
        if node.value is not None:
            self.visit(node.value)
            self._bind_target(node)
        elif not isinstance(node.target, ast.Name):
            self.visit(node.target)
        self.visit(node.annotation)
    def visit_AugAssign(self, node: Any) -> None:
        self._visit_augassign_read(node.target)
        self.visit(node.value)
        self._st.register_targets(node, [node.target])
    def _visit_augassign_read(self, target: ast.AST) -> None:
        if isinstance(target, ast.Name):
            self._record_name_use(target.id, target.lineno)
        elif isinstance(target, ast.Attribute):
            self.visit(target.value)
        elif isinstance(target, ast.Subscript):
            self.visit(target.value)
            self.visit(target.slice)
    def visit_NamedExpr(self, node: Any) -> None:
        self.visit(node.value)
        if self._walrus_scope is None:
            self._bind_target(node)
            return
        self._st.register_targets(
            node, [node.target], scope=self._walrus_scope)
        self.visit(node.target)
    def visit_Lambda(self, node: Any) -> None:
        st = self._st
        self._visit_defaults(node.args)
        self._visit_arg_annotations(node.args)
        previous = self._walrus_scope
        self._walrus_scope = None
        scope = st.child_segment(
            f"<lambda>@{node.lineno}:{node.col_offset}")
        st.scope_stack.append(scope)
        self._late_binding_scopes.add(scope)
        try:
            st.register_params(node)
            self.visit(node.body)
        finally:
            self._late_binding_scopes.discard(scope)
            st.scope_stack.pop()
            self._walrus_scope = previous
    def _visit_comprehension(self, node: Any,
                             values: tuple[Any, ...]) -> None:
        st = self._st
        generators = node.generators
        if not generators:
            for value in values:
                self.visit(value)
            return
        first = generators[0]
        self.visit(first.iter)
        previous = self._walrus_scope
        if previous is None:
            self._walrus_scope = st.cur_scope()
        st.scope_stack.append(st.child_segment(
            f"<comp>@{node.lineno}:{node.col_offset}"))
        try:
            st.register_targets(first, first.target,
                                line=getattr(first.target, "lineno", node.lineno))
            self.visit(first.target)
            for cond in first.ifs:
                self.visit(cond)
            for gen in generators[1:]:
                self.visit(gen.iter)
                st.register_targets(
                    gen, gen.target, line=getattr(gen.target, "lineno",
                                                  node.lineno))
                self.visit(gen.target)
                for cond in gen.ifs:
                    self.visit(cond)
            for value in values:
                self.visit(value)
        finally:
            st.scope_stack.pop()
            self._walrus_scope = previous
    def visit_ListComp(self, node: Any) -> None:
        self._visit_comprehension(node, (node.elt,))
    visit_SetComp = visit_ListComp
    visit_GeneratorExp = visit_ListComp
    def visit_DictComp(self, node: Any) -> None:
        self._visit_comprehension(node, (node.key, node.value))
    def visit_For(self, node: Any) -> None:
        self.visit(node.iter)
        self._bind_target(node)
        for stmt in (*node.body, *node.orelse):
            self.visit(stmt)
    visit_AsyncFor = visit_For
    def visit_With(self, node: Any) -> None:
        for item in node.items:
            self.visit(item.context_expr)
            if item.optional_vars is not None:
                self._st.register_targets(node, [item.optional_vars])
                self.visit(item.optional_vars)
        for stmt in node.body:
            self.visit(stmt)
    visit_AsyncWith = visit_With
    def visit_Global(self, node: Any) -> None:
        for name in node.names:
            self._st.declare_global(name)
    def visit_Nonlocal(self, node: Any) -> None:
        for name in node.names:
            self._st.declare_nonlocal(name)
    def visit_Import(self, node: Any) -> None:
        for alias in node.names:
            name = import_alias_bound_name(alias, from_import=False)
            if name is not None:
                self._st.register(name, node.lineno)
        self.generic_visit(node)
    def visit_ImportFrom(self, node: Any) -> None:
        for alias in node.names:
            name = import_alias_bound_name(alias, from_import=True)
            if name is not None:
                self._st.register(name, node.lineno)
        self.generic_visit(node)
    def visit_ExceptHandler(self, node: Any) -> None:
        if node.type is not None:
            self.visit(node.type)
        if node.name:
            self._st.register(node.name, node.lineno)
        for stmt in node.body:
            self.visit(stmt)
        if node.name:
            self._st.unbind(node.name)
    def visit_Delete(self, node: Any) -> None:
        for target in node.targets:
            for name in iter_unpack_target_names(target):
                self._st.unbind(name)
            self.visit(target)
    def _visit_match_capture(self, node: Any) -> None:
        _name = getattr(node, "name", None)
        if _name:
            self._st.register(_name, node.lineno)
        elif (isinstance(node, getattr(ast, "MatchMapping", ()))
                and node.rest):
            self._st.register(node.rest, node.lineno)
        self.generic_visit(node)
    def visit_MatchAs(self, node: Any) -> None:
        self._visit_match_capture(node)
    visit_MatchStar = visit_MatchAs
    visit_MatchMapping = visit_MatchAs
    def _visit_function(self, node: Any) -> None:
        self._visit_definition_expressions(node)
        self._visit_function_scope(node, bind_name=True)
    def analyze_function(self, node: Any) -> None:
        self._visit_definition_expressions(node)
        self._visit_function_scope(node)
    def _visit_definition_expressions(self, node: Any) -> None:
        for dec in node.decorator_list:
            self.visit(dec)
        self._visit_defaults(node.args)
    def _visit_function_scope(self, node: Any,
                              bind_name: bool = False) -> None:
        st = self._st
        definition_scope = st.cur_scope()
        scope = st.child_segment(node.name)
        st.scope_stack.append(scope)
        self._late_binding_scopes.add(scope)
        previous = self._walrus_scope
        self._walrus_scope = None
        try:
            type_param_names = self._register_type_params(node)
            original_bindings = st.local_bindings.get(scope, frozenset())
            st.local_bindings[scope] = type_param_names
            self._visit_type_param_expressions(node)
            self._late_binding_scopes.discard(scope)
            self._definition_site_scopes.add(scope)
            self._walrus_scope = (
                st.scope_stack[-2] if len(st.scope_stack) > 1 else "")
            try:
                if node.returns is not None:
                    self.visit(node.returns)
                self._visit_arg_annotations(node.args)
            finally:
                st.local_bindings[scope] = (
                    original_bindings | type_param_names)
                self._definition_site_scopes.discard(scope)
                self._late_binding_scopes.add(scope)
                self._walrus_scope = None
            if bind_name:
                owner = st.owner_redirects.get(
                    (definition_scope, node.name), definition_scope)
                st.register_in_scope(owner, node.name, node.lineno)
            st.register_params(node)
            for stmt in node.body:
                self.visit(stmt)
        finally:
            self._late_binding_scopes.discard(scope)
            st.scope_stack.pop()
            self._walrus_scope = previous
    def _register_type_params(self, node: Any) -> frozenset[str]:
        names = tuple(
            name for tp in getattr(node, "type_params", None) or ()
            if isinstance((name := getattr(tp, "name", None)), str) and name)
        for name in names:
            self._st.register(name, node.lineno)
        return frozenset(names)
    def _visit_type_param_expressions(self, node: Any) -> None:
        for type_param in getattr(node, "type_params", None) or ():
            for attr in ("bound", "default_value"):
                value = getattr(type_param, attr, None)
                if value is not None:
                    self.visit(value)
    def _visit_defaults(self, args: Any) -> None:
        for default in list(args.defaults) + list(args.kw_defaults):
            if default is not None:
                self.visit(default)
    def _visit_arg_annotations(self, args: Any) -> None:
        for arg in iter_arg_nodes(args):
            if arg.annotation is not None:
                self.visit(arg.annotation)
    def visit_FunctionDef(self, node: Any) -> None:
        self._visit_function(node)
    visit_AsyncFunctionDef = visit_FunctionDef
    def visit_ClassDef(self, node: Any) -> None:
        st = self._st
        for dec in node.decorator_list:
            self.visit(dec)
        _seg = st.child_segment(node.name)
        st.class_segments.add(_seg)
        st.scope_stack.append(_seg)
        try:
            type_param_names = self._register_type_params(node)
            original_bindings = st.local_bindings.get(_seg, frozenset())
            st.local_bindings[_seg] = type_param_names
            self._late_binding_scopes.add(_seg)
            try:
                self._visit_type_param_expressions(node)
            finally:
                self._late_binding_scopes.discard(_seg)
            self._definition_site_scopes.add(_seg)
            try:
                for base in node.bases:
                    self.visit(base)
                for kw in node.keywords:
                    self.visit(kw.value)
                st.local_bindings[_seg] = (
                    original_bindings | type_param_names)
                for stmt in node.body:
                    self.visit(stmt)
            finally:
                st.local_bindings[_seg] = (
                    original_bindings | type_param_names)
                self._definition_site_scopes.discard(_seg)
        finally:
            st.scope_stack.pop()
        st.register(node.name, node.lineno)
    def visit_Name(self, node: Any) -> None:
        if isinstance(node.ctx, ast.Load):
            self._record_name_use(node.id, node.lineno)
        self.generic_visit(node)
class DUChainAnalyzer:
    def analyze(self, func_node: ast.FunctionDef | ast.AsyncFunctionDef
                ) -> list[DefUse]:
        module = ast.Module(body=[func_node], type_ignores=[])
        state = _DUState(collect_shadow_bindings(module))
        _DUVisitor(state).analyze_function(func_node)
        state.resolve_deferred_uses()
        return [du for _chains in state.du_chains.values() for du in _chains]
def _taint_attr_chain(node: ast.AST) -> str | None:
    parts, cur = _attr_chain_parts(node)
    if not isinstance(cur, ast.Name):
        return None
    parts.append(cur.id)
    return '.'.join(reversed(parts))
def _unpack_pair(targets, value):
    if not isinstance(value, (ast.Tuple, ast.List)):
        return None
    if len(targets) != 1 or not isinstance(targets[0], (ast.Tuple, ast.List)):
        return None
    elts = targets[0].elts
    starred = [index for index, target in enumerate(elts)
               if isinstance(target, ast.Starred)]
    if not starred:
        if len(elts) != len(value.elts):
            return None
        return elts, list(value.elts)
    if len(starred) != 1 or len(value.elts) < len(elts) - 1:
        return None
    index = starred[0]
    trailing = len(elts) - index - 1
    middle_end = len(value.elts) - trailing
    middle = ast.copy_location(ast.Tuple(
        elts=list(value.elts[index:middle_end]), ctx=ast.Load()), value)
    aligned = [*value.elts[:index], middle, *value.elts[middle_end:]]
    return elts, aligned
def _element_binding_pairs(targets, value) -> tuple:
    if len(targets) != 1:
        return tuple(
            _binding
            for _target in targets
            for _binding in _element_binding_pairs([_target], value))
    pair = _unpack_pair(targets, value)
    if pair is None:
        return ((targets, value),)
    return tuple(_binding
                 for _target, _element in zip(*pair, strict=True)
                 for _binding in _element_binding_pairs([_target], _element))
def _container_value_children(_cur: ast.AST) -> list[ast.AST] | None:
    if isinstance(_cur, (ast.Tuple, ast.List, ast.Set)):
        return list(_cur.elts)
    if isinstance(_cur, ast.Dict):
        _children = [_k for _k in _cur.keys if _k is not None]
        _children.extend(_cur.values)
        return _children
    if isinstance(_cur, ast.JoinedStr):
        return _joined_str_value_children(_cur)
    return None
def _joined_str_value_children(_cur: ast.JoinedStr) -> list[ast.AST]:
    _children: list[ast.AST] = []
    for _e in _cur.values:
        if isinstance(_e, ast.FormattedValue):
            _children.append(_e.value)
            if _e.format_spec is not None:
                _children.append(_e.format_spec)
        else:
            _children.append(_e)
    return _children
def _comprehension_value_children(_cur: ast.AST) -> list[ast.AST] | None:
    if isinstance(_cur, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
        _children = [_cur.elt]
        _children.extend(_g.iter for _g in _cur.generators)
        return _children
    if isinstance(_cur, ast.DictComp):
        _children = [_cur.key, _cur.value]
        _children.extend(_g.iter for _g in _cur.generators)
        return _children
    return None
def _operator_value_children(_cur: ast.AST) -> list[ast.AST] | None:
    if isinstance(_cur, (ast.Starred, ast.NamedExpr, ast.Await)):
        return [_cur.value]
    if isinstance(_cur, (ast.Attribute, ast.Subscript)):
        return [_cur.value]
    if isinstance(_cur, ast.UnaryOp):
        return [] if isinstance(_cur.op, ast.Not) else [_cur.operand]
    if isinstance(_cur, ast.BinOp):
        return [_cur.left, _cur.right]
    return None
def _call_value_children(_cur: ast.Call) -> list[ast.AST]:
    _children: list[ast.AST] = []
    if isinstance(_cur.func, ast.Attribute):
        _children.append(_cur.func.value)
    elif isinstance(_cur.func, (ast.Call, ast.Subscript)):
        _children.append(_cur.func)
    _children.extend(_cur.args)
    _children.extend(kw.value for kw in _cur.keywords
                     if kw.value is not None)
    return _children
def _value_channel_children(_cur: ast.AST) -> list[ast.AST] | None:
    if isinstance(_cur, ast.IfExp):
        return [_cur.body, _cur.orelse]
    if isinstance(_cur, ast.BoolOp):
        return list(_cur.values)
    _children = _container_value_children(_cur)
    if _children is not None:
        return _children
    _children = _comprehension_value_children(_cur)
    if _children is not None:
        return _children
    return _operator_value_children(_cur)
def _iter_value_channel_nodes(value: ast.AST, prune=None):
    _stack: list[ast.AST] = [value]
    while _stack:
        _cur = _stack.pop()
        if isinstance(_cur, ast.Call):
            if prune is not None and prune(_cur):
                continue
            yield _cur
            _stack.extend(reversed(_call_value_children(_cur)))
            continue
        yield _cur
        _children = _value_channel_children(_cur)
        if _children:
            _stack.extend(reversed(_children))
def taint_root_name(target: ast.AST):
    while isinstance(target, (ast.Subscript, ast.Attribute, ast.Starred)):
        target = target.value
    return target.id if isinstance(target, ast.Name) else None
class TaintNameResolution:
    @staticmethod
    def owner_key(scope: str, name: str,
                  shadow: tuple[dict, dict, frozenset]) -> tuple[str, str]:
        return (owner_scope(scope, name, shadow[0], shadow[1], shadow[2]),
                name)
    @staticmethod
    def resolve_taint_key(scope: str, name: str, tainted_vars: dict,
                          shadow: tuple[dict, dict, frozenset] | None = None):
        if shadow is None:
            _k = (scope, name)
            if _k in tainted_vars:
                return _k
            return ('', name) if ('', name) in tainted_vars else None
        _k = TaintNameResolution.owner_key(scope, name, shadow)
        return _k if _k in tainted_vars else None
CONTAINER_STMTS = (ast.For, ast.AsyncFor, ast.While,
                   *_TRY_NODE_TYPES, ast.With, ast.AsyncWith, ast.Match)
def iter_calls_pruned(expr: ast.AST):
    stack = [expr]
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda, ast.ClassDef)):
            continue
        if isinstance(node, ast.Call):
            yield node
        stack.extend(reversed(list(ast.iter_child_nodes(node))))
def container_header_exprs(stmt: ast.stmt) -> list[ast.expr]:
    if isinstance(stmt, (ast.If, ast.While)):
        return [stmt.test]
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        return [stmt.iter]
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        return [item.context_expr for item in stmt.items]
    if isinstance(stmt, ast.Match):
        return _match_header_exprs(stmt)
    return []
def _match_header_exprs(stmt: ast.Match) -> list[ast.expr]:
    guards = [case.guard for case in stmt.cases if case.guard is not None]
    return [stmt.subject, *guards]
def container_sub_bodies(stmt: ast.stmt) -> list[list[ast.stmt]]:
    if isinstance(stmt, _TRY_NODE_TYPES):
        return _try_sub_bodies(stmt)
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        return [stmt.body]
    if isinstance(stmt, ast.Match):
        return [case.body for case in stmt.cases]
    if isinstance(stmt, (ast.For, ast.AsyncFor, ast.While, ast.If)):
        return [stmt.body] + ([stmt.orelse] if stmt.orelse else [])
    return []
def _try_sub_bodies(stmt: ast.stmt) -> list[list[ast.stmt]]:
    subs = [stmt.body] + [handler.body for handler in stmt.handlers]
    subs.extend(body for body in (stmt.orelse, stmt.finalbody) if body)
    return subs
@dataclass
class TaintSource:
    name: str = ""
    pattern: str = ""
    category: str = ""
    severity: str = "P1"
    description: str = ""
    tainted_return: bool = False
@dataclass
class TaintSink:
    name: str = ""
    pattern: str = ""
    category: str = ""
    severity: str = "P0"
    description: str = ""
    dangerous_params: list[int] = field(default_factory=list)
    cwe_id: str = ""
@dataclass
class TaintSanitizer:
    name: str = ""
    pattern: str = ""
    category: str = ""
    description: str = ""
    sanitized_return: bool = True
BUILTIN_SOURCES: list[TaintSource] = []  # nosec E1-MUTABLE-GLOBAL  # jwsgj:suppress TP-07 — 导入期一次性填充（锁串行化）
BUILTIN_SINKS: list[TaintSink] = []  # nosec E1-MUTABLE-GLOBAL  # jwsgj:suppress TP-07 — 导入期填充+知识库扩展幂等防重
_EXTRA_SOURCES = frozenset(TAINT_SOURCE_CATEGORY_BY_NAME) | {
    'file.read', 'file.readline', 'file.readlines',
    'socket.recv', 'socket.recvfrom',
}
BUILTIN_SANITIZERS: list[TaintSanitizer] = []  # nosec E1-MUTABLE-GLOBAL  # jwsgj:suppress TP-07 — 导入期一次性填充
_REGISTRY_FILL_LOCK = threading.Lock()
_registry_filled = False
def _populate_builtin_registry() -> None:
    global _registry_filled
    with _REGISTRY_FILL_LOCK:
        if _registry_filled:
            return
        _fill_builtin_registry_once()
        _registry_filled = True
def _fill_builtin_registry_once() -> None:
    BUILTIN_SOURCES.extend(_builtin_source_entries())
    BUILTIN_SINKS.extend(_builtin_sink_entries())
    try:
        BUILTIN_SINKS.extend(_kb_sink_entries({s.name for s in BUILTIN_SINKS}))
    except Exception:
        logger.warning("[TaintRegistry] 漏洞知识库 sink 合并失败，降级为纯内置注册表", exc_info=True)
    BUILTIN_SANITIZERS.extend(_builtin_sanitizer_entries())
_BUILTIN_SOURCE_SPECS: tuple[tuple[str, str, str, str], ...] = (
    ('request.GET.get', 'user_input', 'P0', 'HTTP GET 参数'),
    ('request.POST.get', 'user_input', 'P0', 'HTTP POST 参数'),
    ('request.args.get', 'user_input', 'P0', 'Flask 请求参数'),
    ('request.json', 'user_input', 'P0', '请求体 JSON'),
    ('input', 'user_input', 'P1', 'stdin 输入'),
    ('sys.argv', 'user_input', 'P1', '命令行参数'),
    ('os.environ.get', 'environment', 'P2', '环境变量'),
    ('open', 'file_input', 'P2', '文件读取'),
    ('os.getenv', 'environment', 'P2', '环境变量读取'),
    ('sys.stdin', 'user_input', 'P1', '标准输入'),
    ('subprocess.check_output', 'user_input', 'P2', '子进程输出回读'),
    ('request.cookies.get', 'user_input', 'P0', 'HTTP Cookie'),
    ('request.headers.get', 'user_input', 'P0', 'HTTP 请求头'),
    ('request.form.get', 'user_input', 'P0', 'HTTP 表单参数'),
    ('globals', 'dynamic_namespace', 'P2', 'globals() 动态命名空间读取（任意属性注入风险）'),
    ('requests.get', 'network_response', 'P2', 'HTTP 响应体（外部数据，与 SSRF sink 双角色）'),
    ('flask.request.args.get', 'user_input', 'P0', 'Flask 请求参数（模块前缀形态）'),
    ('flask.request.form.get', 'user_input', 'P0', 'Flask 表单参数（模块前缀形态）'),
    ('flask.request.json.get', 'user_input', 'P0', 'Flask JSON 体（模块前缀形态）'),
    ('flask.request.values.get', 'user_input', 'P0', 'Flask 合并参数（模块前缀形态）'),
    ('flask.request.data.get', 'user_input', 'P0', 'Flask 原始体（模块前缀形态）'),
    ('flask.request.cookies.get', 'user_input', 'P0', 'Flask Cookie（模块前缀形态）'),
    ('flask.request.headers.get', 'user_input', 'P0', 'Flask 请求头（模块前缀形态）'),
    ('flask.request.files.get', 'user_input', 'P0', 'Flask 上传文件（模块前缀形态）'),
    ('flask.request.get_json', 'user_input', 'P0', 'Flask JSON 体（方法形态）'),
    ('request.get_json', 'user_input', 'P0', 'Flask JSON 体（裸方法形态）'),
    ('os.popen', 'process_output', 'P2', '子进程输出回读（与命令注入 sink 双角色）'),
    ('urlopen', 'network_response', 'P2', 'urllib 响应体（外部数据）'),
)
def _builtin_source_entries() -> list[TaintSource]:
    _entries = [
        TaintSource(name=name, category=category, severity=severity,
                    description=description, tainted_return=True)
        for name, category, severity, description in _BUILTIN_SOURCE_SPECS
    ]
    _seen = {_entry.name for _entry in _entries}
    for _name in sorted(_EXTRA_SOURCES):
        if _name in _seen:
            continue
        _entries.append(TaintSource(
            name=_name,
            category=TAINT_SOURCE_CATEGORY_BY_NAME.get(_name, "user_input"),
            severity="P1",
            description="内置输入源（补充注册表）",
            tainted_return=True,
        ))
    return _entries
_BUILTIN_SINK_SPECS: tuple[tuple[str, str, str, str, tuple[int, ...], str], ...] = (
    ('os.system', 'command_injection', 'P0', 'OS 命令执行', (0,), 'CWE-78'),
    ('subprocess.run', 'command_injection', 'P0', '子进程执行', (0,), 'CWE-78'),
    ('subprocess.Popen', 'command_injection', 'P0', '子进程创建', (0,), 'CWE-78'),
    ('subprocess.call', 'command_injection', 'P0', '子进程调用', (0,), 'CWE-78'),
    ('eval', 'code_injection', 'P0', '动态代码执行', (0,), 'CWE-94'),
    ('exec', 'code_injection', 'P0', '动态代码执行', (0,), 'CWE-94'),
    ('pickle.loads', 'deserialization', 'P0', '反序列化', (0,), 'CWE-502'),
    ('pickle.load', 'deserialization', 'P0', '反序列化', (0,), 'CWE-502'),
    ('yaml.load', 'deserialization', 'P0', 'YAML 反序列化', (0,), 'CWE-502'),
    ('open', 'path_traversal', 'P1', '文件操作', (0,), 'CWE-22'),
    ('os.remove', 'path_traversal', 'P1', '文件删除', (0,), 'CWE-22'),
    ('shutil.rmtree', 'path_traversal', 'P1', '目录删除', (0,), 'CWE-22'),
    ('sqlite3.execute', 'sql_injection', 'P0', 'SQL 执行', (0,), 'CWE-89'),
    ('cursor.execute', 'sql_injection', 'P0', 'SQL 执行', (0,), 'CWE-89'),
    ('os.popen', 'command_injection', 'P0', 'OS 管道命令执行', (0,), 'CWE-78'),
    ('subprocess.getoutput', 'command_injection', 'P1', '子进程输出获取', (0,), 'CWE-78'),
    ('subprocess.getstatusoutput', 'command_injection', 'P1', '子进程状态输出获取', (0,), 'CWE-78'),
    ('__import__', 'code_injection', 'P1', '动态导入', (0,), 'CWE-94'),
    ('conn.execute', 'sql_injection', 'P0', '数据库连接直接 SQL 执行', (0,), 'CWE-89'),
    ('session.execute', 'sql_injection', 'P0', 'SQLAlchemy 会话 SQL 执行', (0,), 'CWE-89'),
    ('os.unlink', 'path_traversal', 'P1', '文件删除', (0,), 'CWE-22'),
    ('jinja2.Template', 'ssti', 'P0', 'Jinja2 模板构造（含用户输入时 SSTI）', (0,), 'CWE-1336'),
    ('render_template_string', 'ssti', 'P0', 'Flask 字符串模板渲染 SSTI', (0,), 'CWE-1336'),
    ('django.template.Template', 'ssti', 'P1', 'Django 模板构造', (0,), 'CWE-1336'),
    ('mark_safe', 'xss', 'P1', 'Django mark_safe 绕过自动转义', (0,), 'CWE-79'),
    ('Markup', 'xss', 'P1', 'Flask Markup 标记安全内容', (0,), 'CWE-79'),
    ('etree.parse', 'xxe', 'P1', 'lxml XML 解析（默认解析外部实体）', (0,), 'CWE-611'),
    ('redirect', 'open_redirect', 'P2', 'Flask redirect 开放重定向', (0,), 'CWE-601'),
    ('HttpResponseRedirect', 'open_redirect', 'P2', 'Django HttpResponseRedirect 开放重定向', (0,), 'CWE-601'),
    ('requests.get', 'ssrf', 'P2', 'HTTP GET（URL 可控时 SSRF）', (0,), 'CWE-918'),
    ('requests.post', 'ssrf', 'P2', 'HTTP POST（URL 可控时 SSRF）', (0,), 'CWE-918'),
    ('urlopen', 'ssrf', 'P2', 'urllib URL 打开 SSRF', (0,), 'CWE-918'),
    ('httpx.get', 'ssrf', 'P2', 'httpx HTTP GET SSRF', (0,), 'CWE-918'),
    ('HttpResponse', 'xss', 'P1', 'Django HttpResponse 直接输出（未转义 XSS）', (0,), 'CWE-79'),
    ('marshal.loads', 'deserialization', 'P0', 'marshal 反序列化（不可信数据代码执行）', (0,), 'CWE-502'),
    ('xml.sax.parse', 'xxe', 'P1', 'xml.sax 解析（默认解析外部实体）', (0,), 'CWE-611'),
    ('Environment.from_string', 'ssti', 'P0', 'Jinja2 Environment.from_string 模板注入', (0,), 'CWE-1336'),
    ('os.path.join', 'path_traversal', 'P2', '路径拼接（含用户输入时 ../ 穿越）', (0,), 'CWE-22'),  # jwsgj:suppress SS-02 — 污点规则表，非执行面
)
def _builtin_sink_entries() -> list[TaintSink]:
    return [TaintSink(name=name, category=category, severity=severity,
                      description=description,
                      dangerous_params=list(params), cwe_id=cwe_id)
            for name, category, severity, description, params, cwe_id
            in _BUILTIN_SINK_SPECS]
_BUILTIN_SANITIZER_SPECS = (
    ('int', 'type_cast', '整数类型转换'),
    ('float', 'type_cast', '浮点类型转换'),
    ('bool', 'type_cast', '布尔类型转换'),
    ('html.escape', 'xss_prevention', 'HTML 转义'),
    ('markupsafe.escape', 'xss_prevention', 'MarkupSafe 转义'),
    ('shlex.quote', 'cmd_injection_prevention', 'Shell 参数引用'),
    ('bleach.clean', 'xss_prevention', 'Bleach HTML 净化'),
    ('escape', 'xss_prevention', 'HTML 转义（html.escape / django escape 同形态）'),
    ('pipes.quote', 'cmd_injection_prevention', 'Shell 参数引用（pipes）'),
    ('os.path.basename', 'path_sanitize', '去除路径部分（防路径遍历）'),
    ('secure_filename', 'path_sanitize', 'Werkzeug 安全文件名'),
    ('hashlib.sha256', 'hash_sanitize', 'SHA256 哈希（不可逆去污）'),
    ('hmac.new', 'hash_sanitize', 'HMAC 哈希（不可逆去污）'),
    ('conditional_escape', 'xss_prevention',
     'Django 条件 HTML 转义（自动转义关闭时仍安全）'),
    ('safe_join', 'path_sanitize', 'Django safe_join 安全路径拼接（阻断穿越）'),
    ('hashlib.md5', 'hash_sanitize', 'MD5 哈希（不可逆去污）'),
)
def _builtin_sanitizer_entries() -> list[TaintSanitizer]:
    return [TaintSanitizer(name=name, category=category, description=description)
            for name, category, description in _BUILTIN_SANITIZER_SPECS]
def _kb_sink_entries(existing_names: set[str]) -> list[TaintSink]:
    _entries: list[TaintSink] = []
    for _pattern in search_vuln_patterns():
        _kb_severity = severity_key(_pattern.get("severity") or "medium", "P1")
        for _sink_name in _pattern.get("sinks", []):
            if not _sink_name or _sink_name in existing_names:
                continue
            existing_names.add(_sink_name)
            _entries.append(TaintSink(
                name=_sink_name,
                category=_pattern.get("category", "general"),
                severity=_kb_severity,
                description="漏洞知识库 {}: {}".format(
                    _pattern.get("rule_id", ""), _pattern.get("description", "")),
                dangerous_params=[0],
            ))
    return _entries
_populate_builtin_registry()
SOURCE_NAMES = frozenset({s.name for s in BUILTIN_SOURCES} | _EXTRA_SOURCES)
SINK_NAMES = frozenset(s.name for s in BUILTIN_SINKS)

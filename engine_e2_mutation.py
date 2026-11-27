from __future__ import annotations

import ast
import importlib.util
import logging
import os
import random
import re
import subprocess
import sys
import tokenize
from bisect import bisect_right
from collections import defaultdict
from collections.abc import Iterator
from dataclasses import dataclass, field

try:
    import coverage as _coverage
except ImportError as _imp_err:
    logging.getLogger(__name__).debug(
        "[engine_e2_mutation] coverage 导入失败，行级覆盖通道降级占位 None: %s", _imp_err)
    _coverage = None
from jwsgj.diag_guard_io import safe_delete
from jwsgj.diag_shared_ast_nodes import (
    ast_name,
    dump_len,
    iter_def_site_nodes,
    split_identifier,
)
from jwsgj.diag_shared_ast_views import register_cache_release
from jwsgj.diag_shared_source_core import (
    ast_split_lines,
    byte_col_to_char_col,
    physical_lines_keepends,
    read_source_tree,
    read_source_with_fingerprint,
)
from jwsgj.diag_shared_source_scan import (
    tokenize_source_cached,
)
from jwsgj.diag_testing_test_index import (
    build_test_index,
    parse_pytest_summary,
    release_e_group_caches,
)
from jwsgj.diag_wiring_import_scan import (
    resolve_project_package,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import (
    get_temp_base,
    source_import_roots,
    subprocess_noartifact_env,
)
from jwsgj.runtime_scope import (
    SCAN_COLLECT_PRUNE_DIRS_LOWER,
    collect_py_files_default,
    is_backup_like_dir,
    is_runtime_log_artifact,
    is_test_file_path,
    is_test_source_basename,
)
from jwsgj.shared_cache import SharedCache, require_warmed

register_cache_release(
    "e_group_caches", release_e_group_caches, "E 组测试索引缓存", order=170)
__all__ = [
    'MAX_INDIVIDUAL_FINDINGS',
    'SCOPE_END',
    'ClosureEvidence',
    'MutationFinding',
    'MutationTarget',
    'TargetedMutationAnalyzer',
    'build_kill_closure',
    'build_ti_by_module',
    'check_static_survival',
    'iter_module_level_exprs',
    'iter_own_nodes',
    'load_reexport_map',
    'module_name_for_path',
    'own_scope_visit_node',
    'run_f2_mutation_targeted',
    'visit_module_ref_node',
]
logger = logging.getLogger("jwsgj.engine_e2_mutation")
_MUTATION_VERIFY_SAMPLE_SIZE = 6
_MUTATION_VERIFY_MIN_SAMPLE = _MUTATION_VERIFY_SAMPLE_SIZE - 1
_MUTATION_VERIFY_FALSE_KILLED_LIMIT = 0.2
_VERIFY_FLIP_BINOP = {ast.Add: "-", ast.Sub: "+", ast.Mult: "//",
                      ast.FloorDiv: "*", ast.Mod: "-"}
_VERIFY_OP_SRC = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*",
                  ast.FloorDiv: "//", ast.Mod: "%"}
_VERIFY_FLIP_CMP = {ast.Eq: "!=", ast.NotEq: "==", ast.Lt: ">=", ast.GtE: "<",
                    ast.LtE: ">", ast.Gt: "<=", ast.Is: "is not",
                    ast.IsNot: "is", ast.In: " not in ", ast.NotIn: " in "}
_VERIFY_CMP_SRC = {ast.Eq: "==", ast.NotEq: "!=", ast.Lt: "<", ast.Gt: ">",
                   ast.LtE: "<=", ast.GtE: ">=", ast.Is: "is",
                   ast.IsNot: "is not", ast.In: " in ", ast.NotIn: " not in "}
_STATUS_COUNTER_KEYS = frozenset({"verified_killed", "baseline_failed", "false_killed"})
_EMPTY_SUBMODULE_BINDS = frozenset()
_BASELINE_FAILED_RCS = (1, 2, 3)
_RESTORE_ABORT_NOTE = "源码恢复失败，剩余样本中止（详见 details）"
_TARGET_COMPLEXITY_DUMP_LIMIT = 100
_PYTEST_RUN_TIMEOUT = 180
_BRANCH_LINE_UNPROVEN = -1
@dataclass(slots=True)
class MutationTarget:
    file: str
    line: int
    col_offset: int
    node_type: str
    mutation_op: str
    risk_source: str
    confidence: float
    func_name: str = ""
    end_lineno: int = 0
    end_col_offset: int = -1
    module: str = field(init=False, default="")
    def __post_init__(self):
        bn = os.path.basename(self.file)
        self.module = bn[:-3] if bn.casefold().endswith(".py") else bn
@dataclass(slots=True)
class MutationFinding:
    rule_id: str
    severity: str
    confidence: float
    message: str
    file: str
    line: int
    extra: dict = field(default_factory=dict)
@dataclass(slots=True)
class ClosureEvidence:
    kill_closure: set = field(default_factory=set)
    module_assert_imports: set = field(default_factory=set)
    ambiguous_mods: set = field(default_factory=set)
    ambiguous_funcs: set = field(default_factory=set)
MAX_INDIVIDUAL_FINDINGS = 5
def iter_own_nodes(func_node: ast.AST) -> Iterator[ast.AST]:
    stack = list(ast.iter_child_nodes(func_node))
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        yield node
        stack.extend(ast.iter_child_nodes(node))
def _test_file_name(mod: str) -> str:
    return f"test_{mod}.py"
def _mirror_source_dir(rel_file: str) -> str:
    return rel_file.replace("\\", "/").rpartition("/")[0]
def _pick_mirror_candidate(cands: list, rel_file: str) -> str:
    src_dir = _mirror_source_dir(rel_file)
    if not src_dir:
        return cands[0][0]
    src_segs = src_dir.split("/")
    best, best_depth = cands[0][0], 0
    for ap, rel in cands:
        segs = rel.split("/")[:-1]
        depth = 0
        for got, want in zip(reversed(segs), reversed(src_segs),
                             strict=False):
            if got != want:
                break
            depth += 1
        if depth > best_depth:
            best, best_depth = ap, depth
    return best
def _resolve_test_file(skill_dir: str, mod: str,
                       rel_file: str = "") -> str | None:
    if not skill_dir:
        return None
    cands = _test_file_candidates(skill_dir, mod)
    if not cands:
        return None
    return _pick_mirror_candidate(cands, rel_file)
def _engine_test_files(skill_dir: str) -> list[str]:
    files: list[str] = []
    for root, dirs, filenames in os.walk(skill_dir):
        _prune_execution_walk_dirs(dirs)
        dirs.sort()
        for name in sorted(filenames):
            if (name.lower().endswith(".py")
                    and is_test_source_basename(name)):
                files.append(os.path.join(root, name))
    return files
def _test_file_candidates(skill_dir: str, mod: str) -> list[tuple[str, str]]:
    wanted = {_test_file_name(mod), f"{mod}_test.py"}
    root = os.path.abspath(skill_dir)
    cands: list[tuple[str, str]] = []
    for tf in _engine_test_files(skill_dir):
        if os.path.basename(tf) not in wanted:
            continue
        ap = os.path.abspath(tf)
        try:
            rel = os.path.relpath(ap, root)
        except ValueError as _e:
            log_swallowed(__name__, _e,
                          context=f'_test_file_candidates:{type(_e).__name__}')
            continue
        if rel == os.pardir or rel.startswith(os.pardir + os.sep):
            continue
        cands.append((ap, rel.replace(os.sep, "/")))
    return cands
def _test_target_rel(ap: str, skill_dir: str) -> str:
    rel = os.path.relpath(ap, os.path.abspath(skill_dir))
    return rel.replace(os.sep, "/")
def _pytest_run_cmd(test_target: str) -> list[str]:
    cmd = [sys.executable, "-m", "pytest", test_target,
           "-x", "-q", "--no-header", "-p", "no:cacheprovider",
           "-o", "addopts="]
    if importlib.util.find_spec("xdist") is not None:
        cmd += ["-n", "0"]
    return cmd
def _pytest_env(skill_dir: str) -> dict:
    env = subprocess_noartifact_env()
    env["PYTHONPYCACHEPREFIX"] = os.path.join(
        get_temp_base(skill_dir), f"jwsgj_f2_pyc_isolate_{os.getpid()}")
    roots = [os.path.abspath(skill_dir)]
    roots.extend(source_import_roots(roots[0]))
    ambient = env.get("PYTHONPATH", "")
    if ambient:
        roots.append(ambient)
    env["PYTHONPATH"] = os.pathsep.join(roots)
    return env
def _baseline_state(skill_dir: str, test_target: str,
                    cache: dict) -> bool | None:
    key = test_target
    if key in cache:
        return cache[key]
    state: bool | None
    try:
        r = subprocess.run(  # jwsgj:suppress SYM-TAINT — 审计认可：cmd 由 _pytest_run_cmd 内部构造（sys.executable 起始）
            _pytest_run_cmd(test_target),
            cwd=skill_dir, capture_output=True, text=True,
            encoding="utf-8", errors="replace", timeout=_PYTEST_RUN_TIMEOUT,
            check=False, env=_pytest_env(skill_dir))
        output = ((getattr(r, "stdout", "") or "")
                  + (getattr(r, "stderr", "") or ""))
        summary = parse_pytest_summary(output)
        if r.returncode == 0:
            state = True if summary is not None and summary[1] > 0 else None
        elif summary is None or r.returncode not in _BASELINE_FAILED_RCS:
            state = None
        else:
            state = False
    except (OSError, subprocess.TimeoutExpired):
        logger.debug("基线运行异常，三态判定为不可判定: %s", test_target,
                     exc_info=True)
        state = None
    cache[key] = state
    return state
def _starts_with_keyword(text: str, keyword: str) -> bool:
    if not text.startswith(keyword):
        return False
    nxt = text[len(keyword):len(keyword) + 1]
    return not nxt or not (nxt.isalnum() or nxt == "_")
def _line_symbol_span(seg_b: bytes, osym: str,
                      lo: int, hi: int) -> tuple[int, int] | None:
    if " " in osym:
        pattern = re.escape(osym).replace(r"\ ", r"\s+").encode("ascii")
        match = re.search(pattern, seg_b[lo:hi])
        if match is None:
            return None
        return lo + match.start(), lo + match.end()
    idx = seg_b.find(osym.encode("utf-8"), lo, hi)
    return (idx, idx + len(osym)) if idx >= 0 else None
def _flip_line_symbol(lines: list[str], lineno: int, lo: int, hi: int,
                      osym: str, nsym: str) -> bool:
    seg_b = lines[lineno - 1].encode("utf-8")
    span = _line_symbol_span(seg_b, osym, lo, hi)
    if span is None and osym != osym.strip():
        osym = osym.strip()
        nsym = nsym.strip()
        span = _line_symbol_span(seg_b, osym, lo, hi)
    if span is None:
        return False
    start, end = span
    lines[lineno - 1] = (
        seg_b[:start] + nsym.encode("utf-8")
        + seg_b[end:]).decode("utf-8")
    return True
def _single_line_infix_span(node, left, right) -> tuple[int, int] | None:
    if (node.end_lineno != node.lineno or left.end_lineno != node.lineno
            or right.lineno != node.lineno):
        return None
    lo, hi = left.end_col_offset, right.col_offset
    if not (node.col_offset <= lo <= hi <= node.end_col_offset):
        return None
    return lo, hi
def _flip_symbol_between(node, lines: list[str], left, right,
                         src_map: dict, dst_map: dict,
                         op_type) -> str | None:
    osym = src_map.get(op_type)
    nsym = dst_map.get(op_type)
    if not osym or not nsym:
        return None
    span = _single_line_infix_span(node, left, right)
    if span is None:
        return None
    if not _flip_line_symbol(lines, node.lineno, span[0], span[1],
                             osym, nsym):
        return None
    return "".join(lines)
def _mutate_flip_operator(node: ast.BinOp, lines: list[str]) -> str | None:
    return _flip_symbol_between(node, lines, node.left, node.right,
                                _VERIFY_OP_SRC, _VERIFY_FLIP_BINOP,
                                type(node.op))
def _mutate_flip_comparator(node: ast.Compare, lines: list[str]) -> str | None:
    if not node.ops:
        return None
    return _flip_symbol_between(node, lines, node.left, node.comparators[0],
                                _VERIFY_CMP_SRC, _VERIFY_FLIP_CMP,
                                type(node.ops[0]))
def _bool_operator_span(seg_b: bytes, op: str, lo: int,
                        hi: int) -> tuple[int, int] | None:
    span = _line_symbol_span(seg_b, f" {op} ", lo, hi)
    if span is not None:
        return span
    span = _line_symbol_span(seg_b, op, lo, hi)
    if span is None:
        return None
    start, end = span
    while (start > lo and seg_b[start - 1:start]
           in (b" ", b"\t", b"\f", b"\x0b")):
        start -= 1
    return start, end
def _mutate_remove_operand(node: ast.BoolOp, lines: list[str]) -> str | None:
    v1 = node.values[0]
    v2 = node.values[1]
    if (v1.end_lineno != node.lineno or v2.lineno != node.lineno
            or node.end_lineno != node.lineno):
        return None
    seg = lines[node.lineno - 1]
    _seg_b = seg.encode("utf-8")
    _op = "or" if isinstance(node.op, ast.Or) else "and"
    op_span = _bool_operator_span(
        _seg_b, _op, v1.end_col_offset, v2.col_offset)
    if op_span is None:
        return None
    remove_end = node.end_col_offset
    if len(node.values) > 2:
        next_op = _bool_operator_span(
            _seg_b, _op, v2.end_col_offset, node.values[2].col_offset)
        if next_op is None:
            return None
        remove_end = next_op[0]
    left = _seg_b[:op_span[0]]
    right = _seg_b[remove_end:]
    if (len(node.values) > 2 and left and right
            and not left[-1:].isspace() and not right[:1].isspace()
            and right.startswith(_op.encode("ascii"))):
        left += b" "
    lines[node.lineno - 1] = (left + right).decode("utf-8")
    return "".join(lines)
def _condition_colon_end(lines: list[str],
                          node: ast.If) -> tuple[int, int] | None:
    tokens = tokenize_source_cached("".join(lines))
    if tokens is None:
        return None
    start_pos = (
        node.test.end_lineno,
        byte_col_to_char_col(
            lines[node.test.end_lineno - 1], node.test.end_col_offset),
    )
    statement_pos = (
        node.lineno,
        byte_col_to_char_col(lines[node.lineno - 1], node.col_offset),
    )
    depth = 0
    for tok in tokens:
        if tok.start < statement_pos or tok.end > start_pos:
            continue
        if tok.type == tokenize.OP:
            if tok.string in ("(", "[", "{"):
                depth += 1
            elif tok.string in (")", "]", "}"):
                depth -= 1
    for tok in tokens:
        if tok.start < start_pos:
            continue
        if tok.type == tokenize.OP:
            if tok.string in ("(", "[", "{"):
                depth += 1
            elif tok.string in (")", "]", "}"):
                depth -= 1
            elif tok.string == ":" and depth == 0:
                return tok.start[0], tok.end[1]
        elif tok.type == tokenize.NEWLINE:
            return None
    return None
def _mutate_remove_condition(node: ast.If, lines: list[str]) -> str | None:
    seg = lines[node.lineno - 1]
    stripped = seg.lstrip()
    indent = seg[:len(seg) - len(stripped)]
    _is_elif = _starts_with_keyword(stripped, "elif")
    _is_if = _starts_with_keyword(stripped, "if")
    if not (_is_if or _is_elif):
        return None
    _t = node.test
    if _t.end_lineno != node.lineno:
        return None
    cond_end = _condition_colon_end(lines, node)
    if cond_end is None:
        return None
    colon_line, colon_end = cond_end
    _kw = "elif True:" if _is_elif else "if True:"
    suffix = lines[colon_line - 1][colon_end:]
    lines[node.lineno - 1:colon_line] = [indent + _kw + suffix]
    return "".join(lines)
_MUTATION_DISPATCH = {
    "flip_operator": (ast.BinOp, None, _mutate_flip_operator, "cmp_op"),
    "flip_comparator": (ast.Compare, lambda n: bool(n.ops),
                        _mutate_flip_comparator, "cmp_op"),
    "remove_operand": (ast.BoolOp, lambda n: len(n.values) >= 2,
                        _mutate_remove_operand, "bool"),
    "remove_condition": (ast.If, None, _mutate_remove_condition, "if"),
}
def _same_target_node(node, target: MutationTarget) -> bool:
    if (node.lineno != target.line
            or node.col_offset != target.col_offset):
        return False
    if not target.end_lineno:
        return True
    return (node.end_lineno == target.end_lineno
            and node.end_col_offset == target.end_col_offset)
def _dispatch_mutation(node, target: MutationTarget, lines: list) -> tuple:
    entry = _MUTATION_DISPATCH.get(target.mutation_op)
    if entry is None:
        return False, None
    ast_type, extra_gate, handler, _layer = entry
    if not isinstance(node, ast_type):
        return False, None
    if not _same_target_node(node, target):
        return False, None
    if extra_gate is not None and not extra_gate(node):
        return False, None
    return True, handler(node, lines)
def _apply_real_mutation(src: str, target: MutationTarget) -> str | None:
    try:
        tree = ast.parse(src)
    except (SyntaxError, ValueError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_apply_real_mutation:{type(_e).__name__}')
        return None
    lines = physical_lines_keepends(src)
    for node in walk_nodes(tree):
        matched, mutated = _dispatch_mutation(node, target, lines)
        if matched:
            return mutated
    return None
def _append_note(entry: dict, text: str, limit: int = 120) -> None:
    prev = entry.get("note")
    merged = (prev + "; " + text) if prev else text
    if len(merged) <= limit:
        entry["note"] = merged
        return
    kept = ""
    dropped = False
    for seg in reversed(merged.split("; ")):
        trial = (seg + "; " + kept) if kept else seg
        if len(trial) > limit:
            dropped = True
            break
        kept = trial
    if kept:
        entry["note"] = ("… " if dropped else "") + kept
        return
    entry["note"] = merged[:max(limit - 1, 1)] + "…"
def _read_source_with_encoding(ap: str) -> tuple[str, str] | None:
    try:
        with open(ap, "rb") as fh:
            encoding, _ = tokenize.detect_encoding(fh.readline)
    except (OSError, SyntaxError, LookupError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_read_source_with_encoding:{type(_e).__name__}')
        return None
    try:
        with open(ap, encoding=encoding, newline="") as fh:
            return fh.read(), encoding
    except (OSError, LookupError, UnicodeDecodeError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_read_source_with_encoding:{type(_e).__name__}')
        return None
def _write_read_roundtrip(ap: str, src: str,
                          encoding: str) -> tuple:
    try:
        with open(ap, "w", encoding=encoding, newline="") as fh:
            fh.write(src)
        with open(ap, encoding=encoding, newline="") as fh:
            restored = fh.read()
    except (OSError, LookupError, UnicodeDecodeError) as err:
        log_swallowed(__name__, err,
                      context=f'_write_read_roundtrip:{type(err).__name__}')
        return False, err
    return restored == src, None
def _rewrite_source_with_verify(ap: str, src: str, entry: dict,
                                encoding: str) -> tuple:
    for attempt in (1, 2):
        ok, err = _write_read_roundtrip(ap, src, encoding)
        if err is not None:
            return False, err
        if ok:
            if attempt == 2:
                _append_note(entry, "恢复校验触发重写")
            return True, None
    return False, None
def _dump_recovery_backup(bak: str, src: str, ap: str, entry: dict,
                          encoding: str) -> None:
    try:
        os.makedirs(os.path.dirname(bak), exist_ok=True)
        with open(bak, "w", encoding=encoding, newline="") as fh:
            fh.write(src)
        logger.error(
            "[F2] 源码恢复失败（内存重写 OSError），突变可能残留于"
            " %s；内存源码应急转储于 %s 供人工恢复", ap, bak)
        entry["recovery_backup"] = bak
        _append_note(entry, "恢复材料已转储", limit=320)
    except OSError as _dump_err:
        logger.exception(
            "[F2] 源码恢复失败（内存重写 OSError），突变可能残留于"
            " %s；应急转储亦失败，人工恢复无从下手", ap)
        _append_note(entry, f"转储失败: {_dump_err}", limit=320)
def _restore_mutated_source(ap: str, bak: str, src: str, entry: dict,
                            orig_stat=None, encoding: str = "utf-8",
                            expected: str | None = None) -> bool:
    current = _read_source_with_encoding(ap)
    if current is not None and current[0] == src:
        # 突变写入未发生或源文件已回到原态，无需重写，也不能误判为恢复失败。
        return True
    if expected is not None and current is not None and current[0] != expected:
        _append_note(entry, "回放期间源文件被外部修改，保留当前文件并中止剩余样本")
        _dump_recovery_backup(bak, src, ap, entry, encoding)
        return False
    _restored_ok, _rw_err = _rewrite_source_with_verify(ap, src, entry, encoding)
    if not _restored_ok:
        _append_note(entry, (
            f"源码恢复失败: {_rw_err}" if _rw_err is not None
            else "源码恢复失败: 写后读回校验两轮均不一致"))
        _dump_recovery_backup(bak, src, ap, entry, encoding)
        return False
    if orig_stat is not None:
        try:
            os.utime(ap, (orig_stat.st_atime, orig_stat.st_mtime))
        except OSError as _ut_err:
            log_swallowed(
                __name__, _ut_err,
                context=f'_restore_mutated_source:{type(_ut_err).__name__}')
            _append_note(entry, f"mtime还原失败: {_ut_err}")
    if not safe_delete(bak):
        logger.warning(
            "[F2] 历史恢复材料清理失败（残留于工作空间 Temp）: %s", bak)
    return True
def _identity_key(file: str, line, col_offset, mutation_op,
                  end_lineno, end_col_offset) -> tuple:
    return (file, line, col_offset, mutation_op, end_lineno, end_col_offset)
def _target_key(target) -> tuple:
    return _identity_key(target.file, target.line, target.col_offset,
                         target.mutation_op, target.end_lineno,
                         target.end_col_offset)
def _f2_survived_keys(analyzer) -> set:
    direct_keys = getattr(analyzer, "_survived_keys", None)
    if direct_keys is not None:
        return set(direct_keys)
    survived_keys: set = set()
    for f in analyzer.findings:
        survived_keys |= _finding_survived_keys(f)
    return survived_keys
def _finding_identity(finding, extra: dict) -> tuple:
    def _pick(name, default):
        value = extra.get(name)
        if value is None:
            value = getattr(finding, name, None)
        return default if value is None else value
    return _identity_key(
        str(_pick("file", "") or ""),
        _pick("line", 0),
        _pick("col_offset", 0),
        str(_pick("mutation_op", "") or ""),
        _pick("end_lineno", 0),
        _pick("end_col_offset", -1),
    )
def _finding_survived_keys(finding) -> set:
    if isinstance(finding, MutationTarget):
        return {_target_key(finding)}
    extra = getattr(finding, "extra", None)
    if not isinstance(extra, dict):
        extra = {}
    exact_keys = extra.get("survived_keys")
    if exact_keys is not None:
        return {tuple(key) for key in exact_keys}
    return {_finding_identity(finding, extra)}
_LAYER_ORDER = tuple(
    dict.fromkeys(spec[3] for spec in _MUTATION_DISPATCH.values()))
_LAYER_BY_MUTATION_OP = {
    op: spec[3] for op, spec in _MUTATION_DISPATCH.items()
}
def _stratified_layers(killed: list) -> dict:
    layers: dict = {layer: [] for layer in _LAYER_ORDER}
    for target in killed:
        layer = _LAYER_BY_MUTATION_OP.get(target.mutation_op)
        if layer is not None:
            layers[layer].append(target)
    return layers
def _sample_unpicked_targets(targets: list, n: int, rng: random.Random,
                             picked_keys: set) -> list:
    pool = sorted((target for target in targets
                   if _target_key(target) not in picked_keys),
                  key=_target_key)
    picked = rng.sample(pool, min(n, len(pool)))
    picked_keys.update(_target_key(target) for target in picked)
    return picked
def _f2_stratified_sample(killed: list, n: int, seed: int) -> list:
    layers = _stratified_layers(killed)
    rng = random.Random(seed)  # nosec B311 — 突变分层抽样确定性种子，非安全/加密用途
    sample: list = []
    picked_keys: set = set()
    _qbase, _qrem = divmod(n, len(_LAYER_ORDER))
    for _pos, layer in enumerate(_LAYER_ORDER):
        _quota = _qbase + (1 if _pos < _qrem else 0)
        sample.extend(_sample_unpicked_targets(
            layers[layer], _quota, rng, picked_keys))
    if len(sample) < n:
        sample.extend(_sample_unpicked_targets(
            killed, n - len(sample), rng, picked_keys))
    return sample
def _collect_killed_targets(analyzer) -> list:
    survived_keys = _f2_survived_keys(analyzer)
    killed, seen = [], set()
    for t in analyzer.targets:
        k = _target_key(t)
        if k in survived_keys or k in seen:
            continue
        seen.add(k)
        killed.append(t)
    return killed
def _judge_rc_outcome(skill_dir: str, test_target: str, _rc, entry: dict,
                      baseline_states: dict, output: str) -> str:
    if _rc is None:
        _append_note(entry, "无returncode，样本作废")
        return "skip"
    _bl = _baseline_state(skill_dir, test_target, baseline_states)
    if _bl is not True:
        _note = ("基线失败(无突变时测试已失败)，无法区分突变效果"
                 if _bl is False else
                 "基线不可判定(运行异常/超时/无实际通过用例)，不采信verified")
        _append_note(entry, _note)
        return "baseline_failed"
    summary = parse_pytest_summary(output)
    if _rc == 0:
        if summary is not None and summary[1] > 0:
            return "false_killed"
        _append_note(entry, "突变回放无实际通过用例，存活结论不可判定")
        return "skip"
    if _rc == 1:
        if summary is not None and summary[0].failures:
            return "verified_killed"
        _append_note(entry, "pytest 仅报告 error 或无可解析失败，击杀不可判定")
        return "skip"
    _append_note(
        entry,
        f"pytest 退出码 {_rc} 非用例失败（收采/中断/内部错误），不可判定")
    return "skip"
@dataclass(slots=True)
class _ProbeRun:
    skill_dir: str
    path: str
    source: str
    backup: str
    entry: dict
    original_stat: os.stat_result
    encoding: str
    test_target: str
    def run(self, mutated: str) -> tuple:
        _rc: int | None = None
        restore_ok = True
        error: Exception | None = None
        output = ""
        written = False
        try:
            with open(self.path, "w", encoding=self.encoding, newline="") as fh:
                fh.write(mutated)
            written = True
            r = subprocess.run(  # jwsgj:suppress SYM-TAINT — 审计认可：cmd 由 _pytest_run_cmd 内部构造（sys.executable 起始）
                _pytest_run_cmd(self.test_target),
                cwd=self.skill_dir, capture_output=True, text=True,
                encoding="utf-8", errors="replace", timeout=_PYTEST_RUN_TIMEOUT,
                check=False, env=_pytest_env(self.skill_dir))
            _rc = r.returncode
            output = ((getattr(r, "stdout", "") or "")
                      + (getattr(r, "stderr", "") or ""))
        except Exception as exc:  # noqa: BLE001
            log_swallowed(__name__, exc,
                          context=f'_ProbeRun.run:{type(exc).__name__}')
            error = exc
        finally:
            try:
                restore_ok = _restore_mutated_source(
                    self.path, self.backup, self.source, self.entry,
                    orig_stat=self.original_stat, encoding=self.encoding,
                    expected=mutated if written else None)
            except Exception as _restore_err:
                restore_ok = False
                _append_note(self.entry, (
                    f"恢复调用异常: {type(_restore_err).__name__}:"
                    f" {_restore_err}"))
                logger.exception(
                    "[F2] 源码恢复调用自身异常（源文件状态未知，"
                    "突变可能残留于 %s），剩余样本按恢复失败中止", self.path)
        return _rc, restore_ok, error, output
def _probe_entry(tgt) -> dict:
    return {"file": tgt.file, "line": tgt.line,
            "col_offset": tgt.col_offset, "end_lineno": tgt.end_lineno,
            "end_col_offset": tgt.end_col_offset,
            "op": tgt.mutation_op, "status": "skip", "note": "",
            "recovery_backup": ""}
def _prepare_probe_source(ap: str, tgt) -> tuple:
    _read = _read_source_with_encoding(ap)
    if _read is None:
        return None, "源码读取失败（编码/IO 不可用）"
    src, encoding = _read
    orig_stat = os.stat(ap)
    mutated = _apply_real_mutation(src, tgt)
    if mutated is None:
        return None, "突变不适用（跨行/形态不支持）"
    return (src, encoding, orig_stat, mutated), ""
def _probe_entry_status(entry: dict, probe_err,
                        restore_ok: bool) -> str | None:
    if probe_err is not None:
        _append_note(
            entry, f"异常: {type(probe_err).__name__}: {probe_err}")
    if not restore_ok:
        return "restore_failed"
    if probe_err is not None:
        return "skip"
    return None
def _verify_one_sample(skill_dir: str, bak_dir: str, tgt,
                       baseline_states: dict) -> dict:
    entry = _probe_entry(tgt)
    ap = os.path.join(skill_dir, tgt.file)
    mod = module_name_for_path(tgt.file, skill_dir)
    tf = _resolve_test_file(skill_dir, mod, tgt.file)
    bak = os.path.join(bak_dir, f"f2_mutbak_{mod}_{tgt.line}.py")
    try:
        if tf is None:
            entry["note"] = "无对应测试文件"
            return entry
        test_target = _test_target_rel(tf, skill_dir)
        payload, note = _prepare_probe_source(ap, tgt)
        if payload is None:
            entry["note"] = note
            return entry
        src, encoding, orig_stat, mutated = payload
        compile(mutated, ap, "exec")
        probe = _ProbeRun(skill_dir, ap, src, bak, entry, orig_stat,
                          encoding, test_target)
        _rc, restore_ok, probe_err, output = probe.run(mutated)
        status = _probe_entry_status(entry, probe_err, restore_ok)
        if status is not None:
            entry["status"] = status
            return entry
        entry["status"] = _judge_rc_outcome(
            skill_dir, test_target, _rc, entry, baseline_states, output)
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e,
                      context=f'_verify_one_sample:{type(e).__name__}')
        _append_note(entry, f"异常: {type(e).__name__}: {e}")
    return entry
def _empty_mutation_verification() -> dict:
    return {"enabled": False, "sampled": 0, "verified_killed": 0,
            "false_killed": 0, "skipped": 0, "false_killed_rate": None,
            "baseline_failed": 0, "details": []}
def _verification_reliability_findings(verification: dict) -> list:
    if not isinstance(verification, dict) or not verification.get("enabled"):
        return []
    checked = ((verification.get("verified_killed") or 0)
               + (verification.get("false_killed") or 0))
    rate = verification.get("false_killed_rate")
    if checked < _MUTATION_VERIFY_MIN_SAMPLE:
        return []
    if not isinstance(rate, (int, float)):
        return []
    if rate <= _MUTATION_VERIFY_FALSE_KILLED_LIMIT:
        return []
    return [{
        "rule_id": "TM-VERIFY-UNRELIABLE",
        "severity": "P1",
        "confidence": 0.7,
        "message": (
            f"突变杀死判定不可信: 抽样 {checked} 项假杀死率 {rate:.0%}"
            f"（阈值 {_MUTATION_VERIFY_FALSE_KILLED_LIMIT:.0%}），"
            "存活集合可能被系统性低估"),
        "file": "",
        "line": 0,
        "source": "F2",
        "mutation_op": "verification",
        "node_type": "verification",
        "risk_source": "self-check",
    }]
def _finalize_false_killed_rate(out: dict) -> None:
    checked = out["verified_killed"] + out["false_killed"]
    if checked:
        out["false_killed_rate"] = round(out["false_killed"] / checked, 3)
def _record_verification_entry(out: dict, entry: dict) -> bool:
    out["details"].append(entry)
    status = entry["status"]
    if status == "restore_failed":
        out["skipped"] += 1
        out["note"] = _RESTORE_ABORT_NOTE
        return False
    out[status if status in _STATUS_COUNTER_KEYS else "skipped"] += 1
    return True
def _sampled_mutation_verification(skill_dir: str, analyzer,
                                   sample_size: int | None = None,
                                   seed: int = 20260908) -> dict:
    out = _empty_mutation_verification()
    if os.environ.get("JWSGJ_F2_DISABLE_MUTATION_VERIFY"):
        out["note"] = "环境变量禁用"
        return out
    n = (sample_size if sample_size is not None
         else _MUTATION_VERIFY_SAMPLE_SIZE)
    if n <= 0:
        out["note"] = "sample_size 非正，抽样禁用"
        return out
    try:
        killed = _collect_killed_targets(analyzer)
        if not killed:
            out["note"] = "无 killed 目标可校验"
            return out
        sample = _f2_stratified_sample(killed, n, seed)
        out["enabled"] = True
        _run_sample_batch(out, skill_dir, sample)
        out["sampled"] = len(out["details"])
        _finalize_false_killed_rate(out)
        return out
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e,
                      context=f'_sampled_mutation_verification:{type(e).__name__}')
        out["enabled"] = False
        out["sampled"] = len(out["details"])
        out["false_killed_rate"] = None
        out["note"] = f"校验通道降级: {type(e).__name__}: {e}"[:160]
        return out
def _run_sample_batch(out: dict, skill_dir: str, sample: list) -> None:
    bak_dir = get_temp_base(skill_dir)
    baseline_states: dict = {}
    for tgt in sample:
        entry = _verify_one_sample(
            skill_dir, bak_dir, tgt, baseline_states)
        if not _record_verification_entry(out, entry):
            return
def _prune_execution_walk_dirs(dirs: list[str]) -> None:
    dirs[:] = [d for d in dirs
               if not d.startswith(".")
               and not is_backup_like_dir(d)
               and d.lower() not in SCAN_COLLECT_PRUNE_DIRS_LOWER]
def _newest_execution_mtime(skill_dir: str) -> float:
    newest = 0.0
    for root, dirs, files in os.walk(skill_dir):
        _prune_execution_walk_dirs(dirs)
        for fn in files:
            if (fn.startswith(_COVERAGE_PREFIX)
                    or fn.lower().endswith((".pyc", ".pyo"))):
                continue
            path = os.path.join(root, fn)
            if is_runtime_log_artifact(fn) and not is_test_file_path(path):
                continue
            try:
                mtime = os.path.getmtime(path)
            except OSError as e:
                logger.debug("文件状态探测失败（跳过）: %s", e)
                continue
            newest = max(newest, mtime)
    return newest
def _coverage_data_is_fresh(data_path: str, skill_dir: str,
                            newest: float | None = None) -> bool:
    if newest is None:
        newest = _newest_execution_mtime(skill_dir)
    try:
        data_mtime = os.path.getmtime(data_path)
    except OSError as _e:
        log_swallowed(__name__, _e,
                      context=f'_coverage_data_is_fresh:{type(_e).__name__}')
        return False
    return data_mtime >= newest
def _fresh_coverage_candidates(cands: list[str], skill_dir: str) -> list[str]:
    newest = _newest_execution_mtime(skill_dir)
    return [cand for cand in cands
            if _coverage_data_is_fresh(cand, skill_dir, newest=newest)]
_COVERAGE_PREFIX = ".coverage"
_LINE_COVERAGE_ENV = "JWSGJ_F2_LINE_COVERAGE"
def _iter_coverage_candidates(cdir: str) -> list[str]:
    entries: list[str] = []
    pending = [cdir]
    seen_dirs: set[str] = set()
    while pending:
        current = pending.pop()
        identity = os.path.realpath(current)
        if identity in seen_dirs:
            continue
        seen_dirs.add(identity)
        for fn in sorted(_listdir_or_empty(current, "coverage 归口目录")):
            path = os.path.join(current, fn)
            if os.path.isdir(path):
                if not fn.startswith(_COVERAGE_PREFIX):
                    pending.append(path)
            elif fn.startswith(_COVERAGE_PREFIX):
                entries.append(path)
    return sorted(entries)
def _listdir_or_empty(path: str, label: str) -> list[str]:
    try:
        return os.listdir(path)
    except OSError as e:
        logger.debug("%s列举失败（跳过）: %s: %s", label, path, e)
        return []
def _load_line_coverage(skill_dir: str | None = None) -> dict | None:
    env_path = os.environ.get(_LINE_COVERAGE_ENV, "")
    if not env_path:
        return _auto_load_coverage(skill_dir)
    loaded = _load_coverage_from(env_path, skill_dir, gated=False)
    if loaded is None:
        logger.warning(
            "[F2] 显式行级覆盖数据不可用（路径缺失/不可读/coverage 未安装），"
            "落回纯静态判定: %s", env_path)
    return loaded
def _auto_load_coverage(skill_dir: str | None) -> dict | None:
    cands = _auto_coverage_candidates(skill_dir)
    if not cands or not skill_dir:
        return None
    skill_py: set[str] | None = None
    fresh = _fresh_coverage_candidates(cands, skill_dir)
    for cand in fresh:
        if skill_py is None:
            skill_py = _skill_py_realpaths(skill_dir)
        loaded = _load_coverage_from(
            cand, skill_dir, gated=True, skill_py=skill_py)
        if loaded is not None:
            return loaded
    if not fresh:
        logger.info("[F2] 归口目录 %d 个 coverage 候选均早于源码修改（陈旧），"
                    "落回静态判定", len(cands))
    else:
        logger.info("[F2] 归口目录 %d 个 coverage 候选（新鲜 %d 个）均未通过"
                    "采信门控，落回静态判定", len(cands), len(fresh))
    return None
def _resolve_coverage_dir(skill_dir: str | None) -> str | None:
    if not skill_dir:
        logger.debug("[F2] skill_dir 缺失，自动发现通道门控不可施加，落回纯静态判定")
        return None
    try:
        cdir = os.path.join(get_temp_base(skill_dir), "coverage")
    except (RuntimeError, ValueError) as e:
        logger.debug("[F2] 行级覆盖归口解析失败，落回纯静态判定: %s", e)
        return None
    return cdir if os.path.isdir(cdir) else None
def _auto_coverage_candidates(skill_dir: str | None) -> list[str]:
    cdir = _resolve_coverage_dir(skill_dir)
    if cdir is None:
        return []
    cands: list[tuple[float, str]] = []
    for p in _iter_coverage_candidates(cdir):
        try:
            if os.path.isfile(p):
                cands.append((os.path.getmtime(p), p))
        except OSError as e:
            logger.debug("文件状态探测失败（跳过）: %s: %s", p, e)
            continue
    cands.sort(reverse=True)
    return [p for _mt, p in cands]
def _skill_py_realpaths(skill_dir: str) -> set[str]:
    skill_py = set()
    for _dp, _dns, _fns in os.walk(skill_dir):
        _prune_execution_walk_dirs(_dns)
        for fn in _fns:
            if fn.lower().endswith(".py"):
                skill_py.add(os.path.realpath(os.path.join(_dp, fn)))
    return skill_py
def _cov_overlap_sufficient(loaded: dict, skill_py: set[str], path: str) -> bool:
    overlap = sum(1 for f in loaded if f in skill_py)
    if not skill_py:
        logger.warning(
            "[F2] 自动发现的行级覆盖数据无技能内 Python 文件可比对，"
            "拒绝采信，落回纯静态判定: %s", path)
        return False
    min_files = min(len(skill_py), max(5, int(len(skill_py) * 0.05)))
    if overlap >= min_files:
        return True
    logger.warning(
        "[F2] 自动发现的行级覆盖数据充分性不足(仅测量 %d/%d 个技能内"
        ".py 文件，门槛 %d)，拒绝采信，落回纯静态判定: %s",
        overlap, len(skill_py), min_files, path)
    return False
def _read_coverage_data(path: str) -> dict | None:
    """读取行级覆盖数据（纯只读，不创建 Collector）。

    必须用 ``CoverageData`` 而非 ``Coverage``：后者构造即初始化 Collector
    并挂上进程级 tracer，其 ``data_lock`` 在并行 worker 超时被放弃后仍可能
    被残留线程持有，与后续 tracing 互等形成硬死锁（实测 E 方法 9 线程全部
    阻塞在 ``Collector.lock_data``）。``CoverageData`` 只做文件解析。
    """
    try:
        data = _coverage.CoverageData(basename=path)
        data.read()
        return {os.path.realpath(f): set(data.lines(f) or ())
                for f in data.measured_files()}
    except Exception as e:  # noqa: BLE001
        logger.warning("[F2] 行级覆盖数据加载失败(%s): %s", path, e)
        return None
def _load_coverage_from(path: str, skill_dir: str | None,
                        gated: bool,
                        skill_py: set[str] | None = None) -> dict | None:
    if not os.path.isfile(path) or _coverage is None:
        return None
    loaded = _read_coverage_data(path)
    if loaded is None or not (gated and skill_dir):
        return loaded
    baseline = (skill_py if skill_py is not None
                else _skill_py_realpaths(skill_dir))
    return loaded if _cov_overlap_sufficient(loaded, baseline, path) else None
def _classify_f2_evidence(findings: list, line_cov: dict,
                         skill_dir: str, cov_mtime,
                         analyzer=None) -> tuple:
    ctx = _CoverageEvidence(line_cov, skill_dir, cov_mtime, analyzer)
    counts = {"line-coverage": 0, "static-fallback": 0, "stale-coverage": 0}
    for f in findings:
        state = ctx.state_for(f)
        f["evidence"] = state
        counts[state] += 1
    return (counts["line-coverage"], counts["static-fallback"],
            counts["stale-coverage"])
@dataclass(frozen=True)
class _CoverageEvidence:
    line_cov: dict
    skill_dir: str
    cov_mtime: float | None
    analyzer: object | None
    def state_for(self, finding: dict) -> str:
        af = os.path.realpath(os.path.join(self.skill_dir, finding["file"]))
        if af not in self.line_cov:
            return "static-fallback"
        if (self.analyzer is not None
                and self.analyzer.cov_file_drifted(finding["file"])):
            return "stale-coverage"
        if _source_newer_than_coverage(af, self.cov_mtime):
            return "stale-coverage"
        return "line-coverage"
def _source_newer_than_coverage(
    source_path: str, cov_mtime: float | None,
) -> bool:
    if cov_mtime is None:
        return False
    try:
        return os.path.getmtime(source_path) > cov_mtime
    except OSError as _e:
        log_swallowed(__name__, _e,
                      context=f'_source_newer_than_coverage:{type(_e).__name__}')
        return False
def _f2_error_result(summary: str) -> dict:
    _verification = _empty_mutation_verification()
    _verification["note"] = "分析异常，校验通道未执行"
    return {
        "status": "error",
        "findings_count": 0,
        "summary": summary,
        "findings": [],
        "mode": "error",
        "evidence_breakdown": {"line-coverage": 0,
                               "static-fallback": 0,
                               "stale-coverage": 0},
        "drifted_coverage_files": [],
        "mutation_verification": _verification,
        "ai_execution": {
            "next_action": "investigate_error",
            "instruction": (
                "F2 定向突变验证异常终止（status=error）：按 summary 排查"
                "异常根因并修复后重跑；异常态无 findings 可审，不进入"
                "补测加固流程"),
        },
    }
def _convert_f2_findings(raw_findings: list) -> list:
    findings = []
    for rf in raw_findings:
        fd = {
            "rule_id": rf.rule_id,
            "severity": rf.severity,
            "confidence": rf.confidence,
            "message": rf.message,
            "file": rf.file,
            "line": rf.line,
            "source": "F2",
            "mutation_op": rf.extra.get("mutation_op", ""),
            "node_type": rf.extra.get("node_type", ""),
            "risk_source": rf.extra.get("risk_source", ""),
        }
        for identity_field in ("col_offset", "end_lineno", "end_col_offset",
                               "survived_keys"):
            if identity_field in rf.extra:
                fd[identity_field] = rf.extra[identity_field]
        if rf.extra.get("aggregated"):
            fd["aggregated"] = True
            fd["batch_count"] = rf.extra.get("batch_count")
            fd["survived_lines"] = rf.extra.get("survived_lines")
            fd["individual_overlap"] = min(
                rf.extra.get("batch_count") or 0,
                MAX_INDIVIDUAL_FINDINGS)
        findings.append(fd)
    return findings
def _resolve_f2_mode_note(line_cov, n_hard: int, n_static: int,
                          n_stale: int) -> tuple:
    if line_cov and n_static == 0 and n_stale == 0:
        return "line-coverage", (
            "口径: 行级覆盖硬证据(发现均为行未执行的真实盲区); "
            "killed判定(行执行→视为已覆盖)为覆盖近似, 断言不敏感的"
            "执行行可能实际存活(真实盲区被掩盖), 假killed率实测见 "
            "mutation_verification")
    if line_cov and n_stale:
        return "line-coverage-stale", (
            f"口径: 混合(行级硬证据 {n_hard} + 静态回退 {n_static}"
            f" + 陈旧数据 {n_stale}); 陈旧部分的目标文件在覆盖数据"
            "采集后被修改，行号可能漂移，已移交交叉验证，"
            "建议重新采集后经 JWSGJ_F2_LINE_COVERAGE 复跑")
    if line_cov:
        return "line-coverage-partial", (
            f"口径: 混合(行级硬证据 {n_hard} + 静态回退 {n_static}); "
            "静态回退部分存在高误报风险，建议全量采集后经 "
            "JWSGJ_F2_LINE_COVERAGE 复跑")
    return "static", (
        "口径: 纯静态(未提供行级覆盖数据，存在高误报风险; "
        "建议采集后经 JWSGJ_F2_LINE_COVERAGE 复跑)")
def _coverage_mtime() -> float | None:
    _cov_path = os.environ.get(_LINE_COVERAGE_ENV, "")
    try:
        return (os.path.getmtime(_cov_path)
                if _cov_path and os.path.isfile(_cov_path) else None)
    except OSError as _e:
        log_swallowed(__name__, _e,
                      context=f'_coverage_mtime:{type(_e).__name__}')
        return None
def run_f2_mutation_targeted(skill_dir: str, cache: SharedCache | None = None) -> dict:
    require_warmed(cache, "F2 定向突变验证")
    try:
        line_cov = _load_line_coverage(skill_dir)
        coverage_mtime = _coverage_mtime()
        analyzer = TargetedMutationAnalyzer(
            skill_dir, cache, line_coverage=line_cov,
            coverage_mtime=coverage_mtime)
        findings = _convert_f2_findings(analyzer.analyze())
        survived_count = len(_f2_survived_keys(analyzer))
        n = len(findings)
        n_hard, n_static, n_stale = (
            _classify_f2_evidence(
                findings, line_cov, skill_dir, coverage_mtime,
                analyzer=analyzer)
            if line_cov else (0, 0, 0))
        mode, mode_note = _resolve_f2_mode_note(line_cov, n_hard, n_static, n_stale)
        if not line_cov and os.environ.get(_LINE_COVERAGE_ENV):
            mode_note = (f"{mode_note}；显式行级覆盖数据不可用"
                         f"（{_LINE_COVERAGE_ENV} 未加载），已回退静态")
        if line_cov:
            mutation_verification = _sampled_mutation_verification(
                skill_dir, analyzer)
        else:
            mutation_verification = _empty_mutation_verification()
            mutation_verification["note"] = "非行级口径不校验（无覆盖数据）"
        _guard = _verification_reliability_findings(mutation_verification)
        if _guard:
            findings = findings + _guard
            n = len(findings)
            mode_note = f"{mode_note}；校验可靠性告警{len(_guard)}条"
        return {
            "status": "pass",
            "findings_count": n,
            "summary": f"定向突变验证: {survived_count}个存活突变 ({mode_note})",
            "findings": findings,
            "mode": mode,
            "evidence_breakdown": {"line-coverage": n_hard,
                                   "static-fallback": n_static,
                                   "stale-coverage": n_stale},
            "drifted_coverage_files": analyzer.drifted_coverage_files,
            "mutation_verification": mutation_verification,
            "ai_execution": {
                "next_action": "review_and_execute_test_hardening",
                "instruction": (
                    "逐项审核 findings 中 survived/false_killed 的突变目标；"
                    "确认后为对应代码路径补充行级断言测试（先写复现测试），"
                    "补测后复跑 F2 确认 killed；不成立的目标按 evidence 驳回"
                ),
            },
        }
    except AttributeError as e:
        logger.warning("[F2] 定向突变验证属性错误: %s", e, exc_info=True)
        return _f2_error_result(f"定向突变验证错误: {e}")
    except Exception as e:
        logger.warning("[F2] 执行异常: %s", e, exc_info=True)
        return _f2_error_result(f"定向突变验证异常: {e}")
def _multiline_token_lines(lines: list[str]) -> frozenset:
    tokens = tokenize_source_cached("".join(_ln + "\n" for _ln in lines))
    if tokens is None:
        return frozenset()
    return frozenset(
        row
        for tok in tokens if tok.end[0] > tok.start[0]
        for row in range(tok.start[0], tok.end[0] + 1))
@dataclass(slots=True)
class _ScanState:
    noisy_ids: set = field(default_factory=set)
    stmt_spans: list = field(default_factory=list)
    if_branches: dict = field(default_factory=dict)
    test_rects: list = field(default_factory=list)
    defs: defaultdict = field(default_factory=lambda: defaultdict(int))
    imps: set = field(default_factory=set)
    from_import_binds: dict = field(default_factory=dict)
    raw_by_id: dict = field(default_factory=dict)
    name_by_id: dict = field(default_factory=dict)
    dup_names: set = field(default_factory=set)
    func_records: list = field(default_factory=list)
def _collect_scan_state(tree: ast.AST) -> _ScanState:
    state = _ScanState()
    lambda_body_ids = {
        id(descendant)
        for node in walk_nodes(tree) if isinstance(node, ast.Lambda)
        for descendant in walk_nodes(node.body)
    }
    attribute_part_ids = _dotted_attribute_part_ids(tree)
    stack = [tree]
    active: list = []
    while stack:
        node = stack.pop()
        if node is SCOPE_END:
            rec = active.pop()
            state.raw_by_id[rec.node_id] = rec.refs
            state.name_by_id[rec.node_id] = rec.name
            state.func_records.append(rec)
            continue
        if (id(node) not in lambda_body_ids
                and id(node) not in attribute_part_ids
                and visit_module_ref_node(
                    node, state.defs, state.imps, state.dup_names, active)):
            stack.append(SCOPE_END)
        _f2_span_branch_collect(node, state.stmt_spans,
                                state.if_branches, state.test_rects)
        _collect_noisy_ids(node, state.noisy_ids)
        if active and id(node) not in lambda_body_ids:
            own_scope_visit_node(node, active[-1])
        stack.extend(ast.iter_child_nodes(node))
    state.from_import_binds = _from_import_ref_binds(tree)
    return state
class TargetedMutationAnalyzer:
    COMPLEXITY_THRESHOLD = 10
    def __init__(self, skill_dir: str, cache=None, line_coverage=None,
                 coverage_mtime: float | None = None):
        self.skill_dir = os.path.abspath(skill_dir)
        self._cache = cache
        self._line_cov = line_coverage or None
        self._coverage_mtime = coverage_mtime
        self._reset_state()
    def _reset_state(self):
        self.py_files: list[str] = []
        self.targets: list[MutationTarget] = []
        self.findings: list[MutationFinding] = []
        self._current_gate = _TargetGate(frozenset(), (), ())
        self._stmt_spans: dict = {}
        self._current_stmt_spans: list = []
        self._realpath_cache: dict[str, str] = {}
        self._if_branch_map: dict = {}
        self._test_rects: dict = {}
        self._test_rect_hit_lines: dict = {}
        self._cov_drifted: dict[str, bool] = {}
        self._mod_refs_by_rel: dict = {}
        self._ambiguous_funcs: set = set()
        self._survived_keys: set = set()
        self._clear_static_evidence()
    def _clear_static_evidence(self, ti_src=None) -> None:
        self._submodule_binds: set = set()
        self._kill_closure: set = set()
        self._module_assert_imports: set = set()
        self._ambiguous_mods: set = set()
        self._ti_by_module: dict = {}
        self._ti_by_module_src: list | None = ti_src
    def _realpath_of(self, rel_file: str) -> str:
        p = self._realpath_cache.get(rel_file)
        if p is None:
            p = os.path.realpath(os.path.join(self.skill_dir, rel_file))
            self._realpath_cache[rel_file] = p
        return p
    def analyze(self) -> list[MutationFinding]:
        self._reset_state()
        self.collect_py_files()
        self._identify_high_risk_paths()
        self._evaluate_mutations()
        self._generate_findings()
        return self.findings
    def collect_py_files(self):
        self.py_files = collect_py_files_default(self.skill_dir)
    def _identify_high_risk_paths(self):
        for filepath in self.py_files:
            try:
                self._scan_high_risk(filepath)
            except (SyntaxError, UnicodeDecodeError) as e:
                logger.warning("[ExtraAnalyzers] 扫描失败,跳过 %s: %s", filepath, e)
                continue
            except Exception as e:
                logger.warning("[ExtraAnalyzers] 扫描未预期异常,跳过 %s: %s",
                               filepath, e, exc_info=True)
                continue
    def _publish_scan_aux(self, rel_path: str, noisy_ids: set,
                          stmt_spans: list, if_branches: dict,
                          test_rects: list) -> None:
        self._current_stmt_spans = sorted(stmt_spans)
        self._stmt_spans[rel_path] = self._current_stmt_spans
        self._if_branch_map[rel_path] = if_branches
        test_rects.sort(key=lambda r: (r[0], r[1]))
        self._test_rects[rel_path] = test_rects
        stmt_starts, prefix_max_end, hit_lines = _span_lookup_tables(
            self._current_stmt_spans, test_rects)
        self._test_rect_hit_lines[rel_path] = hit_lines
        self._current_gate = _TargetGate(
            frozenset(noisy_ids), tuple(stmt_starts), tuple(prefix_max_end))
    def _scan_high_risk(self, filepath: str):
        rel_path = os.path.relpath(filepath, self.skill_dir)
        tree = _load_scan_tree(filepath, self.skill_dir, self._cache)
        if tree is None:
            return
        state = _collect_scan_state(tree)
        self._publish_scan_aux(rel_path, state.noisy_ids, state.stmt_spans,
                               state.if_branches, state.test_rects)
        self._mod_refs_by_rel[rel_path] = (
            state.defs, state.imps, state.raw_by_id,
            state.name_by_id, state.dup_names, tree,
            state.from_import_binds)
        module = module_name_for_path(rel_path, self.skill_dir)
        self._ambiguous_funcs.update(
            (module, name) for name in state.dup_names)
        _publish_func_targets(
            state.func_records, rel_path, self.COMPLEXITY_THRESHOLD,
            self._current_gate, self.targets)
        _publish_expr_targets(iter_module_level_exprs(tree), rel_path, "",
                              self._current_gate, self.targets)
    def _generate_findings(self):
        self.findings = _dedupe_and_batch_findings(self.findings)
    def _build_static_evidence(self, need_static: bool) -> list:
        test_index: list = []
        try:
            if need_static:
                _reexport = load_reexport_map(self.skill_dir, self._cache)
                test_index, self._submodule_binds = build_test_index(
                    _engine_test_files(self.skill_dir), self._cache,
                    self.skill_dir, _reexport)
                (self._kill_closure, self._module_assert_imports,
                 self._ambiguous_mods) = build_kill_closure(
                    self.py_files, self.skill_dir, self._mod_refs_by_rel,
                    self._cache, _reexport, test_index)
            else:
                logger.info("[F2] 行级覆盖已覆盖全部目标文件,跳过静态索引与闭包构建")
            self._ti_by_module = build_ti_by_module(
                test_index, frozenset(self._submodule_binds))
            self._ti_by_module_src = test_index
        except Exception as e:
            logger.warning(
                "[F2] 静态测试证据构建失败,降级为空静态证据"
                "(目标保守存活,移交CV): %s: %s",
                type(e).__name__, e, exc_info=True)
            self._clear_static_evidence(ti_src=[])
            test_index = []
        return test_index
    def _judge_targets(self, test_index: list) -> None:
        for target in self.targets:
            try:
                survived = self._check_survived(target, test_index)
            except Exception as e:  # noqa: BLE001
                log_swallowed(
                    __name__, e,
                    context=(f'TargetedMutationAnalyzer._judge_targets:'
                             f'{type(e).__name__}'))
                _log_judge_failure(target, e)
                survived = True
            if survived:
                self.findings.append(target)
                self._survived_keys.add(_target_key(target))
    def _evaluate_mutations(self):
        need_static = _needs_static_index(
            self._line_cov, self.targets, self._realpath_of)
        self._judge_targets(self._build_static_evidence(need_static))
    def cov_file_drifted(self, rel_file: str) -> bool:
        cached = self._cov_drifted.get(rel_file)
        if cached is not None:
            return cached
        drifted = False
        if self._line_cov:
            realpath = self._realpath_of(rel_file)
            cov_lines = self._line_cov.get(realpath)
            if cov_lines is not None:
                if _source_newer_than_coverage(realpath, self._coverage_mtime):
                    drifted = True
                elif cov_lines:
                    src = _load_drift_source(
                        self.skill_dir, rel_file, self._cache)
                    if src is not None:
                        drifted = _scan_cov_line_drift(
                            rel_file, cov_lines, ast_split_lines(src))
        self._cov_drifted[rel_file] = drifted
        return drifted
    @property
    def drifted_coverage_files(self) -> list[str]:
        return sorted(f for f, d in self._cov_drifted.items() if d)
    def _check_survived(self, target, test_index: list) -> bool:
        cov_lines = (self._line_cov or {}).get(self._realpath_of(target.file))
        if cov_lines is not None:
            return _linecov_survived(target, self._view_for(
                cov_lines,
                stmt_spans=self._stmt_spans.get(target.file, ()),
                drifted=self.cov_file_drifted(target.file)))
        return check_static_survival(
            target, self.skill_dir,
            ClosureEvidence(self._kill_closure,
                            self._module_assert_imports,
                            self._ambiguous_mods,
                            self._ambiguous_funcs),
            self._ti_by_module, self._ti_by_module_src,
            self._submodule_binds, test_index)
    def _view_for(self, cov_lines, *, stmt_spans=(),
                  drifted: bool = False) -> _CoverageView:
        return _CoverageView(
            cov_lines=cov_lines,
            drifted=drifted,
            stmt_spans=stmt_spans,
            if_branch_map=self._if_branch_map,
            test_rect_hit_lines=self._test_rect_hit_lines,
            test_rects=self._test_rects)
def _scan_cov_line_drift(rel_file: str, cov_lines,
                         lines: list[str]) -> bool:
    for ln in cov_lines:
        if ln > len(lines):
            logger.warning(
                "[F2] 覆盖数据行号漂移铁证: %s 执行行 %d "
                "超出当前源码末尾 %d 行（文件在采集窗口内"
                "被删减，行级判定降级 stale）",
                rel_file, ln, len(lines))
            return True
    str_lines = _multiline_token_lines(lines)
    for ln in cov_lines:
        if 1 <= ln <= len(lines):
            stripped = lines[ln - 1].strip()
            if ((not stripped
                    or stripped.startswith("#"))
                    and ln not in str_lines):
                logger.warning(
                    "[F2] 覆盖数据行号漂移铁证: %s 执行行 %d "
                    "在当前源码中为空行/注释行（采集窗口内"
                    "源码被并发修改，行级判定降级 stale）",
                    rel_file, ln)
                return True
    return False
def _rect_contains(rect, target, ln: int) -> bool:
    tl, tc, tel, tec, _bf, _of = rect
    if ln < tl or ln > tel:
        return False
    if ln == tl and target.col_offset < tc:
        return False
    return not (ln == tel and target.col_offset >= tec)
def _rect_branch_gap(rect, cov_lines) -> bool:
    _tl, _tc, _tel, _tec, bf, of = rect
    return ((bf is not None and bf not in cov_lines)
            or (of is not None and of not in cov_lines))
def _test_rect_branch_untested(target, ln, cov_lines, rects) -> bool:
    for rect in rects:
        if _rect_contains(rect, target, ln):
            return _rect_branch_gap(rect, cov_lines)
    return False
@dataclass(frozen=True, slots=True)
class _CoverageView:
    cov_lines: set
    drifted: bool
    stmt_spans: list
    if_branch_map: dict
    test_rect_hit_lines: dict
    test_rects: dict
def _linecov_covers_branches(target, ln: int, view: _CoverageView) -> bool:
    if target.node_type == "If":
        return not _if_branch_gap(target, ln, view)
    if ln in view.test_rect_hit_lines.get(target.file, ()):
        return not _test_rect_branch_untested(
            target, ln, view.cov_lines,
            view.test_rects.get(target.file, ()))
    return True
def _if_branch_gap(target, ln: int, view: _CoverageView) -> bool:
    body_line, else_line = view.if_branch_map.get(
        target.file, {}).get((ln, target.col_offset), (None, None))
    return ((body_line is not None and body_line not in view.cov_lines)
            or (else_line is None or else_line not in view.cov_lines))
def _linecov_survived(target, view: _CoverageView) -> bool:
    if view.drifted:
        return True
    ln = target.line
    if ln in view.cov_lines:
        return not _linecov_covers_branches(target, ln, view)
    span = _enclosing_stmt_span(ln, view.stmt_spans)
    if span is not None:
        return not any(_ln in view.cov_lines
                       for _ln in range(span[0], span[1] + 1))
    return not any(ln + d in view.cov_lines for d in (1, -1, 2, -2))
def _enclosing_stmt_span(ln: int, stmt_spans) -> tuple[int, int] | None:
    best: tuple[int, int] | None = None
    for start, end in stmt_spans:
        if start <= ln <= end and (best is None or end - start < best[1] - best[0]):
            best = (start, end)
    return best
def _load_drift_source(skill_dir: str, rel_file: str, cache):
    ap = os.path.join(skill_dir, rel_file)
    src = _cached_source(cache, ap)
    if src is None:
        src = read_source_with_fingerprint(ap, strict=True)[0]
    return src
def _span_lookup_tables(stmt_spans: list, test_rects: list) -> tuple:
    starts = [s for s, _ in stmt_spans]
    prefix_max: list = []
    mx = -1
    for _, e in stmt_spans:
        mx = max(mx, e)
        prefix_max.append(mx)
    hit: set = set()
    for tl, _tc, tel, _tec, _bf, _of in test_rects:
        hit.update(range(tl, tel + 1))
    return starts, prefix_max, hit
@dataclass(frozen=True, slots=True)
class _TargetGate:
    noisy_ids: frozenset
    stmt_starts: tuple
    prefix_max_end: tuple
    def build(self, node: ast.AST, rel_path: str, mutation_op: str,
              risk_source: str, func_name: str = "") -> MutationTarget | None:
        if id(node) in self.noisy_ids:
            return None
        ln = node.lineno
        idx = bisect_right(self.stmt_starts, ln)
        if idx == 0 or self.prefix_max_end[idx - 1] < ln:
            return None
        if dump_len(node, _TARGET_COMPLEXITY_DUMP_LIMIT) < 0:
            return None
        if mutation_op == "remove_condition":
            if node.test.end_lineno != node.lineno:
                return None
        elif node.end_lineno != node.lineno:
            return None
        return MutationTarget(
            file=rel_path,
            line=ln,
            col_offset=node.col_offset,
            node_type=type(node).__name__,
            mutation_op=mutation_op,
            risk_source=risk_source,
            confidence=0.6,
            func_name=func_name,
            end_lineno=node.end_lineno,
            end_col_offset=node.end_col_offset,
        )
def _expr_mutation_spec(node: ast.AST) -> tuple[str, str] | None:
    if isinstance(node, ast.BinOp):
        return (("flip_operator", "D6-blindspot")
                if type(node.op) in _VERIFY_OP_SRC else None)
    if isinstance(node, ast.Compare):
        return "flip_comparator", "D6-blindspot"
    if isinstance(node, ast.BoolOp):
        return "remove_operand", "A1-complexity"
    return None
def _publish_expr_targets(exprs, rel_path: str, func_name: str,
                          gate: _TargetGate, targets: list) -> None:
    for child in exprs:
        spec = _expr_mutation_spec(child)
        if spec is None:
            continue
        target = gate.build(child, rel_path, *spec, func_name)
        if target is not None:
            targets.append(target)
def _publish_func_targets(func_records, rel_path: str, threshold: int,
                          gate: _TargetGate, targets: list) -> None:
    for rec in func_records:
        node = rec.func_node
        if rec.complexity >= threshold:
            targets.extend(_high_risk_branch_targets(
                node, rel_path, rec.complexity, if_nodes=rec.if_nodes,
                gate=gate, threshold=threshold))
        _publish_expr_targets(rec.expr_targets, rel_path, node.name, gate,
                              targets)
def _needs_static_index(line_cov, targets, realpath_of) -> bool:
    if not line_cov:
        return True
    return any(realpath_of(t.file) not in line_cov for t in targets)
def _log_judge_failure(target, exc: Exception) -> None:
    logger.warning(
        "[F2] 突变目标存活判定异常,保守存活(%s:%s %s): %s",
        target.file, target.line, target.mutation_op, exc, exc_info=exc)
def _load_scan_tree(filepath: str, skill_dir: str, cache):
    tree = read_source_tree(filepath, cache)
    if tree is None:
        logger.warning("_scan_high_risk: skipped %s (源码不可读或语法损坏/深嵌套)",
                       os.path.relpath(filepath, skill_dir))
    return tree
def _cached_source(cache, filepath: str) -> str | None:
    if cache is None:
        return None
    try:
        return cache.get_source(filepath)
    except Exception:
        logger.warning("共享缓存读取失败，回退直读源码: %s",
                       filepath, exc_info=True)
        return None
def _f2_span_branch_collect(node, stmt_spans, if_branches,
                            test_rects) -> None:
    if isinstance(node, ast.stmt):
        stmt_spans.append((_stmt_start_line(node), node.end_lineno))
    if isinstance(node, (ast.If, ast.While)):
        branch_lines = _branch_first_lines(node)
        if isinstance(node, ast.If):
            if_branches[(node.lineno, node.col_offset)] = branch_lines
        test = node.test
        test_rects.append(
            (test.lineno, test.col_offset,
             test.end_lineno, test.end_col_offset, *branch_lines))
def _stmt_start_line(node: ast.stmt) -> int:
    decorators = getattr(node, "decorator_list", None)
    if not decorators:
        return node.lineno
    return min(node.lineno, *(d.lineno for d in decorators))
def _branch_first_lines(node) -> tuple[int | None, int | None]:
    body_line = node.body[0].lineno if node.body else None
    if body_line == node.test.end_lineno:
        body_line = _BRANCH_LINE_UNPROVEN
    return body_line, node.orelse[0].lineno if node.orelse else None
def _high_risk_branch_targets(
        func_node: ast.FunctionDef | ast.AsyncFunctionDef,
        rel_path: str, complexity: int, if_nodes,
        gate: _TargetGate, *, threshold: int) -> list:
    targets = []
    for node in if_nodes:
        target = gate.build(
            node, rel_path, "remove_condition",
            f"T1-edge(complexity={complexity})", func_node.name)
        if target is not None:
            target.confidence = min(
                0.5 + (complexity - threshold) * 0.05, 0.9)
            targets.append(target)
    return targets
def _dedupe_and_batch_findings(findings: list) -> list:
    seen = set()
    file_groups: dict[str, list] = defaultdict(list)
    for result in findings:
        key = _target_key(result)
        if key in seen:
            continue
        seen.add(key)
        file_groups[result.file].append(result)
    new_findings = []
    for file_path in sorted(file_groups):
        results = file_groups[file_path]
        ordered = sorted(
            results,
            key=lambda r: (r.line, r.col_offset, r.mutation_op,
                           r.end_lineno, r.end_col_offset))
        count = len(ordered)
        new_findings.extend(
            _build_survived_finding(target)
            for target in ordered[:MAX_INDIVIDUAL_FINDINGS])
        if count > MAX_INDIVIDUAL_FINDINGS:
            new_findings.append(
                _build_batch_finding(file_path, ordered, count))
    return new_findings
def _build_survived_finding(target) -> MutationFinding:
    return MutationFinding(
        rule_id="TM-SURVIVED",
        severity="P3",
        confidence=target.confidence,
        message=(
            f"定向突变存活: {target.mutation_op} @ "
            f"{target.file}:{target.line} "
            f"(来源: {target.risk_source})"
        ),
        file=target.file,
        line=target.line,
        extra={
            "mutation_op": target.mutation_op,
            "node_type": target.node_type,
            "risk_source": target.risk_source,
            "col_offset": target.col_offset,
            "end_lineno": target.end_lineno,
            "end_col_offset": target.end_col_offset,
            "survived_keys": [_target_key(target)],
        },
    )
_BATCH_TAG = "batch"
def _build_batch_finding(file_path, ordered,
                         count) -> MutationFinding:
    avg_conf = sum(r.confidence for r in ordered) / count
    ops = {r.mutation_op for r in ordered}
    return MutationFinding(
        rule_id="TM-SURVIVED-BATCH",
        severity="P3",
        confidence=round(avg_conf, 2),
        message=(
            f"测试覆盖不足: {file_path} 有 {count} 处突变存活 "
            f"(操作类型: {', '.join(sorted(ops))})"
        ),
        file=file_path,
        line=ordered[0].line,
        extra={
            "mutation_op": _BATCH_TAG,
            "node_type": _BATCH_TAG,
            "risk_source": _BATCH_TAG,
            "batch_count": count,
            "aggregated": True,
            "survived_lines": [(r.line, r.mutation_op)
                               for r in ordered[:50]],
            "survived_keys": [_target_key(r) for r in ordered],
        },
    )
_LOG_METHOD_ATTRS = frozenset(
    {"warning", "error", "debug", "info", "critical", "exception", "log"})
_TIMING_STRONG_ATTRS = frozenset({
    "monotonic", "monotonic_ns", "perf_counter", "perf_counter_ns",
    "process_time", "process_time_ns", "thread_time", "thread_time_ns",
    "default_timer",
})
_TIMING_MODULE_ONLY_ATTRS = frozenset({"time", "time_ns", "clock"})
_TIMING_CALL_NAMES = _TIMING_STRONG_ATTRS | {"time", "time_ns"}
_LOGGER_GETTER_ATTRS = frozenset({"getLogger"})
_LOG_BASE_WORDS = frozenset({"log", "logger", "logging"})
def _log_semantic_name(name: str) -> bool:
    if not name:
        return False
    return any(word in _LOG_BASE_WORDS for word in split_identifier(name))
def _is_logging_call(call: ast.Call) -> bool:
    f = call.func
    if not (isinstance(f, ast.Attribute) and f.attr in _LOG_METHOD_ATTRS):
        return False
    return _logging_base_is_logger(f.value)
def _logging_base_is_logger(base: ast.AST) -> bool:
    if isinstance(base, ast.Call):
        return ast_name(base.func) in _LOGGER_GETTER_ATTRS
    return _log_semantic_name(ast_name(base))
def _is_timing_call(node: ast.AST) -> bool:
    if not isinstance(node, ast.Call):
        return False
    f = node.func
    if isinstance(f, ast.Attribute):
        if f.attr in _TIMING_STRONG_ATTRS:
            return True
        return (f.attr in _TIMING_MODULE_ONLY_ATTRS
                and isinstance(f.value, ast.Name)
                and f.value.id == "time")
    if isinstance(f, ast.Name):
        return f.id in _TIMING_CALL_NAMES
    return False
def _timing_delta(binop: ast.BinOp) -> bool:
    cur = binop.left
    while isinstance(cur, ast.BinOp) and isinstance(cur.op, ast.Sub):
        cur = cur.left
    return _is_timing_call(cur)
def _is_round_timing_call(node: ast.Call) -> bool:
    return (isinstance(node.func, ast.Name) and node.func.id == "round"
            and bool(node.args) and isinstance(node.args[0], ast.BinOp)
            and isinstance(node.args[0].op, ast.Sub)
            and _timing_delta(node.args[0]))
def _mark_subtree_ids(root: ast.AST, ids: set) -> None:
    for sub in walk_nodes(root):
        ids.add(id(sub))
def _collect_logging_noise(node: ast.AST, ids: set) -> None:
    if isinstance(node, ast.Call) and _is_logging_call(node):
        _mark_subtree_ids(node, ids)
def _collect_timing_noise(node: ast.AST, ids: set) -> None:
    if isinstance(node, ast.Call) and _is_round_timing_call(node):
        _mark_subtree_ids(node.args[0], ids)
def _collect_log_only_if(node: ast.AST, ids: set) -> None:
    if not (isinstance(node, ast.If) and len(node.body) == 1
            and not node.orelse):
        return
    stmt = node.body[0]
    if (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call)
            and _is_logging_call(stmt.value)):
        ids.add(id(node))
        _mark_subtree_ids(node.test, ids)
def _collect_noisy_ids(node: ast.AST, ids: set) -> None:
    _collect_logging_noise(node, ids)
    _collect_timing_noise(node, ids)
    _collect_log_only_if(node, ids)
@dataclass(slots=True)
class _ScopeRecord:
    node_id: int
    name: str
    refs: set
    complexity: int = 1
    if_nodes: list = field(default_factory=list)
    expr_targets: list = field(default_factory=list)
    func_node: object = None
    definition_expr_ids: frozenset = field(default_factory=frozenset)
def own_scope_visit_node(node, rec: _ScopeRecord) -> None:
    if id(node) in rec.definition_expr_ids:
        return
    if isinstance(node, (ast.If, ast.While, ast.For, ast.AsyncFor,
                         ast.ExceptHandler)):
        rec.complexity += 1
        if isinstance(node, ast.If):
            rec.if_nodes.append(node)
    elif isinstance(node, ast.BoolOp):
        rec.complexity += len(node.values) - 1
        rec.expr_targets.append(node)
    elif isinstance(node, ast.comprehension):
        rec.complexity += 1
        if node.ifs:
            rec.complexity += len(node.ifs)
    elif isinstance(node, (ast.BinOp, ast.Compare)):
        rec.expr_targets.append(node)
def iter_module_level_exprs(tree: ast.AST) -> Iterator[ast.AST]:
    stack = [tree]
    while stack:
        node = stack.pop()
        if isinstance(node, ast.Lambda):
            stack.append(node.args)
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            stack.extend(_function_definition_exprs(node))
            continue
        if isinstance(node, (ast.BinOp, ast.Compare, ast.BoolOp)):
            yield node
        stack.extend(ast.iter_child_nodes(node))
@dataclass(frozen=True, slots=True)
class _RefResolveContext:
    mod: str
    defs: dict
    imps: set
    raw_by_id: dict
    name_to_unique_mods: dict
    from_import_binds: dict = field(default_factory=dict)
    pkg: str = ""
    reexport: dict = field(default_factory=dict)
    mod_func_defs: dict = field(default_factory=dict)
def _resolve_imported_ref_name(name, ctx: _RefResolveContext):
    umods = ctx.name_to_unique_mods.get(name)
    if not umods:
        return None
    candidates = umods & ctx.imps
    if len(candidates) == 1:
        return (next(iter(candidates)), name)
    return None
def _resolve_from_import_ref(binding, ctx: _RefResolveContext):
    module, original = binding
    if module == ctx.pkg:
        entries = _from_import_entry(module, original, ctx)
        return next(iter(entries)) if len(entries) == 1 else None
    if not ctx.mod_func_defs:
        return _resolve_imported_ref_name(original, ctx)
    if ctx.mod_func_defs.get(module, {}).get(original) == 1:
        return (module, original)
    return None
def _resolve_ref_name(name, ctx: _RefResolveContext):
    if name in ctx.from_import_binds and ctx.from_import_binds[name] is None:
        return None
    if name in ctx.defs:
        return (ctx.mod, name) if ctx.defs[name] == 1 else None
    if name in ctx.from_import_binds:
        binding = ctx.from_import_binds[name]
        return (_resolve_from_import_ref(binding, ctx)
                if binding is not None else None)
    return _resolve_imported_ref_name(name, ctx)
def _resolve_from_import_attr(binding, name, ctx: _RefResolveContext):
    module, original = binding
    origin = _reexport_origin(ctx.reexport, original)
    if module == ctx.pkg:
        if origin not in ctx.mod_func_defs:
            return None
        module = ctx.reexport.get(original, origin)
    else:
        if original not in ctx.mod_func_defs:
            return None
        module = original
    if ctx.mod_func_defs.get(module, {}).get(name) == 1:
        return (module, name)
    return None
def _resolve_attribute_ref(ref, ctx: _RefResolveContext):
    base, name = ref
    if base in ctx.from_import_binds:
        binding = ctx.from_import_binds[base]
        if binding is None or base in ctx.defs:
            return None
        resolved = _resolve_from_import_attr(binding, name, ctx)
        if resolved is not None:
            return resolved
    if not ctx.imps.intersection(base.split(".")):
        return None
    return _resolve_imported_ref_name(name, ctx)
SCOPE_END = object()
def _dotted_attribute_part_ids(root: ast.AST) -> set[int]:
    return {
        id(node.value)
        for node in walk_nodes(root)
        if isinstance(node, ast.Attribute) and ast_name(node.value)
    }
def _scope_load_ref(node: ast.AST):
    if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
        return node.id
    if isinstance(node, ast.Attribute) and isinstance(node.ctx, ast.Load):
        base = ast_name(node.value)
        return (base, node.attr) if base else None
    return None
def _record_scope_load_ref(node: ast.AST, active) -> None:
    if not active or id(node) in active[-1].definition_expr_ids:
        return
    ref = _scope_load_ref(node)
    if ref is not None:
        active[-1].refs.add(ref)
def _record_function_scope(node, defs, dup_names, active) -> None:
    if active:
        active[-1].refs.update(_definition_time_ref_names(node))
    defs[node.name] += 1
    if defs[node.name] > 1:
        dup_names.add(node.name)
    active.append(_ScopeRecord(
        id(node), node.name, set(), func_node=node,
        definition_expr_ids=_definition_expr_node_ids(node)))
def visit_module_ref_node(node: ast.AST, defs, imps, dup_names, active) -> bool:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        _record_function_scope(node, defs, dup_names, active)
        return True
    _record_scope_load_ref(node, active)
    if isinstance(node, ast.ImportFrom):
        _record_from_import_binds(node, imps)
    elif isinstance(node, ast.Import):
        _record_plain_import_binds(node, imps)
    return False
def _record_from_import_binds(node: ast.ImportFrom, imps: set) -> None:
    if node.module:
        imps.add(node.module.split(".")[-1])
    for alias in node.names:
        if alias.name != "*":
            imps.add(alias.asname or alias.name)
def _from_import_ref_binds(tree) -> dict:
    binds: dict = {}
    ambiguous: set = set()
    shadowed: set = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Name) and isinstance(
                node.ctx, (ast.Store, ast.Del)):
            shadowed.add(node.id)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
            args = node.args
            shadowed.update(
                arg.arg for arg in (args.posonlyargs + args.args
                                    + args.kwonlyargs))
            shadowed.update(
                arg.arg for arg in (args.vararg, args.kwarg) if arg)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            shadowed.add(node.name)
        if isinstance(node, ast.ExceptHandler) and node.name:
            shadowed.add(node.name)
        if type(node).__name__ in {"MatchAs", "MatchStar", "MatchMapping"}:
            for attr in ("name", "rest"):
                value = getattr(node, attr, None)
                if isinstance(value, str):
                    shadowed.add(value)
        if isinstance(node, ast.Import):
            for alias in node.names:
                shadowed.add(alias.asname or alias.name.split(".")[0])
        if not isinstance(node, ast.ImportFrom) or not node.module:
            continue
        module = node.module.split(".")[-1]
        for alias in node.names:
            if alias.name == "*":
                continue
            bind = alias.asname or alias.name
            binding = (module, alias.name)
            previous = binds.get(bind)
            if previous is not None and previous != binding:
                ambiguous.add(bind)
            else:
                binds[bind] = binding
    for bind in ambiguous | (shadowed & binds.keys()):
        binds[bind] = None
    return binds
def _record_plain_import_binds(node: ast.Import, imps: set) -> None:
    for alias in node.names:
        imps.add(alias.name.split(".")[-1])
        if alias.asname:
            imps.add(alias.asname)
        elif "." in alias.name:
            imps.add(alias.name.split(".")[0])
def _function_definition_exprs(node):
    yield from iter_def_site_nodes(node)
    for type_param in getattr(node, "type_params", None) or ():
        for attr in ("bound", "default"):
            expression = getattr(type_param, attr, None)
            if expression is not None:
                yield expression
def _iter_definition_expr_nodes(node):
    stack = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, ast.Lambda):
            stack.extend(iter_def_site_nodes(cur))
            continue
        yield cur
        stack.extend(ast.iter_child_nodes(cur))
def _definition_expr_node_ids(node) -> frozenset:
    return frozenset(
        id(sub)
        for expr in _function_definition_exprs(node)
        for sub in _iter_definition_expr_nodes(expr))
def _definition_time_ref_names(node) -> set:
    refs = set()
    for expr in _function_definition_exprs(node):
        attribute_part_ids = _dotted_attribute_part_ids(expr)
        for sub in _iter_definition_expr_nodes(expr):
            if id(sub) in attribute_part_ids:
                continue
            ref = _scope_load_ref(sub)
            if ref is not None:
                refs.add(ref)
    return refs
def _scan_module_refs(tree) -> tuple:
    state = _collect_scan_state(tree)
    return (state.defs, state.imps, state.raw_by_id, state.name_by_id,
            state.dup_names)
def _resolve_ref_names(names, ctx: _RefResolveContext):
    edges = set()
    for ref in names:
        edge = (_resolve_attribute_ref(ref, ctx) if isinstance(ref, tuple)
                else _resolve_ref_name(ref, ctx))
        if edge is not None:
            edges.add(edge)
    return edges
def _import_from_module_pairs(node: ast.ImportFrom) -> list:
    module_tail = node.module.split(".")[-1]
    return [(alias.asname or alias.name, module_tail)
            for alias in node.names if alias.name != "*"]
def _import_from_relative_pairs(node: ast.ImportFrom) -> list:
    return [(alias.asname or alias.name, alias.name)
            for alias in node.names if alias.name != "*"]
def _import_module_pairs(node: ast.Import) -> list:
    return [(alias.asname or alias.name.split(".")[0],
             alias.name.split(".")[-1])
            for alias in node.names]
def _reexport_binding_pairs(node) -> list:
    if isinstance(node, ast.ImportFrom):
        if node.module:
            return _import_from_module_pairs(node)
        if node.level:
            return _import_from_relative_pairs(node)
        return []
    if isinstance(node, ast.Import):
        return _import_module_pairs(node)
    return []
class _ReexportMap(dict[str, str]):
    def __init__(self) -> None:
        super().__init__()
        self.origins: dict[str, str] = {}
def _bind_reexport_aliases(tree) -> dict:
    direct_ids = {
        id(stmt) for stmt in getattr(tree, "body", ())
        if isinstance(stmt, (ast.Import, ast.ImportFrom))
    }
    direct: list = []
    fallback: list = []
    for node in walk_nodes(tree):
        pairs = _reexport_binding_pairs(node)
        if not pairs:
            continue
        originals = ({
            alias.asname or alias.name: alias.name
            for alias in node.names if alias.name != "*"
        } if isinstance(node, ast.ImportFrom) else {})
        pos = (getattr(node, "lineno", 0), getattr(node, "col_offset", 0))
        bucket = direct if id(node) in direct_ids else fallback
        bucket.extend(
            (pos, key, value, originals.get(key)) for key, value in pairs)
    reexport = _ReexportMap()
    for _pos, key, value, original in sorted(direct):
        reexport[key] = value
        reexport.origins.pop(key, None)
        if original is not None:
            reexport.origins[key] = original
    for _pos, key, value, original in sorted(fallback):
        if key in reexport:
            continue
        reexport[key] = value
        if original is not None:
            reexport.origins[key] = original
    return reexport
def load_reexport_map(skill_dir: str, cache=None) -> dict:
    _package_name, package_root, _import_root = resolve_project_package(
        skill_dir)
    if not package_root:
        return {}
    init_path = os.path.join(package_root, "__init__.py")
    if not os.path.isfile(init_path):
        return {}
    tree = read_source_tree(init_path, cache)
    if tree is None:
        return {}
    return _bind_reexport_aliases(tree)
def _detect_ambiguous_modules(py_files: list, skill_dir: str) -> tuple[dict, set]:
    mod_of: dict = {}
    mod_counts: dict = {}
    for _fp in py_files:
        _mod = module_name_for_path(
            os.path.relpath(_fp, skill_dir), skill_dir)
        mod_of[_fp] = _mod
        mod_counts[_mod] = mod_counts.get(_mod, 0) + 1
    ambiguous_mods = {m for m, c in mod_counts.items() if c > 1}
    return mod_of, ambiguous_mods
def _collect_mod_refs(py_files: list, skill_dir: str, mod_of: dict,
                      ambiguous_mods: set, mod_refs_by_rel: dict, cache) -> tuple[dict, dict, list]:
    mod_func_defs = {}
    name_to_unique_mods: dict = {}
    mod_refs_seq: list = []
    for filepath in py_files:
        mod = mod_of[filepath]
        if mod in ambiguous_mods:
            continue
        rel_path = os.path.relpath(filepath, skill_dir)
        refs = mod_refs_by_rel.get(rel_path)
        if refs is not None:
            defs, imps, raw_by_id, name_by_id, dup_names, scan_tree = refs[:6]
            from_import_binds = (refs[6] if len(refs) > 6
                                 else _from_import_ref_binds(scan_tree))
        else:
            scan_tree = read_source_tree(filepath, cache)
            if scan_tree is None:
                continue
            defs, imps, raw_by_id, name_by_id, dup_names = (
                _scan_module_refs(scan_tree))
            from_import_binds = _from_import_ref_binds(scan_tree)
        mod_func_defs[mod] = defs
        for fname, cnt in defs.items():
            if cnt == 1:
                name_to_unique_mods.setdefault(fname, set()).add(mod)
        mod_refs_seq.append(
            (mod, defs, imps, raw_by_id, name_by_id, dup_names, scan_tree,
             from_import_binds))
    return mod_func_defs, name_to_unique_mods, mod_refs_seq
def _dup_groups(name_by_id: dict) -> dict:
    groups: dict = defaultdict(list)
    for nid, fname in name_by_id.items():
        groups[fname].append(nid)
    return groups
def _ordered_dup_last_defs(tree, need_order: set,
                           raw_by_id: dict) -> dict:
    last_by_name: dict = {}
    if need_order and tree is not None:
        for node in walk_nodes(tree):
            if not _is_orderable_dup_def(node, need_order, raw_by_id):
                continue
            rec = last_by_name.get(node.name)
            position = (node.lineno, node.col_offset)
            if rec is None or position > (rec[1], rec[2]):
                last_by_name[node.name] = (id(node), *position)
        last_by_name = {name: rec[0] for name, rec in last_by_name.items()}
    return last_by_name
def _is_orderable_dup_def(node, need_order: set, raw_by_id: dict) -> bool:
    return (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            and node.name in need_order
            and id(node) in raw_by_id)
def _order_needed_names(groups: dict, dup_names: set,
                        raw_by_id: dict) -> set:
    need_order: set = set()
    for fname, nids in groups.items():
        if fname in dup_names:
            ref_sets = [raw_by_id[n] for n in nids]
            if not all(s == ref_sets[0] for s in ref_sets):
                need_order.add(fname)
    return need_order
def _resolve_dup_group(fname: str, nids: list, ctx: _RefResolveContext,
                       last_by_name: dict) -> set:
    ref_sets = [ctx.raw_by_id[n] for n in nids]
    if all(s == ref_sets[0] for s in ref_sets):
        return _resolve_ref_names(ref_sets[0], ctx)
    nid = last_by_name.get(fname)
    return (_resolve_ref_names(ctx.raw_by_id[nid], ctx)
            if nid is not None else set())
def _build_mod_ref_graph(mod_refs_seq: list, name_to_unique_mods: dict,
                         pkg: str = "", reexport: dict | None = None,
                         mod_func_defs: dict | None = None) -> dict:
    mod_graph: dict = {}
    for record in mod_refs_seq:
        (mod, defs, imps, raw_by_id, name_by_id, dup_names,
         scan_tree) = record[:7]
        from_import_binds = (record[7] if len(record) > 7
                             else _from_import_ref_binds(scan_tree))
        ctx = _RefResolveContext(
            mod, defs, imps, raw_by_id, name_to_unique_mods,
            from_import_binds, pkg, reexport or {}, mod_func_defs or {})
        if dup_names:
            mod_graph[mod] = _ref_graph_with_dup(
                ctx, name_by_id, dup_names, scan_tree)
        else:
            mod_graph[mod] = _ref_graph_without_dup(ctx, name_by_id)
    return mod_graph
def _ref_graph_without_dup(ctx: _RefResolveContext, name_by_id: dict) -> dict:
    return {
        fname: _resolve_ref_names(ctx.raw_by_id[nid], ctx)
        for nid, fname in name_by_id.items()
    }
def _ref_graph_with_dup(ctx: _RefResolveContext, name_by_id: dict,
                        dup_names: set, scan_tree) -> dict:
    groups = _dup_groups(name_by_id)
    need_order = _order_needed_names(groups, dup_names, ctx.raw_by_id)
    last_by_name = _ordered_dup_last_defs(
        scan_tree if need_order else None, need_order, ctx.raw_by_id)
    graph = {}
    for fname, nids in groups.items():
        if fname not in dup_names:
            graph[fname] = _resolve_ref_names(ctx.raw_by_id[nids[0]], ctx)
            continue
        graph[fname] = _resolve_dup_group(fname, nids, ctx, last_by_name)
    return graph
@dataclass(frozen=True, slots=True)
class _AssertResolveContext:
    pkg: str
    reexport: dict
    mod_func_defs: dict
    src_mod_names: set
def _resolve_assert_entries(test_index: list, ctx: _AssertResolveContext,
                            module_assert_imports: set) -> set:
    entries: set = set()
    for ti in test_index:
        if not ti.get("has_assert_global"):
            continue
        module_assert_imports.update(ti.get("module_keys", ()))
        name_to_mods = ti.get("name_to_mods", {})
        aliases = ti.get("module_aliases", {})
        star_mods = ti.get("star_modules", set())
        for n in ti.get("called_names_with_assert", ()):
            entries.update(_resolve_name_entries(
                n, ctx, name_to_mods, star_mods,
                ti.get("from_pkg_binds"),
                ti.get("local_bind_names")))
        for chain in ti.get("asserted_attr_chains", ()):
            entries.update(_resolve_chain_entries(
                chain, ctx, aliases, name_to_mods,
                ti.get("from_pkg_binds")))
    return entries
def build_kill_closure(py_files: list, skill_dir: str,
                        mod_refs_by_rel: dict, cache, reexport: dict,
                        test_index: list) -> tuple[set, set, set]:
    kill_closure = set()
    module_assert_imports = set()
    if not test_index:
        return kill_closure, module_assert_imports, set()
    package_name, _package_root, _import_root = resolve_project_package(
        skill_dir)
    pkg = package_name or os.path.basename(os.path.normpath(skill_dir))
    mod_of, ambiguous_mods = _detect_ambiguous_modules(py_files, skill_dir)
    mod_func_defs, name_to_unique_mods, mod_refs_seq = _collect_mod_refs(
        py_files, skill_dir, mod_of, ambiguous_mods, mod_refs_by_rel, cache)
    mod_graph = _build_mod_ref_graph(
        mod_refs_seq, name_to_unique_mods, pkg, reexport, mod_func_defs)
    assert_ctx = _AssertResolveContext(
        pkg, reexport, mod_func_defs, set(mod_func_defs))
    entries = _resolve_assert_entries(
        test_index, assert_ctx, module_assert_imports)
    closure = set(entries)
    frontier = set(entries)
    while frontier:
        nxt = set()
        for (m, f) in frontier:
            for edge in mod_graph.get(m, {}).get(f, ()):
                if edge not in closure:
                    closure.add(edge)
                    nxt.add(edge)
        frontier = nxt
    kill_closure = closure
    return kill_closure, module_assert_imports, ambiguous_mods
def _star_import_candidates(n: str, ctx: _AssertResolveContext,
                            star_mods: set) -> set:
    candidates: set = set()
    for sm in star_mods:
        if sm == ctx.pkg:
            candidates |= _from_import_entry(ctx.pkg, n, ctx)
        elif ctx.mod_func_defs.get(sm, {}).get(n) == 1:
            candidates.add((sm, n))
    return candidates
def _resolve_name_entries(n: str, ctx: _AssertResolveContext,
                          name_to_mods: dict, star_mods: set,
                          from_pkg_binds: dict | None = None,
                          local_bind_names=None) -> set:
    out: set = set()
    if local_bind_names and n in local_bind_names:
        return out
    orig = (from_pkg_binds or {}).get(n, n)
    mods = name_to_mods.get(n)
    if mods:
        if len(mods) > 1:
            return out
        for m in mods:
            out |= _from_import_entry(m, orig, ctx)
    else:
        candidates = _star_import_candidates(n, ctx, star_mods)
        if len(candidates) == 1:
            out.update(candidates)
    return out
def _reexport_origin(reexport: dict, bound: str) -> str:
    return getattr(reexport, "origins", {}).get(bound, bound)
def _from_import_entry(m: str, orig: str, ctx: _AssertResolveContext) -> set:
    if m == ctx.pkg:
        m2 = ctx.reexport.get(orig)
        original = _reexport_origin(ctx.reexport, orig)
        if m2 and ctx.mod_func_defs.get(m2, {}).get(original) == 1:
            return {(m2, original)}
        if ctx.mod_func_defs.get(ctx.pkg, {}).get(orig) == 1:
            return {(ctx.pkg, orig)}
        return set()
    if ctx.mod_func_defs.get(m, {}).get(orig) == 1:
        return {(m, orig)}
    return set()
def _resolve_chain_root(parts: list, aliases: dict, name_to_mods: dict,
                        ctx: _AssertResolveContext,
                        from_pkg_binds: dict | None) -> tuple:
    if parts[0] in aliases:
        return aliases[parts[0]], 1
    if name_to_mods.get(parts[0]) == {ctx.pkg}:
        bound = (from_pkg_binds or {}).get(parts[0])
        if bound is not None and bound in ctx.src_mod_names:
            return bound, 1
        return ctx.pkg, 1
    return None, 0
def _resolve_chain_entries(chain: str, ctx: _AssertResolveContext,
                           aliases: dict, name_to_mods: dict,
                           from_pkg_binds: dict | None = None) -> set:
    out: set = set()
    parts = chain.split(".")
    m, i = _resolve_chain_root(
        parts, aliases, name_to_mods, ctx, from_pkg_binds)
    if m is None:
        return out
    if m == ctx.pkg and len(parts) >= i + 1:
        _head = _pkg_chain_head(parts, i, ctx, out)
        if _head is None:
            return out
        m, i = _head
    rest = parts[i:]
    if len(rest) == 1 and ctx.mod_func_defs.get(m, {}).get(rest[0]) == 1:
        out.add((m, rest[0]))
    return out
def _pkg_chain_head(parts: list, i: int, ctx: _AssertResolveContext,
                    out: set) -> tuple[str, int] | None:
    cand = parts[i]
    m2 = ctx.reexport.get(cand)
    via_reexport = m2 is not None
    if m2 is None and cand in ctx.src_mod_names:
        m2 = cand
    if m2 is not None:
        original = _reexport_origin(ctx.reexport, cand)
        if (i + 1 == len(parts) and via_reexport
                and ctx.mod_func_defs.get(m2, {}).get(original) == 1):
            out.add((m2, original))
        return m2, i + 1
    if len(parts) - i == 1 and \
            ctx.mod_func_defs.get(ctx.pkg, {}).get(parts[i]) == 1:
        out.add((ctx.pkg, parts[i]))
    return None
def _ti_layer1_killed(ti, target_module: str, target_func: str) -> bool:
    hit = _bound_call_name(ti, target_func)
    if hit is None:
        return False
    return _unique_owner_module(ti, hit) == target_module
def _bound_call_name(ti, target_func: str) -> str | None:
    call_names = ti.get("called_names_with_assert", ())
    if target_func in call_names:
        return target_func
    for bound_name, orig_name in (ti.get("from_pkg_binds") or {}).items():
        if orig_name == target_func and bound_name in call_names:
            return bound_name
    return None
def _unique_owner_module(ti, call_name: str) -> str | None:
    mods_of = ti.get("name_to_mods", {}).get(call_name) or ()
    if len(mods_of) != 1:
        return None
    return next(iter(mods_of))
def _ti_layer2_killed(ti, target_module: str,
                      submodule_binds: set) -> bool:
    return bool(
        ti.get("has_assert_global")
        and (target_module in ti.get("module_keys", ())
             or target_module in submodule_binds))
def _ti_dispatch_killed(ti_iter, target_module: str, target_func: str,
                        submodule_binds: set) -> bool:
    for ti in ti_iter:
        if not _ti_has_import_evidence(ti, target_module, submodule_binds):
            continue
        if target_func:
            if _ti_layer1_killed(ti, target_module, target_func):
                return True
        elif _ti_layer2_killed(ti, target_module, submodule_binds):
            return True
    return False
def _ti_has_import_evidence(ti, target_module: str,
                            submodule_binds=_EMPTY_SUBMODULE_BINDS) -> bool:
    if target_module in ti.get("imports", ()):
        return True
    bind_pkgs = ti.get("from_bind_pkgs") or {}
    if target_module in submodule_binds and target_module in bind_pkgs:
        return True
    return any(target_module in (mods or ())
               for mods in bind_pkgs.values())
def build_ti_by_module(test_index: list,
                       submodule_binds=_EMPTY_SUBMODULE_BINDS) -> dict:
    by_mod: dict = defaultdict(list)
    for ti in test_index:
        imports = ti.get("imports", ())
        seen_mods = set(imports)
        for mod in seen_mods:
            by_mod[mod].append(ti)
        for name, mods in (ti.get("from_bind_pkgs") or {}).items():
            if name in submodule_binds and name not in seen_mods:
                seen_mods.add(name)
                by_mod[name].append(ti)
            for mod in mods or ():
                if mod in seen_mods:
                    continue
                seen_mods.add(mod)
                by_mod[mod].append(ti)
    return by_mod
def module_name_for_path(rel_file: str, skill_dir: str) -> str:
    stem = os.path.splitext(os.path.basename(rel_file))[0]
    if stem != "__init__":
        return stem
    file_dir = os.path.dirname(rel_file)
    return (os.path.basename(file_dir) if file_dir
            else os.path.basename(os.path.normpath(skill_dir)))
def _closure_killed(target_module: str, target_func: str,
                    closure: set, module_assert_imports: set) -> bool:
    if target_func and closure and (target_module, target_func) in closure:
        return True
    return bool(not target_func and module_assert_imports
                and target_module in module_assert_imports)
def _test_entries_for_module(ti_by_module: dict, ti_src, test_index: list,
                             target_module: str):
    if ti_by_module and ti_src is test_index:
        return ti_by_module.get(target_module, ())
    return test_index
def check_static_survival(
    target: MutationTarget,
    skill_dir: str,
    closure_evidence: ClosureEvidence,
    ti_by_module: dict,
    ti_src: list | None,
    submodule_binds: set,
    test_index: list,
) -> bool:
    kill_closure = closure_evidence.kill_closure
    module_assert_imports = closure_evidence.module_assert_imports
    ambiguous_mods = closure_evidence.ambiguous_mods
    ambiguous_funcs = closure_evidence.ambiguous_funcs
    target_module = module_name_for_path(target.file, skill_dir)
    target_func = target.func_name
    if ambiguous_mods and target_module in ambiguous_mods:
        return True
    if target_func and (target_module, target_func) in ambiguous_funcs:
        return True
    if _closure_killed(target_module, target_func, kill_closure,
                       module_assert_imports):
        return False
    ti_iter = _test_entries_for_module(
        ti_by_module, ti_src, test_index, target_module)
    return not _ti_dispatch_killed(ti_iter, target_module, target_func,
                                   submodule_binds)
